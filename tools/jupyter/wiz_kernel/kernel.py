"""The Wiz Jupyter kernel.

A single-threaded message loop over the five sockets of the connection file
(shell, iopub, control, stdin, heartbeat; heartbeat in its own thread), with the
wire protocol of :mod:`wiz_kernel.wire` and the drivers of
:mod:`wiz_kernel.backends`.  There is no Jupyter dependency: ``pyzmq`` is the only
third-party import.
"""

from __future__ import annotations

import json
import os
import re
import subprocess
import threading
import traceback

from . import __version__
from .backends import (Backend, BackendError, BackendUnavailable, CellResult,
                       ErrorReport, Stream, make_backend)
from .magics import handle_magic
from .widgets import (MIME, PREFIX, SCHEMA, TARGET, WidgetError, WidgetManager,
                      decode_eval_text, mime_bundle, parse_display, plain_summary)
from .progress import COMM_TARGET, ProgressChannel
from .wire import Message, Session, WireError, iopub_topic

try:  # the kernel is useless without it, but `--self-test` explains that cleanly
    import zmq
except ImportError:  # pragma: no cover - exercised by the tests' skip path
    zmq = None


BANNER = """Wiz kernel {version}

Wiz is a didactic dependently typed language (https://wiz-pl.github.io/wiz/).
Cells keep their definitions; magics are %%scry (C taint analysis), %%sh (shell),
%%time (wall clock and peak RSS), %%wiz, %backend and %progress.  `wiz check`
reports, not runs: a bare final expression becomes the cell's result.  `Web.Widget`
displays render as an interactive MIME bundle (`application/vnd.wiz.widget+json`)
over a comm.
"""


class Kernel:
    def __init__(self, connection_file: str, *, backend: str = "auto",
                 wiz: str | None = None, cwd: str | None = None,
                 toolchain_args: list[str] | None = None):
        if zmq is None:
            raise RuntimeError("pyzmq is not installed (`pip install pyzmq`)")
        with open(connection_file, encoding="utf-8") as handle:
            self.connection = json.load(handle)
        key = self.connection.get("key", "")
        scheme = self.connection.get("signature_scheme") or "hmac-sha256"
        self.session = Session(key=key, scheme=scheme)
        self.cwd = os.path.abspath(cwd or os.getcwd())
        self.backend_kind = backend
        self.wiz = wiz
        self.toolchain_args = list(toolchain_args or [])
        self.backend: Backend | None = None
        self.widgets = WidgetManager(self.backend)
        self.progress = ProgressChannel(publish=self.publish, stream=self.stream)
        self.fallback_reason: str | None = None
        self.backend_error: str | None = None
        self.execution_count = 0
        self.running = True
        self._announced_backend = False
        self._hb_thread: threading.Thread | None = None
        self._hb_stop = threading.Event()
        self.wiz_version = self._wiz_version()
        self.context = zmq.Context.instance()
        self.shell = self._socket(zmq.ROUTER)
        self.control = self._socket(zmq.ROUTER)
        self.stdin = self._socket(zmq.ROUTER)
        self.iopub = self._socket(zmq.PUB)
        self._connect()

    # -- sockets ---------------------------------------------------------

    def _socket(self, kind: int):
        socket = self.context.socket(kind)
        socket.setsockopt(zmq.LINGER, 0)
        return socket

    def _address(self, port_key: str) -> str:
        transport = self.connection.get("transport", "tcp")
        ip = self.connection.get("ip", "127.0.0.1")
        port = self.connection[port_key]
        return f"{transport}://{ip}:{port}"

    def _connect(self) -> None:
        self.shell.bind(self._address("shell_port"))
        self.control.bind(self._address("control_port"))
        self.stdin.bind(self._address("stdin_port"))
        self.iopub.bind(self._address("iopub_port"))

    def _wiz_version(self) -> str:
        try:
            from .backends import find_wiz
            executable = find_wiz(self.wiz)
            if executable is None:
                return "unknown"
            done = subprocess.run([executable, "--version"], capture_output=True,
                                  text=True, timeout=10)
            text = (done.stdout or "").strip().splitlines()
            return text[0].strip() if text else "unknown"
        except (OSError, subprocess.SubprocessError):
            return "unknown"

    # -- startup ---------------------------------------------------------

    def start(self) -> None:
        self._start_heartbeat()
        try:
            self.backend, self.fallback_reason = make_backend(
                self.backend_kind, self.wiz, self.cwd, self.toolchain_args)
        except BackendUnavailable as exc:
            self.backend_error = str(exc)
        self.widgets.backend = self.backend
        self.publish("status", {"execution_state": "starting"})
        self.loop()

    def _start_heartbeat(self) -> None:
        def beat() -> None:
            socket = self.context.socket(zmq.REP)
            socket.setsockopt(zmq.LINGER, 0)
            try:
                socket.bind(self._address("hb_port"))
            except zmq.ZMQError:
                return
            poller = zmq.Poller()
            poller.register(socket, zmq.POLLIN)
            while not self._hb_stop.is_set():
                events = dict(poller.poll(200))
                if socket in events:
                    try:
                        socket.send(socket.recv())
                    except zmq.ZMQError:
                        break
            socket.close(0)

        self._hb_thread = threading.Thread(target=beat, name="wiz-kernel-heartbeat",
                                           daemon=True)
        self._hb_thread.start()

    # -- sending ---------------------------------------------------------

    def send(self, socket, msg_type: str, content: dict, *,
             parent: dict | None = None, identities=None) -> None:
        frames = self.session.serialize(msg_type, content, parent=parent,
                                        identities=identities or [])
        socket.send_multipart(frames)

    def publish(self, msg_type: str, content: dict, *, parent: dict | None = None,
                metadata: dict | None = None) -> None:
        frames = self.session.serialize(msg_type, content, parent=parent,
                                        metadata=metadata,
                                        identities=[iopub_topic(msg_type)])
        self.iopub.send_multipart(frames)

    def reply(self, socket, msg: Message, msg_type: str, content: dict) -> None:
        self.send(socket, msg_type, content, parent=msg.header,
                  identities=msg.identities)

    def stream(self, name: str, text: str, parent: dict | None = None) -> None:
        if text:
            self.publish("stream", {"name": name, "text": text}, parent=parent)

    # -- the loop --------------------------------------------------------

    def loop(self) -> None:
        poller = zmq.Poller()
        poller.register(self.shell, zmq.POLLIN)
        poller.register(self.control, zmq.POLLIN)
        while self.running:
            try:
                events = dict(poller.poll(200))
            except zmq.ZMQError:
                break
            for socket in (self.shell, self.control):
                if socket not in events:
                    continue
                try:
                    frames = socket.recv_multipart()
                    msg = self.session.deserialize(frames)
                except (WireError, zmq.ZMQError):
                    traceback.print_exc()
                    continue
                try:
                    self.dispatch(socket, msg)
                except Exception:  # keep the kernel alive after a handler bug
                    traceback.print_exc()
                    if msg.msg_type.endswith("_request"):
                        self.reply(socket, msg, msg.msg_type[:-len("_request")] + "_reply",
                                   {"status": "error", "ename": "KernelError",
                                    "evalue": "internal error (see the kernel's stderr)",
                                    "traceback": traceback.format_exc().splitlines()})

    def dispatch(self, socket, msg: Message) -> None:
        """Wrap every request in iopub `status: busy`/`idle`.

        A client that connects late (after `starting` was published and lost to
        ZeroMQ's slow joiner) otherwise sees no iopub traffic at all while
        `kernel_info_request` is answered, and `wait_for_ready`'s iopub check spins
        until its timeout.  ipykernel brackets its requests the same way.
        """
        is_request = msg.msg_type.endswith("_request")
        if is_request:
            self.publish("status", {"execution_state": "busy"}, parent=msg.header)
        try:
            self.handle(socket, msg)
        finally:
            if is_request:
                self.publish("status", {"execution_state": "idle"}, parent=msg.header)

    def handle(self, socket, msg: Message) -> None:
        kind = msg.msg_type
        if kind == "kernel_info_request":
            self.handle_kernel_info(socket, msg)
        elif kind == "execute_request":
            self.handle_execute(socket, msg)
        elif kind == "is_complete_request":
            self.handle_is_complete(socket, msg)
        elif kind == "complete_request":
            self.reply(socket, msg, "complete_reply", {
                "status": "ok", "matches": [], "cursor_start": msg.content.get("cursor_pos", 0),
                "cursor_end": msg.content.get("cursor_pos", 0), "metadata": {}})
        elif kind == "inspect_request":
            self.reply(socket, msg, "inspect_reply",
                       {"status": "ok", "found": False, "data": {}, "metadata": {}})
        elif kind == "history_request":
            self.reply(socket, msg, "history_reply", {"status": "ok", "history": []})
        elif kind == "comm_info_request":
            comms = self.widgets.info()
            if self.progress.comm_id:
                comms[self.progress.comm_id] = {"target_name": COMM_TARGET}
            self.reply(socket, msg, "comm_info_reply", {"status": "ok", "comms": comms})
        elif kind == "comm_open":
            content = msg.content or {}
            if content.get("target_name") == COMM_TARGET:
                self.progress.attach_comm(content.get("comm_id", ""))
            else:
                self.handle_comm_open(msg)
        elif kind == "comm_msg":
            content = msg.content or {}
            if content.get("comm_id") and content["comm_id"] == self.progress.comm_id:
                data = content.get("data") or {}
                if isinstance(data, dict) and data.get("method") == "close":
                    self.progress.detach_comm(content["comm_id"])
            else:
                self.handle_comm_msg(msg)
        elif kind == "comm_close":
            comm_id = (msg.content or {}).get("comm_id", "")
            if comm_id and comm_id == self.progress.comm_id:
                self.progress.detach_comm(comm_id)
            else:
                self.handle_comm_close(msg)
        elif kind == "connect_request":
            self.reply(socket, msg, "connect_reply", {
                "status": "ok",
                "shell_port": self.connection["shell_port"],
                "iopub_port": self.connection["iopub_port"],
                "stdin_port": self.connection["stdin_port"],
                "hb_port": self.connection["hb_port"],
                "control_port": self.connection["control_port"],
            })
        elif kind == "interrupt_request":
            # `interrupt_mode` is "message" in the kernelspec, so Jupyter asks here
            # instead of sending a signal.  The Wiz child is not interrupted: say so.
            self.reply(socket, msg, "interrupt_reply", {"status": "ok"})
            self.stream("stderr", "interrupt: not implemented; the Wiz process is still "
                                  "running the cell\n", parent=msg.header)
        elif kind == "shutdown_request":
            restart = bool(msg.content.get("restart", False))
            self.reply(socket, msg, "shutdown_reply", {"status": "ok", "restart": restart})
            self.running = False
        else:
            # Unknown requests are not answered: a client is not waiting for a reply to
            # a message it did not send.  (Completion, inspection and the debug
            # protocol are intentionally absent.)
            pass

    def handle_kernel_info(self, socket, msg: Message) -> None:
        backend_name = self.backend.name if self.backend is not None else "unavailable"
        banner = BANNER.format(version=__version__)
        banner += f"\nbackend: {backend_name}\n"
        if self.backend_error:
            banner += f"backend error: {self.backend_error}\n"
        self.reply(socket, msg, "kernel_info_reply", {
            "status": "ok",
            "protocol_version": "5.3",
            "implementation": "wiz-kernel",
            "implementation_version": __version__,
            "language_info": {
                "name": "wiz",
                "version": self.wiz_version,
                "mimetype": "text/x-wiz",
                "file_extension": ".wiz",
                "pygments_lexer": "text",
                "codemirror_mode": "text",
            },
            "banner": banner,
            "help_links": [
                {"text": "Wiz documentation", "url": "https://wiz-pl.github.io/wiz/docs/"},
                {"text": "Jupyter kernel source",
                 "url": "https://github.com/wiz-pl/wiz/tree/master/tools/jupyter"},
            ],
            "metadata": {"wiz_backend": backend_name,
                         "wiz_widgets": {"mime": MIME, "comm": TARGET}},
        })

    def handle_is_complete(self, socket, msg: Message) -> None:
        code = msg.content.get("code", "")
        self.reply(socket, msg, "is_complete_reply", {"status": is_complete(code)})

    # -- execution -------------------------------------------------------

    def handle_execute(self, socket, msg: Message) -> None:
        content = msg.content or {}
        code = content.get("code", "") or ""
        silent = bool(content.get("silent", False))
        store_history = bool(content.get("store_history", not silent))
        if store_history:
            self.execution_count += 1
        count = self.execution_count
        parent = msg.header
        if not silent:
            self.publish("execute_input", {"code": code, "execution_count": count},
                         parent=parent)
            if not self._announced_backend:
                self._announced_backend = True
                self.stream("stderr", self._backend_notice(), parent=parent)
        result = self._run_cell(code, parent)
        self.progress.finish()
        for bundle in result.comms:
            self.publish("comm_open", {
                "comm_id": bundle["comm_id"],
                "target_name": TARGET,
                "data": bundle,
            }, parent=parent)
        for stream in result.streams:
            self.stream(stream.name, stream.text, parent=parent)
        for error in result.errors:
            self.publish("error", {"ename": error.ename, "evalue": error.evalue,
                                   "traceback": error.traceback}, parent=parent)
        if not result.errors and result.result is not None and not silent:
            data = result.data or {"text/plain": result.result}
            self.publish("execute_result", {"execution_count": count, "data": data,
                                            "metadata": result.metadata or {}},
                         parent=parent)
        if result.errors:
            first = result.errors[0]
            self.reply(socket, msg, "execute_reply", {
                "status": "error", "execution_count": count,
                "ename": first.ename, "evalue": first.evalue,
                "traceback": first.traceback, "payload": [],
            })
        else:
            self.reply(socket, msg, "execute_reply", {
                "status": "ok", "execution_count": count, "payload": [],
                "user_expressions": {},
            })

    def _backend_notice(self) -> str:
        if self.backend_error:
            return f"wiz kernel: no backend: {self.backend_error}\n"
        assert self.backend is not None
        notice = f"wiz kernel: backend {self.backend.name}"
        if self.fallback_reason:
            notice += f" (`wiz repl` unavailable: {self.fallback_reason})"
        return notice + "\n"

    def _run_cell(self, code: str, parent: dict | None = None) -> CellResult:
        if self.backend is None:
            message = self.backend_error or "no backend"
            return CellResult(errors=[ErrorReport(
                "BackendUnavailable",
                "no Wiz backend: " + message,
                ["no Wiz backend: " + message])])
        try:
            self.progress.parent = parent
            magic = handle_magic(code, self.backend, fallback_reason=self.fallback_reason,
                                 cwd=self.cwd, wiz=self.wiz, progress=self.progress,
                                 emit=lambda name, text: self.stream(name, text,
                                                                     parent=parent))
            if magic is not None:
                return self._attach_widgets(magic)
            result = self.backend.execute(code)
            return self._attach_widgets(result)
        except BackendError as exc:
            return CellResult(errors=[ErrorReport("BackendError", str(exc), [str(exc)])])
        except Exception as exc:  # a broken cell must not kill the kernel
            trace = traceback.format_exc().splitlines()
            return CellResult(errors=[ErrorReport(type(exc).__name__, str(exc), trace)])

    def _attach_widgets(self, result: CellResult) -> CellResult:
        """Turn a `WIZ_WIDGET:` result (or stream line) into a MIME bundle + comm.

        `Widget.display` is a pure String, so it arrives either as the cell's last
        expression (`result.result`) or from an explicit `#eval` (a stream).  One
        display per cell is supported; a second is a stream note, not a second
        execute_result (Jupyter has one per request).
        """
        if result.errors:
            return result
        found: list[dict] = []
        if result.result is not None:
            bundle = parse_display(decode_eval_text(result.result))
            if bundle is not None:
                found.append(bundle)
        for stream in result.streams:
            if PREFIX not in stream.text:
                continue
            kept = []
            for line in stream.text.splitlines(keepends=True):
                bundle = parse_display(decode_eval_text(line))
                if bundle is not None:
                    found.append(bundle)
                else:
                    kept.append(line)
            stream.text = "".join(kept)
        if not found:
            return result
        if len(found) > 1:
            result.streams.append(Stream("stderr", "widget: only the last of "
                                         f"{len(found)} displays in one cell is shown\n"))
        opened = self.widgets.open(found[-1])
        result.comms.append(opened)
        result.data = mime_bundle(opened)
        result.result = plain_summary(opened)
        return result

    # -- comms -----------------------------------------------------------

    def handle_comm_open(self, msg: Message) -> None:
        """Adopt a comm a front end opened (a notebook reconnecting to a display)."""
        content = msg.content or {}
        if content.get("target_name") != TARGET:
            return
        data = content.get("data")
        if isinstance(data, dict) and data.get("schema") == SCHEMA:
            self.widgets.adopt(content.get("comm_id", ""), data)

    def handle_comm_msg(self, msg: Message) -> None:
        content = msg.content or {}
        comm_id = content.get("comm_id", "")
        data = content.get("data") or {}
        if not comm_id:
            return
        if isinstance(data, dict) and data.get("method") == "close":
            self.handle_comm_close(msg)
            return
        try:
            bundle = self.widgets.event(comm_id, data if isinstance(data, dict) else {})
        except WidgetError as exc:
            self.publish("comm_msg", {
                "comm_id": comm_id,
                "data": {"method": "error", "error": str(exc)},
            }, parent=msg.header)
            return
        except Exception as exc:  # a broken callback must not kill the kernel
            traceback.print_exc()
            self.publish("comm_msg", {
                "comm_id": comm_id,
                "data": {"method": "error",
                         "error": f"widget evaluation failed: {type(exc).__name__}: {exc}"},
            }, parent=msg.header)
            return
        self.publish("comm_msg", {
            "comm_id": comm_id,
            "data": {"method": "update", "bundle": bundle,
                     "patches": bundle.get("patches", [])},
        }, parent=msg.header)

    def handle_comm_close(self, msg: Message) -> None:
        comm_id = (msg.content or {}).get("comm_id", "")
        if not comm_id:
            return
        self.widgets.close(comm_id)
        self.publish("comm_close", {"comm_id": comm_id, "data": {}}, parent=msg.header)

    # -- shutdown --------------------------------------------------------

    def close(self) -> None:
        self.running = False
        self._hb_stop.set()
        for comm_id in list(self.widgets.comms):
            try:
                self.publish("comm_close", {"comm_id": comm_id, "data": {}})
            except Exception:
                pass
        self.widgets.comms.clear()
        if self._hb_thread is not None:
            self._hb_thread.join(timeout=2)
        if self.backend is not None:
            try:
                self.backend.close()
            except Exception:
                traceback.print_exc()
        for socket in (self.shell, self.control, self.stdin, self.iopub):
            try:
                socket.close(0)
            except Exception:
                pass
        try:
            self.context.term()
        except Exception:
            pass


def is_complete(code: str) -> str:
    """A heuristic for Jupyter's `is_complete_request`.

    The REPL driver can execute a multi-line cell (it `:load`s the cell as a file),
    so the answer only decides whether a frontend should submit on Enter.  It says
    ``incomplete`` while brackets are open or the last line ends in a token that
    needs more input, and ``complete`` otherwise.  It does not parse Wiz.
    """
    if not code.strip():
        return "complete"
    depth = 0
    in_string = False
    escaped = False
    index = 0
    while index < len(code):
        char = code[index]
        if in_string:
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
        elif char == '"':
            in_string = True
        elif char == "-" and code.startswith("--", index):
            newline = code.find("\n", index)
            index = len(code) if newline < 0 else newline
            continue
        elif char in "([{":
            depth += 1
        elif char in ")]}":
            depth = max(0, depth - 1)
        index += 1
    if depth > 0 or in_string:
        return "incomplete"
    last = code.rstrip().splitlines()[-1].rstrip()
    if re.search(r"(:|:=|=>|\||\bby|\bdo|\bwhere|\bwith|\bthen|\belse|\bmatch)$", last):
        return "incomplete"
    return "complete"
