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
                       ErrorReport, make_backend)
from .lsp import (LspClient, LspError, LspUnavailable, Notebook,
                  command_from_spec, completion_answer, hover_answer,
                  lsp_command as default_lsp_command, notebook_uri)
from .magics import handle_magic
from .wire import Message, Session, WireError, iopub_topic

try:  # the kernel is useless without it, but `--self-test` explains that cleanly
    import zmq
except ImportError:  # pragma: no cover - exercised by the tests' skip path
    zmq = None


BANNER = """Wiz kernel {version}

Wiz is a didactic dependently typed language (https://wiz-pl.github.io/wiz/).
Cells keep their definitions; `:help`-style magics are %%scry (C taint analysis),
%%wiz and %backend.  `wiz check` reports, not runs: a bare final expression becomes
the cell's result.
"""


class Kernel:
    def __init__(self, connection_file: str, *, backend: str = "auto",
                 wiz: str | None = None, cwd: str | None = None,
                 toolchain_args: list[str] | None = None,
                 lsp_command: str | list[str] | None = None,
                 lsp_enabled: bool = True):
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
        self.fallback_reason: str | None = None
        self.backend_error: str | None = None
        self.execution_count = 0
        self.running = True
        self._announced_backend = False
        self._hb_thread: threading.Thread | None = None
        self._hb_stop = threading.Event()
        self.wiz_version = self._wiz_version()
        # Completion and inspection: one lazily started `wiz lsp` child and the
        # notebook source it sees.  A failure is remembered, never raised.
        self.lsp_enabled = lsp_enabled
        self.lsp_spec = lsp_command
        self.lsp: LspClient | None = None
        self.notebook = Notebook()
        self._lsp_attempted = False
        self._lsp_error: str | None = None
        self._lsp_request_error: str | None = None
        self._lsp_uri: str | None = None
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

    # -- the language server --------------------------------------------

    def _lsp_command_line(self) -> list[str] | None:
        """`--lsp-command`, `$WIZ_KERNEL_LSP`, or `<wiz> … -I CWD lsp`."""
        spec = self.lsp_spec
        if spec is None:
            spec = os.environ.get("WIZ_KERNEL_LSP")
        if spec is not None:
            command = command_from_spec(spec)
            if not command:
                raise LspUnavailable("the language server command is empty")
            return command
        from .backends import find_wiz
        executable = find_wiz(self.wiz)
        if executable is None:
            raise LspUnavailable(
                "no wiz executable: pass --wiz PATH, set $WIZ, or put wiz on PATH")
        return default_lsp_command(executable, self.toolchain_args, self.cwd)

    def _ensure_lsp(self) -> LspClient | None:
        """Start `wiz lsp` once; return None (and a reason) when it cannot run."""
        if not self.lsp_enabled:
            self._lsp_attempted = True
            self._lsp_error = "disabled (--no-lsp)"
            return None
        if self._lsp_attempted:
            return self.lsp
        self._lsp_attempted = True
        try:
            command = self._lsp_command_line()
            if command is None:
                raise LspUnavailable("no language server command")
            client = LspClient(command, cwd=self.cwd)
            client.start()
        except (LspUnavailable, ValueError) as exc:
            self._lsp_error = str(exc)
            return None
        try:
            self._lsp_uri = notebook_uri(self.cwd)
        except (OSError, ValueError) as exc:
            client.close()
            self._lsp_error = f"cannot name the notebook document: {exc}"
            return None
        self.lsp = client
        return client

    def lsp_metadata(self) -> dict:
        """What the kernel can say about the language server (never starts it)."""
        if not self.lsp_enabled:
            available = False
        elif not self._lsp_attempted:
            available = None
        else:
            available = self.lsp.alive if self.lsp is not None else False
        metadata = {
            "enabled": self.lsp_enabled,
            "available": available,
            "started": self.lsp is not None,
            "transport": "stdio",
        }
        reason = self._lsp_request_error or self._lsp_error
        if self.lsp is not None and not self.lsp.alive and not reason:
            reason = "the language server exited"
        if reason:
            metadata["reason"] = reason
        if self.lsp is not None:
            metadata["command"] = " ".join(self.lsp.command)
        return metadata

    def _lsp_summary(self) -> str:
        if not self.lsp_enabled:
            return "disabled (--no-lsp)"
        if self.lsp is not None and self.lsp.alive:
            return "connected (stdio; `wiz lsp`)"
        reason = self._lsp_request_error or self._lsp_error
        if self.lsp is not None and not self.lsp.alive and not reason:
            reason = "the language server exited"
        if reason:
            return "unavailable: " + reason
        return "not started (starts on the first completion or inspection)"

    # -- startup ---------------------------------------------------------

    def start(self) -> None:
        self._start_heartbeat()
        try:
            self.backend, self.fallback_reason = make_backend(
                self.backend_kind, self.wiz, self.cwd, self.toolchain_args)
        except BackendUnavailable as exc:
            self.backend_error = str(exc)
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
            self.handle_complete(socket, msg)
        elif kind == "inspect_request":
            self.handle_inspect(socket, msg)
        elif kind == "history_request":
            self.reply(socket, msg, "history_reply", {"status": "ok", "history": []})
        elif kind == "comm_info_request":
            self.reply(socket, msg, "comm_info_reply", {"status": "ok", "comms": {}})
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
        banner += f"lsp: {self._lsp_summary()}\n"
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
            "metadata": {"wiz_backend": backend_name, "wiz_lsp": self.lsp_metadata()},
        })

    def handle_is_complete(self, socket, msg: Message) -> None:
        code = msg.content.get("code", "")
        self.reply(socket, msg, "is_complete_reply", {"status": is_complete(code)})

    # -- completion and inspection (`textDocument/completion`, `hover`) --

    @staticmethod
    def _cursor(content: dict, code: str) -> int:
        cursor = content.get("cursor_pos")
        if isinstance(cursor, bool) or not isinstance(cursor, int):
            try:
                cursor = int(cursor)
            except (TypeError, ValueError):
                cursor = len(code)
        return max(0, min(cursor, len(code)))

    def handle_complete(self, socket, msg: Message) -> None:
        content = msg.content or {}
        code = content.get("code") or ""
        cursor = self._cursor(content, code)
        client = self._ensure_lsp()
        metadata = {"wiz_lsp": self.lsp_metadata()}
        reply = {"status": "ok", "matches": [], "cursor_start": cursor,
                 "cursor_end": cursor, "metadata": metadata}
        if client is None:
            self.reply(socket, msg, "complete_reply", reply)
            return
        document, start, line, character = self.notebook.position(code, cursor)
        try:
            result = client.completion(self._lsp_uri, document, line, character)
        except LspError as exc:
            self._lsp_request_error = str(exc)
            metadata["wiz_lsp"] = self.lsp_metadata()
            self.reply(socket, msg, "complete_reply", reply)
            return
        self._lsp_request_error = None
        metadata["wiz_lsp"] = self.lsp_metadata()
        metadata["wiz_lsp"]["cursor"] = {"line": line, "character": character}
        answer = completion_answer(result, text=document, code=code,
                                   cursor=cursor, cell_start=start)
        metadata["wiz_lsp"]["isIncomplete"] = answer.is_incomplete
        if answer.is_incomplete:
            # There is no field for this in the Jupyter message; a frontend that
            # understands metadata can re-ask, the others see the list anyway.
            metadata["isIncomplete"] = True
        reply.update(matches=answer.items, cursor_start=answer.cursor_start,
                     cursor_end=answer.cursor_end)
        self.reply(socket, msg, "complete_reply", reply)

    def handle_inspect(self, socket, msg: Message) -> None:
        content = msg.content or {}
        code = content.get("code") or ""
        cursor = self._cursor(content, code)
        client = self._ensure_lsp()
        metadata = {"wiz_lsp": self.lsp_metadata()}
        reply = {"status": "ok", "found": False, "data": {}, "metadata": metadata}
        if client is None:
            self.reply(socket, msg, "inspect_reply", reply)
            return
        document, start, line, character = self.notebook.position(code, cursor)
        try:
            result = client.hover(self._lsp_uri, document, line, character)
        except LspError as exc:
            self._lsp_request_error = str(exc)
            metadata["wiz_lsp"] = self.lsp_metadata()
            self.reply(socket, msg, "inspect_reply", reply)
            return
        self._lsp_request_error = None
        metadata["wiz_lsp"] = self.lsp_metadata()
        metadata["wiz_lsp"]["cursor"] = {"line": line, "character": character}
        answer = hover_answer(result)
        reply.update(found=answer.found, data=answer.data)
        self.reply(socket, msg, "inspect_reply", reply)

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
        result = self._run_cell(code)
        source = notebook_cell(code)
        if source is not None and source.strip():
            self.notebook.append(source)
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
        return notice + f"\nlsp: {self._lsp_summary()}\n"

    def _run_cell(self, code: str) -> CellResult:
        if self.backend is None:
            message = self.backend_error or "no backend"
            return CellResult(errors=[ErrorReport(
                "BackendUnavailable",
                "no Wiz backend: " + message,
                ["no Wiz backend: " + message])])
        try:
            magic = handle_magic(code, self.backend, fallback_reason=self.fallback_reason,
                                 cwd=self.cwd, wiz=self.wiz,
                                 lsp_status=self._lsp_summary())
            if magic is not None:
                return magic
            return self.backend.execute(code)
        except BackendError as exc:
            return CellResult(errors=[ErrorReport("BackendError", str(exc), [str(exc)])])
        except Exception as exc:  # a broken cell must not kill the kernel
            trace = traceback.format_exc().splitlines()
            return CellResult(errors=[ErrorReport(type(exc).__name__, str(exc), trace)])

    # -- shutdown --------------------------------------------------------

    def close(self) -> None:
        self.running = False
        self._hb_stop.set()
        if self._hb_thread is not None:
            self._hb_thread.join(timeout=2)
        if self.lsp is not None:
            try:
                self.lsp.close()
            except Exception:
                traceback.print_exc()
            self.lsp = None
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


def notebook_cell(code: str) -> str | None:
    """The Wiz source a cell contributes to the notebook, or None for a magic.

    ``%%wiz`` and ``%wiz`` contribute their body; a ``%%scry`` cell (C source)
    and an unknown magic contribute nothing.  Completion and inspection must see
    the same accumulated source the batch driver would check.
    """
    lines = code.splitlines()
    if not lines:
        return None
    first = lines[0]
    if re.match(r"^%%wiz(?:[ \t]+.*)?$", first):
        return "\n".join(lines[1:])
    match = re.match(r"^%wiz[ \t]+(.*)$", first)
    if match and all(not line.strip() for line in lines[1:]):
        return match.group(1)
    if first.lstrip().startswith("%"):
        return None
    return code


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
