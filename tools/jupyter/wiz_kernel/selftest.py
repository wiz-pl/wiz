"""``python -m wiz_kernel --self-test``: no Jupyter required.

Three sections, each printed as PASS/FAIL/SKIP:

1. the wire protocol (signing, framing, tampered messages) — no ZeroMQ;
2. the drivers (a real ``wiz`` on a temp workspace: definitions persist, a
   multi-line definition, a last expression, an error);
3. the live protocol — a kernel process on ephemeral ports, asked
   ``kernel_info_request`` and ``execute_request`` over raw ZeroMQ (skipped when
   ``pyzmq`` is not installed).  Jupyter itself is never needed.
"""

from __future__ import annotations

import argparse
import json
import os
import socket
import subprocess
import sys
import tempfile
import time
import traceback
import uuid

from . import __version__
from .backends import (BackendUnavailable, CellResult, find_wiz, make_backend)
from .lsp import (LspClient, LspUnavailable, Notebook, completion_answer,
                  hover_answer, lsp_command, offset_to_position,
                  position_to_offset, utf16_units)
from .wire import Session, WireError

TOOL_DIR = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

PASS, FAIL, SKIP = "PASS", "FAIL", "SKIP"


class Results:
    def __init__(self) -> None:
        self.rows: list[tuple[str, str, str]] = []

    def add(self, name: str, status: str, detail: str = "") -> None:
        self.rows.append((name, status, detail))
        line = f"{status} {name}"
        if detail and status != PASS:
            line += f": {detail}"
        print(line, flush=True)

    def check(self, name: str, ok: bool, detail: str = "") -> None:
        self.add(name, PASS if ok else FAIL, "" if ok else detail)

    def skip(self, name: str, detail: str) -> None:
        self.add(name, SKIP, detail)

    @property
    def failed(self) -> int:
        return sum(1 for _, status, _ in self.rows if status == FAIL)

    @property
    def passed(self) -> int:
        return sum(1 for _, status, _ in self.rows if status == PASS)


# -- 1: the wire --------------------------------------------------------

def wire_checks(results: Results) -> None:
    try:
        session = Session(key="s3cret", session_id="s")
        header = session.header("execute_request", "client")
        frames = session.serialize("execute_request", {"code": "1"}, header=header,
                                   identities=[b"client"])
        message = session.deserialize(frames)
        results.check("wire: signed round trip",
                      message.msg_type == "execute_request"
                      and message.content == {"code": "1"}
                      and message.identities == [b"client"],
                      repr(message))
        tampered = list(frames)
        tampered[-1] = b'{"code":"2"}'
        try:
            session.deserialize(tampered)
            results.check("wire: a tampered frame is refused", False, "no error raised")
        except WireError:
            results.check("wire: a tampered frame is refused", True)
        unsigned = Session(key="")
        frames = unsigned.serialize("kernel_info_request", {})
        results.check("wire: no key, empty signature",
                      frames[1] == b"" and unsigned.deserialize(frames).msg_type
                      == "kernel_info_request")
        results.check("wire: 5.3 header", header["version"] == "5.3"
                      and header["msg_type"] == "execute_request")
    except Exception:
        results.check("wire", False, traceback.format_exc())


# -- 2: the drivers -----------------------------------------------------

def _streams(result: CellResult) -> str:
    return "".join(stream.text for stream in result.streams)


def backend_checks(results: Results, wiz: str | None, backend: str, cwd: str) -> None:
    executable = find_wiz(wiz)
    if executable is None:
        results.skip("backend", "no wiz executable (pass --wiz PATH or set $WIZ)")
        return
    try:
        driver, reason = make_backend(backend, wiz, cwd)
    except BackendUnavailable as exc:
        results.check("backend available", False, str(exc))
        return
    detail = driver.name + (f" (repl unavailable: {reason})" if reason else "")
    results.add("backend: " + detail, PASS)
    try:
        result = driver.execute("def answer : Nat := 41 + 1")
        results.check("backend: a definition is accepted", not result.errors,
                      "; ".join(e.evalue for e in result.errors))
        result = driver.execute("#eval answer + 1")
        results.check("backend: definitions persist, #eval prints 43",
                      "43" in _streams(result) and not result.errors,
                      _streams(result) + "; ".join(e.evalue for e in result.errors))
        result = driver.execute("def f (n : Nat) : Nat :=\n  n + 1")
        results.check("backend: a multi-line definition is accepted", not result.errors,
                      "; ".join(e.evalue for e in result.errors))
        result = driver.execute("#eval f 2")
        results.check("backend: the multi-line definition is in scope",
                      "3" in _streams(result) and not result.errors,
                      _streams(result))
        result = driver.execute("1 + 1")
        results.check("backend: a bare last expression becomes the result",
                      result.result == "2" and not result.errors,
                      f"result={result.result!r} errors={[e.evalue for e in result.errors]}")
        result = driver.execute("def bad : Nat := true")
        results.check("backend: an error is reported, not raised",
                      bool(result.errors), "no error reported")
    except Exception:
        results.check("backend: run", False, traceback.format_exc())
    finally:
        driver.close()


# -- 3: completion and inspection (LSP) ---------------------------------

def _mock_lsp_environment() -> dict:
    env = dict(os.environ)
    env["PYTHONPATH"] = TOOL_DIR + os.pathsep + env.get("PYTHONPATH", "")
    return env


def _read_json_lines(path: str) -> list[dict]:
    messages = []
    try:
        with open(path, encoding="utf-8") as handle:
            for line in handle:
                line = line.strip()
                if line:
                    messages.append(json.loads(line))
    except (OSError, json.JSONDecodeError):
        pass
    return messages


def lsp_checks(results: Results, workspace: str) -> None:
    """Positions, the notebook document, and the client against a mock server."""
    try:
        results.check("lsp: UTF-16 counts astral characters twice",
                      utf16_units("a😀b") == 4 and utf16_units("abc") == 3)
        text = "a😀b\nc"
        results.check("lsp: offset -> position (UTF-16)",
                      offset_to_position(text, 3) == (0, 4)
                      and offset_to_position(text, 4) == (1, 0),
                      repr((offset_to_position(text, 3), offset_to_position(text, 4))))
        results.check("lsp: position -> offset (UTF-16)",
                      position_to_offset(text, 0, 4) == 3
                      and position_to_offset(text, 1, 0) == 4)

        notebook = Notebook(["def prior😀 : Nat := 0"])
        code = '#eval String.append "😀" an'
        document, start, line, character = notebook.position(code, len(code))
        results.check("lsp: the cell starts after the accumulated source",
                      start == len(document) - len(code)
                      and document.startswith("import Prelude\n")
                      and document.endswith(code), repr((start, document[:40])))
        results.check("lsp: the cursor is UTF-16 on its own line (astral before it)",
                      line == 2 and character == len(code) + 1
                      and character == utf16_units(code),
                      f"line={line} character={character} utf16={utf16_units(code)}")

        notebook2 = Notebook()
        plain = "#eval ans"
        document2, start2, line2, character2 = notebook2.position(plain, len(plain))
        results.check("lsp: no prior cells, the cell is line 1",
                      line2 == 1 and character2 == len(plain)
                      and document2.startswith("import Prelude\n"))

        notebook3 = Notebook(["import Prelude", "def a : Nat := 1"])
        document3, _, _, _ = notebook3.position("def b : Nat := 2", 0)
        results.check("lsp: an explicit import Prelude is not added twice",
                      document3.count("import Prelude") == 1, document3[:40])
        try:
            LspClient(["/nonexistent/wiz-kernel-no-such-lsp"], cwd=workspace).start()
            results.check("lsp: a missing server is unavailable, not an error", False,
                          "start() did not fail")
        except LspUnavailable:
            results.check("lsp: a missing server is unavailable, not an error", True)
    except Exception:
        results.check("lsp: positions", False, traceback.format_exc())

    log = os.path.join(workspace, "mock-lsp.jsonl")
    client = None
    started = False
    try:
        command = [sys.executable, "-m", "wiz_kernel.mock_lsp", "--log", log]
        client = LspClient(command, cwd=workspace, timeout=10.0, start_timeout=20.0,
                           env=_mock_lsp_environment())
        client.start()
        started = True
        results.check("lsp: mock server initializes over stdio", True)
        notebook = Notebook(["def prior : Nat := 0"])
        code = '#eval String.append "😀" an'
        document, start, line, character = notebook.position(code, len(code))
        answer = completion_answer(
            client.completion("file:///mock-notebook.wiz", document, line, character),
            text=document, code=code, cursor=len(code), cell_start=start)
        labels = [item["text"] for item in answer.items]
        results.check("lsp: completion items are mapped for Jupyter",
                      labels == ["mockValue", "mockFunction"]
                      and answer.items[0]["type"] == "text"
                      and answer.items[1]["type"] == "function"
                      and answer.items[0]["signature"] == "Nat"
                      and "mock" in answer.items[0]["documentation"].lower(),
                      repr(answer.items))
        results.check("lsp: the replacement range is the cell's word",
                      answer.cursor_start == len(code) - 2
                      and answer.cursor_end == len(code),
                      f"start={answer.cursor_start} end={answer.cursor_end} "
                      f"cursor={len(code)}")
        messages = _read_json_lines(log)
        completion_requests = [m for m in messages
                               if m.get("method") == "textDocument/completion"]
        sent = (completion_requests[-1].get("params", {}).get("position")
                if completion_requests else None)
        results.check("lsp: the cursor translation reaches the server (UTF-16)",
                      sent == {"line": line, "character": character}
                      and character == len(code) + 1,
                      f"sent={sent!r} expected line={line} character={character}")

        code2 = "def z : Nat := 0\nMOCK_INCOMPLETE"
        document2, start2, line2, character2 = notebook.position(code2, len(code2))
        answer2 = completion_answer(
            client.completion("file:///mock-notebook.wiz", document2, line2, character2),
            text=document2, code=code2, cursor=len(code2), cell_start=start2)
        results.check("lsp: isIncomplete is carried through", answer2.is_incomplete,
                      repr(answer2))

        empty = "MOCK_NONE"
        document3, start3, line3, character3 = notebook.position(empty, len(empty))
        answer3 = completion_answer(
            client.completion("file:///mock-notebook.wiz", document3, line3, character3),
            text=document3, code=empty, cursor=len(empty), cell_start=start3)
        results.check("lsp: an empty completion is an empty list, not an error",
                      answer3.items == [] and answer3.available, repr(answer3))
        hover3 = hover_answer(
            client.hover("file:///mock-notebook.wiz", document3, line3, character3))
        results.check("lsp: an empty hover is found=False",
                      not hover3.found and hover3.data == {}, repr(hover3))

        hover_doc, _, hover_line, hover_char = notebook.position("#eval mockHover",
                                                                 len("#eval mockHover"))
        hover = hover_answer(client.hover("file:///mock-notebook.wiz", hover_doc,
                                          hover_line, hover_char))
        results.check("lsp: hover markup is text/plain and text/markdown",
                      hover.found
                      and "mockHover" in hover.data.get("text/plain", "")
                      and "mockHover" in hover.data.get("text/markdown", ""),
                      repr(hover.data))
    except Exception:
        results.check("lsp: mock client", False, traceback.format_exc())
    finally:
        if client is not None:
            client.close()
            if started:
                messages = _read_json_lines(log)
                results.check("lsp: close sends shutdown and exit",
                              any(m.get("method") == "shutdown" for m in messages)
                              and any(m.get("method") == "exit" for m in messages),
                              repr([m.get("method") for m in messages]))


def live_lsp_checks(results: Results, wiz: str | None, workspace: str) -> None:
    """Optional: the real `wiz lsp`, skipped cleanly when it cannot start."""
    executable = find_wiz(wiz)
    if executable is None:
        results.skip("live lsp", "no wiz executable")
        return
    client = LspClient(lsp_command(executable, [], workspace), cwd=workspace,
                       timeout=30.0, start_timeout=60.0)
    try:
        client.start()
    except LspUnavailable as exc:
        results.skip("live lsp: `wiz lsp`", str(exc))
        return
    try:
        results.add("live lsp: `wiz lsp` initializes", PASS)
        notebook = Notebook(["def notebookAnswer : Nat := 41",
                             "def notebookBroken : Nat :="])
        code = "#eval notebookAn"
        document, start, line, character = notebook.position(code, len(code))
        answer = completion_answer(
            client.completion("file:///live-notebook.wiz", document, line, character),
            text=document, code=code, cursor=len(code), cell_start=start)
        labels = [item["text"] for item in answer.items]
        results.check("live lsp: completion sees an earlier cell (unparsable cell tolerated)",
                      "notebookAnswer" in labels, repr(labels[:20]))
        hover_code = "#eval notebookAnswer"
        hover_doc, _, hover_line, _ = notebook.position(hover_code, 8)
        hover = hover_answer(client.hover("file:///live-notebook.wiz", hover_doc,
                                          hover_line, 8))
        results.check("live lsp: hover is found and describes the type",
                      hover.found and "Nat" in hover.data.get("text/plain", ""),
                      repr(hover.data))
    except Exception:
        results.check("live lsp", False, traceback.format_exc())
    finally:
        client.close()


# -- 4: the live protocol ----------------------------------------------

def _free_port() -> int:
    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as sock:
        sock.bind(("127.0.0.1", 0))
        return sock.getsockname()[1]


def _connection_file(directory: str) -> tuple[str, dict]:
    config = {
        "transport": "tcp",
        "ip": "127.0.0.1",
        "shell_port": _free_port(),
        "iopub_port": _free_port(),
        "stdin_port": _free_port(),
        "hb_port": _free_port(),
        "control_port": _free_port(),
        "key": uuid.uuid4().hex,
        "signature_scheme": "hmac-sha256",
        "kernel_name": "wiz-kernel",
    }
    path = os.path.join(directory, "connection.json")
    with open(path, "w", encoding="utf-8") as handle:
        json.dump(config, handle)
    return path, config


class Client:
    """A minimal raw-ZeroMQ client (no jupyter_client)."""

    def __init__(self, config: dict):
        import zmq
        self.zmq = zmq
        self.context = zmq.Context.instance()
        self.session = Session(key=config["key"],
                               scheme=config.get("signature_scheme", "hmac-sha256"))
        address = f"tcp://{config['ip']}:{config['shell_port']}"
        self.shell = self.context.socket(zmq.DEALER)
        self.shell.setsockopt(zmq.IDENTITY, b"wiz-selftest")
        self.shell.connect(address)
        self.iopub = self.context.socket(zmq.SUB)
        self.iopub.setsockopt(zmq.SUBSCRIBE, b"")
        self.iopub.connect(f"tcp://{config['ip']}:{config['iopub_port']}")
        self.control = self.context.socket(zmq.DEALER)
        self.control.setsockopt(zmq.IDENTITY, b"wiz-selftest-control")
        self.control.connect(f"tcp://{config['ip']}:{config['control_port']}")
        self.config = config
        time.sleep(0.3)

    def heartbeat(self, timeout: float = 10.0) -> bool:
        request = self.context.socket(self.zmq.REQ)
        request.setsockopt(self.zmq.RCVTIMEO, int(timeout * 1000))
        request.connect(f"tcp://{self.config['ip']}:{self.config['hb_port']}")
        try:
            request.send(b"wiz-selftest-ping")
            return request.recv() == b"wiz-selftest-ping"
        except self.zmq.Again:
            return False
        finally:
            request.close(0)

    def control_request(self, msg_type: str, content: dict) -> str:
        header = self.session.header(msg_type, username="selftest")
        self.control.send_multipart(self.session.serialize(msg_type, content, header=header))
        return header["msg_id"]

    def control_reply(self, msg_id: str, timeout: float = 30.0):
        self.control.setsockopt(self.zmq.RCVTIMEO, int(timeout * 1000))
        while True:
            try:
                frames = self.control.recv_multipart()
            except self.zmq.Again:
                raise TimeoutError(f"no control reply to {msg_id}")
            message = self.session.deserialize(frames)
            if message.parent_header.get("msg_id") == msg_id:
                return message

    def send(self, msg_type: str, content: dict) -> str:
        header = self.session.header(msg_type, username="selftest")
        self.shell.send_multipart(self.session.serialize(msg_type, content, header=header))
        return header["msg_id"]

    def reply(self, msg_id: str, timeout: float = 120.0):
        self.shell.setsockopt(self.zmq.RCVTIMEO, int(timeout * 1000))
        while True:
            try:
                frames = self.shell.recv_multipart()
            except self.zmq.Again:
                raise TimeoutError(f"no reply to {msg_id}")
            message = self.session.deserialize(frames)
            if message.parent_header.get("msg_id") == msg_id:
                return message

    def iopub_until_idle(self, msg_id: str, timeout: float = 120.0) -> list:
        self.iopub.setsockopt(self.zmq.RCVTIMEO, int(timeout * 1000))
        messages = []
        while True:
            try:
                frames = self.iopub.recv_multipart()
            except self.zmq.Again:
                raise TimeoutError(f"no idle for {msg_id}")
            message = self.session.deserialize(frames)
            if message.parent_header.get("msg_id") != msg_id:
                continue
            messages.append(message)
            if (message.msg_type == "status"
                    and message.content.get("execution_state") == "idle"):
                return messages

    def execute(self, code: str):
        msg_id = self.send("execute_request", {
            "code": code, "silent": False, "store_history": True,
            "user_expressions": {}, "allow_stdin": False, "stop_on_error": True})
        reply = self.reply(msg_id)
        return reply, self.iopub_until_idle(msg_id)

    def close(self) -> None:
        self.shell.close(0)
        self.iopub.close(0)
        self.control.close(0)


def _texts(messages, msg_type: str, key: str = "text") -> str:
    return "".join(m.content.get(key, "") for m in messages if m.msg_type == msg_type)


def _execute_result(messages) -> dict:
    for message in messages:
        if message.msg_type == "execute_result":
            return message.content.get("data", {})
    return {}


def live_checks(results: Results, wiz: str | None, backend: str, workspace: str) -> None:
    try:
        import zmq  # noqa: F401
    except ImportError:
        results.skip("live: pyzmq is not installed", "pip install pyzmq")
        return
    executable = find_wiz(wiz)
    if executable is None:
        results.skip("live: kernel", "no wiz executable")
        return
    connection_file, config = _connection_file(workspace)
    env = dict(os.environ)
    env["PYTHONPATH"] = TOOL_DIR + os.pathsep + env.get("PYTHONPATH", "")
    command = [sys.executable, "-m", "wiz_kernel", "-f", connection_file,
               "--backend", backend, "--cwd", workspace]
    if wiz:
        command += ["--wiz", wiz]
    process = subprocess.Popen(command, cwd=workspace, env=env,
                               stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    client = None
    try:
        client = Client(config)
        msg_id = client.send("kernel_info_request", {})
        reply = client.reply(msg_id, timeout=120)
        content = reply.content
        results.check("live: kernel_info_reply",
                      reply.msg_type == "kernel_info_reply"
                      and content.get("protocol_version") == "5.3"
                      and content.get("implementation") == "wiz-kernel",
                      repr(content))
        results.check("live: the reply says which backend is in use",
                      content.get("metadata", {}).get("wiz_backend") in ("repl", "batch"),
                      repr(content.get("metadata")))
        results.check("live: the heartbeat socket echoes", client.heartbeat(),
                      "no echo on the hb port")
        interrupt_id = client.control_request("interrupt_request", {})
        interrupt = client.control_reply(interrupt_id)
        results.check("live: control answers interrupt_request (a documented no-op)",
                      interrupt.msg_type == "interrupt_reply"
                      and interrupt.content.get("status") == "ok",
                      repr(interrupt.content))
        reply, iopub = client.execute("def answer : Nat := 41 + 1")
        results.check("live: execute_reply ok", reply.content.get("status") == "ok",
                      repr(reply.content))
        results.check("live: execute_input on iopub",
                      any(m.msg_type == "execute_input" for m in iopub))
        reply, iopub = client.execute("#eval answer + 1")
        results.check("live: a stream on iopub carries 43",
                      "43" in _texts(iopub, "stream")
                      and reply.content.get("status") == "ok",
                      _texts(iopub, "stream") + repr(reply.content))
        reply, iopub = client.execute("1 + 1")
        bundle = _execute_result(iopub)
        results.check("live: execute_result for the last expression",
                      bundle.get("text/plain") == "2"
                      and reply.content.get("status") == "ok",
                      repr(bundle) + repr(reply.content))
        reply, iopub = client.execute("def bad : Nat := true")
        errors = [m for m in iopub if m.msg_type == "error"]
        results.check("live: an error message with ename/evalue",
                      bool(errors) and errors[0].content.get("ename")
                      and errors[0].content.get("evalue")
                      and reply.content.get("status") == "error",
                      repr([m.content for m in errors]) + repr(reply.content))
        reply, iopub = client.execute("%backend")
        results.check("live: %backend names the driver",
                      "backend:" in _execute_result(iopub).get("text/plain", ""),
                      repr(_execute_result(iopub)))
        from .magics import scry_command
        if scry_command(workspace, wiz) is None:
            results.skip("live: %%scry", "no scry executable (set WIZ_SCRY)")
        else:
            reply, iopub = client.execute(
                "%%scry\nchar *getenv(const char *name);\n"
                "int system(const char *command);\n"
                "int main(void) {\n  char *cmd = getenv(0);\n  system(cmd);\n  return 0;\n}\n")
            bundle = _execute_result(iopub)
            results.check("live: %%scry renders a finding",
                          "command-injection" in json.dumps(bundle),
                          repr(bundle) + repr(reply.content))
        msg_id = client.send("shutdown_request", {"restart": False})
        reply = client.reply(msg_id, timeout=30)
        results.check("live: shutdown_reply", reply.content.get("status") == "ok",
                      repr(reply.content))
        try:
            process.wait(timeout=20)
            results.check("live: the kernel exits", process.returncode == 0,
                          f"status {process.returncode}")
        except subprocess.TimeoutExpired:
            results.check("live: the kernel exits", False, "still running")
    except Exception:
        results.check("live", False, traceback.format_exc())
    finally:
        if client is not None:
            client.close()
        if process.poll() is None:
            process.terminate()
            try:
                process.wait(timeout=10)
            except subprocess.TimeoutExpired:
                process.kill()
        stderr = b""
        try:
            stderr = process.stderr.read() if process.stderr else b""
        except OSError:
            pass
        if stderr.strip():
            print("--- kernel stderr ---", flush=True)
            print(stderr.decode("utf-8", "replace").rstrip(), flush=True)


# -- entry --------------------------------------------------------------

def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(prog="python -m wiz_kernel --self-test",
                                     description="self-test the Wiz kernel (no Jupyter)")
    parser.add_argument("--wiz", metavar="PATH", help="the Wiz executable")
    parser.add_argument("--backend", choices=["auto", "repl", "batch"], default="auto")
    parser.add_argument("--cwd", metavar="DIR", help="the workspace (default: a temp dir)")
    args = parser.parse_args(argv)
    print(f"wiz-kernel {__version__} self-test (Python {sys.version.split()[0]})", flush=True)
    results = Results()
    workspace = args.cwd or tempfile.mkdtemp(prefix="wiz-kernel-selftest-")
    try:
        wire_checks(results)
        lsp_checks(results, workspace)
        backend_checks(results, args.wiz, args.backend, workspace)
        live_checks(results, args.wiz, args.backend, workspace)
        live_lsp_checks(results, args.wiz, workspace)
    finally:
        if args.cwd is None:
            import shutil
            shutil.rmtree(workspace, ignore_errors=True)
    print(f"\n{results.passed} passed, {results.failed} failed, "
          f"{len(results.rows) - results.passed - results.failed} skipped", flush=True)
    return 1 if results.failed else 0
