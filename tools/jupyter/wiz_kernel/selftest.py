"""``python -m wiz_kernel --self-test``: no Jupyter required.

Four sections, each printed as PASS/FAIL/SKIP:

1. the wire protocol (signing, framing, tampered messages) — no ZeroMQ;
2. the drivers (a real ``wiz`` on a temp workspace: definitions persist, a
   multi-line definition, a last expression, an error);
3. the magics (``%%sh`` exit status and stream order, the ``%%time`` line,
   ``%%wiz`` against a plain cell, ``%%scry --progress`` order);
4. the live protocol — a kernel process on ephemeral ports, asked
   ``kernel_info_request`` and ``execute_request`` over raw ZeroMQ (skipped when
   ``pyzmq`` is not installed).  Jupyter itself is never needed.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import socket
import subprocess
import sys
import tempfile
import time
import traceback
import uuid

from . import __version__
from .backends import (BackendUnavailable, CellResult, find_wiz, make_backend)
from .magics import handle_magic, scry_command
from .progress import ProgressChannel
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


# -- 3: the magics ------------------------------------------------------

_FAKE_SCRY = '''import json, sys, time
for i in range(1, 4):
    print(f"progress: {i}/3 files ({(i * 100) // 3}%) taint", file=sys.stderr, flush=True)
    time.sleep(0.02)
print(json.dumps({"counts": {"findings": 1, "checked": 1, "unchecked": 0, "boundary": 0},
                  "findings": [{"severity": "error", "rule": "command-injection",
                                "location": {"uri": "fake.c", "startLine": 7,
                                             "startColumn": 3},
                                "derivation": "checked", "message": "bad"}],
                  "boundary": [], "file": "fake.c"}))
'''


def _fake_scry(workspace: str) -> str:
    path = os.path.join(workspace, "fake-scry.py")
    with open(path, "w", encoding="utf-8") as handle:
        handle.write(_FAKE_SCRY)
    return path


def _channel(**kwargs) -> tuple[ProgressChannel, list]:
    sent: list = []

    def publish(msg_type: str, content: dict, *, parent=None, metadata=None) -> None:
        sent.append(("publish", msg_type, content))

    def stream(name: str, text: str, *, parent=None) -> None:
        sent.append(("stream", name, text))

    return ProgressChannel(publish=publish, stream=stream, **kwargs), sent


def magic_checks(results: Results, wiz: str | None, backend: str, cwd: str) -> None:
    executable = find_wiz(wiz)
    if executable is None:
        results.skip("magics", "no wiz executable")
        return
    try:
        driver, _ = make_backend(backend, wiz, cwd)
    except BackendUnavailable as exc:
        results.check("magics: backend available", False, str(exc))
        return
    try:
        emitted: list[tuple[str, str]] = []
        result = handle_magic("%%sh\necho out\necho err >&2\nexit 0\n", driver,
                              cwd=cwd, emit=lambda name, text: emitted.append((name, text)))
        results.check("magic: %%sh streams stdout then stderr and returns status 0",
                      result is not None and not result.errors
                      and result.result == "exit status 0"
                      and [name for name, _ in emitted] == ["stdout", "stderr"],
                      repr(result))
        result = handle_magic("%%sh\nexit 7\n", driver, cwd=cwd)
        results.check("magic: %%sh reports a non-zero exit status",
                      result is not None and bool(result.errors)
                      and "7" in result.errors[0].evalue,
                      repr(result))
        result = handle_magic("%%time\n6 * 7\n", driver, cwd=cwd)
        timing = result.streams[-1].text.strip() if result and result.streams else ""
        match = re.match(r"^\[time\] wall (\d+\.\d+) s", timing)
        plausible = bool(match) and 0.0 <= float(match.group(1)) < 600.0
        results.check("magic: %%time returns the cell result and appends a wall line",
                      result is not None and result.result == "42"
                      and not result.errors and plausible
                      and ("peak RSS" in timing),
                      f"result={getattr(result, 'result', None)!r} timing={timing!r}")
        plain = driver.execute("def magic_plain : Nat := 5")
        explicit = handle_magic("%%wiz\ndef magic_explicit : Nat := 5\n", driver, cwd=cwd)
        plain_value = driver.execute("#eval magic_plain")
        explicit_value = driver.execute("#eval magic_explicit")
        results.check("magic: %%wiz is the plain-cell path (same driver, same file)",
                      not plain.errors and explicit is not None and not explicit.errors
                      and "5" in _streams(plain_value)
                      and "5" in _streams(explicit_value),
                      f"plain={plain.errors} explicit={getattr(explicit, 'errors', None)}")

        channel, sent = _channel()
        fake = _fake_scry(cwd)
        previous = os.environ.get("WIZ_SCRY")
        os.environ["WIZ_SCRY"] = f"{sys.executable} {fake}"
        try:
            result = handle_magic("%%scry --progress\nint main(void) { return 0; }\n",
                                  driver, cwd=cwd, progress=channel)
        finally:
            if previous is None:
                os.environ.pop("WIZ_SCRY", None)
            else:
                os.environ["WIZ_SCRY"] = previous
        forwarded = [payload[2] for payload in sent if payload[0] == "stream"]
        results.check("magic: %%scry --progress forwards the three lines in order",
                      channel.lines == [
                          "progress: 1/3 files (33%) taint",
                          "progress: 2/3 files (66%) taint",
                          "progress: 3/3 files (100%) taint",
                      ] and forwarded == [line + "\n" for line in channel.lines],
                      repr(channel.lines) + " / " + repr(forwarded))
        results.check("magic: %%scry --progress still renders the report",
                      result is not None and not result.errors
                      and "command-injection" in (result.result or ""),
                      repr(getattr(result, "errors", None)))

        comm_channel, comm_sent = _channel(comm_supported=True, reason="test comm")
        comm_channel.begin()
        comm_channel.forward("progress: 1/4 files (25%) points-to")
        comm_channel.forward("progress: 2/4 files (50%) points-to")
        comm_channel.finish()
        msg_types = [payload[1] for payload in comm_sent]
        fractions = [payload[2]["data"]["fraction"] for payload in comm_sent
                     if payload[1] == "comm_msg"]
        results.check("magic: the comm transport opens, updates with fractions, closes",
                      msg_types == ["comm_open", "comm_msg", "comm_msg", "comm_close"]
                      and comm_sent[0][2]["target_name"] == "wiz.progress"
                      and fractions == [0.25, 0.5]
                      and all(payload[0] == "publish" for payload in comm_sent),
                      repr(comm_sent))
    except Exception:
        results.check("magics: run", False, traceback.format_exc())
    finally:
        driver.close()


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

    def iopub_until(self, predicate, msg_id: str | None = None,
                    timeout: float = 120.0) -> list:
        """Collect iopub messages until `predicate` accepts one (comm messages have no
        busy/idle bracket, so `iopub_until_idle` cannot be used for them)."""
        self.iopub.setsockopt(self.zmq.RCVTIMEO, int(timeout * 1000))
        messages = []
        while True:
            try:
                frames = self.iopub.recv_multipart()
            except self.zmq.Again:
                raise TimeoutError("no matching iopub message")
            message = self.session.deserialize(frames)
            if msg_id is not None and message.parent_header.get("msg_id") != msg_id:
                continue
            messages.append(message)
            if predicate(message):
                return messages

    def execute(self, code: str, timeout: float = 120.0):
        msg_id = self.send("execute_request", {
            "code": code, "silent": False, "store_history": True,
            "user_expressions": {}, "allow_stdin": False, "stop_on_error": True})
        reply = self.reply(msg_id, timeout=timeout)
        return reply, self.iopub_until_idle(msg_id, timeout=timeout)

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
    fake_scry = _fake_scry(workspace)
    using_fake = scry_command(workspace, wiz) is None
    if using_fake:
        env["WIZ_SCRY"] = f"{sys.executable} {fake_scry}"
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
        reply, iopub = client.execute("%progress")
        results.check("live: %progress names the transport",
                      "progress:" in _execute_result(iopub).get("text/plain", ""),
                      repr(_execute_result(iopub)))
        reply, iopub = client.execute("%%sh\necho shell-out\necho shell-err >&2\nexit 0\n")
        results.check("live: %%sh streams both pipes and returns status 0",
                      reply.content.get("status") == "ok"
                      and "shell-out" in _texts(iopub, "stream")
                      and "shell-err" in _texts(iopub, "stream")
                      and _execute_result(iopub).get("text/plain") == "exit status 0",
                      _texts(iopub, "stream") + repr(reply.content))
        reply, iopub = client.execute("%%sh\nexit 3\n")
        errors = [m for m in iopub if m.msg_type == "error"]
        results.check("live: %%sh reports the exit status as an error",
                      reply.content.get("status") == "error" and bool(errors)
                      and "3" in errors[0].content.get("evalue", ""),
                      repr([m.content for m in errors]) + repr(reply.content))
        reply, iopub = client.execute("%%time\n6 * 7\n")
        timing = _texts(iopub, "stream")
        results.check("live: %%time appends a plausible wall/RSS line",
                      reply.content.get("status") == "ok"
                      and "42" in _execute_result(iopub).get("text/plain", "")
                      and re.search(r"\[time\] wall \d+\.\d+ s, peak RSS ", timing)
                      is not None,
                      timing + repr(_execute_result(iopub)))
        reply, iopub = client.execute("%%wiz\ndef live_explicit : Nat := 9\n")
        reply2, iopub2 = client.execute("#eval live_explicit")
        results.check("live: %%wiz behaves like a plain cell",
                      reply.content.get("status") == "ok"
                      and reply2.content.get("status") == "ok"
                      and "9" in _texts(iopub2, "stream"),
                      repr(reply.content) + _texts(iopub2, "stream"))
        if using_fake or scry_command(workspace, wiz) is not None:
            reply, iopub = client.execute(
                "%%scry\nchar *getenv(const char *name);\n"
                "int system(const char *command);\n"
                "int main(void) {\n  char *cmd = getenv(0);\n  system(cmd);\n  return 0;\n}\n")
            bundle = _execute_result(iopub)
            results.check("live: %%scry renders a finding",
                          "command-injection" in json.dumps(bundle),
                          repr(bundle) + repr(reply.content))
        if using_fake:
            reply, iopub = client.execute(
                "%%scry --progress\nint main(void) { return 0; }\n")
            streamed = [line for line in _texts(iopub, "stream").splitlines()
                        if line.startswith("progress:")]
            results.check("live: %%scry --progress forwards three lines in order",
                          reply.content.get("status") == "ok"
                          and streamed == ["progress: 1/3 files (33%) taint",
                                           "progress: 2/3 files (66%) taint",
                                           "progress: 3/3 files (100%) taint"],
                          repr(streamed) + repr(reply.content))
        else:
            results.skip("live: %%scry --progress", "the real scry may not take --progress")
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
        backend_checks(results, args.wiz, args.backend, workspace)
        magic_checks(results, args.wiz, args.backend, workspace)
        live_checks(results, args.wiz, args.backend, workspace)
    finally:
        if args.cwd is None:
            import shutil
            shutil.rmtree(workspace, ignore_errors=True)
    print(f"\n{results.passed} passed, {results.failed} failed, "
          f"{len(results.rows) - results.passed - results.failed} skipped", flush=True)
    return 1 if results.failed else 0
