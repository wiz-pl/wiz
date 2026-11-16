#!/usr/bin/env python3
"""End-to-end smoke test for tools/wiz-mcp/wiz_mcp.py.

Starts the bridge the way an MCP client does, runs two LSP-backed tools
(`diagnostics`, then `hover`) so the lazy `wiz lsp` daemon starts, checks that
the daemon is a child of the bridge, then shuts the bridge down and checks that
the daemon is gone. Prints its measured daemon RSS.

Usage:
    python3 tools/wiz-mcp/tests/smoke.py [--wiz PATH]

Exit status: 0 passed, 1 failed, 2 skipped (no built `wiz`). A skipped run is
not a pass, but it is the right result on a machine without a toolchain.
"""

from __future__ import annotations

import argparse
import json
import os
import signal
import subprocess
import sys
import tempfile
import threading
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
SERVER = HERE.parent / "wiz_mcp.py"
REPO = HERE.parents[2]
OVERALL_TIMEOUT = 300


def children_of(pid: int) -> list[int]:
    """Direct children of `pid` from /proc (Linux); empty elsewhere."""
    found: list[int] = []
    proc = Path("/proc")
    if not proc.is_dir():
        return found
    for entry in proc.iterdir():
        if not entry.name.isdigit():
            continue
        try:
            stat = (entry / "stat").read_text()
        except OSError:
            continue
        # "pid (comm) state ppid ...", and comm may contain spaces or ')'.
        fields = stat.rsplit(")", 1)[-1].split()
        if len(fields) >= 2 and int(fields[1]) == pid:
            found.append(int(entry.name))
    return found


def cmdline(pid: int) -> str:
    try:
        return Path(f"/proc/{pid}/cmdline").read_bytes().replace(b"\0", b" ").decode("utf-8", "replace")
    except OSError:
        return ""


def rss_kib(pid: int) -> int | None:
    try:
        for line in Path(f"/proc/{pid}/status").read_text().splitlines():
            if line.startswith("VmRSS:"):
                return int(line.split()[1])
    except (OSError, ValueError):
        pass
    return None


def alive(pid: int) -> bool:
    try:
        os.kill(pid, 0)
        return True
    except ProcessLookupError:
        return False
    except PermissionError:
        return True


class Bridge:
    def __init__(self, command: list[str], cwd: str) -> None:
        self.proc = subprocess.Popen(
            command,
            cwd=cwd,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            bufsize=1,
        )
        self.stderr_lines: list[str] = []
        assert self.proc.stderr is not None
        self._stderr_thread = threading.Thread(target=self._read_stderr, args=(self.proc.stderr,), daemon=True)
        self._stderr_thread.start()
        self._next_id = 0

    def _read_stderr(self, stream) -> None:
        for line in stream:
            self.stderr_lines.append(line.rstrip())
            del self.stderr_lines[:-80]

    def send(self, message: dict) -> None:
        assert self.proc.stdin is not None
        self.proc.stdin.write(json.dumps(message) + "\n")
        self.proc.stdin.flush()

    def rpc(self, method: str, params: dict) -> dict:
        self._next_id += 1
        msg_id = self._next_id
        self.send({"jsonrpc": "2.0", "id": msg_id, "method": method, "params": params})
        assert self.proc.stdout is not None
        while True:
            line = self.proc.stdout.readline()
            if not line:
                raise RuntimeError(f"the bridge closed while waiting for {method}")
            message = json.loads(line)
            if message.get("id") == msg_id:
                return message

    def notify(self, method: str, params: dict | None = None) -> None:
        self.send({"jsonrpc": "2.0", "method": method, "params": params or {}})

    def stderr_tail(self) -> str:
        return "\n".join(self.stderr_lines[-40:])

    def kill(self) -> None:
        if self.proc.poll() is None:
            self.proc.kill()
        try:
            self.proc.wait(timeout=10)
        except subprocess.TimeoutExpired:
            pass


def envelope_of(response: dict) -> dict:
    content = response.get("result", {}).get("content") or []
    if not content or content[0].get("type") != "text":
        raise RuntimeError(f"tools/call returned no text content: {response}")
    return json.loads(content[0]["text"])


def daemon_pids(bridge: Bridge) -> list[int]:
    """Children of the bridge whose command line is a `wiz lsp`."""
    return [pid for pid in children_of(bridge.proc.pid) if "lsp" in cmdline(pid)]


def wait_until(predicate, timeout: float, interval: float = 0.1) -> bool:
    deadline = time.monotonic() + timeout
    while time.monotonic() < deadline:
        if predicate():
            return True
        time.sleep(interval)
    return predicate()


def run(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--wiz", default=os.environ.get("WIZ"), help="the wiz executable (default: this checkout's build)")
    args = parser.parse_args(argv)

    wiz = args.wiz or str(REPO / ".lake" / "build" / "bin" / "wiz")
    if not (os.path.isfile(wiz) and os.access(wiz, os.X_OK)):
        print(f"SKIP: no built wiz at {wiz} (run `lake build wiz` first)")
        return 2

    if hasattr(signal, "alarm"):
        signal.alarm(OVERALL_TIMEOUT)

    with tempfile.TemporaryDirectory(prefix="wiz-mcp-smoke-") as workspace:
        probe = Path(workspace) / "probe.wiz"
        probe.write_text("import Prelude\n\ndef answer : Nat := 42\n", encoding="utf-8")
        bridge = Bridge(
            [
                sys.executable,
                str(SERVER),
                "--workspace",
                workspace,
                "--wiz",
                os.path.abspath(wiz),
                "--idle",
                "600",
                "--timeout",
                "120",
            ],
            cwd=workspace,
        )
        daemons: list[int] = []
        try:
            initialize = bridge.rpc(
                "initialize",
                {
                    "protocolVersion": "2025-06-18",
                    "capabilities": {},
                    "clientInfo": {"name": "wiz-mcp-smoke", "version": "1"},
                },
            )
            info = initialize["result"]["serverInfo"]
            print(f"initialize: {info['name']} {info['version']}")
            bridge.notify("notifications/initialized")
            tools = {tool["name"] for tool in bridge.rpc("tools/list", {})["result"]["tools"]}
            # `build` is listed only with --allow-build; the smoke test runs the default (read-only) server.
            expected = {"version", "check", "parse", "fmt", "diagnostics", "hover", "goals"}
            if tools != expected:
                raise RuntimeError(f"tools/list mismatch: {sorted(tools)}")
            print(f"tools: {len(tools)} listed")

            started = time.monotonic()
            diagnostics = envelope_of(
                bridge.rpc("tools/call", {"name": "diagnostics", "arguments": {"path": "probe.wiz"}})
            )
            first_ms = (time.monotonic() - started) * 1000
            if not diagnostics["ok"] or diagnostics["error"]:
                raise RuntimeError(f"diagnostics failed: {diagnostics}")
            if not isinstance(diagnostics["result"], list):
                raise RuntimeError(f"diagnostics result is not a list: {diagnostics['result']!r}")
            print(f"diagnostics: ok ({first_ms:.0f} ms including daemon startup), {len(diagnostics['result'])} messages")

            daemons = daemon_pids(bridge)
            if not daemons:
                raise RuntimeError("no `wiz lsp` child appeared after the first LSP call")
            rss = rss_kib(daemons[0])
            print(f"daemon: pid {daemons[0]}, RSS {rss / 1024:.1f} MiB" if rss else f"daemon: pid {daemons[0]}")

            started = time.monotonic()
            hover = envelope_of(
                bridge.rpc(
                    "tools/call",
                    {"name": "hover", "arguments": {"path": "probe.wiz", "line": 2, "character": 13}},
                )
            )
            second_ms = (time.monotonic() - started) * 1000
            if not hover["ok"] or hover["error"]:
                raise RuntimeError(f"hover failed: {hover}")
            if hover["result"] is None:
                raise RuntimeError("hover returned null at `Nat` in the definition of `answer`")
            if "Nat" not in json.dumps(hover["result"]):
                raise RuntimeError(f"hover did not mention Nat: {hover['result']!r}")
            print(f"hover: ok ({second_ms:.0f} ms), {json.dumps(hover['result'])[:120]}")

            shutdown = bridge.rpc("shutdown", {})
            if "error" in shutdown:
                raise RuntimeError(f"shutdown failed: {shutdown}")
            bridge.notify("exit")
            try:
                code = bridge.proc.wait(timeout=30)
            except subprocess.TimeoutExpired as exc:
                raise RuntimeError("the bridge did not exit after `exit`") from exc
            if code != 0:
                raise RuntimeError(f"the bridge exited {code}")
            if daemons and not wait_until(lambda: not any(alive(pid) for pid in daemons), timeout=10):
                raise RuntimeError(f"the daemon outlived the bridge: {daemons}")
            print("shutdown: bridge and daemon exited")
            print("RESULT: PASS")
            return 0
        except Exception as exc:
            print(f"RESULT: FAIL ({type(exc).__name__}: {exc})")
            tail = bridge.stderr_tail()
            if tail:
                print("bridge stderr:\n" + tail)
            for pid in daemons or daemon_pids(bridge):
                try:
                    os.kill(pid, signal.SIGTERM)
                except OSError:
                    pass
            bridge.kill()
            return 1
        finally:
            if hasattr(signal, "alarm"):
                signal.alarm(0)


if __name__ == "__main__":
    sys.exit(run(sys.argv[1:]))
