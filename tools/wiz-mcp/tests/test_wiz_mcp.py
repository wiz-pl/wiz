#!/usr/bin/env python3
"""Unit tests for tools/wiz-mcp/wiz_mcp.py (stdlib only).

Run from the repository root:

    python3 -m unittest discover -s tools/wiz-mcp/tests -p 'test_*.py' -v

These tests never need a built `wiz`: the subprocess tests use tiny shell
scripts, and the daemon tests use pipes, a stand-in connection and a small fake
stdio language server.
"""

from __future__ import annotations

import io
import json
import os
import threading
import sys
import tempfile
import time
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))

import wiz_mcp  # noqa: E402


#: The tools a server lists without --allow-build (all read-only).
DEFAULT_TOOLS = {
    "version", "check", "parse", "fmt", "diagnostics", "hover", "goals",
    "definition", "references", "document_symbols", "workspace_symbols", "term_goal",
    "completion", "signature_help", "inlay_hints", "code_actions", "rename",
    "search", "doc",
}


def write_exe(directory: str, name: str, body: str) -> str:
    path = Path(directory) / name
    path.write_text("#!/bin/sh\nset -eu\n" + body + "\n", encoding="utf-8")
    path.chmod(0o755)
    return str(path)


class DeadConn:
    """A stand-in connection that records sends and never answers."""

    def __init__(self) -> None:
        self.sent: list[str] = []
        self.closed = False

    def send_text(self, text: str, deadline=None) -> None:  # noqa: ARG002
        self.sent.append(text)

    def close(self) -> None:
        self.closed = True


class EnvelopeTests(unittest.TestCase):
    def test_every_envelope_has_the_same_keys(self) -> None:
        ok = wiz_mcp.make_envelope("check", path="/w/a.wiz", exit_code=0)
        err = wiz_mcp.error_envelope("check", "timeout", "too slow", path="/w/a.wiz")
        self.assertEqual(set(ok), set(wiz_mcp.ENVELOPE_KEYS))
        self.assertEqual(set(err), set(wiz_mcp.ENVELOPE_KEYS))
        self.assertTrue(ok["ok"])
        self.assertIsNone(ok["error"])
        self.assertFalse(err["ok"])
        self.assertEqual(err["error"]["kind"], "timeout")

    def test_text_is_clipped_with_an_explicit_marker(self) -> None:
        env = wiz_mcp.make_envelope("parse", stdout="x" * (wiz_mcp.MAX_TEXT + 17))
        self.assertTrue(env["truncated"])
        self.assertEqual(len(env["stdout"]), wiz_mcp.MAX_TEXT + len(wiz_mcp.TRUNCATION_MARK.format(n=17)))
        self.assertIn("truncated: 17 characters omitted", env["stdout"])

    def test_result_is_clipped_with_a_preview_object(self) -> None:
        env = wiz_mcp.make_envelope("diagnostics", result=["y" * 1000] * 200)
        self.assertTrue(env["truncated"])
        self.assertIsInstance(env["result"], dict)
        self.assertTrue(env["result"]["_truncated"])
        self.assertIn("truncated:", env["result"]["preview"])

    def test_small_values_are_untouched(self) -> None:
        env = wiz_mcp.make_envelope("hover", result={"contents": "Nat"})
        self.assertFalse(env["truncated"])
        self.assertEqual(env["result"], {"contents": "Nat"})


class PathTests(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory(prefix="wiz-mcp-unit-")
        self.workspace = self.tmp.name

    def tearDown(self) -> None:
        self.tmp.cleanup()

    def test_relative_paths_use_the_workspace(self) -> None:
        got = wiz_mcp.resolve_path(self.workspace, "examples/church.wiz")
        self.assertEqual(got, os.path.join(self.workspace, "examples", "church.wiz"))

    def test_absolute_paths_stay_absolute(self) -> None:
        self.assertEqual(wiz_mcp.resolve_path(self.workspace, "/tmp/x.wiz"), "/tmp/x.wiz")

    def test_dotdot_is_normalized(self) -> None:
        got = wiz_mcp.resolve_path(self.workspace, "a/../b.wiz")
        self.assertEqual(got, os.path.join(self.workspace, "b.wiz"))

    def test_empty_path_is_rejected(self) -> None:
        with self.assertRaises(wiz_mcp.ToolError) as caught:
            wiz_mcp.resolve_path(self.workspace, "  ")
        self.assertEqual(caught.exception.kind, "invalid_args")

    def test_file_uri_escapes_spaces_hashes_and_unicode(self) -> None:
        uri = wiz_mcp.path_to_uri("/tmp/a b#c/λ.wiz")
        self.assertTrue(uri.startswith("file:///tmp/"))
        self.assertIn("a%20b%23c", uri)
        self.assertIn("%CE%BB", uri)
        self.assertNotIn(" ", uri)
        self.assertNotIn("#", uri)


class FramingTests(unittest.TestCase):
    def test_blank_and_bad_lines_are_skipped(self) -> None:
        messages = list(wiz_mcp.iter_messages(io.StringIO('{"id":1}\r\n\nnot json\n{"id":2}\n')))
        self.assertEqual([message["id"] for message in messages], [1, 2])

    def test_non_object_values_are_skipped(self) -> None:
        messages = list(wiz_mcp.iter_messages(io.StringIO("[1,2]\nnull\n{\"id\":3}\n")))
        self.assertEqual(messages, [{"id": 3}])


class DispatchTests(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory(prefix="wiz-mcp-unit-")
        self.workspace = self.tmp.name
        self.wiz = write_exe(
            self.workspace,
            "wiz",
            'if [ "$1" = "--version" ]; then echo "wiz 9.9.9"; else echo "$@"; fi',
        )
        self.config = wiz_mcp.Config(workspace=self.workspace, wiz=self.wiz, idle=0, timeout=5)
        self.server = wiz_mcp.Server(self.config)

    def tearDown(self) -> None:
        self.server.close()
        self.tmp.cleanup()

    def dispatch(self, message: dict) -> tuple[list[dict], bool]:
        return self.server.dispatch(message)

    def test_initialize_echoes_a_supported_protocol_version(self) -> None:
        responses, stop = self.dispatch(
            {"jsonrpc": "2.0", "id": 1, "method": "initialize", "params": {"protocolVersion": "2025-03-26"}}
        )
        self.assertFalse(stop)
        result = responses[0]["result"]
        self.assertEqual(result["protocolVersion"], "2025-03-26")
        self.assertEqual(result["serverInfo"]["name"], "wiz")
        self.assertIn("check", result["instructions"])

    def test_initialize_falls_back_for_an_unknown_version(self) -> None:
        responses, _ = self.dispatch(
            {"jsonrpc": "2.0", "id": 1, "method": "initialize", "params": {"protocolVersion": "1999-01-01"}}
        )
        self.assertEqual(responses[0]["result"]["protocolVersion"], wiz_mcp.PROTOCOL_VERSION)

    def test_tools_list_has_only_read_only_tools_by_default(self) -> None:
        responses, _ = self.dispatch({"jsonrpc": "2.0", "id": 2, "method": "tools/list", "params": {}})
        names = {tool["name"] for tool in responses[0]["result"]["tools"]}
        self.assertEqual(names, DEFAULT_TOOLS)

    def test_tools_list_has_build_with_allow_build(self) -> None:
        server = wiz_mcp.Server(wiz_mcp.Config(workspace=self.workspace, wiz=self.wiz, idle=0, timeout=5, allow_build=True))
        try:
            responses, _ = server.dispatch({"jsonrpc": "2.0", "id": 2, "method": "tools/list", "params": {}})
        finally:
            server.close()
        names = {tool["name"] for tool in responses[0]["result"]["tools"]}
        self.assertEqual(names, DEFAULT_TOOLS | {"build"})

    def test_notifications_get_no_reply(self) -> None:
        self.assertEqual(self.dispatch({"jsonrpc": "2.0", "method": "notifications/initialized"}), ([], False))
        self.assertEqual(self.dispatch({"jsonrpc": "2.0", "method": "exit"}), ([], True))

    def test_unknown_tool_is_a_jsonrpc_error(self) -> None:
        responses, _ = self.dispatch(
            {"jsonrpc": "2.0", "id": 3, "method": "tools/call", "params": {"name": "nope", "arguments": {}}}
        )
        self.assertEqual(responses[0]["error"]["code"], -32602)

    def test_unknown_method_is_a_jsonrpc_error(self) -> None:
        responses, _ = self.dispatch({"jsonrpc": "2.0", "id": 4, "method": "prompts/list", "params": {}})
        self.assertEqual(responses[0]["error"]["code"], -32601)

    def test_version_runs_the_configured_binary(self) -> None:
        responses, _ = self.dispatch(
            {"jsonrpc": "2.0", "id": 5, "method": "tools/call", "params": {"name": "version", "arguments": {}}}
        )
        result = responses[0]["result"]
        self.assertFalse(result["isError"])
        envelope = json.loads(result["content"][0]["text"])
        self.assertTrue(envelope["ok"])
        self.assertEqual(envelope["exit"], 0)
        self.assertEqual(envelope["stdout"], "wiz 9.9.9\n")
        # Text tools must not start the language server.
        self.assertIsNone(self.server.daemon.conn)
        self.assertIsNone(self.server.daemon.proc)

    def test_missing_wiz_is_a_clear_error_envelope(self) -> None:
        config = wiz_mcp.Config(
            workspace=self.workspace, wiz=os.path.join(self.workspace, "not-built", "wiz"), idle=0, timeout=2
        )
        server = wiz_mcp.Server(config)
        try:
            envelope = server.call_tool("check", {"path": "probe.wiz"})
        finally:
            server.close()
        self.assertFalse(envelope["ok"])
        self.assertEqual(envelope["error"]["kind"], "wiz_not_found")
        self.assertIn("lake build wiz", envelope["error"]["message"])

    def test_missing_arguments_are_an_error_envelope(self) -> None:
        envelope = self.server.call_tool("check", {})
        self.assertFalse(envelope["ok"])
        self.assertEqual(envelope["error"]["kind"], "invalid_args")

    def test_nonzero_exit_is_not_ok_but_is_not_a_bridge_error(self) -> None:
        failing = write_exe(self.workspace, "failing-wiz", "echo 'type mismatch' >&2; exit 1")
        config = wiz_mcp.Config(workspace=self.workspace, wiz=failing, idle=0, timeout=5)
        server = wiz_mcp.Server(config)
        try:
            envelope = server.call_tool("check", {"path": "probe.wiz"})
        finally:
            server.close()
        self.assertFalse(envelope["ok"])
        self.assertEqual(envelope["exit"], 1)
        self.assertIsNone(envelope["error"])
        self.assertIn("type mismatch", envelope["stderr"])

    def test_subprocess_timeout_is_bounded_and_reported(self) -> None:
        slow = write_exe(self.workspace, "slow-wiz", "exec sleep 5")
        config = wiz_mcp.Config(workspace=self.workspace, wiz=slow, idle=0, timeout=0.2)
        server = wiz_mcp.Server(config)
        started = time.monotonic()
        try:
            envelope = server.call_tool("check", {"path": "probe.wiz"})
        finally:
            server.close()
        elapsed = time.monotonic() - started
        self.assertFalse(envelope["ok"])
        self.assertEqual(envelope["error"]["kind"], "timeout")
        self.assertLess(elapsed, 3.0)

    def test_a_flooding_child_is_killed_and_clipped(self) -> None:
        """security-07: drain in chunks; kill past the cap instead of buffering it all."""
        flood = Path(self.workspace) / "flood-wiz"
        flood.write_text(
            "#!/usr/bin/env python3\n"
            "import sys, time\n"
            "while True:\n"
            "    sys.stdout.write('x' * 1000)\n"
            "    sys.stdout.flush()\n"
            "    time.sleep(0.001)\n"
        )
        flood.chmod(0o755)
        config = wiz_mcp.Config(workspace=self.workspace, wiz=str(flood), idle=0, timeout=3)
        server = wiz_mcp.Server(config)
        saved = getattr(wiz_mcp, "MAX_OUTPUT", None)
        if saved is not None:
            wiz_mcp.MAX_OUTPUT = 1_000_000
        try:
            envelope = server.call_tool("version", {})
        finally:
            if saved is not None:
                wiz_mcp.MAX_OUTPUT = saved
            server.close()
        self.assertIsNotNone(envelope["exit"], envelope)
        self.assertLess(envelope["exit"], 0, envelope)  # killed at the cap, not timed out
        self.assertTrue(envelope["truncated"], envelope)
        self.assertLessEqual(len(envelope["stdout"]), wiz_mcp.MAX_TEXT)
        self.assertIn("truncated:", envelope["stdout"])

    def test_lsp_startup_failure_is_reported_with_stderr(self) -> None:
        failing = write_exe(
            self.workspace,
            "bad-lsp-wiz",
            'if [ "$1" = "lsp" ]; then echo "boom: no module roots" >&2; exit 3; fi\necho ok',
        )
        Path(self.workspace, "probe.wiz").write_text("def x : Nat := 1\n")
        config = wiz_mcp.Config(workspace=self.workspace, wiz=failing, idle=0, timeout=10)
        server = wiz_mcp.Server(config)
        try:
            envelope = server.call_tool("diagnostics", {"path": "probe.wiz"})
        finally:
            server.close()
        self.assertFalse(envelope["ok"])
        self.assertEqual(envelope["error"]["kind"], "lsp_startup")
        self.assertIn("boom", envelope["error"]["message"])

    def test_build_out_is_resolved_against_the_workspace(self) -> None:
        self.server.close()
        self.server = wiz_mcp.Server(
            wiz_mcp.Config(workspace=self.workspace, wiz=self.wiz, idle=0, timeout=5, allow_build=True)
        )
        responses, _ = self.dispatch(
            {
                "jsonrpc": "2.0",
                "id": 6,
                "method": "tools/call",
                "params": {"name": "build", "arguments": {"path": "probe.wiz", "out": "probe"}},
            }
        )
        envelope = json.loads(responses[0]["result"]["content"][0]["text"])
        self.assertTrue(envelope["ok"])
        expected_out = os.path.join(self.workspace, "probe")
        self.assertIn(expected_out, envelope["stdout"])


class DaemonTests(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory(prefix="wiz-mcp-unit-")
        self.config = wiz_mcp.Config(workspace=self.tmp.name, wiz="wiz", idle=0, timeout=5)
        self.daemon = wiz_mcp.LSPDaemon(self.config)

    def tearDown(self) -> None:
        self.daemon.close()
        self.tmp.cleanup()

    def test_request_without_a_reply_hits_the_deadline_and_closes(self) -> None:
        conn = DeadConn()
        self.daemon.conn = conn
        self.daemon.dead = False
        started = time.monotonic()
        with self.assertRaises(wiz_mcp.LSPTimeout):
            self.daemon.request("textDocument/hover", {}, time.monotonic() + 0.2)
        self.assertLess(time.monotonic() - started, 2.0)
        self.assertTrue(conn.closed)
        self.assertIsNone(self.daemon.conn)

    def test_wait_diagnostics_matches_the_uri(self) -> None:
        self.daemon.conn = DeadConn()
        self.daemon.dead = False
        self.daemon.inbox = [
            {"method": "textDocument/publishDiagnostics", "params": {"uri": "file:///other", "diagnostics": [1]}},
            {"method": "textDocument/publishDiagnostics", "params": {"uri": "file:///mine", "diagnostics": [2]}},
        ]
        self.assertEqual(self.daemon.wait_diagnostics("file:///mine", time.monotonic() + 1), [2])

    def test_wait_diagnostics_times_out_without_a_push(self) -> None:
        self.daemon.conn = DeadConn()
        self.daemon.dead = False
        with self.assertRaises(wiz_mcp.LSPTimeout):
            self.daemon.wait_diagnostics("file:///mine", time.monotonic() + 0.1)

    def test_daemon_is_wrapped_with_pdeathsig_on_linux(self) -> None:
        command = wiz_mcp.daemon_command(["/x/wiz", "lsp"])
        if sys.platform.startswith("linux"):
            self.assertEqual(command[0], sys.executable)
            self.assertIn("prctl", command[2])
            self.assertEqual(command[-2:], ["/x/wiz", "lsp"])
        else:
            self.assertEqual(command, ["/x/wiz", "lsp"])


def frame(payload: object) -> bytes:
    body = json.dumps(payload).encode("utf-8")
    return b"Content-Length: %d\r\n\r\n" % len(body) + body


class StdioTransportTests(unittest.TestCase):
    """`StdioLSP` over a pair of OS pipes, as it is used on the daemon's stdin/stdout."""

    def setUp(self) -> None:
        to_daemon_r, to_daemon_w = os.pipe()
        from_daemon_r, from_daemon_w = os.pipe()
        self.daemon_in = os.fdopen(to_daemon_r, "rb", buffering=0)
        self.daemon_out = os.fdopen(from_daemon_w, "wb", buffering=0)
        self.client_read = os.fdopen(from_daemon_r, "rb", buffering=0)
        self.conn = wiz_mcp.StdioLSP(os.fdopen(to_daemon_w, "wb", buffering=0), self.client_read.fileno())

    def tearDown(self) -> None:
        self.conn.close()
        for stream in (self.daemon_in, self.daemon_out, self.client_read):
            stream.close()

    def test_send_frames_with_a_byte_length(self) -> None:
        self.conn.send_text('{"x":"λ"}', time.monotonic() + 1)
        self.assertEqual(self.daemon_in.read(64), b'Content-Length: 10\r\n\r\n{"x":"\xce\xbb"}')

    def test_two_messages_in_one_write(self) -> None:
        self.daemon_out.write(frame({"id": 1}) + frame({"id": 2, "s": "λ"}))
        self.assertEqual(json.loads(self.conn.recv_text(time.monotonic() + 1)), {"id": 1})
        self.assertEqual(json.loads(self.conn.recv_text(time.monotonic() + 1)), {"id": 2, "s": "λ"})

    def test_a_message_split_across_writes(self) -> None:
        data = b"Content-Type: x\r\n" + frame({"method": "m", "params": {"k": "v" * 5000}})

        def dribble() -> None:
            for i in range(0, len(data), 7):
                self.daemon_out.write(data[i : i + 7])

        writer = threading.Thread(target=dribble)
        writer.start()
        message = json.loads(self.conn.recv_text(time.monotonic() + 5))
        writer.join()
        self.assertEqual(message["params"]["k"], "v" * 5000)

    def test_a_header_without_content_length_is_an_error(self) -> None:
        self.daemon_out.write(b"X-Other: 1\r\n\r\n{}")
        with self.assertRaises(wiz_mcp.LSPError):
            self.conn.recv_text(time.monotonic() + 1)

    def test_a_bad_content_length_is_an_error(self) -> None:
        self.daemon_out.write(b"Content-Length: lots\r\n\r\n{}")
        with self.assertRaises(wiz_mcp.LSPError):
            self.conn.recv_text(time.monotonic() + 1)

    def test_eof_is_closed(self) -> None:
        self.daemon_out.close()
        with self.assertRaises(wiz_mcp.LSPClosed):
            self.conn.recv_text(time.monotonic() + 1)

    def test_a_silent_daemon_hits_the_read_deadline(self) -> None:
        started = time.monotonic()
        with self.assertRaises(wiz_mcp.LSPTimeout):
            self.conn.recv_text(time.monotonic() + 0.2)
        self.assertLess(time.monotonic() - started, 2.0)

    def test_a_daemon_that_does_not_read_hits_the_write_deadline(self) -> None:
        started = time.monotonic()
        with self.assertRaises(wiz_mcp.LSPTimeout):
            self.conn.send_text("x" * (4 * 1024 * 1024), time.monotonic() + 0.3)
        self.assertLess(time.monotonic() - started, 2.0)

    def test_send_after_close_is_closed_and_close_is_idempotent(self) -> None:
        self.conn.close()
        self.conn.close()
        with self.assertRaises(wiz_mcp.LSPClosed):
            self.conn.send_text("{}", time.monotonic() + 1)

    def test_a_dead_reader_is_closed(self) -> None:
        self.daemon_in.close()
        with self.assertRaises(wiz_mcp.LSPClosed):
            self.conn.send_text("{}", time.monotonic() + 1)


#: A stand-in `wiz lsp`: Content-Length LSP on stdio, as the real one speaks it.
FAKE_LSP = r'''
import json, os, sys
inp, out = sys.stdin.buffer, sys.stdout.buffer

def send(message):
    body = json.dumps(message).encode()
    out.write(b"Content-Length: %d\r\n\r\n" % len(body) + body)
    out.flush()

def read():
    length = None
    while True:
        line = inp.readline()
        if not line:
            return None
        line = line.strip()
        if not line:
            break
        name, _, value = line.decode().partition(":")
        if name.lower() == "content-length":
            length = int(value)
    return json.loads(inp.read(length))

if sys.argv[1:2] != ["lsp"]:
    print("not lsp:", sys.argv[1:]); sys.exit(0)
if os.environ.get("FAKE_LSP_MODE") == "mute":
    while read() is not None:
        pass
    sys.exit(0)
# A server-to-client request the bridge never answers must not confuse it.
send({"jsonrpc": "2.0", "id": "s1", "method": "window/workDoneProgress/create", "params": {"token": "t"}})
while True:
    message = read()
    if message is None:
        break
    method, mid = message.get("method"), message.get("id")
    if method == "initialize":
        send({"jsonrpc": "2.0", "id": mid, "result": {"capabilities": {}}})
    elif method == "textDocument/didOpen":
        doc = message["params"]["textDocument"]
        diags = [{"range": {"start": {"line": 0, "character": 0}, "end": {"line": 0, "character": 1}},
                  "severity": 1, "message": "fake: %d chars" % len(doc["text"])}]
        send({"jsonrpc": "2.0", "method": "textDocument/publishDiagnostics",
              "params": {"uri": doc["uri"], "diagnostics": diags}})
    elif method == "textDocument/hover":
        send({"jsonrpc": "2.0", "id": mid, "result": {"contents": "Nat"}})
    elif method in ("textDocument/definition", "textDocument/declaration", "textDocument/references"):
        uri = message["params"]["textDocument"]["uri"]
        rng = {"start": {"line": 2, "character": 4}, "end": {"line": 2, "character": 10}}
        outside = os.environ.get("FAKE_OUTSIDE", "/nonexistent")
        send({"jsonrpc": "2.0", "id": mid, "result": [
            {"uri": uri, "range": rng},
            {"targetUri": uri, "targetRange": rng, "targetSelectionRange": rng},
            {"uri": "file://" + outside + "/secret.wiz", "range": rng},
            {"uri": "https://example.com/x.wiz", "range": rng},
            {"uri": "file://" + os.environ.get("FAKE_LIB", "/nonexistent") + "/Prelude.wiz", "range": rng},
        ]})
    elif method == "textDocument/documentSymbol":
        send({"jsonrpc": "2.0", "id": mid, "result": [{"name": "S", "kind": 23, "children": [{"name": "f", "kind": 8}]}]})
    elif method == "workspace/symbol":
        uri = "file://" + os.getcwd() + "/probe.wiz"
        send({"jsonrpc": "2.0", "id": mid, "result": [
            {"name": "mine", "kind": 12, "location": {"uri": uri, "range": {"start": {"line": 0, "character": 0}}}},
            {"name": "theirs", "kind": 12, "location": {"uri": "file://" + os.environ.get("FAKE_OUTSIDE", "/x") + "/s.wiz"}},
            {"name": "q=" + message["params"]["query"], "kind": 13, "location": None},
        ]})
    elif method in ("wiz/plainTermGoal", "wiz/plainGoal", "textDocument/signatureHelp"):
        send({"jsonrpc": "2.0", "id": mid, "result": {"method": method, "position": message["params"]["position"]}})
    elif method == "textDocument/completion":
        items = [{"label": "c%d" % i, "kind": 3, "detail": "Nat", "documentation": {"kind": "markdown", "value": "doc"},
                  "textEdit": {"newText": "c%d" % i}} for i in range(120)]
        send({"jsonrpc": "2.0", "id": mid, "result": {"isIncomplete": True, "items": items}})
    elif method == "textDocument/inlayHint":
        send({"jsonrpc": "2.0", "id": mid, "result": [{"position": {"line": 0, "character": 1}, "label": ": Nat", "range": message["params"]["range"]}]})
    elif method == "textDocument/codeAction":
        uri = message["params"]["textDocument"]["uri"]
        outside = os.environ.get("FAKE_OUTSIDE", "/nonexistent")
        edit = lambda u: {"changes": {u: [{"range": {"start": {"line": 0, "character": 0}, "end": {"line": 0, "character": 1}}, "newText": "y"}]}}
        send({"jsonrpc": "2.0", "id": mid, "result": [
            {"title": "fix here", "kind": "quickfix", "edit": edit(uri),
             "diagnostics": [{"range": {"start": {"line": 0, "character": 0}, "end": {"line": 0, "character": 1}}, "severity": 1, "message": "m", "code": "c"}]},
            {"title": "fix elsewhere", "kind": "quickfix", "edit": edit("file://" + outside + "/secret.wiz")},
            {"title": "no edit", "kind": "refactor"},
        ]})
    elif method == "textDocument/rename":
        uri = message["params"]["textDocument"]["uri"]
        new = message["params"]["newName"]
        outside = os.environ.get("FAKE_OUTSIDE", "/nonexistent")
        te = [{"range": {"start": {"line": 2, "character": 4}, "end": {"line": 2, "character": 10}}, "newText": new}]
        if new == "nothing":
            send({"jsonrpc": "2.0", "id": mid, "result": None})
        elif new == "refused":
            send({"jsonrpc": "2.0", "id": mid, "error": {"code": -32803, "message": "declared in the toolchain"}})
        elif new == "outside":
            send({"jsonrpc": "2.0", "id": mid, "result": {"changes": {uri: te, "file://" + outside + "/secret.wiz": te}}})
        elif new == "create":
            send({"jsonrpc": "2.0", "id": mid, "result": {"documentChanges": [{"kind": "create", "uri": uri + ".new"}]}})
        else:
            send({"jsonrpc": "2.0", "id": mid, "result": {"documentChanges": [{"textDocument": {"uri": uri, "version": 1}, "edits": te}]}})
    elif method == "fake/selfcheck":
        links = []
        for fd in os.listdir("/proc/self/fd"):
            try:
                links.append(os.readlink("/proc/self/fd/" + fd))
            except OSError:
                pass
        send({"jsonrpc": "2.0", "id": mid, "result": {"argv": sys.argv[1:], "fds": links,
              "token_env": sorted(k for k in os.environ if "TOKEN" in k)}})
    elif mid is not None:
        send({"jsonrpc": "2.0", "id": mid, "error": {"code": -32601, "message": method}})
'''


class StdioDaemonTests(unittest.TestCase):
    """The bridge against a fake stdio language server: the whole LSP path, no socket."""

    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory(prefix="wiz-mcp-stdio-")
        self.workspace = os.path.realpath(self.tmp.name)
        self.script = os.path.join(self.workspace, "fake_lsp.py")
        Path(self.script).write_text(FAKE_LSP, encoding="utf-8")
        self.wiz = write_exe(self.workspace, "wiz", f'exec "{sys.executable}" "{self.script}" "$@"')
        Path(self.workspace, "probe.wiz").write_text("def x : Nat := 1\n")

    def tearDown(self) -> None:
        self.tmp.cleanup()

    def server(self, wiz: str = "", timeout: float = 10) -> wiz_mcp.Server:
        config = wiz_mcp.Config(workspace=self.workspace, wiz=wiz or self.wiz, idle=0, timeout=timeout)
        server = wiz_mcp.Server(config)
        self.addCleanup(server.close)
        return server

    def test_diagnostics_and_hover_over_stdio(self) -> None:
        server = self.server()
        envelope = server.call_tool("diagnostics", {"path": "probe.wiz", "text": "abc"})
        self.assertTrue(envelope["ok"], envelope)
        result = envelope["result"]
        self.assertEqual(result["diagnostics"][0]["message"], "fake: 3 chars")
        self.assertEqual(result["counts"], {"error": 1, "warning": 0, "info": 0})
        self.assertEqual(result["source"], "lsp")
        # The language server's own objects stay available, unchanged.
        self.assertEqual(result["raw"][0]["message"], "fake: 3 chars")
        self.assertEqual(result["raw"][0]["severity"], 1)
        self.assertEqual(result["diagnostics"][0]["range"], result["raw"][0]["range"])
        proc = server.daemon.proc
        envelope = server.call_tool("hover", {"path": "probe.wiz", "line": 0, "character": 4})
        self.assertTrue(envelope["ok"], envelope)
        self.assertEqual(envelope["result"], {"contents": "Nat"})
        self.assertIs(server.daemon.proc, proc)  # one daemon served both calls

    @unittest.skipUnless(os.path.isdir("/proc/self/fd"), "needs /proc")
    def test_the_daemon_listens_on_no_socket_and_gets_no_tokens(self) -> None:
        saved = os.environ.get("GH_TOKEN")
        os.environ["GH_TOKEN"] = "do-not-leak"

        def restore() -> None:
            if saved is None:
                os.environ.pop("GH_TOKEN", None)
            else:
                os.environ["GH_TOKEN"] = saved

        self.addCleanup(restore)
        server = self.server()
        deadline = time.monotonic() + 10
        server.daemon.ensure(deadline)
        result = server.daemon.request("fake/selfcheck", {}, deadline)["result"]
        self.assertEqual(result["argv"], ["lsp"])
        self.assertFalse([link for link in result["fds"] if link.startswith("socket:")], result["fds"])
        self.assertEqual(result["token_env"], [])

    def test_close_stops_the_daemon(self) -> None:
        server = self.server()
        self.assertTrue(server.call_tool("hover", {"path": "probe.wiz", "line": 0, "character": 0})["ok"])
        proc = server.daemon.proc
        assert proc is not None
        server.close()
        self.assertIsNotNone(proc.poll())
        self.assertIsNone(server.daemon.conn)

    def test_a_daemon_that_never_answers_initialize_times_out(self) -> None:
        # The child environment is filtered, so the mode is set in the wrapper itself.
        mute = write_exe(self.workspace, "mute-wiz", f'FAKE_LSP_MODE=mute exec "{sys.executable}" "{self.script}" "$@"')
        server = self.server(wiz=mute, timeout=0.5)
        started = time.monotonic()
        envelope = server.call_tool("diagnostics", {"path": "probe.wiz"})
        self.assertLess(time.monotonic() - started, 5.0)
        self.assertFalse(envelope["ok"])
        self.assertEqual(envelope["error"]["kind"], "timeout")
        self.assertIsNone(server.daemon.proc)

    def test_check_with_source_lsp_uses_the_daemon(self) -> None:
        server = self.server()
        envelope = server.call_tool("check", {"path": "probe.wiz", "source": "lsp", "text": "abcd"})
        self.assertFalse(envelope["ok"], envelope)  # the fake reports one error
        self.assertIsNone(envelope["exit"])
        self.assertIsNone(envelope["error"])
        result = envelope["result"]
        self.assertEqual(result["source"], "lsp")
        self.assertEqual(result["counts"], {"error": 1, "warning": 0, "info": 0})
        (diagnostic,) = result["diagnostics"]
        self.assertEqual(diagnostic["message"], "fake: 4 chars")
        self.assertEqual(diagnostic["file"], os.path.join(self.workspace, "probe.wiz"))
        self.assertEqual((diagnostic["line"], diagnostic["column"]), (1, 1))
        self.assertEqual(diagnostic["range"]["end"], {"line": 0, "character": 1})


#: Every language-server tool with the smallest valid arguments (besides `path`).
LSP_TOOL_ARGS = {
    "diagnostics": {},
    "hover": {"line": 0, "character": 0},
    "goals": {"line": 0, "character": 0},
    "definition": {"line": 0, "character": 0},
    "references": {"line": 0, "character": 0},
    "document_symbols": {},
    "workspace_symbols": {"query": "x"},
    "term_goal": {"line": 0, "character": 0},
    "completion": {"line": 0, "character": 0},
    "signature_help": {"line": 0, "character": 0},
    "inlay_hints": {},
    "code_actions": {"line": 0, "character": 0},
    "rename": {"line": 0, "character": 0, "new_name": "y"},
}


class NavigationToolTests(unittest.TestCase):
    """P1c: the read-only language-server tools, against the fake stdio server."""

    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory(prefix="wiz-mcp-nav-")
        base = os.path.realpath(self.tmp.name)
        self.workspace = os.path.join(base, "ws")
        self.outside = os.path.join(base, "outside")
        self.lib = os.path.join(base, "toolchain", "share", "wiz", "lib")
        for d in (self.workspace, self.outside, self.lib, os.path.join(base, "toolchain", "bin")):
            os.makedirs(d)
        Path(self.outside, "secret.wiz").write_text("secret\n")
        Path(self.lib, "Prelude.wiz").write_text("-- prelude\n")
        Path(self.workspace, "probe.wiz").write_text("def x : Nat := 1\n")
        script = os.path.join(base, "fake_lsp.py")
        Path(script).write_text(FAKE_LSP, encoding="utf-8")
        # The child environment is filtered, so the fake's settings live in the wrapper.
        self.wiz = write_exe(
            os.path.join(base, "toolchain", "bin"),
            "wiz",
            f'FAKE_OUTSIDE="{self.outside}" FAKE_LIB="{self.lib}" exec "{sys.executable}" "{script}" "$@"',
        )
        self.server = wiz_mcp.Server(wiz_mcp.Config(workspace=self.workspace, wiz=self.wiz, idle=0, timeout=10))
        self.probe = os.path.join(self.workspace, "probe.wiz")

    def tearDown(self) -> None:
        self.server.close()
        self.tmp.cleanup()

    def call(self, name: str, **args) -> dict:
        envelope = self.server.call_tool(name, dict({"path": "probe.wiz"}, **args))
        return envelope

    def ok(self, name: str, **args):
        envelope = self.call(name, **args)
        self.assertTrue(envelope["ok"], envelope)
        return envelope["result"]

    def test_every_new_tool_is_listed_read_only(self) -> None:
        responses, _ = self.server.dispatch({"jsonrpc": "2.0", "id": 1, "method": "tools/list", "params": {}})
        tools = {tool["name"]: tool for tool in responses[0]["result"]["tools"]}
        for name in LSP_TOOL_ARGS:
            self.assertIn(name, tools)
            self.assertIs(tools[name]["annotations"]["readOnlyHint"], True, name)
            self.assertIs(tools[name]["annotations"]["destructiveHint"], False, name)

    def test_every_lsp_tool_refuses_an_input_path_outside(self) -> None:
        for name, args in LSP_TOOL_ARGS.items():
            for path in (os.path.join(self.outside, "secret.wiz"), "../outside/secret.wiz"):
                envelope = self.server.call_tool(name, dict(args, path=path))
                self.assertFalse(envelope["ok"], (name, envelope))
                self.assertEqual(envelope["error"]["kind"], "path_denied", (name, envelope))
        self.assertIsNone(self.server.daemon.proc)  # nothing reached the daemon

    def test_definition_keeps_workspace_and_toolchain_locations_and_withholds_the_rest(self) -> None:
        result = self.ok("definition", line=0, character=4)
        files = [loc["file"] for loc in result["locations"]]
        self.assertEqual(files, [self.probe, self.probe, os.path.join(self.lib, "Prelude.wiz")])
        self.assertEqual(result["withheld"], 2)  # the outside file and the https: URI
        self.assertNotIn(self.outside, json.dumps(result))
        first = result["locations"][0]
        self.assertEqual((first["line"], first["column"]), (3, 5))
        self.assertEqual(first["range"]["end"], {"line": 2, "character": 10})

    def test_declaration_and_references_use_their_methods(self) -> None:
        self.assertEqual(self.ok("definition", line=0, character=4, declaration=True)["withheld"], 2)
        self.assertEqual(len(self.ok("references", line=0, character=4)["locations"]), 3)

    def test_document_symbols_have_kind_names(self) -> None:
        result = self.ok("document_symbols")
        self.assertEqual(result[0]["kindName"], "struct")
        self.assertEqual(result[0]["children"][0]["kindName"], "field")

    def test_workspace_symbols_withhold_outside_locations(self) -> None:
        result = self.ok("workspace_symbols", query="mi")
        names = [symbol["name"] for symbol in result["symbols"]]
        self.assertEqual(names, ["mine", "q=mi"])
        self.assertEqual(result["withheld"], 1)
        self.assertEqual(result["symbols"][0]["location"]["file"], self.probe)
        self.assertIsNone(result["symbols"][1]["location"])
        self.assertNotIn(self.outside, json.dumps(result))
        self.assertEqual(self.call("workspace_symbols")["error"]["kind"], "invalid_args")

    def test_goal_and_signature_tools_use_their_methods(self) -> None:
        self.assertEqual(self.ok("term_goal", line=1, character=2)["method"], "wiz/plainTermGoal")
        self.assertEqual(self.ok("goals", line=1, character=2, plain=True)["method"], "wiz/plainGoal")
        self.assertEqual(self.ok("signature_help", line=1, character=2)["position"], {"line": 1, "character": 2})

    def test_completion_is_limited_and_compact(self) -> None:
        result = self.ok("completion", line=0, character=1, limit=5)
        self.assertEqual(len(result["items"]), 5)
        self.assertEqual(result["total"], 120)
        self.assertTrue(result["incomplete"])
        self.assertEqual(result["items"][0], {"label": "c0", "kind": "function", "detail": "Nat", "documentation": "doc", "insert": "c0"})
        self.assertEqual(len(self.ok("completion", line=0, character=1)["items"]), 50)
        self.assertEqual(self.call("completion", line=0, character=1, limit=0)["error"]["kind"], "invalid_args")

    def test_inlay_hints_default_to_the_whole_file(self) -> None:
        result = self.ok("inlay_hints")
        self.assertEqual(result[0]["range"], {"start": {"line": 0, "character": 0}, "end": {"line": 2, "character": 0}})
        result = self.ok("inlay_hints", start_line=1, end_line=1)
        self.assertEqual(result[0]["range"]["start"]["line"], 1)

    def test_code_actions_are_proposals_confined_to_the_workspace(self) -> None:
        before = Path(self.probe).read_text()
        result = self.ok("code_actions", line=0, character=0)
        self.assertIs(result["applied"], False)
        self.assertEqual([action["title"] for action in result["actions"]], ["fix here", "no edit"])
        self.assertEqual(result["withheld"], 1)
        fix = result["actions"][0]
        self.assertEqual(fix["edit"]["files"][0]["file"], self.probe)
        self.assertIs(fix["edit"]["applied"], False)
        self.assertEqual(fix["fixes"][0]["code"], "c")
        self.assertIsNone(result["actions"][1]["edit"])
        self.assertNotIn(self.outside, json.dumps(result))
        self.assertEqual(Path(self.probe).read_text(), before)  # nothing applied

    def test_rename_is_a_proposal(self) -> None:
        before = Path(self.probe).read_text()
        result = self.ok("rename", line=2, character=5, new_name="twice")
        self.assertEqual(result, {
            "applied": False,
            "files": [{"file": self.probe, "edits": [{"range": {"start": {"line": 2, "character": 4}, "end": {"line": 2, "character": 10}}, "newText": "twice"}]}],
            "edit_count": 1,
        })
        self.assertEqual(Path(self.probe).read_text(), before)

    def test_rename_touching_a_file_outside_is_refused_whole(self) -> None:
        envelope = self.call("rename", line=2, character=5, new_name="outside")
        self.assertEqual(envelope["error"]["kind"], "path_denied")
        self.assertIsNone(envelope["result"])
        self.assertNotIn(self.outside, json.dumps(envelope))

    def test_rename_creating_files_is_refused(self) -> None:
        self.assertEqual(self.call("rename", line=2, character=5, new_name="create")["error"]["kind"], "path_denied")

    def test_rename_refusals_keep_the_daemon(self) -> None:
        self.assertEqual(self.call("rename", line=2, character=5, new_name="nothing")["error"]["kind"], "lsp_refused")
        proc = self.server.daemon.proc
        envelope = self.call("rename", line=2, character=5, new_name="refused")
        self.assertEqual(envelope["error"]["kind"], "lsp_refused")
        self.assertIn("declared in the toolchain", envelope["error"]["message"])
        self.assertIs(self.server.daemon.proc, proc)
        self.assertIsNone(proc.poll())


class LocationHelperTests(unittest.TestCase):
    def test_uri_to_path(self) -> None:
        with tempfile.TemporaryDirectory(prefix="wiz-mcp-uri-") as tmp:
            plain = os.path.join(tmp, "a b%20c.wiz")
            Path(plain).write_text("")
            # Wiz writes library URIs unescaped: a literal "%20" in a name must survive.
            self.assertEqual(wiz_mcp.uri_to_path("file://" + plain), plain)
        self.assertEqual(wiz_mcp.uri_to_path("file:///no/such/a%20b.wiz"), "/no/such/a b.wiz")
        self.assertEqual(wiz_mcp.uri_to_path("file://localhost/x.wiz"), "/x.wiz")
        self.assertEqual(wiz_mcp.uri_to_path("file:///x/../y.wiz"), "/y.wiz")
        for bad in ("https://example.com/x", "untitled:1", "file://host/x", None, 3):
            self.assertIsNone(wiz_mcp.uri_to_path(bad))
        self.assertEqual(wiz_mcp.uri_to_path("file:///enc%23", {"file:///enc%23": "/w/enc#"}), "/w/enc#")

    def test_confine_locations_accepts_one_many_or_none(self) -> None:
        roots = ["/w"]
        loc = {"uri": "file:///w/a.wiz", "range": {"start": {"line": 1, "character": 2}}}
        self.assertEqual(wiz_mcp.confine_locations(None, roots), ([], 0))
        one, hidden = wiz_mcp.confine_locations(loc, roots)
        self.assertEqual((one[0]["line"], one[0]["column"], hidden), (2, 3, 0))
        self.assertEqual(one[0]["range"]["end"], {"line": 1, "character": 2})
        self.assertEqual(wiz_mcp.confine_locations([loc, {"uri": "file:///etc/passwd"}, "junk"], roots)[1], 1)

    def test_a_symlink_out_of_a_root_is_withheld(self) -> None:
        with tempfile.TemporaryDirectory(prefix="wiz-mcp-uri-") as tmp:
            base = os.path.realpath(tmp)
            os.makedirs(os.path.join(base, "w"))
            os.makedirs(os.path.join(base, "o"))
            Path(base, "o", "s.wiz").write_text("")
            os.symlink(os.path.join(base, "o", "s.wiz"), os.path.join(base, "w", "link.wiz"))
            locations, hidden = wiz_mcp.confine_locations({"uri": "file://" + os.path.join(base, "w", "link.wiz")}, [os.path.join(base, "w")])
            self.assertEqual((locations, hidden), ([], 1))
            with self.assertRaises(wiz_mcp.ToolError) as caught:
                wiz_mcp.propose_edit({"changes": {"file://" + os.path.join(base, "w", "link.wiz"): []}}, [os.path.join(base, "w")])
            self.assertEqual(caught.exception.kind, "path_denied")

    def test_propose_edit_merges_changes_and_document_changes(self) -> None:
        te = {"range": {}, "newText": "z"}
        got = wiz_mcp.propose_edit(
            {"changes": {"file:///w/b.wiz": [te]},
             "documentChanges": [{"textDocument": {"uri": "file:///w/a.wiz"}, "edits": [te, te]}]},
            ["/w"],
        )
        self.assertEqual(got["applied"], False)
        self.assertEqual([f["file"] for f in got["files"]], ["/w/a.wiz", "/w/b.wiz"])
        self.assertEqual(got["edit_count"], 3)
        for bad in (None, {"documentChanges": [{"kind": "delete", "uri": "file:///w/a.wiz"}]},
                    {"changes": {"untitled:1": [te]}}):
            with self.assertRaises(wiz_mcp.ToolError):
                wiz_mcp.propose_edit(bad, ["/w"])


# Real `wiz check` output (master d23473da), with PATH standing for the checked file.
REAL_STDOUT = "PATH:3:1: info: a : Nat\n"
REAL_STDERR = (
    "PATH:4:16: error: type mismatch\n"
    "  expected: Nat\n"
    "  inferred: Bool\n"
    "PATH:6:6: error: unexpected 'λ'; expected '.{', '(', '{', '[', ':' or ':='\n"
    "PATH:7:1: error: unexpected 'theorem'; expected command\n"
)


class CheckDiagnosticsTests(unittest.TestCase):
    """`check`'s structured diagnostics: the CLI parser, the LSP normalizer, the tool."""

    path = "/w/dir:with colon/errs.wiz"

    def parse(self, stdout: str, stderr: str = "") -> tuple[list, list]:
        return wiz_mcp.parse_check_output(
            self.path, stdout.replace("PATH", self.path), stderr.replace("PATH", self.path)
        )

    def test_real_output_is_parsed_in_position_order(self) -> None:
        diagnostics, unparsed = self.parse(REAL_STDOUT, REAL_STDERR)
        self.assertEqual(unparsed, [])
        self.assertEqual(
            [(d["line"], d["column"], d["severity"]) for d in diagnostics],
            [(3, 1, "info"), (4, 16, "error"), (6, 6, "error"), (7, 1, "error")],
        )
        self.assertEqual(diagnostics[1]["message"], "type mismatch\n  expected: Nat\n  inferred: Bool")
        self.assertEqual(diagnostics[1]["range"], {"start": {"line": 3, "character": 15}, "end": {"line": 3, "character": 15}})
        self.assertTrue(all(d["file"] == self.path and d["code"] is None for d in diagnostics))

    def test_a_colon_in_the_path_does_not_confuse_the_parser(self) -> None:
        diagnostics, _ = self.parse("", "PATH:1:9: error: unknown identifier 'Nat'\n")
        self.assertEqual((diagnostics[0]["line"], diagnostics[0]["column"]), (1, 9))
        self.assertEqual(diagnostics[0]["message"], "unknown identifier 'Nat'")

    def test_a_message_without_severity_is_an_error(self) -> None:
        diagnostics, _ = self.parse("", "PATH:2:1: unexpected end of input\n")
        self.assertEqual(diagnostics[0]["severity"], "error")
        self.assertEqual(diagnostics[0]["message"], "unexpected end of input")

    def test_an_import_error_keeps_its_indented_list(self) -> None:
        stderr = "PATH:1:1: error: module Foo has errors:\n  Foo:3:4: error: unknown identifier 'x'\nimported module Foo → bad\n"
        diagnostics, unparsed = self.parse("", stderr)
        self.assertEqual(len(diagnostics), 1)
        self.assertEqual(unparsed, [])
        self.assertIn("  Foo:3:4: error: unknown identifier 'x'", diagnostics[0]["message"])
        self.assertTrue(diagnostics[0]["message"].endswith("imported module Foo → bad"))

    def test_lines_that_are_not_messages_are_kept_apart(self) -> None:
        stderr = "warming up\nPATH:1:1: error: boom\nregion cache: 3 modules from a region\nuncaught exception: oops\n"
        diagnostics, unparsed = self.parse("", stderr)
        self.assertEqual([d["message"] for d in diagnostics], ["boom"])
        self.assertEqual(unparsed, ["warming up", "region cache: 3 modules from a region", "uncaught exception: oops"])

    def test_another_files_messages_are_not_this_files(self) -> None:
        diagnostics, unparsed = self.parse("", "/w/other.wiz:1:1: error: elsewhere\n")
        self.assertEqual(diagnostics, [])
        self.assertEqual(unparsed, ["/w/other.wiz:1:1: error: elsewhere"])

    def test_lsp_diagnostics_are_normalized(self) -> None:
        got = wiz_mcp.lsp_diagnostic(
            "/w/a.wiz",
            {"range": {"start": {"line": 3, "character": 15}, "end": {"line": 3, "character": 24}},
             "severity": 1, "source": "wiz", "message": "type mismatch", "code": "type-mismatch", "data": {"x": 1}},
        )
        self.assertEqual(
            got,
            {"file": "/w/a.wiz", "line": 4, "column": 16,
             "range": {"start": {"line": 3, "character": 15}, "end": {"line": 3, "character": 24}},
             "severity": "error", "code": "type-mismatch", "message": "type mismatch"},
        )
        self.assertEqual(wiz_mcp.lsp_diagnostic("/w/a.wiz", {"severity": 2, "message": "w"})["severity"], "warning")
        self.assertEqual(wiz_mcp.lsp_diagnostic("/w/a.wiz", {"severity": 3, "message": "i", "code": ""})["code"], None)

    def test_counts_cover_every_severity(self) -> None:
        diagnostics, _ = self.parse(REAL_STDOUT, REAL_STDERR)
        self.assertEqual(wiz_mcp.check_result("cli", diagnostics)["counts"], {"error": 3, "warning": 0, "info": 1})
        self.assertEqual(wiz_mcp.check_result("cli", [])["counts"], {"error": 0, "warning": 0, "info": 0})

    def test_the_check_tool_returns_them_with_the_raw_output(self) -> None:
        with tempfile.TemporaryDirectory(prefix="wiz-mcp-check-") as tmp:
            workspace = os.path.realpath(tmp)
            Path(workspace, "errs.wiz").write_text("x\n")
            out = Path(workspace, "out.txt")
            err = Path(workspace, "err.txt")
            target = os.path.join(workspace, "errs.wiz")
            out.write_text(REAL_STDOUT.replace("PATH", target))
            err.write_text(REAL_STDERR.replace("PATH", target))
            wiz = write_exe(workspace, "wiz", f'cat "{out}"; cat "{err}" >&2; exit 1')
            server = wiz_mcp.Server(wiz_mcp.Config(workspace=workspace, wiz=wiz, idle=0, timeout=5))
            try:
                envelope = server.call_tool("check", {"path": "errs.wiz"})
                bad_source = server.call_tool("check", {"path": "errs.wiz", "source": "both"})
                text_without_lsp = server.call_tool("check", {"path": "errs.wiz", "text": "x"})
            finally:
                server.close()
        self.assertFalse(envelope["ok"])
        self.assertEqual(envelope["exit"], 1)
        self.assertIsNone(envelope["error"])
        self.assertIn("type mismatch", envelope["stderr"])
        self.assertEqual(envelope["result"]["source"], "cli")
        self.assertEqual(envelope["result"]["counts"], {"error": 3, "warning": 0, "info": 1})
        self.assertEqual(envelope["result"]["diagnostics"][0]["file"], target)
        self.assertEqual(bad_source["error"]["kind"], "invalid_args")
        self.assertEqual(text_without_lsp["error"]["kind"], "invalid_args")

    def test_a_clean_check_has_an_empty_list(self) -> None:
        with tempfile.TemporaryDirectory(prefix="wiz-mcp-check-") as tmp:
            workspace = os.path.realpath(tmp)
            Path(workspace, "ok.wiz").write_text("x\n")
            wiz = write_exe(workspace, "wiz", "exit 0")
            server = wiz_mcp.Server(wiz_mcp.Config(workspace=workspace, wiz=wiz, idle=0, timeout=5))
            try:
                envelope = server.call_tool("check", {"path": "ok.wiz"})
            finally:
                server.close()
        self.assertTrue(envelope["ok"])
        self.assertEqual(envelope["result"], {"source": "cli", "diagnostics": [], "counts": {"error": 0, "warning": 0, "info": 0}, "unparsed": []})


class ArgumentTests(unittest.TestCase):
    def test_relative_wiz_defaults_to_the_workspace_build(self) -> None:
        config = wiz_mcp.parse_args(["--workspace", "/tmp"])
        self.assertEqual(config.wiz, "./.lake/build/bin/wiz")
        self.assertEqual(config.workspace, "/tmp")

    def test_zero_idle_disables_unloading(self) -> None:
        config = wiz_mcp.parse_args(["--workspace", "/tmp", "--idle", "0"])
        self.assertEqual(config.idle, 0)

    def test_bad_timeout_is_a_usage_error(self) -> None:
        with self.assertRaises(SystemExit):
            wiz_mcp.parse_args(["--workspace", "/tmp", "--timeout", "0"])

    def test_safety_flags_default_off(self) -> None:
        config = wiz_mcp.parse_args(["--workspace", "/tmp"])
        self.assertFalse(config.allow_build)
        self.assertEqual(config.extra_roots, ())
        self.assertEqual(config.pass_env, ())

    def test_safety_flags_parse(self) -> None:
        with tempfile.TemporaryDirectory(prefix="wiz-mcp-unit-") as tmp:
            os.mkdir(os.path.join(tmp, "extra"))
            config = wiz_mcp.parse_args(
                ["--workspace", tmp, "--allow-build", "--allow-root", "extra", "--pass-env", "FOO"]
            )
            self.assertTrue(config.allow_build)
            self.assertEqual(config.extra_roots, (os.path.realpath(os.path.join(tmp, "extra")),))
            self.assertEqual(config.pass_env, ("FOO",))
            with self.assertRaises(SystemExit):
                wiz_mcp.parse_args(["--workspace", tmp, "--allow-root", "missing"])


class PolicyTests(unittest.TestCase):
    """Path confinement, the build gate, the child environment and annotations."""

    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory(prefix="wiz-mcp-policy-")
        base = os.path.realpath(self.tmp.name)
        self.workspace = os.path.join(base, "ws")
        self.outside = os.path.join(base, "outside")
        os.makedirs(os.path.join(self.workspace, "sub"))
        os.makedirs(self.outside)
        Path(self.workspace, "probe.wiz").write_text("def x : Nat := 1\n")
        Path(self.workspace, "sub", "inner.wiz").write_text("def y : Nat := 2\n")
        Path(self.outside, "secret.wiz").write_text("def s : Nat := 3\n")
        # The stand-in wiz lives outside the workspace, like a tower toolchain.
        tc = os.path.join(base, "toolchain")
        os.makedirs(os.path.join(tc, "bin"))
        os.makedirs(os.path.join(tc, "share", "wiz", "lib"))
        Path(tc, "share", "wiz", "lib", "Prelude.wiz").write_text("-- prelude\n")
        Path(tc, "README").write_text("not library\n")
        self.toolchain = tc
        self.wiz = write_exe(os.path.join(tc, "bin"), "wiz", 'echo "ARGS $*"; env')

    def tearDown(self) -> None:
        self.tmp.cleanup()

    def server(self, **overrides) -> wiz_mcp.Server:
        options = {"workspace": self.workspace, "wiz": self.wiz, "idle": 0, "timeout": 5}
        options.update(overrides)
        server = wiz_mcp.Server(wiz_mcp.Config(**options))
        self.addCleanup(server.close)
        return server

    def assertDenied(self, envelope: dict, kind: str = "path_denied") -> None:
        self.assertFalse(envelope["ok"], envelope)
        self.assertEqual(envelope["error"]["kind"], kind, envelope)
        # The tool must not have run at all.
        self.assertNotIn("ARGS", envelope["stdout"])

    # -- reads -----------------------------------------------------------

    def test_relative_and_absolute_paths_inside_the_workspace_run(self) -> None:
        server = self.server()
        for path in ("probe.wiz", "sub/inner.wiz", "sub/../probe.wiz", os.path.join(self.workspace, "probe.wiz")):
            envelope = server.call_tool("check", {"path": path})
            self.assertTrue(envelope["ok"], (path, envelope))
            self.assertIn("ARGS check", envelope["stdout"])

    def test_absolute_path_outside_is_refused(self) -> None:
        server = self.server()
        for path in (os.path.join(self.outside, "secret.wiz"), "/etc/passwd"):
            for tool in ("check", "parse", "fmt"):
                self.assertDenied(server.call_tool(tool, {"path": path}))

    def test_dotdot_escape_is_refused(self) -> None:
        server = self.server()
        self.assertDenied(server.call_tool("check", {"path": "../outside/secret.wiz"}))
        self.assertDenied(server.call_tool("check", {"path": "sub/../../outside/secret.wiz"}))

    def test_home_expansion_outside_is_refused(self) -> None:
        self.assertDenied(self.server().call_tool("check", {"path": "~/.bashrc"}))

    def test_symlink_out_of_the_workspace_is_refused(self) -> None:
        os.symlink(os.path.join(self.outside, "secret.wiz"), os.path.join(self.workspace, "link.wiz"))
        os.symlink(self.outside, os.path.join(self.workspace, "linkdir"))
        server = self.server()
        self.assertDenied(server.call_tool("check", {"path": "link.wiz"}))
        self.assertDenied(server.call_tool("check", {"path": "linkdir/secret.wiz"}))

    def test_symlink_within_the_workspace_is_allowed(self) -> None:
        os.symlink(os.path.join(self.workspace, "sub", "inner.wiz"), os.path.join(self.workspace, "alias.wiz"))
        envelope = self.server().call_tool("check", {"path": "alias.wiz"})
        self.assertTrue(envelope["ok"], envelope)

    def test_lsp_tools_are_confined_before_the_daemon_starts(self) -> None:
        server = self.server()
        outside = os.path.join(self.outside, "secret.wiz")
        self.assertDenied(server.call_tool("diagnostics", {"path": outside, "text": "def z : Nat := 0\n"}))
        self.assertDenied(server.call_tool("hover", {"path": "../outside/secret.wiz", "line": 0, "character": 4}))
        self.assertDenied(server.call_tool("goals", {"path": outside, "line": 0, "character": 4}))
        self.assertIsNone(server.daemon.proc)

    def test_toolchain_library_is_readable_but_not_the_rest_of_the_prefix(self) -> None:
        server = self.server()
        lib = os.path.join(self.toolchain, "share", "wiz", "lib", "Prelude.wiz")
        self.assertTrue(server.call_tool("check", {"path": lib})["ok"])
        self.assertDenied(server.call_tool("check", {"path": os.path.join(self.toolchain, "README")}))

    def test_checkout_build_reads_its_checkout_lib(self) -> None:
        checkout = os.path.join(os.path.dirname(self.workspace), "checkout")
        os.makedirs(os.path.join(checkout, ".lake", "build", "bin"))
        os.makedirs(os.path.join(checkout, "lib"))
        Path(checkout, "lib", "Nat.wiz").write_text("-- nat\n")
        Path(checkout, "notes.txt").write_text("not library\n")
        wiz = write_exe(os.path.join(checkout, ".lake", "build", "bin"), "wiz", 'echo "ARGS $*"')
        server = self.server(wiz=wiz)
        self.assertTrue(server.call_tool("check", {"path": os.path.join(checkout, "lib", "Nat.wiz")})["ok"])
        self.assertDenied(server.call_tool("check", {"path": os.path.join(checkout, "notes.txt")}))

    def test_allow_root_adds_a_readable_directory(self) -> None:
        server = self.server(extra_roots=(self.outside,))
        self.assertTrue(server.call_tool("check", {"path": os.path.join(self.outside, "secret.wiz")})["ok"])

    # -- the build gate and writes -----------------------------------------

    def test_build_is_off_by_default(self) -> None:
        envelope = self.server().call_tool("build", {"path": "probe.wiz", "out": "probe"})
        self.assertDenied(envelope, kind="not_enabled")
        self.assertIn("--allow-build", envelope["error"]["message"])
        self.assertFalse(os.path.exists(os.path.join(self.workspace, "probe")))

    def test_build_is_off_by_default_over_the_wire_too(self) -> None:
        responses, _ = self.server().dispatch(
            {"jsonrpc": "2.0", "id": 9, "method": "tools/call",
             "params": {"name": "build", "arguments": {"path": "probe.wiz", "out": "probe"}}}
        )
        result = responses[0]["result"]
        self.assertTrue(result["isError"])
        self.assertEqual(result["structuredContent"]["error"]["kind"], "not_enabled")

    def test_build_output_inside_the_workspace_is_allowed(self) -> None:
        envelope = self.server(allow_build=True).call_tool("build", {"path": "probe.wiz", "out": "sub/probe"})
        self.assertTrue(envelope["ok"], envelope)
        self.assertIn("-o " + os.path.join(self.workspace, "sub", "probe"), envelope["stdout"])

    def test_build_output_escapes_are_refused(self) -> None:
        os.symlink(self.outside, os.path.join(self.workspace, "outdir"))
        os.symlink(os.path.join(self.outside, "victim"), os.path.join(self.workspace, "dangling"))
        server = self.server(allow_build=True)
        for out in (
            os.path.join(self.outside, "probe"),  # absolute
            "../outside/probe",  # ..
            "outdir/probe",  # a symlinked directory
            "dangling",  # a symlink to a file that does not exist yet
        ):
            self.assertDenied(server.call_tool("build", {"path": "probe.wiz", "out": out}))
        self.assertEqual(os.listdir(self.outside), ["secret.wiz"])

    def test_build_will_not_write_through_a_symlink_inside_the_workspace(self) -> None:
        os.symlink(os.path.join(self.workspace, "probe.wiz"), os.path.join(self.workspace, "out-link"))
        envelope = self.server(allow_build=True).call_tool("build", {"path": "probe.wiz", "out": "out-link"})
        self.assertDenied(envelope)

    def test_build_output_may_not_go_to_the_toolchain_or_an_extra_root(self) -> None:
        server = self.server(allow_build=True, extra_roots=(self.outside,))
        self.assertDenied(server.call_tool("build", {"path": "probe.wiz", "out": os.path.join(self.outside, "x")}))
        lib = os.path.join(self.toolchain, "share", "wiz", "lib", "x")
        self.assertDenied(server.call_tool("build", {"path": "probe.wiz", "out": lib}))

    # -- environment -------------------------------------------------------

    def test_child_env_is_an_allowlist_without_secrets(self) -> None:
        environ = {
            "PATH": "/bin", "HOME": "/home/u", "LC_ALL": "C.UTF-8",
            "WIZ_CFLAGS": "-I/x", "NIX_CFLAGS_COMPILE": "-I/y",
            "GH_TOKEN": "t", "CACHIX_AUTH_TOKEN": "t", "WIZ_NTFY_TOKEN_FILE": "/t",
            "ANTHROPIC_API_KEY": "k", "AWS_SECRET_ACCESS_KEY": "k", "SSH_AUTH_SOCK": "/s",
            "NIX_GITHUB_PRIVATE_USERNAME": "u", "DBUS_SESSION_BUS_ADDRESS": "x", "FOO": "bar",
        }
        env = wiz_mcp.child_env(environ)
        self.assertEqual(
            set(env), {"PATH", "HOME", "LC_ALL", "WIZ_CFLAGS", "NIX_CFLAGS_COMPILE"}
        )
        self.assertEqual(set(wiz_mcp.child_env(environ, extra=("FOO", "GH_TOKEN"))) - set(env), {"FOO"})

    def test_wiz_runs_with_the_filtered_environment(self) -> None:
        saved = {name: os.environ.get(name) for name in ("GH_TOKEN", "WIZ_MCP_TEST_PLAIN")}
        os.environ["GH_TOKEN"] = "do-not-leak"
        os.environ["WIZ_MCP_TEST_PLAIN"] = "kept"

        def restore() -> None:
            for name, value in saved.items():
                if value is None:
                    os.environ.pop(name, None)
                else:
                    os.environ[name] = value

        self.addCleanup(restore)
        envelope = self.server().call_tool("check", {"path": "probe.wiz"})
        self.assertTrue(envelope["ok"], envelope)
        self.assertNotIn("do-not-leak", envelope["stdout"])
        self.assertNotIn("GH_TOKEN", envelope["stdout"])
        self.assertIn("WIZ_MCP_TEST_PLAIN=kept", envelope["stdout"])

    # -- annotations -------------------------------------------------------

    def test_every_tool_is_annotated(self) -> None:
        for tool in wiz_mcp.TOOLS:
            annotations = tool["annotations"]
            self.assertIs(annotations["openWorldHint"], False, tool["name"])
            self.assertIsInstance(annotations["title"], str)
            if tool["name"] == "build":
                self.assertIs(annotations["readOnlyHint"], False)
                self.assertIs(annotations["destructiveHint"], True)
            else:
                self.assertIs(annotations["readOnlyHint"], True, tool["name"])
                self.assertIs(annotations["destructiveHint"], False, tool["name"])


if __name__ == "__main__":
    unittest.main()
