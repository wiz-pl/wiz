#!/usr/bin/env python3
"""Unit tests for tools/wiz-mcp/wiz_mcp.py (stdlib only).

Run from the repository root:

    python3 -m unittest discover -s tools/wiz-mcp/tests -p 'test_*.py' -v

These tests never need a built `wiz`: the subprocess tests use tiny shell
scripts, and the daemon tests use a stand-in WebSocket object.
"""

from __future__ import annotations

import io
import json
import os
import struct
import sys
import tempfile
import time
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))

import wiz_mcp  # noqa: E402


def write_exe(directory: str, name: str, body: str) -> str:
    path = Path(directory) / name
    path.write_text("#!/bin/sh\nset -eu\n" + body + "\n", encoding="utf-8")
    path.chmod(0o755)
    return str(path)


def decode_client_frame(frame: bytes) -> tuple[int, bytes]:
    """Decode the frames `ws_frame` produces (always FIN + mask)."""
    first, second = frame[0], frame[1]
    length = second & 0x7F
    offset = 2
    if length == 126:
        length = struct.unpack("!H", frame[offset : offset + 2])[0]
        offset += 2
    elif length == 127:
        length = struct.unpack("!Q", frame[offset : offset + 8])[0]
        offset += 8
    assert second & 0x80, "client frames must be masked"
    mask = frame[offset : offset + 4]
    payload = frame[offset + 4 :]
    assert len(payload) == length
    return first & 0x0F, bytes(byte ^ mask[i % 4] for i, byte in enumerate(payload))


class DeadWebSocket:
    """A stand-in that records sends and never answers."""

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

    def test_ws_accept_key_matches_rfc_6455(self) -> None:
        self.assertEqual(
            wiz_mcp.ws_accept_key("dGhlIHNhbXBsZSBub25jZQ=="),
            "s3pPLMBiTxaQ9kYGzzhZRbK+xOo=",
        )

    def test_frame_encoding_for_each_length_form(self) -> None:
        for size in (0, 5, 125, 126, 65535, 65536):
            payload = bytes(range(256)) * (size // 256) + bytes(range(size % 256))
            op, decoded = decode_client_frame(wiz_mcp.ws_frame(0x1, payload))
            self.assertEqual(op, 1)
            self.assertEqual(decoded, payload)


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

    def test_tools_list_has_the_eight_tools(self) -> None:
        responses, _ = self.dispatch({"jsonrpc": "2.0", "id": 2, "method": "tools/list", "params": {}})
        names = {tool["name"] for tool in responses[0]["result"]["tools"]}
        self.assertEqual(
            names,
            {"version", "check", "parse", "fmt", "build", "diagnostics", "hover", "goals"},
        )

    def test_notifications_get_no_reply(self) -> None:
        self.assertEqual(self.dispatch({"jsonrpc": "2.0", "method": "notifications/initialized"}), ([], False))
        self.assertEqual(self.dispatch({"jsonrpc": "2.0", "method": "exit"}), ([], True))

    def test_unknown_tool_is_a_jsonrpc_error(self) -> None:
        responses, _ = self.dispatch(
            {"jsonrpc": "2.0", "id": 3, "method": "tools/call", "params": {"name": "nope", "arguments": {}}}
        )
        self.assertEqual(responses[0]["error"]["code"], -32602)

    def test_unknown_method_is_a_jsonrpc_error(self) -> None:
        responses, _ = self.dispatch({"jsonrpc": "2.0", "id": 4, "method": "resources/list", "params": {}})
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
        self.assertIsNone(self.server.daemon.ws)
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
        ws = DeadWebSocket()
        self.daemon.ws = ws
        self.daemon.dead = False
        started = time.monotonic()
        with self.assertRaises(wiz_mcp.LSPTimeout):
            self.daemon.request("textDocument/hover", {}, time.monotonic() + 0.2)
        self.assertLess(time.monotonic() - started, 2.0)
        self.assertTrue(ws.closed)
        self.assertIsNone(self.daemon.ws)

    def test_wait_diagnostics_matches_the_uri(self) -> None:
        self.daemon.ws = DeadWebSocket()
        self.daemon.dead = False
        self.daemon.inbox = [
            {"method": "textDocument/publishDiagnostics", "params": {"uri": "file:///other", "diagnostics": [1]}},
            {"method": "textDocument/publishDiagnostics", "params": {"uri": "file:///mine", "diagnostics": [2]}},
        ]
        self.assertEqual(self.daemon.wait_diagnostics("file:///mine", time.monotonic() + 1), [2])

    def test_wait_diagnostics_times_out_without_a_push(self) -> None:
        self.daemon.ws = DeadWebSocket()
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


if __name__ == "__main__":
    unittest.main()
