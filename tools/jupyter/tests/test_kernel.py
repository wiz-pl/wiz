"""Protocol-level tests for the Wiz Jupyter kernel.

Run from a checkout (no install needed)::

    python3 -m unittest discover -s tools/jupyter/tests -v

They start the kernel as Jupyter does (a connection file and ``-f``) and talk to
it with ``jupyter_client``, so they cover the wire, the five sockets and the
drivers.  Everything is skipped cleanly when ``pyzmq``/``jupyter_client`` are
absent, or when no ``wiz`` executable can be found (``$WIZ``, ``wiz`` on PATH, a
checkout's ``.lake/build/bin/wiz``; ``$WIZ_TEST_WIZ`` overrides).

Set ``$WIZ_TEST_BACKEND`` to ``repl`` or ``batch`` to pin a driver.
"""

from __future__ import annotations

import json
import os
import shlex
import shutil
import subprocess
import sys
import tempfile
import time
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
TOOL_DIR = os.path.dirname(HERE)
if TOOL_DIR not in sys.path:
    sys.path.insert(0, TOOL_DIR)

try:
    import zmq  # noqa: F401
    from jupyter_client import BlockingKernelClient
    from jupyter_client.connect import write_connection_file
    HAVE_JUPYTER = True
except ImportError:  # pragma: no cover - the skip path
    HAVE_JUPYTER = False

from wiz_kernel.backends import find_wiz  # noqa: E402
from wiz_kernel.magics import scry_command  # noqa: E402


def _kernel_command(connection_file: str, backend: str, wiz: str | None,
                    cwd: str) -> list[str]:
    command = [sys.executable, "-m", "wiz_kernel", "-f", connection_file,
               "--backend", backend, "--cwd", cwd]
    if wiz:
        command += ["--wiz", wiz]
    return command


@unittest.skipUnless(HAVE_JUPYTER, "pyzmq and jupyter_client are not installed")
class KernelProtocolTest(unittest.TestCase):
    backend = os.environ.get("WIZ_TEST_BACKEND", "auto")

    @classmethod
    def setUpClass(cls) -> None:
        cls.wiz = find_wiz(os.environ.get("WIZ_TEST_WIZ"))
        if cls.wiz is None:
            raise unittest.SkipTest("no wiz executable (set $WIZ or $WIZ_TEST_WIZ)")
        cls.tmp = tempfile.mkdtemp(prefix="wiz-kernel-test-")
        cls.workspace = os.path.join(cls.tmp, "ws")
        os.makedirs(cls.workspace, exist_ok=True)
        cls.connection_file, _ = write_connection_file(
            os.path.join(cls.tmp, "connection.json"), ip="127.0.0.1")
        env = dict(os.environ)
        env["PYTHONPATH"] = TOOL_DIR + os.pathsep + env.get("PYTHONPATH", "")
        cls.process = subprocess.Popen(
            _kernel_command(cls.connection_file, cls.backend, cls.wiz, cls.workspace),
            cwd=cls.workspace, env=env,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        cls.client = BlockingKernelClient()
        cls.client.load_connection_file(cls.connection_file)
        cls.client.start_channels()
        try:
            cls.client.wait_for_ready(timeout=180)
        except Exception:
            cls.process.terminate()
            out, err = cls.process.communicate(timeout=10)
            raise
        cls.backend_name = None
        msg_id = cls.client.kernel_info()
        msg = cls._reply(msg_id)
        cls.backend_name = (msg.get("content", {}).get("metadata") or {}).get("wiz_backend")
        cls.info = msg["content"]

    @classmethod
    def tearDownClass(cls) -> None:
        if not hasattr(cls, "client"):
            return
        try:
            cls.client.stop_channels()
        except Exception:
            pass
        if getattr(cls, "process", None) is not None:
            if cls.process.poll() is None:
                cls.process.terminate()
                try:
                    cls.process.wait(timeout=10)
                except subprocess.TimeoutExpired:
                    cls.process.kill()
            for pipe in (cls.process.stdout, cls.process.stderr):
                try:
                    pipe.close()
                except Exception:
                    pass
        shutil.rmtree(getattr(cls, "tmp", ""), ignore_errors=True)

    # -- helpers -------------------------------------------------------

    @classmethod
    def _reply(cls, msg_id: str, timeout: float = 180):
        deadline = time.time() + timeout
        while time.time() < deadline:
            msg = cls.client.get_shell_msg(timeout=max(0.1, deadline - time.time()))
            if msg.get("parent_header", {}).get("msg_id") == msg_id:
                return msg
        raise TimeoutError(f"no reply to {msg_id}")

    @classmethod
    def execute(cls, code: str):
        msg_id = cls.client.execute(code)
        reply = cls._reply(msg_id)
        iopub = []
        deadline = time.time() + 180
        while time.time() < deadline:
            msg = cls.client.get_iopub_msg(timeout=max(0.1, deadline - time.time()))
            if msg.get("parent_header", {}).get("msg_id") != msg_id:
                continue
            iopub.append(msg)
            if msg["msg_type"] == "status" and \
                    msg["content"].get("execution_state") == "idle":
                break
        return reply, iopub

    @staticmethod
    def streams(iopub, name: str = "stdout") -> str:
        return "".join(m["content"].get("text", "") for m in iopub
                       if m["msg_type"] == "stream" and m["content"].get("name") == name)

    @staticmethod
    def result(iopub) -> dict:
        for msg in iopub:
            if msg["msg_type"] == "execute_result":
                return msg["content"].get("data", {})
        return {}

    # -- tests ---------------------------------------------------------

    def test_kernel_info(self):
        self.assertEqual(self.info.get("protocol_version"), "5.3")
        self.assertEqual(self.info.get("implementation"), "wiz-kernel")
        self.assertEqual(self.info.get("language_info", {}).get("name"), "wiz")
        self.assertIn(self.backend_name, ("repl", "batch"))
        self.assertIn("Wiz kernel", self.info.get("banner", ""))

    def test_execute_streams_stdout_and_persists_definitions(self):
        reply, iopub = self.execute("def notebook_answer : Nat := 41 + 1")
        self.assertEqual(reply["content"]["status"], "ok", reply["content"])
        self.assertTrue(any(m["msg_type"] == "execute_input" for m in iopub))
        reply, iopub = self.execute("#eval notebook_answer + 1")
        self.assertEqual(reply["content"]["status"], "ok", reply["content"])
        self.assertIn("43", self.streams(iopub))
        self.assertIsInstance(reply["content"]["execution_count"], int)

    def test_multiline_definition(self):
        reply, _ = self.execute("def notebook_twice (n : Nat) : Nat :=\n  n + n")
        self.assertEqual(reply["content"]["status"], "ok", reply["content"])
        reply, iopub = self.execute("#eval notebook_twice 4")
        self.assertIn("8", self.streams(iopub))

    def test_last_expression_is_execute_result(self):
        reply, iopub = self.execute("20 + 22")
        self.assertEqual(reply["content"]["status"], "ok", reply["content"])
        self.assertEqual(self.result(iopub).get("text/plain"), "42", self.result(iopub))

    def test_error_message_and_reply(self):
        reply, iopub = self.execute("def notebook_bad : Nat := true")
        self.assertEqual(reply["content"]["status"], "error", reply["content"])
        errors = [m for m in iopub if m["msg_type"] == "error"]
        self.assertTrue(errors, "no error message on iopub")
        self.assertEqual(errors[0]["content"]["ename"], "WizError")
        self.assertTrue(errors[0]["content"]["evalue"])
        self.assertTrue(errors[0]["content"]["traceback"])

    def test_backend_magic(self):
        reply, iopub = self.execute("%backend")
        text = self.result(iopub).get("text/plain", "")
        self.assertIn("backend:", text)
        self.assertIn(self.backend_name, text)

    def test_unknown_magic_is_an_error(self):
        reply, iopub = self.execute("%%nope")
        self.assertEqual(reply["content"]["status"], "error")
        errors = [m for m in iopub if m["msg_type"] == "error"]
        self.assertEqual(errors[0]["content"]["ename"], "UnknownMagic")

    def test_scry_cell_magic(self):
        wiz = os.environ.get("WIZ_TEST_WIZ") or self.wiz
        if scry_command(self.workspace, wiz) is None:
            self.skipTest("no scry executable (set $WIZ_SCRY)")
        source = ("%%scry\n"
                  "char *getenv(const char *name);\n"
                  "int system(const char *command);\n"
                  "int main(void) {\n"
                  "  char *cmd = getenv(0);\n"
                  "  system(cmd);\n"
                  "  return 0;\n"
                  "}\n")
        reply, iopub = self.execute(source)
        self.assertEqual(reply["content"]["status"], "ok", reply["content"])
        bundle = self.result(iopub)
        self.assertIn("command-injection", json.dumps(bundle))

    def test_is_complete(self):
        msg_id = self.client.is_complete("def f (n : Nat) : Nat :=\n  n + 1\nimport Prelude\n")
        reply = self._reply(msg_id)
        self.assertIn(reply["content"].get("status"), ("complete", "incomplete", "unknown"))

    def test_self_test_command(self):
        env = dict(os.environ)
        env["PYTHONPATH"] = TOOL_DIR + os.pathsep + env.get("PYTHONPATH", "")
        done = subprocess.run(
            [sys.executable, "-m", "wiz_kernel", "--self-test", "--wiz", self.wiz,
             "--backend", "auto"],
            cwd=TOOL_DIR, env=env, capture_output=True, text=True, timeout=300)
        self.assertEqual(done.returncode, 0, done.stdout + done.stderr)
        self.assertIn("0 failed", done.stdout)


@unittest.skipUnless(HAVE_JUPYTER, "pyzmq and jupyter_client are not installed")
class _ExtraKernelTest(unittest.TestCase):
    """Start a kernel with extra argv; the LSP tests need no wiz backend."""

    extra_args: list[str] = []

    @classmethod
    def setUpClass(cls) -> None:
        cls.tmp = tempfile.mkdtemp(prefix="wiz-kernel-lsp-test-")
        cls.workspace = os.path.join(cls.tmp, "ws")
        os.makedirs(cls.workspace, exist_ok=True)
        cls.connection_file, _ = write_connection_file(
            os.path.join(cls.tmp, "connection.json"), ip="127.0.0.1")
        cls.wiz = find_wiz(os.environ.get("WIZ_TEST_WIZ"))
        command = [sys.executable, "-m", "wiz_kernel", "-f", cls.connection_file,
                   "--backend", "auto", "--cwd", cls.workspace, *cls.extra_args]
        if cls.wiz:
            command += ["--wiz", cls.wiz]
        env = dict(os.environ)
        env["PYTHONPATH"] = TOOL_DIR + os.pathsep + env.get("PYTHONPATH", "")
        cls.process = subprocess.Popen(command, cwd=cls.workspace, env=env,
                                       stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        cls.client = BlockingKernelClient()
        cls.client.load_connection_file(cls.connection_file)
        cls.client.start_channels()
        try:
            cls.client.wait_for_ready(timeout=180)
        except Exception:
            cls.process.terminate()
            cls.process.communicate(timeout=10)
            raise

    @classmethod
    def tearDownClass(cls) -> None:
        try:
            cls.client.stop_channels()
        except Exception:
            pass
        if cls.process.poll() is None:
            cls.process.terminate()
            try:
                cls.process.wait(timeout=10)
            except subprocess.TimeoutExpired:
                cls.process.kill()
        for pipe in (cls.process.stdout, cls.process.stderr):
            try:
                pipe.close()
            except Exception:
                pass
        shutil.rmtree(getattr(cls, "tmp", ""), ignore_errors=True)

    @classmethod
    def _reply(cls, msg_id: str, timeout: float = 180):
        deadline = time.time() + timeout
        while time.time() < deadline:
            msg = cls.client.get_shell_msg(timeout=max(0.1, deadline - time.time()))
            if msg.get("parent_header", {}).get("msg_id") == msg_id:
                return msg
        raise TimeoutError(f"no reply to {msg_id}")

    @classmethod
    def execute(cls, code: str):
        msg_id = cls.client.execute(code)
        reply = cls._reply(msg_id)
        iopub = []
        deadline = time.time() + 180
        while time.time() < deadline:
            msg = cls.client.get_iopub_msg(timeout=max(0.1, deadline - time.time()))
            if msg.get("parent_header", {}).get("msg_id") != msg_id:
                continue
            iopub.append(msg)
            if msg["msg_type"] == "status" and \
                    msg["content"].get("execution_state") == "idle":
                break
        return reply, iopub

    @staticmethod
    def result(iopub) -> dict:
        for msg in iopub:
            if msg["msg_type"] == "execute_result":
                return msg["content"].get("data", {})
        return {}

    def complete(self, code: str, cursor: int | None = None):
        cursor = len(code) if cursor is None else cursor
        return self._reply(self.client.complete(code, cursor))

    def inspect(self, code: str, cursor: int | None = None):
        cursor = len(code) if cursor is None else cursor
        return self._reply(self.client.inspect(code, cursor, 0))


@unittest.skipUnless(HAVE_JUPYTER, "pyzmq and jupyter_client are not installed")
class MockLspKernelTest(_ExtraKernelTest):
    """The kernel's completion/inspection against a mock language server."""

    @classmethod
    def setUpClass(cls) -> None:
        cls.log_dir = tempfile.mkdtemp(prefix="wiz-kernel-mock-log-")
        cls.log = os.path.join(cls.log_dir, "mock.jsonl")
        command = " ".join(shlex.quote(part) for part in
                           [sys.executable, "-m", "wiz_kernel.mock_lsp",
                            "--log", cls.log])
        cls.extra_args = ["--lsp-command", command]
        super().setUpClass()

    @classmethod
    def tearDownClass(cls) -> None:
        super().tearDownClass()
        shutil.rmtree(getattr(cls, "log_dir", ""), ignore_errors=True)

    def test_complete_and_inspect_use_the_lsp(self):
        self.execute("def previousAnswer : Nat := 41")
        code = "def x : Nat := 1\n#eval moc"
        reply = self.complete(code)
        content = reply["content"]
        self.assertEqual(content["status"], "ok", content)
        matches = content.get("matches") or []
        self.assertEqual([m["text"] for m in matches], ["mockValue", "mockFunction"])
        self.assertEqual(matches[0]["type"], "text")
        self.assertEqual(matches[1]["type"], "function")
        self.assertEqual(matches[0]["signature"], "Nat")
        self.assertIn("mock", matches[0]["documentation"].lower())
        self.assertEqual(content["cursor_start"], code.index("moc"))
        self.assertEqual(content["cursor_end"], len(code))
        lsp = content["metadata"]["wiz_lsp"]
        self.assertTrue(lsp["available"], lsp)
        self.assertEqual(lsp["cursor"], {"line": 3, "character": 9}, lsp)

        with open(self.log, encoding="utf-8") as handle:
            messages = [json.loads(line) for line in handle if line.strip()]
        opened = [m for m in messages if m.get("method") == "textDocument/didOpen"]
        self.assertTrue(opened, "the kernel did not open a document")
        text = opened[-1]["params"]["textDocument"]["text"]
        self.assertIn("def previousAnswer : Nat := 41", text)
        self.assertTrue(text.endswith(code), text[-80:])

        hover = self.inspect("#eval mockHover", 8)
        self.assertTrue(hover["content"]["found"], hover["content"])
        data = hover["content"]["data"]
        self.assertIn("mockHover", data["text/plain"])
        self.assertIn("mockHover", data["text/markdown"])

        empty = self.complete("MOCK_NONE")
        self.assertEqual(empty["content"]["matches"], [])
        missing = self.inspect("MOCK_NONE")
        self.assertFalse(missing["content"]["found"])

        incomplete = self.complete("MOCK_INCOMPLETE")
        self.assertTrue(incomplete["content"]["metadata"].get("isIncomplete"),
                        incomplete["content"]["metadata"])

    def test_backend_magic_reports_the_lsp(self):
        if self.wiz is None:
            self.skipTest("no wiz executable")
        reply, iopub = self.execute("%backend")
        self.assertEqual(reply["content"]["status"], "ok", reply["content"])
        self.assertIn("lsp:", self.result(iopub).get("text/plain", ""))


@unittest.skipUnless(HAVE_JUPYTER, "pyzmq and jupyter_client are not installed")
class NoLspKernelTest(_ExtraKernelTest):
    """`--no-lsp`: empty answers, no error, and the reason in metadata."""

    extra_args = ["--no-lsp"]

    def test_completion_and_inspection_degrade(self):
        reply = self.complete("anything")
        content = reply["content"]
        self.assertEqual(content["status"], "ok", content)
        self.assertEqual(content["matches"], [])
        self.assertFalse(content["metadata"]["wiz_lsp"]["enabled"])
        self.assertFalse(content["metadata"]["wiz_lsp"]["available"])
        self.assertIn("--no-lsp", content["metadata"]["wiz_lsp"]["reason"])

        hover = self.inspect("anything")
        self.assertEqual(hover["content"]["status"], "ok", hover["content"])
        self.assertFalse(hover["content"]["found"])
        self.assertFalse(hover["content"]["metadata"]["wiz_lsp"]["available"])


@unittest.skipUnless(HAVE_JUPYTER, "pyzmq and jupyter_client are not installed")
class MissingLspKernelTest(_ExtraKernelTest):
    """A server that cannot start is a stated reason, not an error reply."""

    extra_args = ["--lsp-command", "/nonexistent/wiz-kernel-no-such-lsp"]

    def test_missing_server_degrades(self):
        content = self.complete("anything")["content"]
        self.assertEqual(content["status"], "ok", content)
        self.assertEqual(content["matches"], [])
        lsp = content["metadata"]["wiz_lsp"]
        self.assertFalse(lsp["available"], lsp)
        self.assertIn("reason", lsp)

        content = self.inspect("anything")["content"]
        self.assertEqual(content["status"], "ok", content)
        self.assertFalse(content["found"])
        self.assertFalse(content["metadata"]["wiz_lsp"]["available"])


if __name__ == "__main__":
    unittest.main()
