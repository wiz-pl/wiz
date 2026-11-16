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

# A scry that takes `taint FILE --json [--progress]`: three progress lines on
# stderr, then one JSON report on stdout.  `--progress` is deliberately ignored
# here; the kernel only has to pass it through and forward the stderr lines.
FAKE_SCRY = '''import json, sys, time
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


def _kernel_command(connection_file: str, backend: str, wiz: str | None,
                    cwd: str) -> list[str]:
    command = [sys.executable, "-m", "wiz_kernel", "-f", connection_file,
               "--backend", backend, "--cwd", cwd]
    if wiz:
        command += ["--wiz", wiz]
    return command


class KernelFixture:
    """One kernel process per test class; subclasses add tests only."""

    backend = os.environ.get("WIZ_TEST_BACKEND", "auto")

    @classmethod
    def extra_env(cls, workspace: str) -> dict:
        return {}

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
        env.update(cls.extra_env(cls.workspace))
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


@unittest.skipUnless(HAVE_JUPYTER, "pyzmq and jupyter_client are not installed")
class KernelProtocolTest(KernelFixture, unittest.TestCase):

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

    def test_progress_magic_names_the_transport(self):
        reply, iopub = self.execute("%progress")
        text = self.result(iopub).get("text/plain", "")
        self.assertIn("progress:", text)
        self.assertIn("iopub stream", text)

    def test_sh_streams_both_pipes_and_returns_status(self):
        reply, iopub = self.execute("%%sh\necho shell-out\necho shell-err >&2\n")
        self.assertEqual(reply["content"]["status"], "ok", reply["content"])
        self.assertIn("shell-out", self.streams(iopub, "stdout"))
        self.assertIn("shell-err", self.streams(iopub, "stderr"))
        self.assertEqual(self.result(iopub).get("text/plain"), "exit status 0")

    def test_sh_nonzero_exit_is_an_error(self):
        reply, iopub = self.execute("%%sh\nexit 7\n")
        self.assertEqual(reply["content"]["status"], "error", reply["content"])
        errors = [m for m in iopub if m["msg_type"] == "error"]
        self.assertTrue(errors)
        self.assertEqual(errors[0]["content"]["ename"], "ShellError")
        self.assertIn("7", errors[0]["content"]["evalue"])

    def test_time_appends_a_plausible_line(self):
        reply, iopub = self.execute("%%time\n6 * 7\n")
        self.assertEqual(reply["content"]["status"], "ok", reply["content"])
        self.assertEqual(self.result(iopub).get("text/plain"), "42")
        timing = [line for line in self.streams(iopub).splitlines()
                  if line.startswith("[time] wall ")]
        self.assertEqual(len(timing), 1, self.streams(iopub))
        wall = float(timing[0].split()[2])
        self.assertGreaterEqual(wall, 0.0)
        self.assertLess(wall, 600.0)
        self.assertIn("peak RSS", timing[0])

    def test_wiz_magic_is_the_plain_cell_path(self):
        reply, _ = self.execute("def notebook_plain : Nat := 9")
        self.assertEqual(reply["content"]["status"], "ok", reply["content"])
        reply, _ = self.execute("%%wiz\ndef notebook_explicit : Nat := 9\n")
        self.assertEqual(reply["content"]["status"], "ok", reply["content"])
        reply, iopub = self.execute("#eval notebook_explicit + notebook_plain")
        self.assertIn("18", self.streams(iopub))

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
class ProgressTransportTest(KernelFixture, unittest.TestCase):
    """`%%scry --progress` with a scry that emits three stderr progress lines."""

    @classmethod
    def extra_env(cls, workspace: str) -> dict:
        path = os.path.join(workspace, "fake-scry.py")
        with open(path, "w", encoding="utf-8") as handle:
            handle.write(FAKE_SCRY)
        return {"WIZ_SCRY": f"{sys.executable} {path}"}

    def test_progress_lines_are_forwarded_in_order_while_the_cell_runs(self):
        reply, iopub = self.execute(
            "%%scry --progress\nint main(void) { return 0; }\n")
        self.assertEqual(reply["content"]["status"], "ok", reply["content"])
        progress = [line for line in self.streams(iopub).splitlines()
                    if line.startswith("progress:")]
        self.assertEqual(progress, [
            "progress: 1/3 files (33%) taint",
            "progress: 2/3 files (66%) taint",
            "progress: 3/3 files (100%) taint",
        ])

    def test_progress_cell_still_renders_the_report(self):
        reply, iopub = self.execute(
            "%%scry --progress\nint main(void) { return 0; }\n")
        self.assertEqual(reply["content"]["status"], "ok", reply["content"])
        self.assertIn("command-injection", json.dumps(self.result(iopub)))


if __name__ == "__main__":
    unittest.main()
