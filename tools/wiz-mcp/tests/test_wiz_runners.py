#!/usr/bin/env python3
"""Unit tests for the phase 3 runners (tools/wiz-mcp/wiz_runners.py and the wiz-mcp
tools that use them). Stdlib only, light: the scheduler, the sandbox and the test
driver are small shell stand-ins that record what they were given. One test uses the
real `bwrap` when it is installed and works (and is reported as skipped otherwise).

    python3 -m unittest discover -s tools/wiz-mcp/tests -p 'test_*.py' -v
"""

from __future__ import annotations

import os
import shutil
import subprocess
import sys
import tempfile
import time
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))

import wiz_mcp  # noqa: E402
import wiz_runners  # noqa: E402

#: `heavy --status` on an idle machine (the real format, 2026-11-16).
STATUS_IDLE = """perf-window: none
memory: full avg10=0% some avg10=0% avail=14898MiB swapfree=36907MiB
slot0: free mem=-
pslot: free mem=-
limits: budget 16G ceiling 18G (effective 18432 MiB, slice max 18432 MiB) psi<25% floor 1536MiB swap 512M bypass 4 maxwait 900s headroom on [/x/limits.conf]
admission: reserved 0 MiB of 16G in 0 jobs; growth 0 MiB (nix-daemon 731 MiB); headroom for a new job 12000 MiB
"""
#: Two 8G jobs running and no headroom: a new job would wait.
STATUS_BUSY = """perf-window: none
slot0: busy mem=8589934592 cur=2171MiB unit=heavy-1-1
slot1: busy mem=8589934592 cur=17MiB unit=heavy-2-2
limits: budget 16G ceiling 18G (effective 18432 MiB, slice max 18432 MiB) psi<25% floor 1536MiB swap 512M bypass 4 maxwait 900s headroom on [/x/limits.conf]
admission: reserved 16384 MiB of 16G in 2 jobs; growth 14194 MiB (nix-daemon 731 MiB); headroom for a new job -832 MiB
"""
STATUS_PERF = STATUS_IDLE.replace("perf-window: none", "perf-window: perf-agent bench 12:00")
STATUS_QUEUE = STATUS_IDLE.replace(
    "admission: reserved 0 MiB of 16G in 0 jobs",
    "admission: reserved 4096 MiB of 16G in 1 jobs",
) + "waiting (FIFO order):\n  pid=99 since=12:00:00 mem=7G t=1 req=1 cmd=lake build\n"

#: The stand-in heavy: --status/--queue from files beside it; a job records its argv and
#: environment, holds while `hold` exists (listing itself in the queue), then runs CMD.
FAKE_HEAVY = r'''d=$(dirname "$0")
case "${1:-}" in
  --status) cat "$d/status.txt"; exit 0 ;;
  --queue)
    if [ -f "$d/queued.pid" ]; then echo "  1. pid=$(cat "$d/queued.pid") since=00:00:00 mem=7G t=1 req=1 cmd=x"
    else echo 'heavy: no waiters'; fi
    exit 0 ;;
esac
printf '%s\n' "$@" > "$d/heavy.argv"
env > "$d/heavy.env"
[ "$1" = --mem ] && shift 2
if [ -f "$d/hold" ]; then
  echo $$ > "$d/queued.pid"
  while [ -f "$d/hold" ]; do sleep 0.05; done
  rm -f "$d/queued.pid"
fi
exec "$@"'''
FAKE_LIGHT = r'''d=$(dirname "$0")
printf '%s\n' "$@" > "$d/light.argv"
exec "$@"'''
#: The stand-in bwrap: records its options and runs what follows `--` unsandboxed.
FAKE_BWRAP = r'''d=$(dirname "$0")
printf '%s\n' "$@" > "$d/bwrap.argv"
while [ "$#" -gt 0 ] && [ "$1" != "--" ]; do shift; done
shift
exec "$@"'''
FAKE_TESTS = r'''case "${1:-}" in
  --list) printf 'native\nsmt\n' ;;
  --list-cases) printf 'native\t0\tfirst\nnative\t1\tsecond\n' ;;
  --trust-ledger) printf 'Prelude\tfoo\taxiom foo\nWord\tbar\timplemented_by\n' ;;
  =slow) echo $$ > "$(dirname "$0")/slow.pid"; sleep 60 ;;
  =green) printf '\342\224\200\342\224\200 green (x)\n  \342\234\223 a (0.1 s)\n\n1 passed, 0 failed\n' ;;
  *) printf '\342\224\200\342\224\200 native (x)\n  \342\234\223 a (0.1 s)\n  \342\234\227 b (0.2 s)\n      boom\n  \342\212\230 c (0.0 s)\n      skipped (no toolchain)\n\n1 passed, 1 failed, 1 skipped\n'; exit 1 ;;
esac'''


def write_exe(directory: Path, name: str, body: str) -> str:
    path = directory / name
    path.write_text("#!/bin/sh\nset -eu\n" + body + "\n", encoding="utf-8")
    path.chmod(0o755)
    return str(path)


class ParserTests(unittest.TestCase):
    def test_status_is_parsed(self) -> None:
        status = wiz_runners.parse_heavy_status(STATUS_BUSY)
        self.assertEqual((status.reserved_mib, status.budget_mib, status.jobs, status.headroom_mib),
                         (16384, 16384, 2, -832))
        self.assertEqual(status.ceiling_mib, 18432)
        self.assertEqual(status.perf_window, "none")
        self.assertEqual(wiz_runners.parse_heavy_status(STATUS_QUEUE).waiting[0][:6], "pid=99")
        self.assertEqual(wiz_runners.parse_heavy_status(STATUS_PERF).perf_window, "perf-agent bench 12:00")

    def test_a_status_without_its_admission_line_is_refused(self) -> None:
        with self.assertRaises(wiz_runners.RunnerError) as caught:
            wiz_runners.parse_heavy_status("perf-window: none\n")
        self.assertEqual(caught.exception.kind, "scheduler_error")

    def test_admission_follows_heavys_rules(self) -> None:
        idle = wiz_runners.parse_heavy_status(STATUS_IDLE)
        busy = wiz_runners.parse_heavy_status(STATUS_BUSY)
        self.assertTrue(wiz_runners.admission(idle, 8192)[0])
        self.assertFalse(wiz_runners.admission(busy, 1024)[0])
        self.assertFalse(wiz_runners.admission(wiz_runners.parse_heavy_status(STATUS_PERF), 1)[0])
        # FIFO: a waiter ahead means this job would wait too.
        self.assertFalse(wiz_runners.admission(wiz_runners.parse_heavy_status(STATUS_QUEUE), 1024)[0])
        # Over the budget but within the measured headroom: heavy admits it.
        roomy = wiz_runners.parse_heavy_status(STATUS_BUSY.replace("for a new job -832", "for a new job 9000"))
        self.assertTrue(wiz_runners.admission(roomy, 2048)[0])

    def test_queue_position(self) -> None:
        text = "  1. pid=10 since=x mem=7G cmd=a\n  2. pid=42 since=x mem=4G cmd=b\n"
        self.assertEqual(wiz_runners.queue_position(text, 42), 2)
        self.assertIsNone(wiz_runners.queue_position(text, 4))
        self.assertIsNone(wiz_runners.queue_position("heavy: no waiters\n", 42))

    def test_sizes_and_limits(self) -> None:
        self.assertEqual(wiz_runners.parse_size_mib("6G"), 6144)
        self.assertEqual(wiz_runners.parse_size_mib("512M"), 512)
        for bad in ("6", "6g", "0G", "1.5G", "6GB", "-1G", 6, None, "6G; rm -rf /"):
            with self.assertRaises(wiz_runners.RunnerError, msg=repr(bad)):
                wiz_runners.parse_size_mib(bad)
        self.assertEqual(wiz_runners.check_mem(None, "7G", "8G"), "7G")
        with self.assertRaises(wiz_runners.RunnerError):
            wiz_runners.check_mem("9G", "7G", "8G")

    def test_selectors_are_exact(self) -> None:
        self.assertEqual(wiz_runners.check_selectors(["=native", "=smt#0,3"]), ["=native", "=smt#0,3"])
        for bad in ([], ["native"], ["s"], ["--list"], ["=a b"], ["=x;rm"], ["=$(id)"], "=native", [1], ["=a#x"]):
            with self.assertRaises(wiz_runners.RunnerError, msg=repr(bad)):
                wiz_runners.check_selectors(bad)

    def test_test_output_counts_and_skips(self) -> None:
        out = ("── native (27a)\n  ✓ a (0.1 s)\n  ✗ b (0.2 s)\n      boom\n      more\n"
               "  ⊘ c (0.0 s)\n      skipped (no toolchain)\n  (native: 1 s)\n\n1 passed, 1 failed, 1 skipped\n")
        parsed = wiz_runners.parse_test_output(out)
        self.assertEqual(parsed["summary"], {"passed": 1, "failed": 1, "skipped": 1})
        self.assertEqual(parsed["groups"]["native"], {"passed": 1, "failed": 1, "skipped": 1})
        self.assertEqual(parsed["failed"][0]["name"], "b")
        self.assertEqual(parsed["failed"][0]["output"], "boom\nmore")
        self.assertEqual(parsed["skipped"][0]["output"], "skipped (no toolchain)")
        self.assertFalse(parsed["all_passed"])
        # A skip alone is not a pass either; no summary means an incomplete run.
        self.assertFalse(wiz_runners.parse_test_output("\n2 passed, 0 failed, 1 skipped\n")["all_passed"])
        self.assertTrue(wiz_runners.parse_test_output("\n2 passed, 0 failed\n")["all_passed"])
        self.assertFalse(wiz_runners.parse_test_output("── g (x)\n  ✓ a (1 s)\n")["complete"])

    def test_ledger_comparison(self) -> None:
        live = wiz_runners.parse_ledger_sources("A\tf\taxiom f\nB\tg\tpartial\nnot a row\n")
        rows = [{"module": "A", "declaration": "f", "item": "axiom f"},
                {"module": "C", "declaration": "h", "item": "sorry"}]
        full = wiz_runners.compare_ledger(live, rows, complete=True)
        self.assertEqual(full["unreviewed"], [{"module": "B", "declaration": "g", "item": "partial"}])
        self.assertEqual(full["stale"], [{"module": "C", "declaration": "h", "item": "sorry"}])
        self.assertEqual(full["sources"], 2)
        partial = wiz_runners.compare_ledger(live, rows, complete=False)
        self.assertIsNone(partial["stale"])
        self.assertIn("stale_note", partial)

    def test_runner_env_drops_scheduler_overrides(self) -> None:
        env = wiz_runners.runner_env(
            {"PATH": "/bin", "WIZ_HEAVY_TOTAL_MEM": "999G", "WIZ_LOCK_HELD": "heavy", "WIZ_LIGHT_SECS": "99999",
             "WIZ_LOCKS": "/tmp/x", "WIZ_BIN": "/w"},
            {"DBUS_SESSION_BUS_ADDRESS": "unix:path=/run/user/1/bus", "XDG_RUNTIME_DIR": "/run/user/1"})
        self.assertEqual(env, {"PATH": "/bin", "WIZ_BIN": "/w",
                               "DBUS_SESSION_BUS_ADDRESS": "unix:path=/run/user/1/bus", "XDG_RUNTIME_DIR": "/run/user/1"})


class SandboxArgvTests(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory(prefix="wiz-runners-box-")
        root = Path(os.path.realpath(self.tmp.name))
        self.home = root / "home"
        (self.home / ".ssh").mkdir(parents=True)
        (self.home / ".config").mkdir()
        (self.home / ".netrc").write_text("machine x password y\n")
        (self.home / ".cache" / "wiz").mkdir(parents=True)
        self.ws = root / "ws"
        self.ws.mkdir()

    def tearDown(self) -> None:
        self.tmp.cleanup()

    def test_hidden_home_and_isolation(self) -> None:
        box = wiz_runners.Sandbox(workspace=str(self.ws), hide_home=True, home=str(self.home),
                                  writable=(str(self.home / ".cache" / "wiz"),))
        argv = wiz_runners.sandbox_argv("bwrap", box)
        for flag in ("--unshare-net", "--unshare-ipc", "--unshare-pid", "--die-with-parent", "--new-session"):
            self.assertIn(flag, argv)
        self.assertEqual(argv[-1], "--")
        joined = " ".join(argv)
        self.assertIn("--ro-bind / /", joined)
        self.assertIn(f"--tmpfs {self.home}", joined)
        # The workspace is read-only; only the cache is writable, and it comes after the hidden home.
        self.assertIn(f"--ro-bind {self.ws} {self.ws}", joined)
        cache = str(self.home / ".cache" / "wiz")
        self.assertIn(f"--bind {cache} {cache}", joined)
        self.assertLess(argv.index("--tmpfs", argv.index("--tmpfs") + 1), argv.index(cache))
        self.assertNotIn("--share-net", argv)

    def test_masked_home_for_the_test_driver(self) -> None:
        box = wiz_runners.Sandbox(workspace=str(self.ws), workspace_rw=True, hide_home=False, home=str(self.home))
        joined = " ".join(wiz_runners.sandbox_argv("bwrap", box))
        self.assertIn(f"--tmpfs {self.home / '.ssh'}", joined)
        self.assertIn(f"--tmpfs {self.home / '.config'}", joined)
        self.assertIn(f"--ro-bind /dev/null {self.home / '.netrc'}", joined)
        self.assertNotIn(f"--tmpfs {self.home} ", joined)
        self.assertIn(f"--bind {self.ws} {self.ws}", joined)

    @unittest.skipUnless(shutil.which("bwrap"), "bwrap is not installed (skipped, not passed)")
    def test_real_bwrap_has_no_network_and_a_read_only_workspace(self) -> None:
        box = wiz_runners.Sandbox(workspace=str(self.ws), hide_home=True, home=str(self.home))
        # /proc is the sandbox's own, so /proc/net/dev lists its network namespace's interfaces.
        probe = ("echo IF $(tail -n +3 /proc/net/dev | cut -d: -f1); touch \"$1/written\" 2>/dev/null && echo WS-WRITABLE; "
                 "ls -A \"$2\"; echo END")
        argv = wiz_runners.sandbox_argv(shutil.which("bwrap") or "bwrap", box) + [
            "sh", "-c", probe, "sh", str(self.ws), str(self.home)]
        result = subprocess.run(argv, capture_output=True, text=True, timeout=30)
        if result.returncode != 0 and "END" not in result.stdout:
            self.skipTest(f"bwrap cannot create namespaces here: {result.stderr.strip()[:200]}")
        interfaces = next(line for line in result.stdout.splitlines() if line.startswith("IF ")).split()[1:]
        self.assertEqual(interfaces, ["lo"], result.stdout)  # only the loopback interface
        self.assertNotIn("WS-WRITABLE", result.stdout)
        self.assertNotIn(".ssh", result.stdout)  # the home directory is hidden
        self.assertFalse((self.ws / "written").exists())


class RunnerToolTests(unittest.TestCase):
    """The wiz-mcp runner tools against stand-in heavy/light/bwrap/tests scripts."""

    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory(prefix="wiz-runners-tools-")
        root = Path(os.path.realpath(self.tmp.name))
        self.bin = root / "bin"
        self.bin.mkdir()
        self.ws = root / "ws"
        (self.ws / ".lake" / "build" / "bin").mkdir(parents=True)
        (self.ws / ".github").mkdir()
        (self.ws / ".github" / "trust-baseline.tsv").write_text(
            "# header\nPrelude\tfoo\taxiom foo\tr\to\t2099-01-01\nGone\tx\tsorry\tr\to\t2099-01-01\n")
        (self.ws / "main.wiz").write_text("def main : Nat := 1\n")
        self.outside = root / "outside"
        self.outside.mkdir()
        (self.outside / "evil.wiz").write_text("def main : Nat := 2\n")
        self.heavy = write_exe(self.bin, "heavy", FAKE_HEAVY)
        self.light = write_exe(self.bin, "light", FAKE_LIGHT)
        self.bwrap = write_exe(self.bin, "bwrap", FAKE_BWRAP)
        self.tests = write_exe(self.ws / ".lake" / "build" / "bin", "tests", FAKE_TESTS)
        self.wiz = write_exe(self.ws / ".lake" / "build" / "bin", "wiz", 'echo "WIZ $*"')
        self.cache = root / "cache"
        self.set_status(STATUS_IDLE)

    def tearDown(self) -> None:
        for name in ("hold",):
            (self.bin / name).unlink(missing_ok=True)
        self.tmp.cleanup()

    def set_status(self, text: str) -> None:
        (self.bin / "status.txt").write_text(text)

    def server(self, **overrides) -> wiz_mcp.Server:
        runner = wiz_runners.RunnerConfig(heavy=overrides.pop("heavy", self.heavy), light=self.light,
                                          bwrap=overrides.pop("bwrap", self.bwrap),
                                          max_mem=overrides.pop("max_mem", "8G"))
        options = {"workspace": str(self.ws), "wiz": self.wiz, "idle": 0, "timeout": 20, "cache": str(self.cache),
                   "allow_tests": True, "allow_run": True, "runner": runner}
        options.update(overrides)
        server = wiz_mcp.Server(wiz_mcp.Config(**options))
        self.addCleanup(server.close)
        return server

    def lines(self, name: str) -> list[str]:
        path = self.bin / name
        return path.read_text().splitlines() if path.exists() else []

    # -- gating ----------------------------------------------------------------

    def test_runners_are_listed_only_with_their_flags(self) -> None:
        def names(**flags) -> set:
            server = self.server(**flags)
            return {t["name"] for t in server.dispatch({"jsonrpc": "2.0", "id": 1, "method": "tools/list"})[0][0]["result"]["tools"]}

        runners = set(wiz_mcp.RUNNER_TOOL_NAMES)
        self.assertFalse(names(allow_tests=False, allow_run=False) & runners)
        self.assertEqual(names(allow_tests=True, allow_run=False) & runners,
                         {"test_groups", "test_group", "trust_ledger_live", "job_status", "job_cancel"})
        self.assertEqual(names(allow_tests=False, allow_run=True) & runners, {"run", "job_status", "job_cancel"})

    def test_a_runner_without_its_flag_is_refused_before_anything_runs(self) -> None:
        server = self.server(allow_tests=False, allow_run=False)
        for name, args in (("test_group", {"selectors": ["=native"]}), ("test_groups", {}),
                           ("trust_ledger_live", {}), ("run", {"path": "main.wiz"}), ("job_status", {})):
            envelope = server.call_tool(name, args)
            self.assertEqual(envelope["error"]["kind"], "not_enabled", name)
        self.assertEqual(self.lines("heavy.argv") + self.lines("light.argv"), [])

    def test_bad_arguments_never_reach_the_scheduler(self) -> None:
        server = self.server()
        for args in ({"selectors": ["nat"]}, {"selectors": ["--list"]}, {"selectors": ["=native"], "mem": "9G"},
                     {"selectors": ["=native"], "mem": "lots"}, {"selectors": ["=native"], "timeout": 99999},
                     {"selectors": ["=native"], "jobs": 0}, {"selectors": ["=native"], "shell": "id"}):
            envelope = server.call_tool("test_group", args)
            self.assertEqual(envelope["error"]["kind"], "invalid_args", args)
        self.assertEqual(self.lines("heavy.argv"), [])

    def test_missing_scheduler_or_sandbox_refuses_rather_than_running_directly(self) -> None:
        envelope = self.server(heavy=str(self.bin / "nope")).call_tool("test_group", {"selectors": ["=native"]})
        self.assertEqual(envelope["error"]["kind"], "scheduler_not_found")
        envelope = self.server(bwrap=str(self.bin / "nope")).call_tool("run", {"path": "main.wiz"})
        self.assertEqual(envelope["error"]["kind"], "sandbox_unavailable")
        self.assertEqual(self.lines("heavy.argv"), [])

    # -- admission ---------------------------------------------------------------

    def test_busy_heavy_is_refused_with_its_status(self) -> None:
        self.set_status(STATUS_BUSY)
        envelope = self.server().call_tool("test_group", {"selectors": ["=native"]})
        self.assertEqual(envelope["error"]["kind"], "heavy_busy")
        self.assertEqual(envelope["result"]["heavy"]["reserved_mib"], 16384)
        self.assertEqual(self.lines("heavy.argv"), [])

    def test_a_measurement_window_is_refused_even_with_queue(self) -> None:
        self.set_status(STATUS_PERF)
        envelope = self.server().call_tool("test_group", {"selectors": ["=native"], "queue": True})
        self.assertEqual(envelope["error"]["kind"], "measurement_window")
        self.assertEqual(self.lines("heavy.argv"), [])

    def test_queue_true_returns_the_queue_position_instead_of_blocking(self) -> None:
        self.set_status(STATUS_BUSY)
        (self.bin / "hold").write_text("")
        server = self.server()
        started = time.monotonic()
        envelope = server.call_tool("test_group", {"selectors": ["=green"], "queue": True, "wait": 1})
        self.assertLess(time.monotonic() - started, 10)
        self.assertTrue(envelope["ok"], envelope)
        job = envelope["result"]["job"]
        for _ in range(50):
            if (self.bin / "queued.pid").exists():
                break
            time.sleep(0.05)
        status = server.call_tool("job_status", {"job": job})
        self.assertEqual(status["result"]["state"], "queued", status)
        self.assertEqual(status["result"]["queue_position"], 1)
        (self.bin / "hold").unlink()
        done = server.call_tool("job_status", {"job": job, "wait": 10})
        self.assertEqual(done["result"]["state"], "done", done)
        self.assertTrue(done["result"]["result"]["all_passed"])

    # -- test groups ---------------------------------------------------------------

    def test_test_group_runs_through_heavy_and_the_sandbox(self) -> None:
        envelope = self.server().call_tool("test_group", {"selectors": ["=native"], "mem": "6G", "timeout": 600, "wait": 10})
        heavy = self.lines("heavy.argv")
        self.assertEqual(heavy[:7], ["--mem", "6G", "timeout", "-k", "30", "600", self.bwrap])
        self.assertEqual(heavy[heavy.index("--") + 1:], [self.tests, "=native"])
        bwrap = self.lines("bwrap.argv")
        self.assertIn("--unshare-net", bwrap)
        self.assertIn("--bind", bwrap)  # the test driver may write in the workspace
        result = envelope["result"]
        self.assertEqual(result["state"], "failed")
        self.assertFalse(envelope["ok"])
        self.assertEqual(result["result"]["summary"], {"passed": 1, "failed": 1, "skipped": 1})
        self.assertEqual(result["result"]["failed"][0]["output"], "boom")
        self.assertIn("1 passed, 1 failed, 1 skipped", envelope["stdout"])

    def test_a_clean_run_is_ok(self) -> None:
        envelope = self.server().call_tool("test_group", {"selectors": ["=green"], "wait": 10})
        self.assertTrue(envelope["ok"], envelope)
        self.assertEqual(envelope["result"]["state"], "done")

    def test_scheduler_overrides_never_reach_heavy(self) -> None:
        saved = {k: os.environ.get(k) for k in ("WIZ_HEAVY_TOTAL_MEM", "WIZ_LOCK_HELD", "GH_TOKEN")}
        os.environ.update({"WIZ_HEAVY_TOTAL_MEM": "999G", "WIZ_LOCK_HELD": "heavy", "GH_TOKEN": "do-not-leak"})

        def restore() -> None:
            for k, v in saved.items():
                if v is None:
                    os.environ.pop(k, None)
                else:
                    os.environ[k] = v
        self.addCleanup(restore)
        self.server().call_tool("test_group", {"selectors": ["=green"], "wait": 10})
        env = "\n".join(self.lines("heavy.env"))
        self.assertNotIn("WIZ_HEAVY_TOTAL_MEM", env)
        self.assertNotIn("WIZ_LOCK_HELD", env)
        self.assertNotIn("do-not-leak", env)

    def test_one_job_at_a_time_and_cancel_stops_the_whole_session(self) -> None:
        server = self.server()
        first = server.call_tool("test_group", {"selectors": ["=slow"], "wait": 0})
        self.assertTrue(first["ok"], first)
        job = first["result"]["job"]
        for _ in range(100):
            if (self.ws / ".lake" / "build" / "bin" / "slow.pid").exists():
                break
            time.sleep(0.05)
        slow_pid = int((self.ws / ".lake" / "build" / "bin" / "slow.pid").read_text())
        second = server.call_tool("test_group", {"selectors": ["=green"]})
        self.assertEqual(second["error"]["kind"], "busy")
        cancelled = server.call_tool("job_cancel", {"job": job})
        self.assertEqual(cancelled["result"]["state"], "cancelled")
        # The driver's process (under coreutils timeout, its own process group) is gone too.
        for _ in range(100):
            try:
                os.kill(slow_pid, 0)
            except ProcessLookupError:
                break
            time.sleep(0.05)
        else:
            self.fail("the test driver survived job_cancel")
        listing = server.call_tool("job_status", {})
        self.assertEqual([j["job"] for j in listing["result"]["jobs"]], [job])

    def test_test_groups_lists_through_light(self) -> None:
        server = self.server()
        groups = server.call_tool("test_groups", {})
        self.assertEqual(groups["result"], {"groups": ["native", "smt"]})
        self.assertEqual(self.lines("light.argv")[0], self.bwrap)
        cases = server.call_tool("test_groups", {"selectors": ["=native"]})
        self.assertEqual(cases["result"]["cases"][1], {"group": "native", "index": 1, "name": "second"})
        self.assertEqual(self.lines("heavy.argv"), [])

    def test_missing_driver_is_never_built(self) -> None:
        os.remove(self.tests)
        envelope = self.server().call_tool("test_group", {"selectors": ["=native"]})
        self.assertEqual(envelope["error"]["kind"], "tests_not_found")
        self.assertEqual(self.lines("heavy.argv"), [])

    # -- trust ledger ------------------------------------------------------------------

    def test_trust_ledger_live_compares_with_the_checked_in_ledger(self) -> None:
        envelope = self.server().call_tool("trust_ledger_live", {"wait": 10})
        heavy = self.lines("heavy.argv")
        self.assertEqual(heavy[heavy.index("--") + 1:], [self.tests, "--trust-ledger", "--print"])
        self.assertIn("--ro-bind", self.lines("bwrap.argv"))
        result = envelope["result"]["result"]
        self.assertEqual(result["unreviewed"], [{"module": "Word", "declaration": "bar", "item": "implemented_by"}])
        self.assertEqual(result["stale"], [{"module": "Gone", "declaration": "x", "item": "sorry"}])
        lib_only = self.server().call_tool("trust_ledger_live", {"lib_only": True, "wait": 10})
        self.assertIsNone(lib_only["result"]["result"]["stale"])

    # -- run -----------------------------------------------------------------------------

    def test_run_is_sandboxed_with_the_home_hidden(self) -> None:
        envelope = self.server().call_tool("run", {"path": "main.wiz", "target": "c", "wait": 10})
        self.assertEqual(envelope["result"]["state"], "done", envelope)
        self.assertIn("WIZ --cache", envelope["stdout"])
        self.assertIn("run " + str(self.ws / "main.wiz") + " --target c", envelope["stdout"])
        heavy = self.lines("heavy.argv")
        self.assertEqual(heavy[:2], ["--mem", "4G"])
        joined = " ".join(self.lines("bwrap.argv"))
        self.assertIn("--tmpfs " + os.path.realpath(os.path.expanduser("~")), joined)
        self.assertIn(f"--ro-bind {self.ws} {self.ws}", joined)
        self.assertIn(f"--bind {self.cache} {self.cache}", joined)

    def test_run_outside_the_workspace_is_refused(self) -> None:
        server = self.server()
        for path in (str(self.outside / "evil.wiz"), "../outside/evil.wiz"):
            self.assertEqual(server.call_tool("run", {"path": path})["error"]["kind"], "path_denied")
        self.assertEqual(server.call_tool("run", {"path": "main.wiz", "target": "wasm"})["error"]["kind"], "invalid_args")
        self.assertEqual(self.lines("heavy.argv"), [])

    def test_closing_the_server_stops_its_jobs(self) -> None:
        server = self.server()
        job = server.call_tool("test_group", {"selectors": ["=slow"], "wait": 0})["result"]["job"]
        proc = server.runner.jobs.get(job).proc
        server.close()
        self.assertIsNotNone(proc.poll())


if __name__ == "__main__":
    unittest.main()
