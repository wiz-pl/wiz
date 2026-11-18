"""Unit tests for tools/scry-mcp (no real scry needed: a fake records its calls)."""

from __future__ import annotations

import json
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))

import scry_mcp  # noqa: E402

#: A fake scry: records argv/cwd/env to $FAKE_LOG, writes a SARIF where asked, and
#: prints a taint/project report naming $FAKE_FILES (comma-separated) as finding files.
FAKE_SCRY = r'''#!/usr/bin/env python3
import json, os, sys
argv = sys.argv[1:]
def ctl(name):
    p = os.path.join(os.path.dirname(__file__), name)
    return open(p).read().strip() if os.path.exists(p) else ""
def read_json(p):
    try:
        return json.load(open(p))
    except Exception:
        return None
def wfjoin(a, b):
    # Scry's Path.join is plain concatenation: a + "/" + b.
    return a + "/" + b
log = os.environ.get("FAKE_LOG_PATH") or open(os.path.join(os.path.dirname(__file__), "log-path")).read().strip()
with open(log, "a") as h:
    h.write(json.dumps({"argv": argv, "cwd": os.getcwd(), "env": dict(os.environ)}) + "\n")
# stray writes land in the cwd and HOME; the test checks they stay in the temp dir
open("stray.txt", "w").write("x")
files = open(os.path.join(os.path.dirname(__file__), "files")).read().split(",")
if argv[:1] == ["--version"]:
    print("scry 0.0.0-fake"); sys.exit(0)
if argv[0] in ("taint", "project"):
    if "--sarif" in argv:
        out = argv[argv.index("--sarif") + 1]
        json.dump({"version": "2.1.0", "runs": [{"results": [
            {"ruleId": "r", "locations": [{"physicalLocation": {"artifactLocation": {"uri": "file://" + f}}}]}
            for f in files]}]}, open(out, "w"))
    report = {"tool": "scry", "counts": {"findings": len(files)},
              "findings": [{"rule": "r", "location": {"uri": f, "startLine": 1}} for f in files]}
    cache_dir = ctl("cache-dir")
    if cache_dir:
        report["cache"] = {"dir": cache_dir}
    skipped_file = ctl("skipped-file")
    if skipped_file:
        report["skipped"] = [{"file": skipped_file,
                              "reason": "cc: " + skipped_file + ":1:10: fatal error: missing.h: No such file"}]
    if "--changed-lines" in argv:
        report["diff"] = {"argument": "--changed-lines " + argv[argv.index("--changed-lines") + 1],
                          "text": open(argv[argv.index("--changed-lines") + 1]).read()}
    print(json.dumps(report)); sys.exit(0)
if argv[0] in ("facts", "query", "explain"):
    print("ok " + " ".join(argv[2:])); sys.exit(0)
if argv[0] == "findings":
    db = argv[argv.index("--db") + 1]
    records = json.load(open(db))["findings"]
    if argv[1] == "show":
        # The real `scry findings show --json` bundle (wfRootBundle), not the
        # record: it has no top-level `source`, and it embeds the *parsed*
        # evidence files named by the record's artifacts/static/dynamic/verify.
        rec = next((r for r in records if r.get("id") == argv[2]), None)
        if rec is None:
            print("no such finding: " + argv[2], file=sys.stderr); sys.exit(1)
        art = rec.get("artifacts") if isinstance(rec.get("artifacts"), str) else ""
        def evidence(key):
            rel = rec.get(key)
            return read_json(wfjoin(art, rel)) if isinstance(rel, str) else None
        bundle = {
            "schema": "scry-workflow-finding/1",
            "id": rec.get("id", ""),
            "key": rec.get("key", ""),
            "fingerprint": {"semantic": rec.get("id", ""), "lineHash": rec.get("lineHash", ""),
                            "algorithm": "fnv1a64", "inputs": "rule, normalized path"},
            "cweTier": "T1",
            "state": rec.get("state", "new"),
            "history": rec.get("history", []),
            "finding": rec.get("finding", {"source": rec.get("source", "")}),
            "evidence": {"static": rec.get("static", ""), "dynamic": rec.get("dynamic", ""),
                         "verify": rec.get("verify", "")},
            "evidenceItems": [],
            "static": evidence("static"),
            "dynamic": evidence("dynamic"),
            "verify": evidence("verify"),
            "repro": read_json(wfjoin(art, "repro.json")),
            "environment": {"schema": "scry-workflow-environment/1",
                            "cwd": ctl("env-cwd") or os.getcwd(),
                            "uname": ctl("env-uname") or "Linux fake 0.0",
                            "tool": {"name": "scry", "version": "0.1.0-fake",
                                     "binary": {"path": ctl("env-bin") or "scry"}}},
            "limits": ["Static and dynamic evidence are separate."],
        }
        print(json.dumps(bundle)); sys.exit(0)
    print(json.dumps(records)); sys.exit(0)
print("unknown", file=sys.stderr); sys.exit(2)
'''

#: A fake scry in the vulnerable shape: it reads a compile database and, for a `-B<dir>`
#: flag, runs `<dir>/cc1`, which is what `cc` would do. It records nothing; the marker
#: file that `cc1` touches is the evidence that the payload ran.
FAKE_SCRY_WITH_B = r'''#!/usr/bin/env python3
import json, os, shlex, subprocess, sys
argv = sys.argv[1:]
open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "ran"), "w").write("x")
if argv[:1] == ["--version"]:
    print("scry 0.0.0-fake"); sys.exit(0)
if argv[:1] == ["project"]:
    root = argv[1]
    db = json.load(open(os.path.join(root, "compile_commands.json")))
    for entry in db:
        args = entry.get("arguments")
        if not isinstance(args, list):
            args = shlex.split(entry.get("command", ""))
        for arg in args[1:]:
            if arg.startswith("-B") and len(arg) > 2:
                subprocess.run([os.path.join(entry.get("directory") or root, arg[2:], "cc1")], check=False)
    print(json.dumps({"tool": "scry", "counts": {"findings": 0}, "findings": []}))
    sys.exit(0)
print("unknown", file=sys.stderr); sys.exit(2)
'''


class Base(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory(prefix="scry-mcp-unit-")
        root = Path(self.tmp.name)
        self.ws = root / "ws"
        (self.ws / "src").mkdir(parents=True)
        (self.ws / "lib" / "Scry" / "rules").mkdir(parents=True)
        (self.ws / "lib" / "Scry" / "rules" / "default.scry").write_text("rules\n")
        (self.ws / "src" / "a.c").write_text("int main(void) { return 0; }\n")
        (self.ws / "store.json").write_text("{}")
        self.outside = root / "outside"
        self.outside.mkdir()
        (self.outside / "secret.c").write_text("int x;\n")
        bindir = root / "bin"
        bindir.mkdir()
        self.scry = bindir / "scry"
        self.scry.write_text(FAKE_SCRY)
        self.scry.chmod(0o755)
        self.log = root / "calls.jsonl"
        (bindir / "log-path").write_text(str(self.log))
        self.set_files([str(self.ws / "src" / "a.c")])
        self.server = scry_mcp.Server(scry_mcp.Config(workspace=str(self.ws), scry=str(self.scry), timeout=30))

    def tearDown(self) -> None:
        self.server.close()
        self.tmp.cleanup()

    def set_files(self, files: list[str]) -> None:
        (self.scry.parent / "files").write_text(",".join(files))

    def calls(self) -> list[dict]:
        if not self.log.exists():
            return []
        return [json.loads(line) for line in self.log.read_text().splitlines()]

    def call(self, name: str, args: dict) -> dict:
        return self.server.call_tool(name, args)

    def rpc(self, method: str, params: dict) -> dict:
        return self.server.dispatch({"jsonrpc": "2.0", "id": 1, "method": method, "params": params})[0][0]


class ToolListTests(Base):
    def test_every_tool_is_read_only_and_closed_world(self) -> None:
        tools = self.rpc("tools/list", {})["result"]["tools"]
        self.assertEqual({t["name"] for t in tools}, {
            "scry_version", "scry_taint", "scry_project", "scry_facts", "scry_query", "scry_explain", "scry_findings"})
        for tool in tools:
            self.assertTrue(tool["annotations"]["readOnlyHint"], tool["name"])
            self.assertFalse(tool["annotations"]["destructiveHint"], tool["name"])
            self.assertFalse(tool["annotations"]["openWorldHint"], tool["name"])
        names = " ".join(t["name"] for t in tools)
        for absent in ("dynamic", "repro", "triage", "scan", "repl", "bench"):
            self.assertNotIn(absent, names)

    def test_initialize_offers_resources(self) -> None:
        result = self.rpc("initialize", {"protocolVersion": "2025-06-18"})["result"]
        self.assertIn("resources", result["capabilities"])
        self.assertEqual(result["serverInfo"]["name"], "scry")

    def test_unknown_arguments_and_tools(self) -> None:
        self.assertEqual(self.call("scry_taint", {"path": "src/a.c", "sarif": "/tmp/x"})["error"]["kind"], "invalid_args")
        self.assertIn("error", self.rpc("tools/call", {"name": "scry_dynamic", "arguments": {}}))


class TaintTests(Base):
    def test_taint_runs_in_a_private_temp_dir(self) -> None:
        out = self.call("scry_taint", {"path": "src/a.c"})
        self.assertTrue(out["ok"], out)
        call = self.calls()[-1]
        self.assertEqual(call["argv"][:2], ["taint", str(self.ws / "src" / "a.c")])
        self.assertIn("--json", call["argv"])
        self.assertEqual(call["argv"][call["argv"].index("--rules") + 1],
                         str(self.ws / "lib" / "Scry" / "rules" / "default.scry"))
        sarif = call["argv"][call["argv"].index("--sarif") + 1]
        self.assertTrue(sarif.startswith(self.server.tmp + os.sep))
        self.assertTrue(call["cwd"].startswith(self.server.tmp + os.sep))
        self.assertTrue(call["env"]["HOME"].startswith(self.server.tmp + os.sep))
        self.assertEqual(oct(os.stat(self.server.tmp).st_mode & 0o777), "0o700")
        # nothing was written to the workspace
        self.assertFalse(any(p.name == "stray.txt" for p in self.ws.rglob("*")))
        self.assertEqual(out["result"]["_run"]["sarif_uri"], "scry://runs/r1/sarif")

    def test_secrets_never_reach_scry(self) -> None:
        os.environ["SCRY_TEST_API_KEY"] = "do-not-pass"
        os.environ["GH_TOKEN"] = "do-not-pass"
        try:
            self.call("scry_taint", {"path": "src/a.c"})
        finally:
            del os.environ["SCRY_TEST_API_KEY"], os.environ["GH_TOKEN"]
        env = self.calls()[-1]["env"]
        self.assertNotIn("GH_TOKEN", env)
        self.assertNotIn("SCRY_TEST_API_KEY", env)
        self.assertNotIn("do-not-pass", json.dumps(env))

    def test_paths_are_confined(self) -> None:
        link = self.ws / "src" / "link.c"
        link.symlink_to(self.outside / "secret.c")
        for path in (str(self.outside / "secret.c"), "../outside/secret.c", "src/link.c"):
            self.assertEqual(self.call("scry_taint", {"path": path})["error"]["kind"], "path_denied", path)
        self.assertEqual(self.call("scry_taint", {"path": "src/a.c", "rules": str(self.outside / "secret.c")})["error"]["kind"],
                         "path_denied")
        self.assertEqual(self.calls(), [])

    def test_control_characters_are_invalid_arguments(self) -> None:
        for path in ("src/a\u0000.c", "src/\u0001a.c", "src/a.c\n"):
            out = self.call("scry_taint", {"path": path})
            self.assertEqual(out["error"]["kind"], "invalid_args", out)
        self.assertEqual(self.call("scry_taint", {"path": "src/a.c", "rules": "r\u0000.scry"})["error"]["kind"],
                         "invalid_args")
        self.assertEqual(self.calls(), [])

    def test_findings_outside_the_roots_are_withheld(self) -> None:
        self.set_files([str(self.ws / "src" / "a.c"), str(self.outside / "secret.c")])
        out = self.call("scry_taint", {"path": "src/a.c"})
        self.assertEqual(len(out["result"]["findings"]), 1)
        self.assertEqual(out["result"]["_run"]["withheld"], 1)
        self.assertNotIn(str(self.outside), json.dumps(out))
        sarif = self.rpc("resources/read", {"uri": out["result"]["_run"]["sarif_uri"]})["result"]["contents"][0]["text"]
        self.assertNotIn(str(self.outside), sarif)
        self.assertEqual(len(json.loads(sarif)["runs"][0]["results"]), 1)

    def test_diff_base_is_validated_and_git_runs_in_the_workspace(self) -> None:
        for bad in ("--output=/tmp/x", "-p", "a..b", "HEAD;rm", "a b"):
            self.assertEqual(self.call("scry_taint", {"path": "src/a.c", "diff": bad})["error"]["kind"], "invalid_args", bad)
        self.assertEqual(self.calls(), [])
        subprocess.run(["git", "init", "-q", str(self.ws)], check=True)
        subprocess.run(["git", "-C", str(self.ws), "-c", "user.name=t", "-c", "user.email=t@t", "add", "src/a.c"], check=True)
        subprocess.run(["git", "-C", str(self.ws), "-c", "user.name=t", "-c", "user.email=t@t", "commit", "-qm", "a"], check=True)
        (self.ws / "src" / "a.c").write_text("int main(void) { return 1; }\n")
        out = self.call("scry_taint", {"path": "src/a.c", "diff": "HEAD", "diff_context": 2})
        self.assertTrue(out["ok"], out)
        argv = self.calls()[-1]["argv"]
        self.assertIn("--changed-lines", argv)
        self.assertEqual(argv[argv.index("--diff-context") + 1], "2")
        self.assertIn("return 1", out["result"]["diff"]["text"])
        self.assertEqual(out["result"]["diff"]["argument"], "--diff HEAD")
        self.assertEqual(self.call("scry_taint", {"path": "src/a.c", "diff_context": 1})["error"]["kind"], "invalid_args")

    def test_limits(self) -> None:
        self.call("scry_taint", {"path": "src/a.c", "timeout": 9999, "max_nodes": 5})
        argv = self.calls()[-1]["argv"]
        self.assertEqual(argv[argv.index("--timeout") + 1], "30")  # capped at the server's
        self.assertEqual(argv[argv.index("--max-nodes") + 1], "5")
        self.assertEqual(self.call("scry_taint", {"path": "src/a.c", "max_nodes": 0})["error"]["kind"], "invalid_args")

    def test_runs_are_kept_and_bounded(self) -> None:
        for _ in range(scry_mcp.MAX_RUNS + 2):
            self.call("scry_taint", {"path": "src/a.c"})
        uris = [r["uri"] for r in self.rpc("resources/list", {})["result"]["resources"]]
        self.assertEqual(len(uris), 2 * scry_mcp.MAX_RUNS)
        self.assertNotIn("scry://runs/r1/sarif", uris)
        self.assertFalse(os.path.exists(os.path.join(self.server.tmp, "r1")))
        self.assertIn("error", self.rpc("resources/read", {"uri": "scry://runs/r1/sarif"}))
        self.assertIn("error", self.rpc("resources/read", {"uri": "scry://runs/../../etc/passwd"}))

    def test_close_removes_the_temp_dir(self) -> None:
        self.call("scry_taint", {"path": "src/a.c"})
        tmp = self.server.tmp
        self.server.close()
        self.assertFalse(os.path.exists(tmp))

    def test_missing_scry(self) -> None:
        server = scry_mcp.Server(scry_mcp.Config(workspace=str(self.ws), scry=str(self.ws / "nope")))
        try:
            self.assertEqual(server.call_tool("scry_taint", {"path": "src/a.c"})["error"]["kind"], "scry_not_found")
        finally:
            server.close()


class ProjectTests(Base):
    def compdb(self, entries: list[dict]) -> None:
        (self.ws / "src" / "compile_commands.json").write_text(json.dumps(entries))

    def test_project_runs_with_its_compdb(self) -> None:
        self.compdb([{"directory": str(self.ws / "src"), "file": "a.c", "command": "cc -I. -Iinclude -DX -c a.c"}])
        out = self.call("scry_project", {"path": "src"})
        self.assertTrue(out["ok"], out)
        argv = self.calls()[-1]["argv"]
        self.assertEqual(argv[:2], ["project", str(self.ws / "src")])
        self.assertIn("--taint", argv)
        self.assertNotIn("--cc", argv)
        self.assertNotIn("--facts", argv)
        self.assertNotIn("--cache", " ".join(argv))
        self.assertEqual(out["result"]["_run"]["units"], 1)

    def test_allowlisted_flags_still_run(self) -> None:
        self.compdb([{"directory": str(self.ws / "src"), "file": "a.c", "arguments": [
            "cc", "-I.", "-Iinclude", "-isystem", "/usr/include", "-iquote", "q",
            "-DNDEBUG", "-U", "OLD", "-DPAIR(x,y)=x", "-include", "force.h", "-std=c11",
            "-c", "a.c", "-o", "a.o", "-MF", "a.d"]}])
        out = self.call("scry_project", {"path": "src"})
        self.assertTrue(out["ok"], out)

    def test_flags_outside_the_allowlist_are_refused_by_name(self) -> None:
        vectors = [
            (["cc", "-Bbin", "a.c"], "-Bbin"),
            (["cc", "-B", "bin", "a.c"], "-B"),
            (["cc", "-fplugin=bin/p.so", "a.c"], "-fplugin=bin/p.so"),
            (["cc", "-specs=bin/p.specs", "a.c"], "-specs=bin/p.specs"),
            (["cc", "-wrapper", "bin/w", "a.c"], "-wrapper"),
            (["cc", "@bin/args.rsp", "a.c"], "@bin/args.rsp"),
            (["cc", "-Xclang", "-load", "a.c"], "-Xclang"),
            (["cc", "-cc1", "a.c"], "-cc1"),
            (["cc", "-Xlinker", "-rpath", "a.c"], "-Xlinker"),
            (["cc", "-imacros", "x.h", "a.c"], "-imacros"),
            (["cc", "--sysroot=.", "a.c"], "--sysroot=."),
            (["cc", "-O2", "a.c"], "-O2"),
            (["cc", "-fPIC", "a.c"], "-fPIC"),
            (["cc", "stray.o", "a.c"], "stray.o"),
            # a separate value that looks like an option must not be re-read by cc
            (["cc", "-I", "-Bbin", "a.c"], "-Bbin"),
            (["cc", "-D", "@bin/args", "a.c"], "@bin/args"),
        ]
        for args, refused in vectors:
            self.compdb([{"directory": str(self.ws / "src"), "file": "a.c", "arguments": args}])
            out = self.call("scry_project", {"path": "src"})
            self.assertEqual(out["error"]["kind"], "invalid_args", args)
            self.assertIn(refused, out["error"]["message"], args)
        self.assertEqual(self.calls(), [])

    def test_compdb_that_leaves_the_roots_is_refused(self) -> None:
        cases = [
            ([{"directory": str(self.outside), "file": "secret.c"}], "path_denied"),
            ([{"directory": str(self.ws / "src"), "file": "../../outside/secret.c"}], "path_denied"),
            ([{"directory": str(self.ws / "src"), "file": "a.c", "arguments": ["cc", "-I", str(self.outside), "a.c"]}], "path_denied"),
            ([{"directory": str(self.ws / "src"), "file": "a.c", "command": f"cc -include {self.outside}/secret.c a.c"}], "path_denied"),
            ([{"directory": str(self.ws / "src"), "file": "a.c", "command": f"cc -isystem{self.outside} a.c"}], "path_denied"),
            # Scry falls back to `command` when `arguments` has no strings; the
            # bridge used to take the `arguments` branch and confine nothing.
            ([{"directory": str(self.ws / "src"), "file": "a.c", "arguments": [],
               "command": f"cc -I{self.outside} -include {self.outside}/secret.c a.c"}], "path_denied"),
            ([{"directory": str(self.ws / "src"), "file": "a.c", "arguments": [1, None],
               "command": f"cc -include {self.outside}/secret.c a.c"}], "invalid_args"),
            # A non-string element shifts the flag/value adjacency Scry sees.
            ([{"directory": str(self.ws / "src"), "file": "a.c",
               "arguments": ["cc", "-I", 5, str(self.outside), "a.c"]}], "invalid_args"),
            # The system-include exemption is a containment test, not a prefix.
            ([{"directory": str(self.ws / "src"), "file": "a.c", "command": "cc -I/usr/include-anything a.c"}], "path_denied"),
            ([{"directory": str(self.ws / "src"), "file": "a.c", "command": "cc -I/nix/storeXYZ a.c"}], "path_denied"),
            # NUL/control characters are invalid arguments, not `internal` errors.
            ([{"directory": str(self.ws / "src"), "file": "a\u0000.c"}], "invalid_args"),
            ([{"directory": str(self.ws / "src"), "file": "a.c", "command": f"cc -I{self.outside}/x\u0000y a.c"}], "invalid_args"),
        ]
        for entries, kind in cases:
            self.compdb(entries)
            self.assertEqual(self.call("scry_project", {"path": "src"})["error"]["kind"], kind, entries)
        self.compdb([{"directory": str(self.ws / "src"), "file": "a.c", "command": "cc -isystem /usr/include a.c"}])
        self.assertTrue(self.call("scry_project", {"path": "src"})["ok"])
        self.assertEqual(len(self.calls()), 1)
        # The database Scry is handed is the bridge's normalised copy, in the
        # private run dir, so Scry can never re-interpret the original entry.
        argv = self.calls()[0]["argv"]
        passed = argv[argv.index("--compdb") + 1]
        self.assertTrue(passed.startswith(self.server.tmp + os.sep), passed)
        normalized = json.loads(Path(passed).read_text())
        self.assertEqual(normalized[0]["arguments"], ["cc", "-isystem", "/usr/include", "a.c"])

    def test_oversized_compile_db_is_refused_before_reading(self) -> None:
        cap = getattr(scry_mcp, "MAX_COMPDB_BYTES", 64 * 1024 * 1024)
        path = self.ws / "src" / "compile_commands.json"
        with open(path, "w", encoding="utf-8") as handle:  # valid JSON, over the cap
            handle.write("[")
            handle.write(" " * cap)
            handle.write("]")
        out = self.call("scry_project", {"path": "src"})
        self.assertEqual(out["error"]["kind"], "invalid_args", out)
        self.assertEqual(self.calls(), [])

    def test_bad_compdb(self) -> None:
        (self.ws / "src" / "compile_commands.json").write_text("{")
        self.assertEqual(self.call("scry_project", {"path": "src"})["error"]["kind"], "invalid_args")
        self.assertEqual(self.call("scry_project", {"path": "store.json"})["error"]["kind"], "invalid_args")


class GitHardeningTests(Base):
    def test_git_config_cannot_run_a_command(self) -> None:
        subprocess.run(["git", "init", "-q", str(self.ws)], check=True)
        git = ["git", "-C", str(self.ws), "-c", "user.name=t", "-c", "user.email=t@t"]
        subprocess.run(git + ["add", "src/a.c"], check=True)
        subprocess.run(git + ["commit", "-qm", "a"], check=True)
        marker = Path(self.tmp.name, "pwned")
        hook = Path(self.tmp.name, "fsmon.sh")
        hook.write_text(f"#!/bin/sh\ntouch {marker}\nexit 0\n")
        hook.chmod(0o755)
        subprocess.run(["git", "-C", str(self.ws), "config", "core.fsmonitor", str(hook)], check=True)
        subprocess.run(["git", "-C", str(self.ws), "config", "core.hooksPath", str(Path(self.tmp.name, "hooks"))],
                       check=True)
        Path(self.tmp.name, "hooks").mkdir()
        (Path(self.tmp.name, "hooks") / "post-index-change").write_text(f"#!/bin/sh\ntouch {marker}.hook\n")
        (Path(self.tmp.name, "hooks") / "post-index-change").chmod(0o755)
        (self.ws / "src" / "a.c").write_text("int main(void) { return 1; }\n")
        out = self.call("scry_taint", {"path": "src/a.c", "diff": "HEAD"})
        self.assertTrue(out["ok"], out)
        self.assertFalse(marker.exists(), "core.fsmonitor from the workspace .git/config ran")
        self.assertFalse(Path(str(marker) + ".hook").exists(), "a hook from core.hooksPath ran")


class FindingsBundleTests(Base):
    def write_db(self, records: list[dict]) -> str:
        (self.ws / "findings.json").write_text(json.dumps({"schema": "scry-workflow-store/1", "findings": records}))
        return "findings.json"

    def test_show_does_not_return_evidence_from_an_outside_artifacts_dir(self) -> None:
        (self.outside / "config.json").write_text(json.dumps({"auths": {"registry.example": "secret-token"}}))
        (self.outside / "repro.json").write_text(json.dumps({"witness": "secret-witness"}))
        db = self.write_db([{"id": "f_1", "key": "k", "state": "new", "source": "src/a.c",
                             "artifacts": str(self.outside), "static": "config.json"}])
        out = self.call("scry_findings", {"action": "show", "id": "f_1", "db": db})
        self.assertNotIn("secret-token", json.dumps(out), out)
        self.assertNotIn("secret-witness", json.dumps(out), out)
        self.assertNotIn(str(self.outside), json.dumps(out), out)
        self.assertIsNone(out["result"]["static"], out)
        self.assertIsNone(out["result"]["repro"], out)

    def test_show_still_returns_evidence_inside_the_roots(self) -> None:
        artifacts = self.ws / "scry-workflow"
        artifacts.mkdir()
        (artifacts / "static.json").write_text(json.dumps({"derivation": {"status": "checked"}}))
        db = self.write_db([{"id": "f_4", "key": "k", "state": "new", "source": "src/a.c",
                             "artifacts": str(artifacts), "static": "static.json"}])
        out = self.call("scry_findings", {"action": "show", "id": "f_4", "db": db})
        self.assertTrue(out.get("ok"), out)
        self.assertEqual(out["result"]["static"]["derivation"]["status"], "checked", out)

    def test_show_confines_the_bundle_finding_source(self) -> None:
        # The real bundle has `finding.source`, not a top-level `source`; the old
        # check read the key that is never there and returned the bundle anyway.
        db = self.write_db([{"id": "f_2", "key": "k", "state": "new", "source": str(self.outside / "secret.c"),
                             "finding": {"rule": "r", "source": str(self.outside / "secret.c")}}])
        self.assertEqual(self.call("scry_findings", {"action": "show", "id": "f_2", "db": db})["error"]["kind"],
                         "path_denied")

    def test_list_redacts_the_artifacts_and_nested_source(self) -> None:
        db = self.write_db([
            {"id": "f_1", "key": "k", "state": "new", "source": "src/a.c", "artifacts": str(self.outside)},
            {"id": "f_2", "key": "k", "state": "new", "source": "src/a.c",
             "finding": {"source": str(self.outside / "secret.c")}},
        ])
        out = self.call("scry_findings", {"action": "list", "db": db})
        self.assertNotIn(str(self.outside), json.dumps(out), out)
        self.assertEqual([f["id"] for f in out["result"]["findings"]], ["f_1"])
        self.assertEqual(out["result"]["findings"][0]["artifacts"], "(withheld)")
        self.assertEqual(out["result"]["withheld"], 1)

    def test_project_report_redacts_skipped_reasons_cache_and_environment(self) -> None:
        (self.scry.parent / "cache-dir").write_text(str(self.outside / "cache"))
        (self.scry.parent / "skipped-file").write_text(str(self.outside / "bad.c"))
        (self.scry.parent / "env-cwd").write_text(str(self.outside / "private-run"))
        (self.scry.parent / "env-bin").write_text(str(self.outside / "scry"))
        self.set_files([str(self.ws / "src" / "a.c")])
        (self.ws / "src" / "compile_commands.json").write_text(json.dumps(
            [{"directory": str(self.ws / "src"), "file": "a.c", "command": "cc a.c"}]))
        out = self.call("scry_project", {"path": "src", "skip_broken": True})
        self.assertTrue(out["ok"], out)
        text = json.dumps(out)
        self.assertNotIn(str(self.outside), text)
        self.assertEqual(out["result"]["skipped"][0]["reason"], "(withheld)")
        self.assertEqual(out["result"]["cache"]["dir"], "(withheld)")
        db = self.write_db([{"id": "f_3", "key": "k", "state": "new", "source": "src/a.c"}])
        shown = self.call("scry_findings", {"action": "show", "id": "f_3", "db": db})
        text = json.dumps(shown)
        self.assertNotIn(str(self.outside), text)
        self.assertEqual(shown["result"]["environment"]["cwd"], "(withheld)")
        self.assertEqual(shown["result"]["environment"]["tool"]["binary"]["path"], "(withheld)")
        self.assertEqual(shown["result"]["environment"]["uname"], "(withheld)")


class SizeCapTests(Base):
    def test_oversized_findings_db_is_refused(self) -> None:
        db = self.ws / "findings.json"
        db.write_text(json.dumps({"schema": "scry-workflow-store/1",
                                  "findings": [{"id": "f_1", "source": "src/a.c"}],
                                  "padding": " " * 2048}))
        saved = getattr(scry_mcp, "MAX_FINDINGS_BYTES", None)
        scry_mcp.MAX_FINDINGS_BYTES = 1024
        try:
            out = self.call("scry_findings", {"action": "show", "id": "f_1", "db": "findings.json"})
        finally:
            if saved is None:
                del scry_mcp.MAX_FINDINGS_BYTES
            else:
                scry_mcp.MAX_FINDINGS_BYTES = saved
        self.assertEqual(out["error"]["kind"], "invalid_args", out)
        self.assertEqual(self.calls(), [])

    def test_oversized_resource_is_refused(self) -> None:
        out = self.call("scry_taint", {"path": "src/a.c"})
        path = Path(self.server.runs[out["result"]["_run"]["run"]]["json"])
        cap = 4096
        with open(path, "w", encoding="utf-8") as handle:
            handle.write(" " * (cap + 1))
        saved = getattr(scry_mcp, "MAX_RESOURCE_BYTES", None)
        scry_mcp.MAX_RESOURCE_BYTES = cap
        try:
            response = self.rpc("resources/read", {"uri": out["result"]["_run"]["json_uri"]})
        finally:
            if saved is None:
                del scry_mcp.MAX_RESOURCE_BYTES
            else:
                scry_mcp.MAX_RESOURCE_BYTES = saved
        self.assertTrue("error" in response, sorted(response))

    def test_size_caps_are_sane(self) -> None:
        self.assertGreaterEqual(scry_mcp.MAX_COMPDB_BYTES, 1024 * 1024)
        self.assertGreaterEqual(scry_mcp.MAX_RESOURCE_BYTES, 1024 * 1024)
        self.assertGreaterEqual(scry_mcp.MAX_FINDINGS_BYTES, 1024 * 1024)
        self.assertGreaterEqual(scry_mcp.MAX_COMPDB_ENTRIES, 1000)


class ProjectFlagExecutionTests(Base):
    """security-01: a database's `-Bbin` must not reach a `cc` that would run `bin/cc1`."""

    def setUp(self) -> None:
        super().setUp()
        self.payload = self.ws / "src" / "bin"
        self.payload.mkdir()
        self.marker = Path(self.tmp.name) / "cc1-ran"
        cc1 = self.payload / "cc1"
        cc1.write_text(f"#!/bin/sh\ntouch '{self.marker}'\nexit 0\n")
        cc1.chmod(0o755)
        self.fake = self.scry.parent / "scry-with-b"
        self.fake.write_text(FAKE_SCRY_WITH_B)
        self.fake.chmod(0o755)
        self.server.close()
        self.server = scry_mcp.Server(scry_mcp.Config(workspace=str(self.ws), scry=str(self.fake), timeout=30))
        (self.ws / "src" / "compile_commands.json").write_text(json.dumps([
            {"directory": str(self.ws / "src"), "file": "a.c",
             "arguments": ["cc", "-Bbin", "-E", "a.c"]}]))

    def test_the_payload_would_run_if_the_database_reached_scry(self) -> None:
        # Control: this is the vulnerable shape the MCP must refuse. A scry that honours
        # the database's -B runs bin/cc1, which touches the marker.
        subprocess.run([str(self.fake), "project", str(self.ws / "src")], check=True,
                       stdout=subprocess.DEVNULL)
        self.assertTrue(self.marker.exists())
        self.marker.unlink()

    def test_the_mcp_refuses_the_database_and_never_runs_the_payload(self) -> None:
        out = self.call("scry_project", {"path": "src"})
        self.assertEqual(out["error"]["kind"], "invalid_args")
        self.assertIn("-Bbin", out["error"]["message"])
        self.assertFalse(self.marker.exists())
        self.assertFalse((self.fake.parent / "ran").exists())
        self.assertEqual(self.calls(), [])


class StoreAndFindingsTests(Base):
    def test_query_explain_facts(self) -> None:
        self.assertEqual(self.call("scry_query", {"path": "store.json", "rel": "cfg"})["stdout"].strip(), "ok --rel cfg")
        self.assertEqual(self.call("scry_query", {"path": "store.json", "edge_src": "child"})["stdout"].strip(), "ok --edge-src child")
        self.assertEqual(self.call("scry_explain", {"path": "store.json", "node": 3})["stdout"].strip(), "ok 3")
        self.assertTrue(self.call("scry_facts", {"path": "store.json"})["ok"])
        for bad in ({"path": "store.json"}, {"path": "store.json", "kind": "a", "rel": "b"},
                    {"path": "store.json", "kind": "--rel"}):
            self.assertEqual(self.call("scry_query", bad)["error"]["kind"], "invalid_args", bad)
        self.assertEqual(self.call("scry_explain", {"path": "store.json", "node": -1})["error"]["kind"], "invalid_args")
        self.assertEqual(self.call("scry_facts", {"path": str(self.outside / "secret.c")})["error"]["kind"], "path_denied")

    def test_findings_list_and_show(self) -> None:
        self.assertEqual(self.call("scry_findings", {"action": "list"})["result"]["db"], "absent")
        self.assertEqual(self.call("scry_findings", {"action": "show", "id": "f_1"})["error"]["kind"], "not_found")
        db = self.ws / "scry-workflow" / "findings.json"
        db.parent.mkdir()
        db.write_text(json.dumps({"schema": "scry-workflow-store/1", "findings": [
            {"id": "f_1", "source": str(self.ws / "src" / "a.c"), "state": "new"},
            {"id": "f_2", "source": str(self.outside / "secret.c"), "state": "new"},
        ]}))
        before = db.read_text()
        listed = self.call("scry_findings", {"action": "list", "state": "new"})
        self.assertEqual([f["id"] for f in listed["result"]["findings"]], ["f_1"])
        self.assertEqual(listed["result"]["withheld"], 1)
        self.assertNotIn(str(self.outside), json.dumps(listed))
        self.assertEqual(self.call("scry_findings", {"action": "show", "id": "f_1"})["result"]["id"], "f_1")
        self.assertEqual(self.call("scry_findings", {"action": "show", "id": "f_2"})["error"]["kind"], "path_denied")
        for bad in ({"action": "triage", "id": "f_1"}, {"action": "show", "id": "--db=/x"}, {"action": "show"},
                    {"action": "list", "id": "f_1"}, {"action": "list", "state": "bogus"},
                    {"action": "list", "db": str(self.outside / "secret.c")}):
            self.assertIn(self.call("scry_findings", bad)["error"]["kind"], ("invalid_args", "path_denied"), bad)
        self.assertEqual(db.read_text(), before)
        argv = self.calls()[-1]["argv"]
        self.assertIn("--json", argv)


class HelperTests(unittest.TestCase):
    def test_include_paths(self) -> None:
        self.assertEqual(scry_mcp._include_paths(["cc", "-Ia", "-I", "b", "-isystem", "c", "-isystemd", "-include", "e.h", "-DX"]),
                         ["a", "b", "c", "d", "e.h"])

    def test_resolve_scry_never_runs_a_workspace_binary(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            ws = Path(tmp, "ws")
            planted = ws / "scry" / ".grail" / "bin" / "scry"
            planted.parent.mkdir(parents=True)
            planted.write_text("#!/bin/sh\ntouch /tmp/pwned\n")
            planted.chmod(0o755)
            bindir = Path(tmp, "bin")
            bindir.mkdir()
            good = bindir / "scry"
            good.write_text("#!/bin/sh\n")
            good.chmod(0o755)
            saved_path = os.environ.get("PATH")
            saved_scry = os.environ.pop("SCRY_BIN", None)
            try:
                os.environ["PATH"] = str(bindir)
                self.assertEqual(scry_mcp.resolve_scry(str(ws), None), str(good))
                os.environ["PATH"] = str(Path(tmp, "empty"))
                self.assertIsNone(scry_mcp.resolve_scry(str(ws), None))
            finally:
                os.environ["PATH"] = saved_path or ""
                if saved_scry is not None:
                    os.environ["SCRY_BIN"] = saved_scry


if __name__ == "__main__":
    unittest.main()
