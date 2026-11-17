#!/usr/bin/env python3
"""End-to-end smoke test for tools/scry-mcp with a real `scry` build.

Run from a checkout (it uses the repository's own corpus and rule pack):

    python3 tools/scry-mcp/tests/smoke.py --scry scry/.grail/bin/scry

It starts the server the way an MCP client does and checks taint on a known
format-string bug (one finding, its SARIF as a resource), a diff filter against
HEAD (the finding is suppressed), a compile_commands project (two findings),
a fact-store query, the findings list, a refused path, and that the checkout's
`git status` is unchanged afterwards (nothing was written to the workspace).
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--scry", required=True)
    args = parser.parse_args()
    status = lambda: subprocess.run(["git", "-C", ROOT, "status", "--porcelain", "--ignored"],  # noqa: E731
                                    capture_output=True, text=True).stdout
    before = status()
    proc = subprocess.Popen([sys.executable, os.path.join(ROOT, "tools", "scry-mcp", "scry_mcp.py"),
                             "--workspace", ROOT, "--scry", os.path.abspath(args.scry), "--timeout", "120"],
                            stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)
    counter = [0]

    def rpc(method: str, params: dict) -> dict:
        counter[0] += 1
        proc.stdin.write(json.dumps({"jsonrpc": "2.0", "id": counter[0], "method": method, "params": params}) + "\n")
        proc.stdin.flush()
        return json.loads(proc.stdout.readline())

    def call(name: str, **arguments: object) -> dict:
        return rpc("tools/call", {"name": name, "arguments": arguments})["result"]["structuredContent"]

    try:
        rpc("initialize", {"protocolVersion": "2025-06-18"})
        print("version:", call("scry_version")["stdout"].strip())
        bug = "scry/bench/corpus/cwe134/printf-unsafe.c"
        taint = call("scry_taint", path=bug)
        findings = taint["result"]["findings"]
        assert taint["ok"] and [f["rule"] for f in findings] == ["format-string"], taint
        sarif = json.loads(rpc("resources/read", {"uri": taint["result"]["_run"]["sarif_uri"]})["result"]["contents"][0]["text"])
        assert len(sarif["runs"][0]["results"]) == 1, sarif
        print("taint: 1 format-string finding, SARIF resource with 1 result")
        diff = call("scry_taint", path=bug, diff="HEAD")["result"]
        assert diff["findings"] == [] and diff["diff"]["findings"]["suppressed"] == 1, diff
        print("taint --diff HEAD: the finding is suppressed on an unchanged file")
        project = call("scry_project", path="scry/corpus/project/taint")
        assert project["ok"] and project["result"]["counts"]["findings"] == 2, project
        print("project: 3 units, 2 findings")
        query = call("scry_query", path="scry/fixtures/demo.facts.json", kind="function_definition")
        assert query["ok"] and "1 match" in query["stdout"], query
        print("query: ok")
        listed = call("scry_findings", action="list")
        assert listed["ok"], listed
        denied = call("scry_taint", path="/etc/passwd")
        assert denied["error"]["kind"] == "path_denied", denied
        print("findings list: ok; /etc/passwd: path_denied")
        rpc("shutdown", {})
        proc.stdin.write(json.dumps({"jsonrpc": "2.0", "method": "exit"}) + "\n")
        proc.stdin.close()
        proc.wait(timeout=30)
    finally:
        if proc.poll() is None:
            proc.kill()
    after = status()
    assert before == after, f"the workspace changed:\n{before}\n---\n{after}"
    print("workspace: unchanged")
    print("RESULT: PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
