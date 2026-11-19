#!/usr/bin/env python3
"""Reject toolchain pins that are not a commit plus a content hash.

A pin is reproducible only when it names the exact bytes it wants (a content hash) and
where they came from (a full commit). A branch, a channel, a short sha or free text
resolves differently tomorrow, or not at all (a `wiz-toolchain` once held a local-merge
description, which tower parsed as a ref). docs/bootstrap-chain.md, "Pins".

Two kinds of file:

  wizc-toolchain.json   the chain pin of a commit (the toolchain that builds it):
                        {"format": 1, "commit": "<40 hex>", "hash": "sha256-<base64>=",
                         "system": "x86_64-linux", "urls": ["https://..."]}
                        commit and hash are required; urls are optional extra mirrors
                        (https only); unknown keys are errors.
  wiz-toolchain         a tower pin (docs/stages/26-tower.md, 26a): one spec line. Pinned
                        means `REF@<40 hex>` followed by ` sha256-<base64>=` (the hash
                        field is the proposed extension; tower does not read it yet).
                        --commit-only accepts `REF@<40 hex>` without the hash, which is
                        what tower can install today.

Usage
  scripts/check-toolchain-pin.py FILE...          check the files (kind by base name)
  scripts/check-toolchain-pin.py --commit-only F  tower pins may omit the hash
  scripts/check-toolchain-pin.py --self-test      run the built-in cases

Exit status: 0 all pins ok, 1 a pin is rejected, 2 usage error.
"""
from __future__ import annotations

import json
import os
import re
import sys

COMMIT = re.compile(r"[0-9a-f]{40}")
SRI = re.compile(r"sha256-[A-Za-z0-9+/]{43}=")
SPEC = re.compile(r"(?P<ref>[A-Za-z0-9._/-]+)@(?P<commit>[^ \t]+)(?:[ \t]+(?P<hash>[^ \t]+))?")


def check_chain(text: str) -> list[str]:
    try:
        pin = json.loads(text)
    except json.JSONDecodeError as e:
        return [f"not JSON: {e}"]
    if not isinstance(pin, dict):
        return ["not a JSON object"]
    errs = []
    unknown = set(pin) - {"format", "commit", "hash", "system", "urls"}
    if unknown:
        errs.append(f"unknown keys: {', '.join(sorted(unknown))}")
    if pin.get("format") != 1:
        errs.append("format must be 1")
    c = pin.get("commit")
    if not isinstance(c, str) or not COMMIT.fullmatch(c):
        errs.append(f"commit must be a full 40-hex commit, got {c!r}")
    h = pin.get("hash")
    if not isinstance(h, str) or not SRI.fullmatch(h):
        errs.append(f"hash must be an SRI sha256 (sha256-...=), got {h!r}")
    urls = pin.get("urls", [])
    if not isinstance(urls, list) or not all(isinstance(u, str) and u.startswith("https://") for u in urls):
        errs.append("urls must be a list of https:// URLs")
    s = pin.get("system", "x86_64-linux")
    if s not in ("x86_64-linux", "aarch64-linux"):
        errs.append(f"unknown system {s!r}")
    return errs


def check_tower(text: str, commit_only: bool) -> list[str]:
    lines = [l.strip() for l in text.splitlines()]
    lines = [l for l in lines if l and not l.startswith("#") and not l.startswith("--")]
    if not lines:
        return ["no spec line"]
    spec = lines[0]
    m = SPEC.fullmatch(spec)
    if not m:
        return [f"not pinned: {spec!r} is not REF@COMMIT (a channel, branch, tag, path or text resolves differently over time)"]
    if not COMMIT.fullmatch(m["commit"]):
        return [f"commit must be the full 40 hex digits, got {m['commit']!r}"]
    if m["hash"] is None:
        return [] if commit_only else [f"no content hash: write `{spec} sha256-...=` (or check with --commit-only)"]
    if not SRI.fullmatch(m["hash"]):
        return [f"hash must be an SRI sha256 (sha256-...=), got {m['hash']!r}"]
    return []


def check_file(path: str, commit_only: bool) -> list[str]:
    name = os.path.basename(path)
    try:
        with open(path, encoding="utf-8") as f:
            text = f.read()
    except OSError as e:
        return [f"cannot read: {e}"]
    if name.endswith(".json"):
        return check_chain(text)
    return check_tower(text, commit_only)


def self_test() -> int:
    good_c = "071a033a433f93bf9bb54325560506c444a19787"
    good_h = "sha256-" + "A" * 43 + "="
    cases = [
        (check_tower(f"master@{good_c} {good_h}\n", False), True),
        (check_tower(f"# pinned\nmaster@{good_c}\n", True), True),
        (check_tower(f"master@{good_c}\n", False), False),
        (check_tower("master@071a033\n", True), False),
        (check_tower("nightly\n", True), False),
        (check_tower("local merge of master + #166 + #199\n", True), False),
        (check_tower("../wiz\n", True), False),
        (check_tower(f"master@{good_c} md5-abc\n", False), False),
        (check_chain(json.dumps({"format": 1, "commit": good_c, "hash": good_h})), True),
        (check_chain(json.dumps({"format": 1, "commit": good_c, "hash": good_h, "urls": ["https://m.example/x"]})), True),
        (check_chain(json.dumps({"format": 1, "commit": "master", "hash": good_h})), False),
        (check_chain(json.dumps({"format": 1, "commit": good_c})), False),
        (check_chain(json.dumps({"format": 1, "commit": good_c, "hash": good_h, "urls": ["http://x"]})), False),
        (check_chain(json.dumps({"format": 1, "commit": good_c, "hash": good_h, "ref": "master"})), False),
        (check_chain("{"), False),
    ]
    bad = [i for i, (errs, ok) in enumerate(cases) if (not errs) != ok]
    for i in bad:
        print(f"self-test case {i} wrong: {cases[i][0]}", file=sys.stderr)
    print(f"self-test: {len(cases) - len(bad)}/{len(cases)} ok")
    return 1 if bad else 0


def main(argv: list[str]) -> int:
    if "--self-test" in argv:
        return self_test()
    commit_only = "--commit-only" in argv
    files = [a for a in argv if a != "--commit-only"]
    if not files or any(a.startswith("-") for a in files):
        print(__doc__, file=sys.stderr)
        return 2
    status = 0
    for f in files:
        errs = check_file(f, commit_only)
        for e in errs:
            print(f"{f}: {e}")
        status |= 1 if errs else 0
    return status


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
