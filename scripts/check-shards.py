#!/usr/bin/env python3
"""The shard plan must be total: every case-listed test group is selected by a shard's
selectors or named in .github/test-shard-exclusions.json with a reason and an owner.

  scripts/check-shards.py [BIN]        the full check `scripts/ci.py check-shards` runs:
                                       every case in exactly one shard (after splitting),
                                       the matrix runs them all once, every group is in a
                                       shard or excluded, no exclusion is stale, and every
                                       .github/skip-allowlist.json entry matches a case
  scripts/check-shards.py --self-test  the same check on stand-in drivers, shard files,
                                       exclusion lists and allow-lists: each failure mode
                                       (a dropped case, a duplicate case, a selector that
                                       selects nothing, a group no shard selects, a stale
                                       or malformed exclusion, a dead allow-list entry) is
                                       a fixture that must fail
  scripts/check-shards.py --groups F   only the group-totality half, against the output of
                                       `lake test -- --list` (one group name per line in
                                       F): every group is in a shard or excluded, and no
                                       exclusion names a group that does not exist
  scripts/check-shards.py --json       the machine-readable plan: shards, selectors,
                                       groups, exclusions and the errors

There is no default-shard fallback: a group that no selector picks is an error naming the
group (and its `Group.shard` hint), so new wiring cannot be forgotten silently. The
exclusions are for groups that deliberately run in no CI shard (with the reason); an
entry that a shard selects after all is stale and fails too.

Options: `--shards FILE`, `--exclusions FILE`, `--timings FILE`, `--skips FILE` override
the checked-in files (the self-test uses temporary ones). The default BIN is
`.lake/build/bin/tests` (or `lake test`'s driver under `.lake`).

The check is `scripts/ci.py check-shards`; this script is its direct entry point (CI
keeps calling the subcommand, so both exercise the same code) and adds the `--groups`
form and the JSON plan for a reviewer.
"""
import argparse
import json
import os
import sys

import ci


def coverage(binary):
    """(groups, shards, selectors, exclusions) for the plan as it stands."""
    out = ci.subprocess.run([binary, "--list-shards"], capture_output=True, text=True,
                            check=True, cwd=ci.ROOT).stdout
    groups = [l.partition("\t")[0] for l in out.split("\n") if l]
    ss = ci.shards()
    return (groups, ss, sum(len(s["select"]) for s in ss), ci.exclusions())


def print_coverage(binary, errors):
    groups, ss, selectors, exclusions = coverage(binary)
    split = sum(1 for s in ss if s.get("split", 1) > 1)
    covered = {g for g in groups
               if any(ci.selects(g, sel) for s in ss for sel in s["select"])}
    excluded = {e["group"] for e in exclusions}
    print(f"coverage: {len(groups)} groups; {len(ss)} shards ({split} split), "
          f"{selectors} selectors; {len(covered)} groups covered, "
          f"{len(excluded)} excluded ({', '.join(sorted(excluded)) or 'none'}), "
          f"{len(set(groups) - covered - excluded)} uncovered; "
          f"{len(errors)} error{'s' if len(errors) != 1 else ''}")


def group_check(path):
    """The group-totality check against a captured `tests --list` (a file, `-` for stdin)."""
    text = sys.stdin.read() if path == "-" else open(path, encoding="utf-8").read()
    groups = [g.strip() for g in text.split("\n") if g.strip()]
    if not groups:
        print("no groups listed: the listing is empty, so it proves nothing", file=sys.stderr)
        return 1
    errors = ci.check_group_plan(groups)
    for e in errors:
        print(e, file=sys.stderr)
    if errors:
        return 1
    ss = ci.shards()
    selectors = sum(len(s["select"]) for s in ss)
    excluded = {e["group"] for e in ci.exclusions()}
    covered = {g for g in groups
               if any(ci.selects(g, sel) for s in ss for sel in s["select"])}
    print(f"ok: {len(groups)} groups from {path}; {len(ss)} shards, {selectors} selectors; "
          f"{len(covered)} covered by a shard, {len(excluded)} excluded "
          f"({', '.join(sorted(excluded)) or 'none'})")
    return 0


def group_self_test():
    """`--groups` on captured listings: a total plan passes; a group no selector picks,
    a stale exclusion and an empty listing fail. Exits 1 if an expectation is wrong."""
    import contextlib, io, tempfile
    saved = (ci.SHARDS, ci.EXCLUSIONS)
    trials = [
        ("a total listing", [{"name": "s", "select": ["=alpha", "=beta"]}], {"groups": []},
         "alpha\nbeta\n", 0, None),
        ("a group no selector picks", [{"name": "s", "select": ["=alpha"]}], {"groups": []},
         "alpha\nbeta\n", 1, "no shard selects"),
        ("an exclusion explains the group", [{"name": "s", "select": ["=alpha"]}],
         {"groups": [{"group": "beta", "reason": "fixture", "owner": "self-test"}]},
         "alpha\nbeta\n", 0, None),
        ("an exclusion names a missing group", [{"name": "s", "select": ["=alpha", "=beta"]}],
         {"groups": [{"group": "gamma", "reason": "fixture", "owner": "self-test"}]},
         "alpha\nbeta\n", 1, "not a test group"),
        ("an empty listing proves nothing", [{"name": "s", "select": ["=alpha"]}],
         {"groups": []}, "", 1, "empty"),
    ]
    bad = 0
    try:
        with tempfile.TemporaryDirectory() as d:
            for i, (name, ss, ex, listing, want, needle) in enumerate(trials):
                ci.SHARDS = os.path.join(d, f"shards{i}.json")
                ci.EXCLUSIONS = os.path.join(d, f"exclusions{i}.json")
                path = os.path.join(d, f"groups{i}.txt")
                with open(ci.SHARDS, "w") as f:
                    json.dump(ss, f)
                with open(ci.EXCLUSIONS, "w") as f:
                    json.dump(ex, f)
                with open(path, "w") as f:
                    f.write(listing)
                err = io.StringIO()
                with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(err):
                    got = group_check(path)
                text = err.getvalue()
                ok = got == want and (needle is None or needle in text)
                print(f"{'ok ' if ok else 'BAD'} groups: {name}: exit {got} (expected {want})"
                      + ("" if ok else f"; stderr: {text.strip()}"))
                bad += not ok
    finally:
        ci.SHARDS, ci.EXCLUSIONS = saved
    return 1 if bad else 0


def main(argv):
    ap = argparse.ArgumentParser(add_help=True, description=__doc__.split("\n")[0])
    ap.add_argument("binary", nargs="?", default=ci.DEFAULT_BIN,
                    help="the test driver (`tests`), default .lake/build/bin/tests")
    ap.add_argument("--self-test", action="store_true", help="check the check on fixtures")
    ap.add_argument("--groups", metavar="FILE",
                    help="only the group-totality check, on `tests --list` output in FILE (- for stdin)")
    ap.add_argument("--shards", default=ci.SHARDS)
    ap.add_argument("--exclusions", default=ci.EXCLUSIONS)
    ap.add_argument("--timings", default=ci.TIMINGS)
    ap.add_argument("--skips", default=ci.SKIPS)
    ap.add_argument("--json", action="store_true", help="print the plan and errors as JSON")
    a = ap.parse_args(argv)
    ci.SHARDS, ci.EXCLUSIONS, ci.TIMINGS, ci.SKIPS = a.shards, a.exclusions, a.timings, a.skips
    if a.self_test:
        shard_rc, groups_rc = ci.check_shards_self_test(), group_self_test()
        return 1 if (shard_rc or groups_rc) else 0
    try:
        if a.groups:
            rc = group_check(a.groups)
            if a.json:
                print(json.dumps({"groups_file": a.groups, "ok": rc == 0,
                                  "exclusions": ci.exclusions()}, indent=2))
            return rc
        if not os.path.exists(a.binary):
            print(f"check-shards: no test driver at {a.binary}; build it (`lake build tests`) "
                  f"or pass BIN", file=sys.stderr)
            return 2
        if a.json:
            import contextlib, io
            err = io.StringIO()
            with contextlib.redirect_stderr(err):
                rc = ci.check_shards(a.binary)
            groups, ss, selectors, exclusions = coverage(a.binary)
            print(json.dumps({"ok": rc == 0, "groups": groups, "shards": ss,
                              "selectors": selectors, "exclusions": exclusions,
                              "errors": [l for l in err.getvalue().split("\n") if l]},
                             indent=2))
            return rc
        rc = ci.check_shards(a.binary)
        print_coverage(a.binary, [] if rc == 0 else ["failed"])
        return rc
    except ci.ShardPlanError as e:
        print(e, file=sys.stderr)
        if a.json:
            print(json.dumps({"ok": False, "errors": str(e).split("\n")}, indent=2))
        return 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
