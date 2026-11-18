#!/usr/bin/env python3
"""Read the JSON of `scripts/check-repro.sh --json` and assert what it says.

The corpus step used to run the script with --json and throw the document away: only
the exit code was read, so the skipped compiler comparison (`"compiler":
{"status": "skip"}`) was invisible. This reader is the CI assertion:

  * the schema is `wiz-repro-paths/v1`, `ok` is true and `status` is "ok";
  * at least one check ran (a comparison that measured nothing proves nothing) and no
    check has status "diff" or "error";
  * with --require-compiler, `compiler.status` must be "ok": a skip means the two-path
    compiler rebuild did not happen, which is the thing the nightly job exists to test.

Without --require-compiler a skipped compiler comparison is a notice (annotated in
Actions), not a failure: the pull-request corpus job does not build the compiler twice.

Usage: scripts/check-repro-report.py [--require-compiler] FILE
       scripts/check-repro-report.py --self-test
Exit 0 passes, 1 fails, 2 usage or unreadable input.
"""
import json
import sys

SCHEMA = "wiz-repro-paths/v1"


def check(doc, require_compiler=False):
    """(errors, notices) for one parsed result document."""
    errors, notices = [], []
    if not isinstance(doc, dict):
        return ["the result is not a JSON object"], notices
    if doc.get("schema") != SCHEMA:
        errors.append(f"the schema is {doc.get('schema')!r}, expected {SCHEMA!r}")
    if doc.get("ok") is not True or doc.get("status") != "ok":
        errors.append(f"the run status is {doc.get('status')!r} (ok: {doc.get('ok')!r})")
    checks = doc.get("checks")
    if not isinstance(checks, list) or not checks:
        errors.append("no checks ran: a run that compared nothing is not a pass")
    else:
        for c in checks:
            if not isinstance(c, dict):
                errors.append(f"a malformed check: {c!r}")
            elif c.get("status") in ("diff", "error"):
                errors.append(f"{c.get('status')} {c.get('name')}: {c.get('detail')}")
    comp = doc.get("compiler")
    cstatus = comp.get("status") if isinstance(comp, dict) else None
    if require_compiler:
        if cstatus != "ok":
            errors.append(f"the compiler comparison is {cstatus or 'missing'!r}; "
                          "--compiler is required here")
    elif cstatus == "skip":
        notices.append("the compiler comparison was skipped; the nightly --compiler "
                       "job runs it")
    return errors, notices


def self_test():
    """Check the reader on synthetic result documents; exit 1 if an expectation is wrong."""
    base = {"schema": SCHEMA, "ok": True, "status": "ok",
            "checks": [{"name": "wiz out", "status": "ok", "detail": "1 files"}],
            "diffs": [],
            "compiler": {"status": "ok", "checks": []}}
    trials = [
        ("a clean run with the compiler compared", base, False, 0, None),
        ("a clean corpus run with the compiler skipped", dict(base, compiler={"status": "skip", "checks": []}),
         False, 0, "skipped"),
        ("--require-compiler rejects a skipped compiler", dict(base, compiler={"status": "skip", "checks": []}),
         True, 1, "required"),
        ("--require-compiler rejects a failed compiler", dict(base, compiler={"status": "fail", "checks": []}),
         True, 1, "compiler comparison"),
        ("a failed run is a failure", dict(base, ok=False, status="fail"), False, 1, "status"),
        ("a skipped run is a failure", dict(base, ok=False, status="skip"), False, 1, "status"),
        ("an empty check list is a failure", dict(base, checks=[]), False, 1, "no checks"),
        ("a diff check is a failure",
         dict(base, checks=[{"name": "wiz out", "status": "diff", "detail": "a vs b"}]),
         False, 1, "diff wiz out"),
        ("an error check is a failure",
         dict(base, checks=[{"name": "grail .grail", "status": "error", "detail": "empty"}]),
         False, 1, "error grail"),
        ("another schema is a failure", dict(base, schema="wiz-repro-paths/v2"), False, 1, "schema"),
        ("a non-object is a failure", [], False, 1, "not a JSON object"),
    ]
    bad = 0
    for name, doc, require, want, needle in trials:
        errors, notices = check(doc, require)
        got = 1 if errors else 0
        ok = got == want and (needle is None or any(needle in e for e in errors + notices))
        bad += not ok
        print(f"{'ok  ' if ok else 'FAIL'} {name}: {len(errors)} error(s), "
              f"{len(notices)} notice(s)"
              + ("" if ok else f", expected {want}"
                 + (f" mentioning {needle!r}" if needle else "")
                 + f": {errors + notices}"))
    checks = len(trials)
    print(f"check-repro report self-test: {checks} checks, {checks - bad} ok")
    return 1 if bad else 0


def main(argv):
    args = list(argv)
    require_compiler, self_test_flag = False, False
    files = []
    while args:
        a = args.pop(0)
        if a == "--require-compiler":
            require_compiler = True
        elif a == "--self-test":
            self_test_flag = True
        elif a == "-h" or a == "--help":
            print(__doc__)
            return 0
        elif a.startswith("--"):
            print(f"check-repro-report: unknown flag {a}", file=sys.stderr)
            return 2
        else:
            files.append(a)
    if self_test_flag:
        return self_test()
    if len(files) != 1:
        print(__doc__, file=sys.stderr)
        return 2
    try:
        with open(files[0], encoding="utf-8") as f:
            doc = json.load(f)
    except (OSError, json.JSONDecodeError) as e:
        print(f"::error title=Reproducibility::cannot read {files[0]}: {e}")
        return 1
    errors, notices = check(doc, require_compiler)
    for n in notices:
        if not errors:
            print(f"::notice title=Reproducibility::{n}")
        else:
            print(f"notice: {n}")
    for e in errors:
        print(f"::error title=Reproducibility::{e}")
    if errors:
        print("check-repro-report: FAILED", file=sys.stderr)
        return 1
    print("check-repro-report: ok")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
