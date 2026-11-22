#!/usr/bin/env python3
"""Fail when a generated companion list no longer describes its source of truth.

Seven failures in one day had the same shape: a commit added or removed a file
or a declaration but not the list generated from it.  The lists are cheap to
regenerate and expensive to notice late (the broken row is usually in a
different file, so review does not pair the two changes):

  * `scry/src/Scry/CsNull.wiz` without `.github/libdiff-corpus.txt`;
  * 72 declarations without a `legacy-names.tsv` row;
  * a regenerated `legacy-names.tsv` without `Wiz/LegacyNames.lean`'s digest;
  * a removed `deriveInhabited` with a stale
    `.github/name-collisions-baseline.json` entry;
  * a trust source without a ledger row (covered by the `trust_ledger` job,
    which needs the compiler);
  * a scry golden without its `.expected` (covered by the scry tests);
  * `test-shards.json` not covering every case exactly once (the
    `scripts/ci.py check-shards` check, which needs the test binary).

This script is the early, no-build gate for the three lists that have a cheap
check already:

  libdiff corpus  `scripts/check-libdiff-corpus.sh --quiet` walks lib/ and
                  scry/; its failure text is turned into one line per file.
  legacy names    `scripts/check-names.py --quiet` compares every declaration
                  with `legacy-names.tsv` and checks `Wiz/LegacyNames.lean`'s
                  digest.  It is the same check the `docs_style` job runs
                  later; this script only rewrites its summary into the
                  companion-drift shape so the cause is obvious.
  name collisions `scripts/check-name-collisions.py --quiet` reports a
                  baseline entry whose group is gone (or has expired).

The test-shard total needs `.lake/build/bin/tests`; `docs_style` has no build,
so it is skipped here.  The build job runs `scripts/ci.py check-shards` on the
real driver, and the `trust_ledger` and scry test jobs own their companions.

Usage
  scripts/check-companion-lists.py             check this checkout
  scripts/check-companion-lists.py --self-test run the parsers on fixtures
  scripts/check-companion-lists.py --quiet     print only drift and the summary
  scripts/check-companion-lists.py -v          also say which lists passed

Exit status: 0 clean, 1 drift, 2 usage or a check that could not run.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CORPUS = ".github/libdiff-corpus.txt"
OLD_NAMES = "legacy-names.tsv"
LEGACY_MODULE = "Wiz/LegacyNames.lean"
COLLISIONS = ".github/name-collisions-baseline.json"
TEST_DRIVER = ".lake/build/bin/tests"


def run(*command: str) -> subprocess.CompletedProcess[str]:
    try:
        return subprocess.run(
            command, cwd=ROOT, capture_output=True, text=True, timeout=120
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise SystemExit(f"check-companion-lists: cannot run {' '.join(command)}: {exc}")


def parse_corpus(output: str) -> list[str]:
    """One `companion drift` line per corpus problem in the shell check's text."""
    drift: list[str] = []
    mode = ""
    for line in output.splitlines():
        if "(corpus entry missing):" in line:
            mode = "missing"
            continue
        if "(covered file absent):" in line:
            mode = "absent"
            continue
        if line.startswith("  ") and not line.startswith("  …"):
            path = line.strip()
            if not path:
                continue
            if mode == "missing":
                drift.append(
                    f"companion drift: lib/ + scry/ gained {path}; "
                    f"{CORPUS} does not list it"
                )
            elif mode == "absent":
                drift.append(
                    f"companion drift: {CORPUS} lists {path}, which is not on disk"
                )
            continue
        if not line.startswith(" "):
            mode = ""
    if not drift:
        drift.append(
            f"companion drift: {CORPUS} does not match the walk over lib/ and "
            "scry/; run scripts/check-libdiff-corpus.sh"
        )
    return drift


def parse_legacy(stdout: str, stderr: str) -> list[str]:
    """Companion lines for the row and digest problems `check-names` reports."""
    drift: list[str] = []
    missing = re.search(r",\s*(\d+)\s+without a row", stdout)
    stale = re.search(r"baseline:\s*(\d+)\s+stale row", stderr)
    digest = re.search(
        rf"{re.escape(LEGACY_MODULE)} records ([0-9a-f]+|\(empty\)), but "
        r"legacy-names\.tsv is ([0-9a-f]+);",
        stderr,
    )
    if missing and int(missing.group(1)):
        drift.append(
            f"companion drift: {OLD_NAMES} rows do not match the declarations "
            f"({missing.group(1)} missing); run scripts/gen-legacy-names.py"
        )
    if stale and int(stale.group(1)):
        drift.append(
            f"companion drift: {OLD_NAMES} has {stale.group(1)} stale row(s); "
            "run scripts/gen-legacy-names.py"
        )
    if digest:
        drift.append(
            f"companion drift: {LEGACY_MODULE} digest {digest.group(1)} != "
            f"{OLD_NAMES} {digest.group(2)}; run "
            "scripts/gen-legacy-names.py --update-digest"
        )
    if not drift:
        drift.append(
            f"companion drift: {OLD_NAMES} does not match the declarations; run "
            "scripts/check-names.py --quiet"
        )
    return drift


def parse_collisions(output: str) -> list[str]:
    """Companion lines for stale and expired baseline entries."""
    drift: list[str] = []
    for line in output.splitlines():
        stale = re.match(
            r"\s+'(?P<name>[^']+)' \[(?P<modules>[^\]]*)\] matches no collision "
            r"group",
            line,
        )
        if stale:
            drift.append(
                f"companion drift: {COLLISIONS} entry '{stale.group('name')}' "
                f"[{stale.group('modules')}] matches no collision group; remove "
                "the entry"
            )
            continue
        expired = re.search(
            r"entry (\d+): '([^']+)' expired on (\d{4}-\d\d-\d\d)", line
        )
        if expired:
            drift.append(
                f"companion drift: {COLLISIONS} entry {expired.group(1)} "
                f"'{expired.group(2)}' expired on {expired.group(3)}; remove or "
                "renew the entry"
            )
    if not drift:
        drift.append(
            f"companion drift: {COLLISIONS} has a stale or expired entry; run "
            "scripts/check-name-collisions.py --quiet"
        )
    return drift


def check_corpus() -> list[str]:
    proc = run("bash", "scripts/check-libdiff-corpus.sh", "--quiet")
    return [] if proc.returncode == 0 else parse_corpus(proc.stdout + proc.stderr)


def check_legacy() -> list[str]:
    proc = run("python3", "scripts/check-names.py", "--quiet")
    return [] if proc.returncode == 0 else parse_legacy(proc.stdout, proc.stderr)


def check_collisions() -> list[str]:
    proc = run("python3", "scripts/check-name-collisions.py", "--quiet")
    return [] if proc.returncode == 0 else parse_collisions(proc.stdout + proc.stderr)


def self_test() -> int:
    failures: list[str] = []

    def expect(name: str, lines: list[str], needles: tuple[str, ...]) -> None:
        joined = "\n".join(lines)
        for needle in needles:
            if needle not in joined:
                failures.append(f"{name}: {needle!r} not in {joined!r}")

    expect(
        "corpus missing",
        parse_corpus(
            "libdiff corpus: 1 file(s) under lib/ and scry/ are not listed "
            "(corpus entry missing):\n  scry/src/Scry/CsNull.wiz\n"
        ),
        ("scry/src/Scry/CsNull.wiz", CORPUS, "does not list it"),
    )
    expect(
        "corpus absent",
        parse_corpus(
            "libdiff corpus: 1 listed file(s) are not on disk (covered file "
            "absent):\n  lib/Gone.wiz\n"
        ),
        ("lib/Gone.wiz", "not on disk"),
    )
    expect(
        "legacy rows",
        parse_legacy(
            "check-names: 1 file(s), 1 declaration(s), 1 baseline row(s), "
            "0 outside the prefix (0 unbaselined), 72 without a row\n",
            "",
        ),
        ("(72 missing)", "gen-legacy-names.py"),
    )
    expect(
        "legacy digest",
        parse_legacy(
            "check-names: 1 file(s), 1 declaration(s), 1 baseline row(s), "
            "0 outside the prefix (0 unbaselined), 0 without a row\n",
            f"cache digest: {LEGACY_MODULE} records 1111, but legacy-names.tsv "
            "is 2222; run scripts/gen-legacy-names.py --update-digest\n",
        ),
        (f"{LEGACY_MODULE} digest 1111 != {OLD_NAMES} 2222", "--update-digest"),
    )
    expect(
        "collisions stale",
        parse_collisions(
            "baseline: 1 stale entry:\n  'deriveInhabited' [lib/Derive.wiz] "
            "matches no collision group; remove the entry (or restore the group)\n"
        ),
        ("'deriveInhabited'", COLLISIONS, "remove the entry"),
    )
    expect(
        "collisions expired",
        parse_collisions(
            f"check-name-collisions: {COLLISIONS}: entry 3: 'Foo.bar' expired on "
            "2026-01-01\n"
        ),
        ("entry 3", "'Foo.bar'", "expired on 2026-01-01"),
    )
    if failures:
        for failure in failures:
            print(f"self-test FAIL: {failure}", file=sys.stderr)
        return 1
    print("check-companion-lists self-test: ok (6 parser fixtures)")
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Check the generated companion lists against their sources."
    )
    parser.add_argument("--self-test", action="store_true",
                        help="run the message parsers on fixtures")
    parser.add_argument("--quiet", action="store_true",
                        help="print only drift and the summary")
    parser.add_argument("-v", "--verbose", action="store_true",
                        help="name every list that passed")
    args = parser.parse_args(argv)

    if args.self_test:
        return self_test()

    checks = (
        (CORPUS, check_corpus),
        (f"{OLD_NAMES} + {LEGACY_MODULE}", check_legacy),
        (COLLISIONS, check_collisions),
    )
    drift: list[str] = []
    failed = 0
    for name, check in checks:
        try:
            problems = check()
        except SystemExit as exc:
            print(str(exc), file=sys.stderr)
            return 2
        if problems:
            failed += 1
            drift.extend(problems)
            if not args.quiet:
                print(f"companion list drifted: {name}", file=sys.stderr)
        elif args.verbose:
            print(f"companion list current: {name}")

    for line in drift:
        print(line)
    skipped = ""
    if not (ROOT / TEST_DRIVER).is_file():
        skipped = f"; skipped test-shards (no {TEST_DRIVER})"
    if drift:
        print(
            f"check-companion-lists: FAIL ({len(drift)} problem(s) in "
            f"{failed} list(s){skipped})",
            file=sys.stderr,
        )
        return 1
    print(
        f"check-companion-lists: clean ({len(checks)} companion list(s){skipped})"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
