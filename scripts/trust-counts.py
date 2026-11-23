#!/usr/bin/env python3
"""The trust ledger's counts, computed from the ledger itself.

The documents that quote the ledger's size (`docs/trust-ledger.md`, `CHANGELOG.md`)
carry a machine-readable marker instead of hand-typed numbers:

  <!-- trust-counts: rows=822 partial=232 ... -->

`--write` replaces every marker with the counts of `.github/trust-baseline.tsv`;
`--check` fails when a marker disagrees with the file (or is missing). The counts are
derived from the TSV only: `rows` is the number of non-comment rows, `pure_axioms` is
`axiom_rows - extern_declarations` (each `extern` has one `axiom` row), `repr` is a
`native` row whose item names a `mk/get` pair (a `/` in the right-hand side), and
`other_builtin` is `builtin_rows - extern_declarations - seal`.

The separate review record for the Scry package (`scry/trust-baseline.tsv`) uses its
own marker, `trust-counts-scry`.

Usage:
  scripts/trust-counts.py --print          print the markers
  scripts/trust-counts.py --check          fail if a marker disagrees with the ledger
  scripts/trust-counts.py --write          replace the markers in place
Exit status: 0 clean, 1 disagreement, 2 usage error.
"""

from __future__ import annotations

import argparse
import datetime
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LIB = ROOT / ".github/trust-baseline.tsv"
SCRY = ROOT / "scry/trust-baseline.tsv"
DOCS = [ROOT / "docs/trust-ledger.md", ROOT / "CHANGELOG.md"]
MARKER = re.compile(r"<!-- (trust-counts(?:-scry)?): (.*?) -->")


def read_rows(path: Path) -> list[list[str]]:
    rows: list[list[str]] = []
    for line in path.read_text().split("\n"):
        if not line or line.startswith("#"):
            continue
        fields = line.split("\t")
        if len(fields) >= 3:
            rows.append(fields)
    return rows


def counts(path: Path, today: str) -> dict[str, int]:
    rows = read_rows(path)
    partial = axiom = builtin = native = extern = seal = repr_rows = 0
    legacy = expired = 0
    reasons: set[str] = set()
    for f in rows:
        module, _name, item = f[0], f[1], f[2]
        reason, owner, review = (f[3], f[4], f[5]) if len(f) >= 6 else ("", "", "")
        reasons.add(reason)
        if reason.startswith("legacy:") or owner == "unassigned":
            legacy += 1
        if review and review < today:
            expired += 1
        if item == "partial":
            partial += 1
        elif item.startswith("axiom "):
            axiom += 1
        elif item.startswith("builtin "):
            builtin += 1
            if item.startswith("builtin extern:"):
                extern += 1
            elif item.startswith("builtin seal:"):
                seal += 1
        elif item.startswith("native "):
            native += 1
            if "/" in item.split(" := ", 1)[-1]:
                repr_rows += 1
    return {
        "rows": len(rows),
        "partial": partial,
        "axiom_rows": axiom,
        "builtin_rows": builtin,
        "native_rows": native,
        "implemented_by": native - repr_rows,
        "repr": repr_rows,
        "extern_declarations": extern,
        "seal": seal,
        "other_builtin": builtin - extern - seal,
        "pure_axioms": axiom - extern,
        "distinct_reasons": len(reasons),
        "shared_reasons": len(rows) - len(reasons),
        "legacy": legacy,
        "expired": expired,
    }


def marker(kind: str, c: dict[str, int]) -> str:
    body = " ".join(f"{k}={v}" for k, v in c.items())
    return f"<!-- {kind}: {body} -->"


def main() -> int:
    ap = argparse.ArgumentParser(add_help=True)
    ap.add_argument("--print", action="store_true", dest="print_")
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--write", action="store_true")
    a = ap.parse_args()
    if sum([a.print_, a.check, a.write]) != 1:
        ap.error("choose exactly one of --print, --check, --write")
    today = datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%d")
    lib = marker("trust-counts", counts(LIB, today))
    scry = marker("trust-counts-scry", counts(SCRY, today))
    if a.print_:
        print(lib)
        print(scry)
        return 0
    failures: list[str] = []
    seen_lib = seen_scry = 0
    for path in DOCS:
        text = path.read_text()
        found = MARKER.findall(text)
        mine = [(k, v) for k, v in found if k == "trust-counts"]
        if not mine:
            failures.append(f"{path.relative_to(ROOT)}: no <!-- trust-counts: ... --> marker")
        for _kind, body in mine:
            seen_lib += 1
            if body != lib[len("<!-- trust-counts: ") : -len(" -->")]:
                failures.append(f"{path.relative_to(ROOT)}: marker says {body!r}")
                failures.append(f"  the ledger gives {lib}")
        if a.write and mine:
            text = MARKER.sub(lambda m: lib if m.group(1) == "trust-counts" else m.group(0), text)
            path.write_text(text)
    text = SCRY.read_text()
    mine = [(k, v) for k, v in MARKER.findall(text) if k == "trust-counts-scry"]
    if not mine:
        failures.append(f"{SCRY.relative_to(ROOT)}: no <!-- trust-counts-scry: ... --> marker")
    for _kind, body in mine:
        seen_scry += 1
        if body != scry[len("<!-- trust-counts-scry: ") : -len(" -->")]:
            failures.append(f"{SCRY.relative_to(ROOT)}: marker says {body!r}")
    if a.write and mine:
        text = MARKER.sub(lambda m: scry if m.group(1) == "trust-counts-scry" else m.group(0), text)
        SCRY.write_text(text)
    if a.write:
        print(f"wrote markers: {lib}")
        print(scry)
        return 0
    if failures:
        for f in failures:
            print(f"trust-counts: {f}", file=sys.stderr)
        print(f"trust-counts: {lib}", file=sys.stderr)
        return 1
    print(f"trust-counts: OK ({seen_lib} lib marker(s), {seen_scry} scry marker(s))")
    return 0


if __name__ == "__main__":
    sys.exit(main())
