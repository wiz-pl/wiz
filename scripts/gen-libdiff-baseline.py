#!/usr/bin/env python3
"""Generate or check Tests/libdiff-baseline.tsv, the libdiff ratchet (R4).

The classification in `wiz-notes/libdiff-classification.md` is the evidence (the
239-file sweep's per-file verdicts); `.github/libdiff-corpus.txt` is the corpus the
sweep walks today. This script intersects the two and writes one `file<TAB>verdict`
line per *classified* swept file, which `=selfhost-libdiff` reads: a file classified
`ok` may not become `diverging`, `rejected` or `bounded`. A corpus file newer than the
classification has no row; the sweep measures it and reports it as unclassified (only a
backward move is a regression), and a reviewer adds a row after reading the report.

The source is prose, so this is a generator, not a checker of the prose: review the
diff of `Tests/libdiff-baseline.tsv` when the classification or the corpus changes.

    scripts/gen-libdiff-baseline.py            # write Tests/libdiff-baseline.tsv
    scripts/gen-libdiff-baseline.py --check    # exit 1 when the file is stale
    scripts/gen-libdiff-baseline.py --print    # write to stdout
"""
from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CORPUS = ROOT / ".github" / "libdiff-corpus.txt"
NOTE = ROOT / "wiz-notes" / "libdiff-classification.md"
OUT = ROOT / "Tests" / "libdiff-baseline.tsv"

GROUPS = {"real selfhost bug", "host-only syntax", "expected divergence", "bounded", "ok"}
VERDICTS = ("ok", "rejected", "diverging", "bounded")
PATH_RE = re.compile(r"`((?:lib|scry|hdl)/[^`]+\.wiz)`")


def canon(path: str) -> str:
    """The corpus name of a classification row.

    The 169-row table and scripts/libdiff-causes.tsv predate two moves: they name
    `lib/Scry/X.wiz` while the corpus names `scry/src/Scry/X.wiz` (`859b28379`), and
    `lib/Hdl/X.wiz` while the Hdl package is `hdl/src/Hdl/X.wiz` (a pending root, not
    swept yet). Only the path changed (libdiff-classification.md, Caveats)."""
    if path.startswith("lib/Scry/"):
        return "scry/src/Scry/" + path[len("lib/Scry/"):]
    if path.startswith("lib/Hdl/"):
        return "hdl/src/Hdl/" + path[len("lib/Hdl/"):]
    return path


def corpus() -> list[str]:
    files: list[str] = []
    for line in CORPUS.read_text().splitlines():
        line = line.strip()
        if line and not line.startswith("#"):
            files.append(line)
    return files


def rows(text: str) -> list[list[str]]:
    out: list[list[str]] = []
    for line in text.splitlines():
        if not line.startswith("|"):
            continue
        cells = [c.strip() for c in line.strip().strip("|").split("|")]
        out.append(cells)
    return out


def classify() -> dict[str, str]:
    text = NOTE.read_text()
    verdicts: dict[str, str] = {}
    for cells in rows(text):
        if len(cells) < 2:
            continue
        m = PATH_RE.search(cells[0])
        if not m:
            continue
        path = canon(m.group(1))
        v = None
        if len(cells) >= 5 and cells[3] in GROUPS:
            # the 169-row table and the train10 additions: `file | cause | error | group | …`
            v = {"real selfhost bug": "diverging", "host-only syntax": "diverging",
                 "expected divergence": "diverging", "bounded": "bounded", "ok": "ok"}[cells[3]]
        elif len(cells) == 4 and (cells[1].startswith(("timeout", "crash")) or
                                  cells[2].startswith(("timeout", "crash"))):
            # the bounded/crash appendix: `file | host | self | note`
            v = "bounded"
        elif len(cells) == 3 and cells[1] in ("ok", "rejected"):
            # the both-reject and ok table: `file | verdict | first error`
            v = cells[1]
        if v is None:
            continue
        old = verdicts.get(path)
        if old is not None and old != v:
            # (a file can appear in the appendix and the gap table; the appendix is the
            # current verdict for a bound, so it wins only when it is not a gap)
            raise SystemExit(f"{path}: classified both {old} and {v}")
        verdicts[path] = v
    return verdicts


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--check", action="store_true", help="exit 1 when the checked-in file is stale")
    ap.add_argument("--print", dest="to_stdout", action="store_true")
    args = ap.parse_args(argv)

    files = corpus()
    verdicts = classify()
    missing = [f for f in files if f not in verdicts]
    if missing:
        # (the classification predates these files: the sweep measures them and reports
        # them as unclassified; a reviewer adds a row after reading the report)
        print(f"{NOTE}: {len(missing)} corpus file(s) are newer than the classification "
              f"(measured, not failed):", file=sys.stderr)
        for f in missing[:40]:
            print(f"  {f}", file=sys.stderr)
        if len(missing) > 40:
            print(f"  … and {len(missing) - 40} more", file=sys.stderr)
    stale = [f for f, v in verdicts.items() if f not in set(files)]
    pending = sorted(f for f in stale if f.startswith("hdl/src/"))
    unexpected = [f for f in stale if not f.startswith("hdl/src/") and not f.startswith("scry/src/")]
    if unexpected:
        print(f"{NOTE}: {len(unexpected)} classified file(s) are neither in the corpus nor a "
              f"pending root (ignored):", file=sys.stderr)
        for f in unexpected[:10]:
            print(f"  {f}", file=sys.stderr)

    lines = [
        "# Tests/libdiff-baseline.tsv: the =selfhost-libdiff ratchet (R4).",
        "# One `file<TAB>verdict` per file the checked-in classification covers; `verdict`",
        "# is ok, rejected, diverging or bounded. A file this file calls `ok` must stay",
        "# `ok`; the listed gaps may be fixed or reclassified. A corpus file newer than",
        "# the classification has no row: the sweep measures it and reports it as",
        "# unclassified. Generated from the checked-in classification by",
        "# scripts/gen-libdiff-baseline.py; review the diff before committing.",
        "#",
        "#   scripts/gen-libdiff-baseline.py            # rewrite this file",
        "#   scripts/gen-libdiff-baseline.py --check    # fail when it is stale",
        "#",
        "# The hdl/src rows below are the pending Hdl root's classification. The sweep",
        "# does not walk hdl/src yet (all 32 diverge; see .github/libdiff-corpus.txt), so",
        "# they have no records to compare: they are here to keep the 239-row work list",
        "# whole, and become gated when the root joins the corpus.",
    ]
    lines += [f"{f}\t{verdicts[f]}" for f in files if f in verdicts]
    lines += [f"{f}\t{verdicts[f]}" for f in pending]
    text = "\n".join(lines) + "\n"

    if args.to_stdout:
        sys.stdout.write(text)
        return 0
    if args.check:
        current = OUT.read_text() if OUT.exists() else ""
        if current != text:
            print(f"{OUT.relative_to(ROOT)} is stale; run scripts/gen-libdiff-baseline.py", file=sys.stderr)
            return 1
        print(f"{OUT.relative_to(ROOT)}: current ({len([l for l in text.splitlines() if l and not l.startswith(chr(35))])} rows)")
        return 0
    OUT.write_text(text)
    print(f"wrote {OUT.relative_to(ROOT)} ({len([l for l in text.splitlines() if l and not l.startswith(chr(35))])} rows)")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
