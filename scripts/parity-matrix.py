#!/usr/bin/env python3
"""Check the machine-readable self-host parity matrix (`selfhost-parity.tsv`).

The matrix in `wiz-notes/selfhost-parity.md` is a hand-written claim.  This script
makes the claim falsifiable:

* every row is a record in `selfhost-parity.tsv` (`row, area, status, evidence_case,
  note`);
* an **S** row must name at least one case that exists in a self-host group *and* runs
  the self-hosted binary (the compiler or the checker built from `selfhost/*.wiz`);
* a **P** row must say what is missing (`missing: …` in `note`);
* an **M** row must not name a positive case (a `!` prefix marks a case that asserts
  the gap, not support);
* every case of the self-host groups must appear in some row (no orphan tests);
* rows with no case at all must be listed in `scripts/parity-matrix-overrides.tsv`
  with a reason;
* the counts in the note's `## Counts` section must equal the TSV's.

The self-hosted-binary test is a call graph over the test sources: a case invokes the
toolchain when it (transitively) reaches `selfhostCompiler` or `selfhostChecker` in
`Tests/Elab.lean`.  That deliberately does **not** count a case that compiles
`selfhost/*.wiz` with the Lean host (`ioRun`): the whole point of the S column is that
the Wiz-hosted binary ran.

Usage:

    scripts/parity-matrix.py --check
    scripts/parity-matrix.py --check --note wiz-notes/selfhost-parity.md
    scripts/parity-matrix.py --write-note          # rewrite only `## Counts`
    scripts/parity-matrix.py --dump-cases          # the case index and invocation flag

The note is looked up in `$WIZ_PARITY_NOTE`, then `wiz-notes/selfhost-parity.md` under
this checkout, then the same path in the checkout's ancestors (the notes tree is often
a sibling).  If it is not found, `--check` says so and checks everything else; CI does
not have the notes tree.  `--check --require-note` makes a missing note an error.
"""

from __future__ import annotations

import argparse
import os
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DEFAULT_TSV = ROOT / "selfhost-parity.tsv"
DEFAULT_OVERRIDES = ROOT / "scripts" / "parity-matrix-overrides.tsv"

# The groups that make up the self-host test surface.  `=selfhost` is the current
# monolithic group (the split group has not landed on origin/master); the others are
# the differential/CLI groups it feeds.
GROUPS = [
    ("selfhost", "Tests/Groups/SelfHost.lean"),
    ("selfhost-macro", "Tests/Groups/SelfHostMacro.lean"),
    ("selfhost-cli", "Tests/Groups/SelfhostCli.lean"),
    ("selfhost-cli-diff", "Tests/Groups/SelfhostCliDiff.lean"),
    ("selfhost-libdiff", "Tests/Groups/SelfhostLibDiff.lean"),
    ("selfhost-parse-diff", "Tests/Groups/SelfHostParseDiff.lean"),
]

# The functions that build or run the Wiz-hosted binary.
BINARY_SEEDS = {"selfhostCompiler", "selfhostChecker"}

AREA_NAMES = {
    "A": "Frontend",
    "B": "Kernel",
    "C": "Backend/FFI",
    "D": "Runtime/CLI",
    "E": "Corpus",
}


# --------------------------------------------------------------------------- parsing

def strip_code(src: str) -> str:
    """Blank out comments, strings and character literals, keeping offsets.

    Case bodies are read from the result, so a `{` in a string or a comment must not
    affect brace/count logic, and a name in a comment must not look like a call.
    """
    out = list(src)
    i, n = 0, len(src)
    while i < n:
        c = src[i]
        if c == '"':
            j = i + 1
            while j < n:
                if src[j] == "\\":
                    j += 2
                    continue
                if src[j] == '"':
                    break
                j += 1
            for k in range(i + 1, min(j, n)):
                out[k] = " "
            i = j + 1
            continue
        if c == "'":
            j = i + 1
            if j < n and src[j] == "\\":
                j += 2
            else:
                j += 1
            if j < n and src[j] == "'":
                j += 1
            for k in range(i + 1, min(j, n)):
                out[k] = " "
            i = j
            continue
        if c == "-" and i + 1 < n and src[i + 1] == "-":
            j = src.find("\n", i)
            if j < 0:
                j = n
            for k in range(i, j):
                out[k] = " "
            i = j
            continue
        if c == "/" and i + 1 < n and src[i + 1] == "-":
            j, depth = i + 2, 1
            while j < n and depth:
                if src.startswith("/-", j):
                    depth += 1
                    j += 2
                elif src.startswith("-/", j):
                    depth -= 1
                    j += 2
                else:
                    j += 1
            for k in range(i, j):
                out[k] = " "
            i = j
            continue
        i += 1
    return "".join(out)


NAME_RE = re.compile(r'\{\s*name := "((?:[^"\\]|\\.)*)"')


def group_cases() -> list[dict]:
    """The cases of every self-host group, in source order."""
    cases: list[dict] = []
    for group, rel in GROUPS:
        path = ROOT / rel
        src = path.read_text(encoding="utf-8")
        stripped = strip_code(src)
        # A group case record has `run := fun`; nested `Decl` records do not.  This is
        # the same identification the audit used (`grep 'run := fun'`), but the record
        # start gives the name and the spans give the body.
        starts = [m.start() for m in re.finditer(r"run := fun", stripped)]
        for k, at in enumerate(starts):
            rec = stripped.rfind("{", 0, at)
            line_start = src.rfind("\n", 0, rec) + 1
            m = NAME_RE.match(src, max(rec, line_start))
            if not m:
                raise SystemExit(f"{rel}: a `run := fun` at offset {at} has no `name :=`")
            name = m.group(1)
            end = starts[k + 1] if k + 1 < len(starts) else len(stripped)
            # the next record's start (not `run := fun`), so the body does not include
            # the next case's prefix; `rfind` is cheap and the records are adjacent
            cases.append({
                "name": name,
                "group": group,
                "file": rel,
                "line": src.count("\n", 0, rec) + 1,
                "body": stripped[rec:end],
            })
    return cases


def top_level_defs() -> dict[str, str]:
    """Top-level `def`s of the group files and `Tests/Elab.lean`, by name."""
    defs: dict[str, list[str]] = {}
    paths = [rel for _, rel in GROUPS] + ["Tests/Elab.lean"]
    for rel in paths:
        path = ROOT / rel
        if not path.exists():
            continue
        src = strip_code(path.read_text(encoding="utf-8"))
        starts = list(re.finditer(
            r"^(?:partial\s+)?def\s+([A-Za-z_][A-Za-z0-9_'!?]*)", src, re.MULTILINE))
        for i, m in enumerate(starts):
            end = starts[i + 1].start() if i + 1 < len(starts) else len(src)
            defs.setdefault(m.group(1), []).append(src[m.start():end])
    return {k: "\n".join(v) for k, v in defs.items()}


IDENT_RE = re.compile(r"\b[A-Za-z_][A-Za-z0-9_'!?]*")


def invokes_selfhost(cases: list[dict]) -> set[str]:
    """The case names that (transitively) reach the self-hosted binary."""
    defs = top_level_defs()
    memo: dict[str, bool] = {}

    def reaches(name: str, stack: frozenset[str] = frozenset()) -> bool:
        if name in BINARY_SEEDS:
            return True
        if name in memo:
            return memo[name]
        if name in stack:
            return False
        body = defs.get(name)
        if body is None:
            return False
        here = stack | {name}
        found = False
        for ident in set(IDENT_RE.findall(body)):
            if ident in defs or ident in BINARY_SEEDS:
                if reaches(ident, here):
                    found = True
                    break
        memo[name] = found
        return found

    out = set()
    for c in cases:
        for ident in set(IDENT_RE.findall(c["body"])):
            if ident in defs or ident in BINARY_SEEDS:
                if reaches(ident):
                    out.add(c["name"])
                    break
    return out


# --------------------------------------------------------------------------- records

class BadTsv(Exception):
    pass


def read_tsv(path: Path) -> list[dict]:
    if not path.exists():
        raise BadTsv(f"{path}: no such file")
    lines = path.read_text(encoding="utf-8").splitlines()
    if not lines or lines[0].strip() != "row\tarea\tstatus\tevidence_case\tnote":
        raise BadTsv(f"{path}: header must be `row\\tarea\\tstatus\\tevidence_case\\tnote`")
    rows = []
    seen = set()
    for lineno, line in enumerate(lines[1:], 2):
        if not line.strip():
            continue
        parts = line.split("\t")
        if len(parts) != 5:
            raise BadTsv(f"{path}:{lineno}: expected 5 tab-separated fields, got {len(parts)}")
        row, area, status, evidence, note = parts
        if not re.fullmatch(r"[A-E][0-9]+", row):
            raise BadTsv(f"{path}:{lineno}: bad row id {row!r}")
        if row in seen:
            raise BadTsv(f"{path}:{lineno}: duplicate row {row}")
        seen.add(row)
        if area not in AREA_NAMES:
            raise BadTsv(f"{path}:{lineno}: area must be one of A/B/C/D/E, got {area!r}")
        if status not in ("S", "P", "M"):
            raise BadTsv(f"{path}:{lineno}: status must be S, P or M, got {status!r}")
        entries = [e.strip() for e in evidence.split(";;") if e.strip()]
        rows.append({"row": row, "area": area, "status": status,
                     "evidence": entries, "note": note, "line": lineno})
    return rows


def read_overrides(path: Path) -> dict[str, str]:
    if not path.exists():
        raise BadTsv(f"{path}: no such file")
    overrides: dict[str, str] = {}
    for lineno, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        parts = line.split("\t")
        if len(parts) != 2:
            raise BadTsv(f"{path}:{lineno}: expected `row<TAB>reason`")
        row, reason = parts
        if not reason.strip():
            raise BadTsv(f"{path}:{lineno}: empty reason for {row}")
        overrides[row] = reason.strip()
    return overrides


def find_note(explicit: str | None) -> Path | None:
    if explicit:
        p = Path(explicit)
        return p if p.exists() else None
    env = os.environ.get("WIZ_PARITY_NOTE")
    if env:
        p = Path(env)
        return p if p.exists() else None
    for base in [ROOT, *ROOT.parents]:
        p = base / "wiz-notes" / "selfhost-parity.md"
        if p.exists():
            return p
    return None


COUNT_HEAD_RE = re.compile(
    r"(\d+)\s+parity rows,.*?\*\*(\d+)\s+supported\*\*,\s*\*\*(\d+)\s+partial\*\*,\s*"
    r"\*\*(\d+)\s+missing\*\*", re.S)
AREA_RE = re.compile(
    r"^\*\s+(Frontend|Kernel|Backend/FFI|Runtime/CLI|Corpus)\s+\((\d+)\):\s*"
    r"(\d+)\s*S,\s*(\d+)\s*P,\s*(\d+)\s*M\.", re.MULTILINE)
TOTAL_RE = re.compile(
    r"^\*\s+Total:\s*(\d+)\s*S\s*\+\s*(\d+)\s*P\s*\+\s*(\d+)\s*M\s*=\s*(\d+)\.", re.MULTILINE)


def counts_of(rows: list[dict]) -> dict:
    total = {"S": 0, "P": 0, "M": 0}
    by_area: dict[str, dict[str, int]] = {a: {"num": 0, "S": 0, "P": 0, "M": 0} for a in AREA_NAMES}
    for r in rows:
        total[r["status"]] += 1
        by_area[r["area"]][r["status"]] += 1
        by_area[r["area"]]["num"] += 1
    return {"total": total, "by_area": by_area, "n": len(rows)}


def counts_section(counts: dict) -> str:
    t = counts["total"]
    out = [
        f"{counts['n']} parity rows, counts generated from `selfhost-parity.tsv` "
        f"(the TSV is the source; the case evidence is checked by "
        f"`scripts/parity-matrix.py`). **{t['S']} supported**, **{t['P']} partial**, "
        f"**{t['M']} missing**.",
        "",
    ]
    for area, name in AREA_NAMES.items():
        a = counts["by_area"][area]
        out.append(f"* {name} ({a['num']}): {a['S']} S, {a['P']} P, {a['M']} M.")
    out.append(f"* Total: {t['S']} S + {t['P']} P + {t['M']} M = {counts['n']}.")
    return "\n".join(out)


def check_note(note: Path, counts: dict, errors: list[str]) -> None:
    text = note.read_text(encoding="utf-8")
    m = re.search(r"^## Counts[ \t]*$", text, re.MULTILINE)
    if not m:
        errors.append(f"{note}: no `## Counts` section")
        return
    after = text[m.end():]
    nxt = re.search(r"^## ", after, re.MULTILINE)
    section = after[:nxt.start()] if nxt else after
    h = COUNT_HEAD_RE.search(section)
    if not h:
        errors.append(f"{note}: `## Counts` does not have the expected sentence")
        return
    got = (int(h.group(1)), int(h.group(2)), int(h.group(3)), int(h.group(4)))
    want = (counts["n"], counts["total"]["S"], counts["total"]["P"], counts["total"]["M"])
    if got != want:
        errors.append(f"{note}: counts say {got[0]} rows / {got[1]} S / {got[2]} P / "
                      f"{got[3]} M; the TSV says {want[0]} / {want[1]} / {want[2]} / {want[3]}")
    areas = {name: tuple(map(int, (num, s, p, mm))) for name, num, s, p, mm
             in AREA_RE.findall(section)}
    for area, name in AREA_NAMES.items():
        a = counts["by_area"][area]
        want = (a["num"], a["S"], a["P"], a["M"])
        if name not in areas:
            errors.append(f"{note}: no `* {name} (…): … S, … P, … M.` line")
        elif areas[name] != want:
            errors.append(f"{note}: {name} says {areas[name]} (rows/S/P/M); the TSV says {want}")
    tm = TOTAL_RE.search(section)
    if not tm:
        errors.append(f"{note}: no `* Total: … S + … P + … M = … .` line")
    else:
        got = tuple(map(int, tm.groups()))
        want = (counts["total"]["S"], counts["total"]["P"], counts["total"]["M"], counts["n"])
        if got != want:
            errors.append(f"{note}: total says {got}; the TSV says {want}")


# --------------------------------------------------------------------------- commands

def check(tsv: Path, overrides_path: Path, note_arg: str | None, require_note: bool) -> int:
    errors: list[str] = []
    try:
        rows = read_tsv(tsv)
        overrides = read_overrides(overrides_path)
    except BadTsv as e:
        print(f"parity-matrix: {e}", file=sys.stderr)
        return 1

    cases = group_cases()
    index = {c["name"]: c for c in cases}
    if len(index) != len(cases):
        errors.append("duplicate case names across the self-host groups")
    invokes = invokes_selfhost(cases)

    mapped: dict[str, list[str]] = {}
    for r in rows:
        positive_invoking = []
        for entry in r["evidence"]:
            negative = entry.startswith("!")
            name = entry[1:].strip() if negative else entry
            if name not in index:
                errors.append(f"{r['row']}: evidence case not found in the self-host groups: {name!r}")
                continue
            mapped.setdefault(name, []).append(r["row"])
            if not negative and name in invokes:
                positive_invoking.append(name)
        if r["status"] == "S":
            if not positive_invoking:
                detail = ", ".join(r["evidence"]) or "none"
                errors.append(
                    f"{r['row']}: S but no positive case runs the self-hosted binary "
                    f"(evidence: {detail}).  A case that compiles selfhost/*.wiz with the "
                    f"Lean host does not count.")
        elif r["status"] == "P":
            if not re.search(r"missing:\s*\S", r["note"]):
                errors.append(f"{r['row']}: P must name what is missing (`missing: …` in note)")
        elif r["status"] == "M":
            pos = [e for e in r["evidence"] if not e.startswith("!")]
            if pos:
                errors.append(f"{r['row']}: M but names positive case(s) {pos}; "
                              f"prefix a case that asserts the gap with `!`")

        if not r["evidence"]:
            if r["row"] not in overrides:
                errors.append(f"{r['row']}: no evidence case and no override reason "
                              f"(add it to {overrides_path.name})")
        elif r["row"] in overrides:
            errors.append(f"{r['row']}: has evidence but is also in the override list "
                          f"(remove the stale override)")

    for name in overrides:
        if name not in {r["row"] for r in rows}:
            errors.append(f"override for unknown row {name}")

    orphans = [n for n in index if n not in mapped]
    for name in orphans:
        errors.append(f"orphan case: {index[name]['group']} `{name}` maps to no row")

    counts = counts_of(rows)
    note = find_note(note_arg)
    if note is None:
        if require_note:
            errors.append("no wiz-notes/selfhost-parity.md found")
        else:
            print("parity-matrix: note not found; checked the TSV, evidence and cases only")
    else:
        check_note(note, counts, errors)
        print(f"parity-matrix: note {note}")

    if errors:
        print(f"parity-matrix: {len(errors)} failure(s) in {tsv.name}", file=sys.stderr)
        for e in errors:
            print(f"  - {e}", file=sys.stderr)
        return 1

    t = counts["total"]
    print(f"parity-matrix: {counts['n']} rows: {t['S']} S, {t['P']} P, {t['M']} M; "
          f"{len(cases)} cases in {len(GROUPS)} groups, all mapped; "
          f"{len(invokes)} cases run the self-hosted binary")
    return 0


def write_note(tsv: Path, note_arg: str | None) -> int:
    rows = read_tsv(tsv)
    counts = counts_of(rows)
    note = find_note(note_arg)
    if note is None:
        print("parity-matrix: no note found (set WIZ_PARITY_NOTE or --note)", file=sys.stderr)
        return 1
    text = note.read_text(encoding="utf-8")
    m = re.search(r"^## Counts[ \t]*$", text, re.MULTILINE)
    if not m:
        print(f"parity-matrix: {note}: no `## Counts` section", file=sys.stderr)
        return 1
    after = text[m.end():]
    nxt = re.search(r"^## ", after, re.MULTILINE)
    section = after[:nxt.start()] if nxt else after
    # keep the section's prose: everything after the generated `* Total:` line
    tail = ""
    total = re.search(r"^\* Total:.*$", section, re.MULTILINE)
    if total:
        tail = section[total.end():].strip("\n")
    body = counts_section(counts)
    if tail:
        body = body + "\n\n" + tail
    if nxt:
        new = text[:m.end()] + "\n\n" + body + "\n\n" + after[nxt.start():]
    else:
        new = text[:m.end()] + "\n\n" + body + "\n"
    note.write_text(new, encoding="utf-8")
    print(f"parity-matrix: wrote the counts section of {note}")
    return 0


def dump_cases() -> int:
    cases = group_cases()
    invokes = invokes_selfhost(cases)
    for c in cases:
        print(f"{c['group']}\t{c['file']}:{c['line']}\t{'selfhost' if c['name'] in invokes else 'host'}\t{c['name']}")
    print(f"# {len(cases)} cases, {len(invokes)} run the self-hosted binary", file=sys.stderr)
    return 0


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--check", action="store_true", help="validate the TSV and the note")
    ap.add_argument("--write-note", action="store_true", help="rewrite only the note's `## Counts`")
    ap.add_argument("--dump-cases", action="store_true", help="print the case index")
    ap.add_argument("--tsv", default=str(DEFAULT_TSV))
    ap.add_argument("--overrides", default=str(DEFAULT_OVERRIDES))
    ap.add_argument("--note", default=None)
    ap.add_argument("--require-note", action="store_true",
                    help="fail when the notes tree is not present")
    args = ap.parse_args(argv)
    if args.write_note:
        return write_note(Path(args.tsv), args.note)
    if args.dump_cases:
        return dump_cases()
    if args.check:
        return check(Path(args.tsv), Path(args.overrides), args.note, args.require_note)
    ap.print_help()
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
