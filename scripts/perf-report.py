#!/usr/bin/env python3
"""Measure the workloads whose complexity a regression is visible on, and print a table.

    python3 scripts/perf-report.py                    # the table, on stdout
    python3 scripts/perf-report.py --check            # ... and exit 1 if a gate fails
    python3 scripts/perf-report.py --out docs/perf.md # regenerate the page
    python3 scripts/perf-report.py --json bench-out/perf.json --markdown "$GITHUB_STEP_SUMMARY"

The six workloads are fixed:

* `cx-structure`, `cx-inductive`, `cx-match` — the three size sweeps of
  `reviews/2026-11-18-complexity-patterns.md` §A.1 (structure fields, inductive
  constructors, match columns).  Each is measured at `n` and `2n`, best of three,
  with the start-up floor (a one-definition file) subtracted; the ratio
  `t(2n)/t(n)` is the number.  These are the loop that review measured; the
  inputs are generated from `n` by the generators below, never checked in.
* `scry-scale` — `scry taint` on the vendored 3.9 MB tree-sitter-c `parser.c`,
  the largest real C input in the tree (`scry/tests/scale.wiz`).
* `wiz-doc` — `wiz doc` on one library module.
* `trust-ledger` — `scripts/trust-ledger.sh --lib-only`, the `native` group's
  ledger walk over `lib/`.

A ratio workload has two numbers: the *target* rule (3× per doubling is linear;
6× is `n log n`) and a *gate* ceiling.  A row is red when the ratio is over the
target, honestly: the three cx workloads were measured superlinear on
2026-11-18 and the page says so.  The gate is a ratchet on the measured shape,
so the nightly fails when one of them gets *worse* (and when a one-size
workload exceeds its budget) rather than failing every night on a known bug.

The floor is measured in the same run and subtracted from both sizes, the way
`Tests.checkScaling` (`Tests/Harness.lean`, agent/cx-guard `002b909b`) does it:
a ~1 s process start otherwise hides a 2× ratio at small `n`.

The toolchain is not built here.  Point `--wiz`, `--grail` and `--tests` at a
build of this revision (the nightly workflow uses the Nix store paths; a local
checkout can use `.lake/build/bin/`).  The `--check` exit status is 0 when every
gate passes, 1 when one fails, 2 on a missing tool or a command error.
"""
from __future__ import annotations

import argparse
import datetime as dt
import json
import os
import platform
import shutil
import subprocess
import sys
import tempfile
import time
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# --------------------------------------------------------------------------- inputs
#
# The generators are the ones the review used (2026-11-18-complexity-patterns.md
# §A.1: gen_struct.py, gen_ind.py, gen_match.py).  They are reproduced here
# because a performance report must generate its own inputs from n rather than
# carry a stale copy of a 27 KiB source file; the structure shape is also
# `Tests.Scaling.wideStructure` (Tests/Scaling.lean:80) without its two uses.
# `wiz check --no-cache` is the measured command in all three.

def cx_structure(n: int) -> str:
    """`structure S where f0 … f{n-1} : Nat` — the wide-structure sweep (cx-01)."""
    return "import Prelude\nstructure S where\n" + "".join(f"  f{i} : Nat\n" for i in range(n))


def cx_inductive(n: int) -> str:
    """`inductive T where | c0 … | c{n-1}` — the constructor sweep (cx-02).

    Every generator imports the Prelude so that the one floor probe (the same
    file with one definition) is the right floor for all three."""
    return ("import Prelude\ninductive T where\n"
            + "".join(f"  | c{i}\n" for i in range(n)))


def cx_match(n: int) -> str:
    """A `match` with `n` columns and two rows — the column sweep (cx-03).

    The two rows differ in the first column only, so the clause set does not
    grow on its own: the only dimension is the column count."""
    params = " ".join(f"(a{i} : Nat)" for i in range(n))
    scrutinee = ", ".join(f"a{i}" for i in range(n))
    zeros = ", ".join("0" for _ in range(n))
    wilds = ", ".join("_" for _ in range(n))
    return (f"import Prelude\ndef f {params} : Nat := match {scrutinee} with\n"
            f"  | {zeros} => 0\n"
            f"  | {wilds} => 1\n")


TRIVIAL = "import Prelude\ndef x : Nat := 0\n"     # the floor probe: start-up, no work


@dataclass
class RatioWorkload:
    id: str
    title: str
    measures: str
    generator: object
    n: int
    target: int          # the complexity claim: 3 = linear, 6 = n log n
    ceiling: float       # the gate: fail above this measured ratio (a ratchet)
    source: str = ""     # where the generator comes from
    runs: int = 3
    timeout: int = 900


@dataclass
class SingleWorkload:
    id: str
    title: str
    measures: str
    command: list            # a command template, filled with {wiz}/{grail}/{tests}
    budget_s: float
    runs: int = 2
    timeout: int = 600
    skip_if_missing: str = ""


RATIO_WORKLOADS = [
    RatioWorkload(
        "cx-structure", "cx-01 wide structure",
        "`wiz check --no-cache` of a structure with n fields (the projection "
        "methods `classMethods` builds per field).",
        cx_structure, 500, 3, 12.0,
        source="the `wideStructure` shape of `Tests/Scaling.lean` (without its two uses)"),
    RatioWorkload(
        "cx-inductive", "cx-02 many-constructor inductive",
        "`wiz check --no-cache` of an inductive with n nullary constructors "
        "(the per-constructor name scan and four list appends in `elabInductive`).",
        cx_inductive, 250, 3, 12.0,
        source="the `gen_ind.py` template of the 2026-11-18 complexity review"),
    RatioWorkload(
        "cx-match", "cx-03 many-column match",
        "`wiz check --no-cache` of a two-row `match` with n columns "
        "(`compileMatch`'s column re-splicing and clause copying).",
        cx_match, 100, 3, 30.0,
        source="the `gen_match.py` template of the 2026-11-18 complexity review"),
]

SINGLE_WORKLOADS = [
    SingleWorkload(
        "scry-scale", "scry scale",
        "`scry taint` on the vendored tree-sitter-c `parser.c` (3.9 MB, 1.1 M CST "
        "nodes): parse, lower, points-to and taint.  The product's own default "
        "limit is 300 s (`scry/tests/scale.wiz` asserts it).",
        ["{scry}", "taint", "native/tree-sitter-c/src/parser.c", "--allow-errors", "--json"],
        budget_s=300, runs=1, timeout=600,
        skip_if_missing="scry/native/tree-sitter-c/src/parser.c"),
    SingleWorkload(
        "wiz-doc", "wiz doc on one module",
        "`wiz doc lib/Text.wiz -o DIR`: elaborate one module and render its pages.  "
        "A guard for documentation generation, not a complexity claim.",
        ["{wiz}", "doc", "lib/Text.wiz", "-o", "{doc_out}"],
        budget_s=120, runs=2, timeout=300),
    SingleWorkload(
        "trust-ledger", "trust-ledger --lib-only",
        "`scripts/trust-ledger.sh --lib-only`: `#print axioms` over every "
        "declaration of `lib/`, the walk the `native` test group runs.",
        ["{ledger}"],
        budget_s=900, runs=1, timeout=900),
]


# --------------------------------------------------------------------------- tools

def find_tool(explicit: str | None, names: list[str], env: str) -> str:
    candidates = []
    if explicit:
        candidates.append(explicit)
    if os.environ.get(env):
        candidates.append(os.environ[env])
    candidates += names
    for c in candidates:
        p = Path(c)
        if p.is_absolute() or os.sep in c:
            if p.is_file() and os.access(p, os.X_OK):
                return str(p)
        else:
            found = shutil.which(c)
            if found:
                return found
    raise SystemExit(f"perf-report: no executable for {env} (tried {', '.join(candidates)})")


def git_sha() -> str:
    try:
        return subprocess.run(["git", "-C", str(ROOT), "rev-parse", "HEAD"],
                              capture_output=True, text=True, check=True).stdout.strip()
    except (OSError, subprocess.CalledProcessError):
        return ""


def run_timed(cmd: list[str], cwd: Path, timeout: int) -> tuple[float, str, int]:
    """One run: (milliseconds, stdout+stderr, exit code).  Raises on a timeout."""
    t0 = time.monotonic()
    try:
        p = subprocess.run(cmd, cwd=str(cwd), capture_output=True, text=True,
                           timeout=timeout)
    except subprocess.TimeoutExpired:
        raise SystemExit(f"perf-report: timed out after {timeout} s: {' '.join(cmd)}")
    ms = (time.monotonic() - t0) * 1000.0
    out = (p.stdout or "") + (p.stderr or "")
    if p.returncode != 0:
        raise SystemExit(f"perf-report: exit {p.returncode}: {' '.join(cmd)}\n{out[-2000:]}")
    return ms, out, p.returncode


def best_ms(cmd: list[str], cwd: Path, runs: int, timeout: int) -> float:
    best = None
    for _ in range(max(1, runs)):
        ms, _, _ = run_timed(cmd, cwd, timeout)
        best = ms if best is None else min(best, ms)
    return best


# --------------------------------------------------------------------------- measure

def measure_ratio(w: RatioWorkload, wiz: str, tmp: Path, floor: float,
                  verbose: bool) -> dict:
    a = tmp / f"{w.id}-{w.n}.wiz"
    b = tmp / f"{w.id}-{2 * w.n}.wiz"
    a.write_text(w.generator(w.n))
    b.write_text(w.generator(2 * w.n))
    base = [wiz, "check", "--no-cache"]
    t1 = best_ms(base + [str(a)], ROOT, w.runs, w.timeout)
    t2 = best_ms(base + [str(b)], ROOT, w.runs, w.timeout)
    net1 = max(1.0, t1 - floor)
    net2 = max(1.0, t2 - floor)
    ratio = net2 / net1
    verdict = "red" if ratio > w.target else "green"
    gate_fail = ratio > w.ceiling
    if verbose:
        print(f"  {w.id}: {w.n} → {2*w.n}  net {net1:.0f} → {net2:.0f} ms "
              f"(raw {t1:.0f} → {t2:.0f}, floor {floor:.0f})  {ratio:.1f}×",
              file=sys.stderr)
    return dict(id=w.id, kind="ratio", title=w.title, measures=w.measures,
                source=w.source,
                unit=f"fields" if w.id == "cx-structure" else
                     ("constructors" if w.id == "cx-inductive" else "columns"),
                n=w.n, n2=2 * w.n, t_n_ms=round(net1), t_2n_ms=round(net2),
                raw_n_ms=round(t1), raw_2n_ms=round(t2),
                ratio=round(ratio, 2), target=w.target, ceiling=w.ceiling,
                budget_s=None, verdict=verdict, gate_fail=gate_fail)


def skipped_single(w: SingleWorkload, why: str, verbose: bool) -> dict:
    if verbose:
        print(f"  {w.id}: skipped ({why})", file=sys.stderr)
    return dict(id=w.id, kind="single", title=w.title, measures=w.measures,
                unit="—", n=None, n2=None, t_n_ms=None, t_2n_ms=None,
                ratio=None, target=None, ceiling=None, budget_s=w.budget_s,
                verdict="skipped", gate_fail=False, note=f"skipped: {why}")


def measure_single(w: SingleWorkload, tools: dict, tmp: Path, verbose: bool) -> dict:
    if w.skip_if_missing and not (ROOT / w.skip_if_missing).exists():
        return skipped_single(w, f"no {w.skip_if_missing}", verbose)
    ledger = ROOT / "scripts" / "trust-ledger.sh"
    best = None
    for i in range(max(1, w.runs)):
        # A fresh output directory per repetition: `wiz doc` refuses to reuse one,
        # and a rep must do the same work as the first.
        doc_out = tmp / f"doc-{w.id}-{i}"
        fills = dict(wiz=tools["wiz"], grail=tools["grail"], tests=tools["tests"],
                     scry=tools["scry"], doc_out=str(doc_out), ledger=str(ledger))
        cmd = [c.format(**fills) for c in w.command]
        cwd = ROOT / "scry" if w.id == "scry-scale" else ROOT
        ms, _, _ = run_timed(cmd, cwd, w.timeout)
        best = ms if best is None else min(best, ms)
    secs = best / 1000.0
    gate_fail = secs > w.budget_s
    if verbose:
        print(f"  {w.id}: {secs:.1f} s (budget {w.budget_s:.0f} s)", file=sys.stderr)
    return dict(id=w.id, kind="single", title=w.title, measures=w.measures,
                unit="—", n=None, n2=None, t_n_ms=round(best), t_2n_ms=None,
                raw_n_ms=round(best), raw_2n_ms=None, ratio=None, target=None,
                ceiling=None, budget_s=w.budget_s,
                verdict="red" if gate_fail else "green", gate_fail=gate_fail)


# --------------------------------------------------------------------------- markdown

def fmt_ms(ms: float | None) -> str:
    if ms is None:
        return "—"
    return f"{ms / 1000:.2f} s"


def summary_rows(rows: list[dict]) -> list[list[str]]:
    out = []
    for r in rows:
        if r["kind"] == "ratio":
            out.append([
                f"`{r['id']}`", f"{r['n']} → {r['n2']} {r['unit']}",
                fmt_ms(r["t_n_ms"]), fmt_ms(r["t_2n_ms"]), f"{r['ratio']:.1f}×",
                f"≤ {r['target']}×", f"≤ {r['ceiling']:g}×",
                r["verdict"], r["measured"],
            ])
        else:
            out.append([
                f"`{r['id']}`", "one size",
                fmt_ms(r["t_n_ms"]), "—", "—",
                f"≤ {r['budget_s']:.0f} s", f"≤ {r['budget_s']:.0f} s",
                r["verdict"], r["measured"],
            ])
    return out


def markdown_table(rows: list[dict], with_measured: bool = True) -> str:
    head = ["workload", "size", "t(n)", "t(2n)", "ratio", "rule", "gate", "status"]
    if with_measured:
        head.append("measured")
    lines = ["| " + " | ".join(head) + " |",
             "|" + "|".join("---" for _ in head) + "|"]
    for row in summary_rows(rows):
        if not with_measured:
            row = row[:-1]
        lines.append("| " + " | ".join(row) + " |")
    return "\n".join(lines)


PAGE_INTRO = """\
# Performance

This page is generated by `scripts/perf-report.py`; do not edit it by hand.  It
measures the six workloads a complexity regression is visible on, and each row
carries the date it was measured.  The numbers come from one run on one machine:
read the ratio, not the absolute time.  A newer report is printed by the nightly
`perf` workflow (`.github/workflows/perf.yml`); this checked-in copy is a
snapshot, so a number without a recent date is history, not a claim about today.

## How to read it

* A **ratio** row is measured at `n` and `2n`, best of three, with the
  start-up floor (a one-definition file, measured in the same run) subtracted
  from both: `ratio = t(2n) / t(n)`.  This is `Tests.checkScaling`
  (`Tests/Harness.lean`) with the same best-of-three and floor subtraction.
* **rule** is the complexity claim.  A claim of linear is 3× per doubling
  (`n log n` is 6×, quadratic is 10×).  A row whose ratio is over its rule is
  **red**: it is a known superlinear path, shown rather than excluded.
* **gate** is the ratchet the nightly enforces.  It is above today's measured
  ratio for a workload that is already red, so the nightly fails when it gets
  worse, not every night on a known bug.
* A **one-size** row has an absolute budget because it has no second size: it
  is a hang guard, not evidence of complexity, and it is gated at that budget.
  The `scry scale` budget is the product's own default 300 s limit; the other
  two are deliberately loose guards (an absolute time moves with the machine).

"""

PAGE_RULES = """\
## The rules, written down

* `cx-structure`: **≤ 3× per doubling** (500 → 1000 fields).  The loop is
  `classMethods` building a projection per earlier field and appending each
  method with `++` (`Wiz/Elab/Command.lean`); the kernel then checks one
  n-sized declaration per field.  Measured superlinear on 2026-11-18 and gated
  as such.
* `cx-inductive`: **≤ 3× per doubling** (250 → 500 constructors).
  `elabInductive` scans the constructor names so far and appends to four lists
  (`Wiz/Elab/Inductive.lean`); the recursor declarations then dominate.
* `cx-match`: **≤ 3× per doubling** (100 → 200 columns).  `compileMatch`
  re-splices the column list with `take`/`drop` and copies the clause rows into
  every branch (`Wiz/Elab/Term.lean`).
* `scry-scale`: **≤ 300 s** for the 3.9 MB parser, the default `--timeout` the
  product promises (`scry/tests/scale.wiz`).
* `wiz-doc`: **≤ 120 s** for one module.  A guard: documentation generation has
  no size sweep on this page.
* `trust-ledger`: **≤ 900 s** for `lib/`.  A guard: the walk is bounded by the
  size of `lib/`, which is not part of this measurement, and the first pass is
  a cold elaboration of every library module.

The three cx rules are aspiration, and their gate ceilings are the recorded
shape; the review `reviews/2026-11-18-complexity-patterns.md` has the loops and
the fix for each.  When one is fixed, lower its ceiling to its rule (3×).

"""


def render_page(rows: list[dict], meta: dict) -> str:
    when = meta["date"]
    sha = meta["commit"]
    total = meta["total_s"]
    red = [r["id"] for r in rows if r["verdict"] == "red"]
    parts = [PAGE_INTRO]
    parts.append(f"**Measured {when} at commit `{sha}`** on {meta['machine']} "
                 f"(Python {meta['python']}).  "
                 + (f"**Red today: {', '.join(f'`{r}`' for r in red)}.**"
                    if red else "Every workload is within its rule.")
                 + f"  This run took {total / 60:.1f} min of measurement "
                   f"(the toolchain build is not counted).\n")
    parts.append("## The numbers\n")
    parts.append(markdown_table(rows))
    parts.append("")
    parts.append(PAGE_RULES)
    parts.append("## What each workload runs\n")
    for r in rows:
        parts.append(f"### `{r['id']}`: {r['title']}\n")
        parts.append(r["measures"] + "\n")
        if r.get("source"):
            parts.append(f"Generator: {r['source']}.  The input is generated at the "
                         f"measured size; no generated file is checked in.\n")
        if r["kind"] == "ratio":
            parts.append(f"Measured at n = {r['n']} and 2n = {2 * r['n']}: "
                         f"{fmt_ms(r['t_n_ms'])} → {fmt_ms(r['t_2n_ms'])}, "
                         f"ratio **{r['ratio']:.1f}×** (rule ≤ {r['target']}×, "
                         f"gate ≤ {r['ceiling']:g}×).\n")
        else:
            parts.append(f"One size, **{fmt_ms(r['t_n_ms'])}** (budget "
                         f"{r['budget_s']:.0f} s).\n")
        parts.append(f"Measured {r['measured']}.\n")
    parts.append("## Reproducing\n")
    parts.append("""\
```text
python3 scripts/perf-report.py                 # the table
python3 scripts/perf-report.py --check         # exit 1 if a gate fails
python3 scripts/perf-report.py --out docs/perf.md --json bench-out/perf.json
```

The measured commands are `wiz check --no-cache` (the three cx files, generated
into a temporary directory), `scry taint native/tree-sitter-c/src/parser.c
--allow-errors --json`, `wiz doc lib/Text.wiz`, and
`scripts/trust-ledger.sh --lib-only`.  The tools are the build of the commit
under test: the nightly takes the Nix store paths of `.#wiz` and `.#tests` and
builds `scry` with `grail build scry`; a local checkout can pass
`--wiz .lake/build/bin/wiz --tests .lake/build/bin/tests`.
""")
    parts.append("## What it costs\n")
    parts.append(f"""\
This run took **{total / 60:.1f} min** end to end on {meta['machine']}.  The
three cx sweeps are the bulk: best of three at both sizes each, so a size pair
that costs `t(n) + t(2n)` costs three times that.  `wiz doc` runs twice; `scry
scale` and the ledger walk run once.  On an idle runner the three sweeps take
about 3 minutes and the whole report about 6; a shared or loaded runner can
double both (the absolute numbers move, the ratio does not).  The toolchain
build is outside that figure: the nightly Nix-substitutes `.#wiz` and `.#tests`
and spends a few minutes on `grail build scry`, so the job's wall time is the
build plus roughly this measurement.  No workload touches the network and no
input is checked in.
""")
    return "\n".join(parts)


# --------------------------------------------------------------------------- main

def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--wiz", default=None, help="the wiz executable (default $WIZ, .lake/build/bin/wiz, wiz)")
    ap.add_argument("--grail", default=None, help="the grail executable (default $GRAIL, .lake, grail)")
    ap.add_argument("--tests", default=None, help="the tests driver (default $TESTS_BIN, .lake, tests)")
    ap.add_argument("--scry", default=None, help="the scry executable (default $SCRY, scry/.grail/bin/scry, grail run)")
    ap.add_argument("--out", default=None, help="write the generated Markdown page here")
    ap.add_argument("--json", default=None, help="write the raw report here")
    ap.add_argument("--markdown", default=None, help="append the summary table to this file (CI summary)")
    ap.add_argument("--check", action="store_true", help="exit 1 when a gate fails")
    ap.add_argument("--runs", type=int, default=None, help="override the per-size repetitions")
    ap.add_argument("--timeout", type=int, default=None, help="override each command's timeout in seconds")
    ap.add_argument("--quiet", action="store_true", help="no progress lines on stderr")
    a = ap.parse_args(argv)
    verbose = not a.quiet

    wiz = find_tool(a.wiz, [str(ROOT / ".lake/build/bin/wiz"), "wiz"], "WIZ")
    grail = find_tool(a.grail, [str(ROOT / ".lake/build/bin/grail"), "grail"], "GRAIL")
    tests = find_tool(a.tests, [str(ROOT / ".lake/build/bin/tests"), "tests"], "TESTS_BIN")
    scry = a.scry or os.environ.get("SCRY") or str(ROOT / "scry/.grail/bin/scry")
    if not Path(scry).is_file():
        scry = ""      # `scry-scale` is skipped if the CLI was not built (documented in the row)

    # scripts/trust-ledger.sh runs $TESTS_BIN, else .lake/build/bin/tests: point it
    # at the same driver this script measured with.
    os.environ["TESTS_BIN"] = tests
    if verbose:
        print(f"perf-report: wiz={wiz}", file=sys.stderr)

    started = time.monotonic()
    today = dt.date.today().isoformat()
    with tempfile.TemporaryDirectory(prefix="wiz-perf-") as td:
        tmp = Path(td)
        trivial = tmp / "floor.wiz"
        trivial.write_text(TRIVIAL)
        floor = best_ms([wiz, "check", "--no-cache", str(trivial)], ROOT, 1, 120)
        if verbose:
            print(f"  floor: {floor:.0f} ms", file=sys.stderr)
        rows = []
        for w in RATIO_WORKLOADS:
            if a.runs:
                w.runs = a.runs
            if a.timeout:
                w.timeout = a.timeout
            r = measure_ratio(w, wiz, tmp, floor, verbose)
            r["measured"] = today
            rows.append(r)
        for w in SINGLE_WORKLOADS:
            if a.runs:
                w.runs = a.runs
            if a.timeout:
                w.timeout = a.timeout
            # The scry row needs a built CLI; without one it is an explicit skip.
            if w.id == "scry-scale" and not scry:
                r = skipped_single(w, "no built scry CLI (run `grail build scry`)", verbose)
            else:
                r = measure_single(w, dict(wiz=wiz, grail=grail, tests=tests, scry=scry),
                                   tmp, verbose)
            r["measured"] = today
            rows.append(r)

    total_s = time.monotonic() - started
    meta = dict(date=today, commit=git_sha(), total_s=round(total_s, 1),
                machine=platform.node() or "unknown host", python=platform.python_version())
    report = dict(schema=1, **meta, floor_ms=round(floor), workloads=rows)

    table = markdown_table(rows)
    print(table)
    failures = [r["id"] for r in rows if r.get("gate_fail")]
    skipped = [r["id"] for r in rows if r["verdict"] == "skipped"]
    red = [r["id"] for r in rows if r["verdict"] == "red"]
    if verbose:
        print(f"perf-report: {len(rows)} workloads, red: {', '.join(red) or 'none'}"
              f"; gate failures: {', '.join(failures) or 'none'}"
              f"; skipped: {', '.join(skipped) or 'none'}; {total_s / 60:.1f} min",
              file=sys.stderr)

    if a.json:
        Path(a.json).parent.mkdir(parents=True, exist_ok=True)
        Path(a.json).write_text(json.dumps(report, indent=1) + "\n")
    if a.out:
        page = render_page(rows, meta)
        Path(a.out).parent.mkdir(parents=True, exist_ok=True)
        Path(a.out).write_text(page)
    if a.markdown:
        with open(a.markdown, "a") as fh:
            fh.write("\n### Performance (complexity ratios)\n\n")
            fh.write(f"Measured {today} at `{meta['commit']}`; red = over the rule, "
                     f"gate failures = over the ceiling.\n\n{table}\n")

    if a.check and failures:
        print(f"perf-report: gate failed: {', '.join(failures)}", file=sys.stderr)
        return 1
    if a.check and skipped:
        # A skipped workload measured nothing: that is not a pass (the same rule as
        # scripts/bench-threshold.py's "an unmeasured mode is not a pass").
        print(f"perf-report: gate not satisfied: skipped {', '.join(skipped)}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
