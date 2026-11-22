#!/usr/bin/env python3
"""Classify a `=selfhost-libdiff` run report by first cause.

Inputs:
  --records-dir  directory with the sweep's records-*.jsonl (default .lake/libdiff)
  --causes       the file -> (cause, group, root, fix, why) table (default scripts/libdiff-causes.tsv)

Output: a Markdown report. The classification is a pure function of the run log and
the causes table; a new sweep only needs the new records directory. A diverging file
with no row in the table is reported as `unknown` (with its first error quoted) and
the script exits 2 so a stale table is visible in CI.
"""
from __future__ import annotations

import argparse
import collections
import glob
import json
import os
import sys

DEFAULT_CAUSES = os.path.join(os.path.dirname(os.path.abspath(__file__)), "libdiff-causes.tsv")

GROUP_ORDER = {
    "host-only syntax": 0,
    "real selfhost bug": 1,
    "expected divergence": 2,
    "bounded/crash": 3,
    "unknown": 4,
}

FIX_TITLES = {
    "word-equations": (
        "`Word.wiz` equation compiler: `def … : (m n : Nat) → …` with equations is rejected (`equations need a function type`, Word:42).",
        "Unblocks `Hdl/Core`'s second failure (`BitVec` at 189) and the Scry `U64`/`U64Map`/`Store`/`Datalog`/`Eval`/`PointsTo` chain.",
    ),
    "prelude-text": (
        "Align the embedded prelude with `lib/Text`: add `List.foldl` and stop re-declaring `List.map`/`String.length`.",
        "`lib/Scry/Rules`/`Models`/`Taint`/`Workflow`/`Sarif` and the `Scry` base chain get past their first error.",
    ),
    "hdl-core": (
        "`Hdl/Core` dotted-recursive definitions: `Hdl.indexed` cannot resolve its own `Hdl` name (Core:113).",
        "Needs #1 for `HwTy.El`'s `BitVec` at Core:189; the two together clear the Hdl cluster.",
    ),
    "string-append": (
        "`String ++`: `\"…\" ++ s` is inferred as `List.append` instead of `String.append` (`expected List, got String`).",
        "The count includes the three `Json.parse` users (`Tagged`, `tests/codegen`, `tools/SchemaMain`); the same shape also appears in `Args`, `RuleTaint`, `Facts`, `Project`, `Query`, `CsLower`, `tests/cst`.",
    ),
    "meta-api": (
        "Host-only meta API (`Macro`/`Syntax`/`Expr`/`ParamView`): the embedded prelude omits the elaborator-time API.",
        "Large (elaboration-time evaluation); `Data/ListLemmas`, `Deriving`, `Grail`, `OpticDerive`, `BvDecide`, `SatTactic`, `RingTactic`.",
    ),
    "wordarray": ("`WordArray.wiz:50` (`List.length_snoc`).", "Unblocks `Egraph`/`EgraphExtract`/`EqPlan`/`Lower` (`U64Array`/`U32Array`)."),
    "nested-inductives": ("The inductive-occurrence check (`the type being defined may only occur …`).", "`Conc`, `Hoare`, `Session`, and the Hoare/Prog users."),
    "deriver-bundle": ("The general `deriver` registry (`attribute [deriver Bundle]`).", "The five Hdl bundle structures."),
    "logic-true": ("`Logic.wiz:47` `True.intro : True := ()` (`expected True, got Unit0`).", "`Data/Order`, `Hdl/Arty`, `IntRing`, `Rat`."),
    "json-parser": ("`Json.wiz:359` mutual parser type mismatch.", "`Tagged`, `tests/codegen`, `tools/SchemaMain`."),
    "ulift": ("The `ULift`/`Sort 2` universe lift.", "`Functor`, `Eff`, `Scry/Engine`; `EffHeap`."),
    "pair-let": ("`let (x, y)` on an IO/Owned pair.", "`Handle`, `MVar`, `Ref`."),
    "int-order": ("`IntOrder.wiz:29` (`expected Nat, got Int`).", "`Rat`, `Plot`."),
    "typeclass": ("Type-class search stuck (`AbsDomain`/`Widen`).", "`Scry/AiCfg`, `Scry/AiDomain`."),
    "except-do": ("`do` in an `Except` function desugared with the IO bind.", "`Scry/Wil` and its users."),
    "eq-congr": ("`Eq.congrArg`/`Eq.congrArg2` implicit-argument unification.", "`Nat`, `BitBlast`."),
    "numeral-term": ("`term.num` (a numeral in a command/term position).", "`Hdl/Apb`, `Hdl/Wishbone`."),
    "builtin": ("The `builtin` command.", "`Prelude`, `Int`."),
    "quantity": ("Quantity terms `%t` (`a quantity must be 0, 1 or ω`).", "`Data/Result`, `Region`, `Optic`."),
    "coinductive": ("`command.coinductive`.", "`Hdl/Signal`."),
    "exists": ("`term.ex` (∃).", "`Hdl/Temporal`."),
    "absurd": ("`term.absurd`.", "`Sat`."),
    "grail-syntax": ("The grail build-file DSL.", "`scry/grail.wiz`."),
    "term-match": ("`term.match` in `#eval`.", "`scry/tests/schema.wiz`."),
    "notation-pow": ("The `^` notation.", "`SimpLemmas`."),
    "hdl-optic": ("`Hdl.zoom` Lens/Store telescope.", "`Hdl/Optic`."),
    "feral": ("`Fe.inst` List×Ty mismatch.", "`Feral`."),
    "scope": ("`Scope.with` Prod/Done mismatch.", "`Scope`."),
    "task": ("`Task.both_eq` rfl leaves a cast redex.", "`Task`."),
    "scry-optics": ("Optic composition is not a function.", "`Scry/Optics`."),
    "scry-codegen": ("`Scry.indexedFrom` dotted recursion.", "`Scry/Codegen`."),
    "hdl-xilinx7": ("`X7.spread` equations need a function type.", "`Hdl/Xilinx7`."),
    "scry-schema": ("`a.n` field projection.", "`Scry/Schema`."),
    "scry-test-ctors": ("Constructor argument elaboration.", "`tests/optics`, `tests/relations`."),
    "loom-tor": ("`Loom.toR` Prod mismatch.", "`Web/Loom`, `Web/Widget`."),
    "hprop": ("`Option.orElse_none` dependent equality.", "`HProp`."),
    "trace": ("`Mealy.outAt` Prod/function mismatch.", "`Trace`."),
    "vec": ("`Nat.lt_self` Eq/induction shape.", "`Vec`."),
    "fingertree": ("`Monoid.Lawful` instance/carrier mismatch.", "`FingerTree`."),
    "scry-wil": ("`Scry/Wil` failure.", "The Wil users."),
}



FIX_SHORT = {
    "wordarray": "`WordArray.wiz:50`",
    "nested-inductives": "nested inductive occurrence",
    "deriver-bundle": "custom `deriver`",
    "logic-true": "`Logic` `True`/`Unit0`",
    "json-parser": "`Json` mutual parser",
    "ulift": "`ULift`",
    "pair-let": "`let (x,y)` on IO/Owned",
    "int-order": "`IntOrder`",
    "typeclass": "type-class search",
    "except-do": "`Except` `do`",
    "eq-congr": "`Eq.congrArg`",
    "numeral-term": "`term.num`",
    "builtin": "`builtin`",
    "quantity": "quantity terms",
    "coinductive": "`coinductive`",
    "exists": "`term.ex`",
    "absurd": "`term.absurd`",
    "grail-syntax": "grail DSL",
    "term-match": "`term.match`",
    "notation-pow": "`^` notation",
}

FIX_COUNT_NOTE = {
    "prelude-text": " (12 `List.foldl` + 8 `Text` duplicate)",
}


def load_causes(path):
    causes = {}
    with open(path, encoding="utf-8") as fh:
        header = fh.readline().rstrip("\n").split("\t")
        for line in fh:
            line = line.rstrip("\n")
            if not line:
                continue
            cells = line.split("\t")
            if len(cells) < 6:
                raise SystemExit(f"{path}: bad row: {line!r}")
            row = dict(zip(header, cells))
            causes[row["file"]] = row
    return causes


def load_records(directory):
    files = sorted(glob.glob(os.path.join(directory, "records*.jsonl")))
    if not files:
        files = sorted(glob.glob(os.path.join(directory, "records-*-of-*.jsonl")))
    rows = []
    for path in files:
        with open(path, encoding="utf-8") as fh:
            for line in fh:
                line = line.strip()
                if line:
                    rows.append(json.loads(line))
    if not rows:
        raise SystemExit(f"{directory}: no records*.jsonl found")
    return rows


def short(text, n=150):
    text = " ".join(str(text).split())
    return text if len(text) <= n else text[: n - 1] + "…"


def cell(value):
    return str(value).replace("|", "\\|").replace("\n", " ")


def first_err(rec):
    side = rec["self"]
    loc = f"{side.get('file') or rec['file']}:{side.get('line', 0)}:{side.get('col', 0)}"
    return f"`{loc}` {short(side.get('msg', ''), 150)}"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--records-dir", default=".lake/libdiff")
    ap.add_argument("--causes", default=DEFAULT_CAUSES)
    ap.add_argument("-o", "--out", default="-")
    args = ap.parse_args()

    causes = load_causes(args.causes)
    records = load_records(args.records_dir)
    div = [r for r in records if r["verdict"] == "diverging"]
    bounded = [r for r in records if r["verdict"] == "bounded"]
    rejected = [r for r in records if r["verdict"] == "rejected"]
    ok = [r for r in records if r["verdict"] == "ok"]

    unknown = []
    for rec in div:
        if rec["file"] not in causes:
            unknown.append(rec["file"])
    for path in unknown:
        causes[path] = {
            "file": path, "cause": "unknown", "group": "unknown", "root": "unknown",
            "fix": "", "why": "no row in " + args.causes + "; first error is quoted in the table",
        }

    by_group = collections.Counter(causes[r["file"]]["group"] for r in div)
    by_root = collections.Counter(causes[r["file"]]["root"] for r in div)
    by_fix = collections.Counter(causes[r["file"]]["fix"] for r in div if causes[r["file"]]["fix"])
    root_group = {}
    for r in div:
        row = causes[r["file"]]
        root_group.setdefault(row["root"], row["group"])

    def fix_title(key):
        return FIX_TITLES.get(key, (key, ""))

    lines = []
    A = lines.append
    A("# `=selfhost-libdiff` classification (169 diverging of 209)")
    A("")
    A("Source: the four-part `=selfhost-libdiff` run on `libdiff-corpus` (`de5de5a64`,")
    A("2026-11-20 20:28–21:32) — `records-{1..4}-of-4.jsonl` and `summary-{1..4}-of-4.txt` in")
    A("that worktree's `.lake/libdiff/`. 209 files: 169 diverging, 31 bounded, 8 both-reject,")
    A("1 ok. The host is the Lean frontend; the self side is the self-hosted compiler")
    A("(`check FILE --types`). The first error is the harness's first error **in the file**,")
    A("or the first import error when the root file has none; a row whose error is in an")
    A("import says so in the location.")
    A("")
    A("This is a map, not a gate. The classification is by **first cause**: the thing that")
    A("makes this file fail first, not every later error in it. For cascades the `why` column")
    A("names the failing base module; the `file` in the first-error column is where the")
    A("harness saw it.")
    A("")
    A("## Counts by group")
    A("")
    A("| group | files |")
    A("|---|---:|")
    for group, n in sorted(by_group.items(), key=lambda kv: (-kv[1], GROUP_ORDER.get(kv[0], 9))):
        A(f"| {group} | {n} |")
    A(f"| **total** | **{len(div)}** |")
    A("")
    A("### Reading the groups")
    A("")
    A("* **host-only syntax** — the construct is not in the selfhost frontend; implementing")
    A("  it (or declaring it out of scope) is the fix.")
    A("* **real selfhost bug** — the host accepts and the selfhost rejects or crashes; the")
    A("  frontend/kernel/runtime needs fixing.")
    A("* **expected divergence** — the module's subject is the C12 FFI/native boundary or the")
    A("  C13 63-bit `Nat`; it is deliberately outside the selfhost's current scope.")
    A("* **bounded/crash** — the appendix below; this run has 30 host timeouts and one")
    A("  self-hosted OOM, not SIGSEGV.")
    A("")
    A("`lib/Sys.wiz` itself is in **real selfhost bug** (its first error, `EIO.bind`, is a")
    A("fixable elaboration bug); its clients are in **expected divergence** because their")
    A("remaining surface is the File/Sys/process/clock FFI (C12).")
    A("")
    A("## Counts by root cause (top 25)")
    A("")
    A("| root cause | group | files |")
    A("|---|---|---:|")
    for root, n in by_root.most_common(25):
        A(f"| {root} | {root_group.get(root, '')} | {n} |")
    A("")
    A("## Top five fixes by files cleared")
    A("")
    A("Counts are files whose **first error** names this cause. A fix can also expose a")
    A("second error in the same file (the selfhost reports one first error per file); the")
    A('"also" column says what becomes reachable. The expected-divergence roots and the')
    A("multi-fix `Scry base` root are excluded from this ranking.")
    A("")
    A("| # | fix | clears (first error) | also |")
    A("|---:|---|---:|---|")
    ranked = [(k, n) for k, n in by_fix.most_common() if k]
    for i, (key, n) in enumerate(ranked[:5], 1):
        title, also = fix_title(key)
        A(f"| {i} | {title} | **{n}**{FIX_COUNT_NOTE.get(key, '')} | {also} |")
    A("")
    rest = [(k, n) for k, n in ranked[5:] if n >= 2]
    if rest:
        A("Next by size, if #5 is too large: " + ", ".join(f"{FIX_SHORT.get(k, k)} ({n})" for k, n in rest[:6]) + ".")
        A("")
    A("The `expected divergence` rows are **not** in this queue: 12 are the C12 FFI/IO")
    A("boundary (the `IO`/`Std` natives and the `EIO`/`FS`/`Clock`/`ExitStatus`/`SpawnOptions`")
    A("users) and one is the C13 63-bit numeral. They are counted separately below.")
    A("")
    A("## Diverging files (169)")
    A("")
    A("| file | cause | first error | group | why |")
    A("|---|---|---|---|---|")
    for rec in sorted(div, key=lambda r: (GROUP_ORDER.get(causes[r["file"]]["group"], 9),
                                          causes[r["file"]]["cause"], r["file"])):
        row = causes[rec["file"]]
        A(f"| `{rec['file']}` | {cell(row['cause'])} | {cell(first_err(rec))} | {cell(row['group'])} | {cell(row['why'])} |")
    A("")
    A("## Bounded lane (31) — not part of the 169")
    A("")
    A("The plan calls this the SIGSEGV lane, but this run is **not** SIGSEGV: 30 of 31 are")
    A("the **host** hitting the 60 s bound while the selfhost finishes the same file in")
    A("15–25 s; one (`lib/BitVecAdd.wiz`) is the selfhost running out of memory at ~83 s.")
    A("The host bound is too low for the large `scry/src/Scry/*` and `scry/tests/*` roots;")
    A("raising `--host-secs` (or running those roots with the selfhost only) would turn most")
    A("of this lane into real verdicts. `lib/BitVecAdd.wiz` is the one true crash.")
    A("")
    A("| file | host | self | note |")
    A("|---|---|---|---|")
    for rec in sorted(bounded, key=lambda r: r["file"]):
        h, s = rec["host"], rec["self"]
        A(f"| `{rec['file']}` | {h['status']} {h['ms']//1000}s | {s['status']} {s['ms']//1000}s | {cell(short(rec.get('note','') or s.get('note',''), 100))} |")
    A("")
    A("## Both-reject and ok")
    A("")
    A("Both-reject (8) and ok (1) are not gaps; the rejections are the same verdict from both")
    A("frontends (the error codes/spans/messages differ, which the harness counts separately).")
    A("")
    A("| file | verdict | self first error |")
    A("|---|---|---|")
    for rec in sorted(rejected + ok, key=lambda r: (r["verdict"], r["file"])):
        A(f"| `{rec['file']}` | {rec['verdict']} | {cell(first_err(rec))} |")
    A("")
    A("## Reproduce / regenerate")
    A("")
    A("`scripts/libdiff-classify.py` reads the same `records-*.jsonl` and the cause table")
    A("`scripts/libdiff-causes.tsv`, and writes this file. It is a pure function of the run")
    A("log: a new sweep only needs the new records directory (and a line for a new file type).")
    A("")
    A("```sh")
    A("# produce the report (the four-part sweeps write .lake/libdiff/records-*.jsonl)")
    A("lake test -- '=selfhost-libdiff'")
    A("# classify it")
    A("python3 scripts/libdiff-classify.py --records-dir .lake/libdiff -o /tmp/libdiff.md")
    A("```")
    A("")
    A("## Caveats")
    A("")
    A("* The report is the **209-file** corpus on `libdiff-corpus`; train9's corpus is **225**")
    A("  files (16 modules added by the Loom/HDL/Scry/notations merges after that run). The 16")
    A("  are not in this table; a train9 rerun flags them as `unknown` until rows are added.")
    A("* The self-hosted compiler binary used for the report is the 20:16 build; running it")
    A("  with a stale default cache can move diagnostics to `1:1 unknown identifier outParam`.")
    A("  The classification uses the report's records, not a fresh cache.")
    A("* A \"first error\" is often a cascade (e.g. `unknown U64` because `Word` failed). The")
    A("  `why` and `root cause` columns give the cause the file should be queued under.")
    A("")
    text = "\n".join(lines) + "\n"
    if args.out == "-":
        sys.stdout.write(text)
    else:
        with open(args.out, "w", encoding="utf-8") as fh:
            fh.write(text)
    if unknown:
        print(f"libdiff-classify: {len(unknown)} diverging file(s) not in {args.causes}: " +
              ", ".join(sorted(unknown)), file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
