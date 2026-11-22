#!/usr/bin/env python3
"""Differential fuzzing for erasure and optimisation bugs (stage 5 / 15c).

Every generated program is run through the three pipelines that must agree:

  eval  the tree interpreter (`#eval`), after erasure
  ir    the IR interpreter (`#run`), after `IR.optimizeProgram` and reference counting
  c     the C backend (`wiz run`), i.e. compiled code

The grammar is a small, typed, closed fragment of Wiz: `Nat`/`Bool` arithmetic,
`if`, structural recursion, `let`, pairs, `Option`, arrays with a pure list model
(local mutation; compiled only), region-scoped values, and the constructs the
erasure audit is about -- quantity-0 arguments, fields and let-bindings whose values
would diverge (or call a native) if they were evaluated, and functions into `Unit`.

Programs are batched: one file with many `#eval`s, one with many `#run`s and one C
program printing every result.  A batch is therefore ~3 processes, not 3 per
program.  A batch that crashes or times out is bisected down to one program; a
disagreement is shrunk by delta-debugging its choice sequence, so the finding is
replayable.

Usage
  scripts/diff-fuzz.py --fast                       # 200 programs, fixed seed (CI)
  scripts/diff-fuzz.py --nightly                    # today's seed, 2000 programs
  scripts/diff-fuzz.py --seed 7 --programs 500      # a campaign
  scripts/diff-fuzz.py --replay SEED INDEX CHOICES  # one case again

A skipped pipeline (no `wiz`, no C compiler) is a skip, not a pass: the run says
which pipelines ran.

The `--wiz-arg` flag is repeatable and forwards a flag to every `wiz` invocation
(the test group passes the driver's toolchain flags: `--cc`, `--cflags`, ...).
"""

from __future__ import annotations

import argparse
import os
import random
import re
import shutil
import subprocess
import sys
import tempfile
import time
from dataclasses import dataclass, field
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DEFAULT_WIZ = ROOT / ".lake" / "build" / "bin" / "wiz"
FAST_SEED = 20261119
FAST_PROGRAMS = 200
NIGHTLY_PROGRAMS = 2000

# ---------------------------------------------------------------------------
# The preamble: helpers the generated definitions may use.
# ---------------------------------------------------------------------------

PREAMBLE = """import Prelude
import IO
import Std

-- pure list helpers (the model for the array programs)
def dfSumL : List Nat \u2192 Nat := fun xs => match xs with | .nil => 0 | .cons x r => Nat.add x (dfSumL r)
def dfLenL : List Nat \u2192 Nat := fun xs => match xs with | .nil => 0 | .cons x r => Nat.succ (dfLenL r)
def dfNthD : List Nat \u2192 Nat \u2192 Nat \u2192 Nat := fun xs i d => match xs, i with | .nil, _ => d | .cons x r, .zero => x | .cons x r, .succ k => dfNthD r k d
def dfSetAt : List Nat \u2192 Nat \u2192 Nat \u2192 List Nat := fun xs i v => match xs, i with | .nil, _ => List.nil | .cons x r, .zero => List.cons v r | .cons x r, .succ k => List.cons x (dfSetAt r k v)

-- values that loop when they are evaluated; they only appear in 0 positions
partial def dfSpinN (u : Unit) : Nat := dfSpinN u
partial def dfSpinU (u : Unit) : Unit := dfSpinU u
def dfGhost : (0 x : Nat) \u2192 Unit := fun x => dfSpinU ()

-- a structure with an erased field, an inductive with an erased field, and a
-- structure whose marker is a function into Unit (erasedFunTy, stage 22e)
structure dfS0 where
  0 ghost : Nat
  val : Nat
inductive dfT0 where
  | mk (0 ghost : Nat) (val : Nat)
structure dfSF where
  n : Nat
  ghost : (0 x : Nat) \u2192 Unit

-- regions as erased type indices (a small stand-in for lib/Region)
axiom dfRg : Type
axiom dfRgStatic : dfRg
structure dfSh (r : dfRg) (A : Type) where
  val : A
def dfShMk {0 r : dfRg} {A : Type} (a : A) : dfSh r A := dfSh.mk a
def dfRscope {B : Type} (0 r : dfRg) (body : (0 r' : dfRg) \u2192 dfSh r' Nat \u2192 B) : B := body r (dfShMk 7)
"""

# ---------------------------------------------------------------------------
# Deterministic choice sequences
# ---------------------------------------------------------------------------


class Gen:
    """A deterministic stream of choices.  A missing choice is 0, so a shrunken
    sequence replays (the generator's shape falls back to its first case)."""

    def __init__(self, choices: list[int]):
        self.choices = choices
        self.i = 0

    def at(self, k: int) -> int:
        v = self.choices[self.i] if self.i < len(self.choices) else 0
        self.i += 1
        return v % k


def rng_for(seed: int, index: int) -> random.Random:
    return random.Random(((seed * 1000003) ^ (index * 7919)) & 0xFFFFFFFF)


def choices_for(seed: int, index: int, n: int = 64) -> list[int]:
    r = rng_for(seed, index)
    return [r.randrange(0, 2**31) for _ in range(n)]


# ---------------------------------------------------------------------------
# The typed expression grammar
# ---------------------------------------------------------------------------

BIG = ["9007199254740993", "18446744073709551617", "4294967297", "1000003"]


def lit(g: Gen) -> str:
    k = g.at(24)
    if k == 23:
        return BIG[g.at(len(BIG))]
    return str(g.at(16))


def gen_nat(g: Gen, d: int) -> str:
    if d <= 0:
        return lit(g)
    op = g.at(24)
    if op == 0:
        return f"(Nat.add {gen_nat(g, d - 1)} {gen_nat(g, d - 1)})"
    if op == 1:
        return f"(Nat.mul {gen_nat(g, d - 1)} {gen_nat(g, d - 1)})"
    if op == 2:
        return f"(Nat.sub {gen_nat(g, d - 1)} {gen_nat(g, d - 1)})"
    if op == 3:
        return f"(Nat.div {gen_nat(g, d - 1)} (Nat.succ {gen_nat(g, d - 1)}))"
    if op == 4:
        return f"(Nat.mod {gen_nat(g, d - 1)} (Nat.succ {gen_nat(g, d - 1)}))"
    if op == 5:
        return f"(Nat.pred {gen_nat(g, d - 1)})"
    if op == 6:
        return f"(if {gen_bool(g, d - 1)} then {gen_nat(g, d - 1)} else {gen_nat(g, d - 1)})"
    if op == 7:
        # the kernel's `n / 0 = 0` and `n % 0 = n` (constant-folded too)
        return f"(Nat.div {gen_nat(g, d - 1)} 0)"
    if op == 8:
        return f"(Nat.mod {gen_nat(g, d - 1)} 0)"
    if op == 9:
        a = gen_nat(g, d - 1)
        b = gen_nat(g, d - 1)
        return f"(let p : Nat \u00d7 Nat := ({a}, {b}); if Nat.beq p.1 p.2 then p.2 else Nat.add p.1 p.2)"
    if op == 10:
        a = gen_nat(g, d - 1)
        b = gen_nat(g, d - 1)
        return (f"(match Option.some {a} with | .some x => Nat.add x {b} | .none => 0)")
    if op == 11:
        a = gen_nat(g, d - 1)
        b = gen_nat(g, d - 1)
        return f"(let n : Nat := {a}; match Nat.beq n {b} with | .true => Nat.add n {b} | .false => {a})"
    if op == 12:
        return f"(Nat.add (Nat.mul {lit(g)} {lit(g)}) {gen_nat(g, d - 1)})"
    if op == 13:
        return f"(Nat.sub (Nat.mul {gen_nat(g, d - 1)} {gen_nat(g, d - 1)}) {gen_nat(g, d - 1)})"
    # the operations the IR's constant folder treats specially (`foldNat`, 15c)
    if op == 14:
        return f"(Nat.pow {g.at(6)} {g.at(6)})"
    if op == 15:
        return f"(Nat.shiftLeft {g.at(300)} {g.at(70)})"
    if op == 16:
        return f"(Nat.shiftRight {g.at(300)} {g.at(9)})"
    if op == 17:
        return f"(Nat.land {lit(g)} {lit(g)})"
    if op == 18:
        return f"(Nat.lor {lit(g)} {lit(g)})"
    if op == 19:
        return f"(Nat.xor {lit(g)} {lit(g)})"
    if op == 20:
        return f"(if Nat.le {gen_nat(g, d - 1)} {gen_nat(g, d - 1)} then 1 else 0)"
    if op == 21:
        return f"(Nat.max {gen_nat(g, d - 1)} {gen_nat(g, d - 1)})"
    if op == 22:
        return f"(Nat.pow 2 {g.at(70)})"
    return lit(g)


def gen_bool(g: Gen, d: int) -> str:
    if d <= 0:
        return "Bool.true" if g.at(2) == 0 else "Bool.false"
    op = g.at(8)
    if op == 0:
        return f"(Nat.beq {gen_nat(g, d - 1)} {gen_nat(g, d - 1)})"
    if op == 1:
        return f"(Nat.lt {gen_nat(g, d - 1)} {gen_nat(g, d - 1)})"
    if op == 2:
        return f"(Bool.and {gen_bool(g, d - 1)} {gen_bool(g, d - 1)})"
    if op == 3:
        return f"(Bool.or {gen_bool(g, d - 1)} {gen_bool(g, d - 1)})"
    if op == 4:
        return f"(Bool.not {gen_bool(g, d - 1)})"
    if op == 5:
        return f"(if {gen_bool(g, d - 1)} then {gen_bool(g, d - 1)} else {gen_bool(g, d - 1)})"
    if op == 6:
        return "Bool.true"
    return "Bool.false"


# ---------------------------------------------------------------------------
# A case is one closed program `pN_out : Nat` (or a compiled-only array program
# `pN_mut` paired with its pure list model `pN_pure`).
# ---------------------------------------------------------------------------


@dataclass
class Case:
    index: int
    shape: str
    choices: list[int]
    eval_defs: list[str] = field(default_factory=list)
    eval_expr: str = ""
    c_defs: list[str] = field(default_factory=list)
    c_exprs: list[str] = field(default_factory=list)
    mult: int = 1  # number of C output lines


def pure_case(index: int, shape: str, choices: list[int], body: str) -> Case:
    name = f"p{index}_out"
    return Case(index, shape, choices, [f"def {name} : Nat := {body}"], name,
                [f"def {name} : Nat := {body}"], [name], 1)


def defs_case(index: int, shape: str, choices: list[int], defs: list[str], expr: str) -> Case:
    name = f"p{index}_out"
    d = list(defs) + [f"def {name} : Nat := {expr}"]
    return Case(index, shape, choices, d, name, d, [name], 1)


def make_case(seed: int, index: int, choices: list[int] | None = None) -> Case:
    ch = choices if choices is not None else choices_for(seed, index)
    g = Gen(ch)
    shape = g.at(22)
    p = f"p{index}"
    # Weighted: erasure shapes and constant folding are over-represented.
    # 0 arithmetic, 1 recursion, 2 list fold, 3 tail loop, 4 erased lambda,
    # 5 let-0/split-0, 6/15 0 field (structure/inductive), 7 function-into-Unit,
    # 8/17 region, 9 dead branch, 10 branch learning, 11 erased native,
    # 12 known ctor, 13 tail count, 14 arrays (compiled only), 18 pair/option,
    # 19 arithmetic (deep), 20 erased argument through a variable's Π type
    if shape in (0, 19):
        body = gen_nat(g, 3 if shape == 0 else 4)
        return pure_case(index, "arith", ch, body)
    if shape == 1:
        base = lit(g)
        c = lit(g)
        n = g.at(10)
        d = [f"def {p}_rec (n : Nat) : Nat := match n with | .zero => {base} | .succ k => Nat.add ({p}_rec k) {c}"]
        return defs_case(index, "recursion", ch, d, f"{p}_rec {n}")
    if shape == 2:
        base = lit(g)
        c = lit(g)
        d = [f"def {p}_sum : List Nat \u2192 Nat := fun xs => match xs with | .nil => {base} | .cons x r => Nat.add (Nat.mul x {c}) ({p}_sum r)"]
        vals = [lit(g) for _ in range(g.at(4) + 1)]
        xs = "List.nil"
        for v in reversed(vals):
            xs = f"(List.cons {v} {xs})"
        return defs_case(index, "list", ch, d, f"{p}_sum {xs}")
    if shape == 3:
        a = lit(g)
        n = g.at(40)
        d = [f"partial def {p}_loop (acc : Nat) (n : Nat) : Nat := match n with | .zero => acc | .succ k => {p}_loop (Nat.add acc k) k"]
        return defs_case(index, "tail-loop", ch, d, f"{p}_loop {a} {n}")
    if shape == 4:
        # (the ascription is needed: a `0` binder's codomain is a metavariable, and
        # solving it from a literal body is outside the pattern fragment)
        inner = gen_nat(g, 1) if g.at(4) == 0 else lit(g)
        body = f"((fun (0 x : Nat) => {inner}) : (0 x : Nat) \u2192 Nat) (dfSpinN ())"
        return pure_case(index, "erased-arg", ch, body)
    if shape == 5:
        k = lit(g)
        if g.at(3) == 0:
            body = f"(let 0 x := dfSpinN (); {k})"
            return pure_case(index, "let0", ch, body)
        body = f"(let 0 (x, y) := ((dfSpinN (), {lit(g)}) : Nat \u00d7 Nat); {k})"
        return pure_case(index, "split0", ch, body)
    if shape == 6 or shape == 15:
        k = lit(g)
        if g.at(2) == 0:
            body = f"(dfS0.mk (dfSpinN ()) {k}).val"
            return pure_case(index, "zero-field-struct", ch, body)
        body = f"(match (dfT0.mk (dfSpinN ()) {k}) with | .mk _ v => v)"
        return pure_case(index, "zero-field-inductive", ch, body)
    if shape == 7:
        n = lit(g)
        body = (f"(let s : dfSF := dfSF.mk {n} dfGhost; "
                f"(match s with | .mk n g => ((g 5, n + 1) : Unit \u00d7 Nat).2))")
        return pure_case(index, "erased-fun-into-unit", ch, body)
    if shape == 8 or shape == 17:
        k = lit(g)
        if g.at(2) == 0:
            body = f"(dfRscope dfRgStatic (fun (0 r) (s : dfSh r Nat) => Nat.add s.val {k}))"
            return pure_case(index, "region-scope", ch, body)
        body = (f"(let f : (0 r : dfRg) \u2192 Nat \u2192 Nat := fun r n => Nat.add n {k}; "
                f"f dfRgStatic {lit(g)})")
        return pure_case(index, "region-arg", ch, body)
    if shape == 9:
        a = lit(g)
        k = lit(g)
        body = f"(if Nat.beq {a} {a} then {k} else dfSpinN ())"
        return pure_case(index, "dead-branch", ch, body)
    if shape == 10:
        a = lit(g)
        b = lit(g)
        c = lit(g)
        body = (f"(let n : Nat := {a}; match Nat.beq n {b} with "
                f"| .true => Nat.add n {c} | .false => {c})")
        return pure_case(index, "branch-learning", ch, body)
    if shape == 11:
        k = lit(g)
        v = lit(g)
        body = f"(fun (0 x : Nat) => {k}) (Array.size (Array.push Array.empty {v}))"
        return pure_case(index, "erased-native", ch, body)
    if shape == 12:
        a = lit(g)
        k = lit(g)
        body = (f"(match Option.some {a} with | .some x => Nat.add x {k} | .none => dfSpinN ())")
        return pure_case(index, "known-ctor", ch, body)
    if shape == 13:
        base = lit(g)
        n = g.at(30)
        d = [f"def {p}_count : Nat \u2192 Nat := fun n => match n with | .zero => {base} | .succ k => {p}_count k"]
        return defs_case(index, "rec-count", ch, d, f"{p}_count {n}")
    if shape == 18:
        a = lit(g)
        b = lit(g)
        k = lit(g)
        body = (f"(let o : Option (Nat \u00d7 Nat) := Option.some ({a}, {b}); "
                f"match o with | .none => {k} | .some p => if Nat.beq p.1 p.2 then p.2 else Nat.add p.1 {k})")
        return pure_case(index, "pair-option", ch, body)
    if shape == 20:
        # the audit's e5: the argument is erased through the *variable's* Π type,
        # not through a lambda head (the two erasure paths in `eraseSpine`)
        k = lit(g)
        body = f"(fun (f : (0 x : Nat) \u2192 Nat) => f (dfSpinN ())) (fun _ => {k})"
        return pure_case(index, "erased-arg-through-var", ch, body)
    if shape == 21:
        # the folder's `case` of a variable tested against itself: `nat.beq n n`
        # is `true` and `nat.lt n n` is `false`, with only one branch live
        k = lit(g)
        n = gen_nat(g, 1)
        body = f"(let n : Nat := {n}; if Nat.beq n n then {k} else dfSpinN ())"
        if g.at(2) == 0:
            body = f"(let n : Nat := {n}; if Nat.lt n n then dfSpinN () else {k})"
        return pure_case(index, "self-compare", ch, body)
    # 14: arrays, compiled only, with a pure list model evaluated by the interpreters
    vals = [lit(g) for _ in range(g.at(4) + 1)]
    i = g.at(len(vals) + 1)
    v = lit(g)
    j = g.at(len(vals) + 1)
    d = lit(g)
    arr = "Array.empty"
    for x in vals:
        arr = f"(Array.push {arr} {x})"
    lst = "List.nil"
    for x in reversed(vals):
        lst = f"(List.cons {x} {lst})"
    mut = (f"(let a0 : Array Nat := {arr}; let a1 : Array Nat := Array.set a0 {i} {v}; "
           f"Nat.add (Array.getD a1 {j} {d}) (Array.size a1))")
    model = (f"(let l0 : List Nat := {lst}; let l1 : List Nat := dfSetAt l0 {i} {v}; "
             f"Nat.add (dfNthD l1 {j} {d}) (dfLenL l1))")
    mut_name = f"p{index}_mut"
    pure_name = f"p{index}_pure"
    mut_defs = [f"def {mut_name} : Nat := {mut}", f"def {pure_name} : Nat := {model}"]
    return Case(index, "array", ch, [f"def {pure_name} : Nat := {model}"], pure_name,
                mut_defs, [mut_name, pure_name], 2)


DIRECTIVE = {"eval": "eval", "ir": "run"}


def source_of(case: Case, directive: str = "eval") -> str:
    """One case alone, for a report or a pin."""
    if directive == "c":
        return PREAMBLE + "\n" + "\n".join(case.c_defs) + "\n" + c_main([case])
    defs = case.eval_defs
    return (PREAMBLE + "\n" + "\n".join(defs) + "\n"
            + f"#{DIRECTIVE[directive]} {case.eval_expr}\n")


def c_main(cases: list[Case]) -> str:
    lines = ["def main : IO Unit := do"]
    flat = [name for c in cases for name in c.c_exprs]
    for i, name in enumerate(flat):
        sep = ";" if i + 1 < len(flat) else ""
        lines.append(f"  IO.println (Nat.toString {name}){sep}")
    return "\n".join(lines) + "\n"


def batch_source(cases: list[Case], kind: str) -> str:
    if kind == "c":
        defs = [d for c in cases for d in c.c_defs]
        return PREAMBLE + "\n" + "\n".join(defs) + "\n" + c_main(cases)
    defs = [d for c in cases for d in c.eval_defs]
    return (PREAMBLE + "\n" + "\n".join(defs) + "\n"
            + "\n".join(f"#{DIRECTIVE[kind]} {c.eval_expr}" for c in cases) + "\n")


# ---------------------------------------------------------------------------
# Running the pipelines
# ---------------------------------------------------------------------------


@dataclass
class Outcome:
    status: str  # "ok" | "timeout" | "failed" | "skip"
    values: list[str] = field(default_factory=list)
    errors: list[str] = field(default_factory=list)
    stderr: str = ""
    exit: int = 0


# A missing C toolchain is a skip, not a finding (the repo's convention).  A genuine
# compile error in generated code must *not* match these.
TOOLCHAIN_MISSING = ["could not execute external process",
                     "gmp.h: No such file", "gc.h: No such file",
                     "fatal error: gmp.h", "fatal error: gc.h",
                     "no such file or directory: 'cc'"]


INFO_RE = re.compile(r": info: (.*)$")
ERR_RE = re.compile(r": error: (.*)$")


def run_wiz(args: list[str], timeout: float, cwd: Path) -> tuple[int, str, str, bool]:
    try:
        p = subprocess.run(args, cwd=str(cwd), capture_output=True, text=True,
                           timeout=timeout)
        return p.returncode, p.stdout, p.stderr, False
    except subprocess.TimeoutExpired:
        return 124, "", "", True


def run_pipeline(kind: str, cases: list[Case], ctx: "Ctx", timeout: float) -> Outcome:
    d = ctx.work / kind
    d.mkdir(parents=True, exist_ok=True)
    path = d / "batch.wiz"
    path.write_text(batch_source(cases, kind))
    args = ctx.wiz + ctx.wiz_args + (["run", str(path)] if kind == "c"
                                     else ["check", str(path)])
    code, out, err, timed = run_wiz(args, timeout, ctx.cwd)
    text = out + "\n" + err
    if timed:
        return Outcome("timeout", stderr=text, exit=code)
    errors = [m.group(1) for m in (ERR_RE.search(l) for l in text.splitlines()) if m]
    if kind == "c":
        vals = [l.strip() for l in out.splitlines() if l.strip() != ""]
        if code != 0:
            if any(m in text for m in TOOLCHAIN_MISSING):
                return Outcome("skip", vals, errors, text, code)
            return Outcome("failed", vals, errors, text, code)
        return Outcome("ok", vals, errors, text, code)
    vals = [m.group(1) for m in (INFO_RE.search(l) for l in text.splitlines()) if m]
    if code != 0 or errors:
        return Outcome("failed", vals, errors, text, code)
    return Outcome("ok", vals, [], text, code)


# ---------------------------------------------------------------------------
# Campaign
# ---------------------------------------------------------------------------


@dataclass
class Ctx:
    wiz: list[str]
    wiz_args: list[str]
    cwd: Path
    work: Path
    timeout: float
    verbose: bool


@dataclass
class Finding:
    kind: str
    index: int
    detail: str
    case: Case
    choices: list[int]
    shrink_note: str = ""


def compiled_lines(cases: list[Case]) -> list[tuple[int, int]]:
    """For each compiled output line, (case position, which)."""
    out: list[tuple[int, int]] = []
    for pos, c in enumerate(cases):
        for which in range(len(c.c_exprs)):
            out.append((pos, which))
    return out


def compare(cases: list[Case], ev: Outcome | None, ir: Outcome | None,
            cc: Outcome | None) -> list[Finding]:
    findings: list[Finding] = []

    def add(kind: str, pos: int, detail: str) -> None:
        findings.append(Finding(kind, cases[pos].index, detail, cases[pos], cases[pos].choices))

    ev = ev if ev is not None and ev.status == "ok" else None
    ir = ir if ir is not None and ir.status == "ok" else None
    cc = cc if cc is not None and cc.status == "ok" else None
    if ev is not None and len(ev.values) != len(cases):
        findings.append(Finding("eval-count", -1,
                                f"expected {len(cases)} values, got {len(ev.values)}",
                                cases[0], []))
        return findings
    if ir is not None and len(ir.values) != len(cases):
        findings.append(Finding("ir-count", -1,
                                f"expected {len(cases)} values, got {len(ir.values)}",
                                cases[0], []))
        return findings
    if ev is not None and ir is not None:
        for pos, c in enumerate(cases):
            a = ev.values[pos]
            b = ir.values[pos]
            if a != b:
                add("eval-vs-ir", pos, f"#eval {a!r}, #run {b!r}")
    if ev is not None and cc is not None:
        lines = compiled_lines(cases)
        if len(cc.values) != len(lines):
            findings.append(Finding("c-count", -1,
                                    f"expected {len(lines)} lines, got {len(cc.values)}",
                                    cases[0], []))
            return findings
        for line_no, (pos, which) in enumerate(lines):
            c = cases[pos]
            got = cc.values[line_no]
            ref = ev.values[pos]
            if got != ref:
                which_name = "mut" if which == 0 and c.mult == 2 else "pure"
                add("c-vs-interpreters", pos, f"C({which_name}) {got!r}, interpreter {ref!r}")
    return findings


def bisect(kind: str, cases: list[Case], ctx: Ctx) -> list[Case]:
    """The smallest subsets of `cases` whose batch for `kind` fails."""
    out = run_pipeline(kind, cases, ctx, ctx.timeout)
    if out.status == "timeout":
        out = run_pipeline(kind, cases, ctx, ctx.timeout * 2)
    if out.status == "ok":
        return []
    if len(cases) == 1:
        return cases
    mid = len(cases) // 2
    left = bisect(kind, cases[:mid], ctx)
    right = bisect(kind, cases[mid:], ctx)
    return left + right


def pipelines_for(kind: str) -> tuple[str, ...]:
    """The pipelines a failure class needs (shrinking runs only these)."""
    if kind in ("eval-vs-ir", "count"):
        return ("eval", "ir")
    if kind.startswith("c"):
        return ("eval", "c")
    if kind.startswith("eval"):
        return ("eval",)
    if kind.startswith("ir"):
        return ("ir",)
    return ("eval", "ir", "c")


def single_outcomes(case: Case, ctx: Ctx, keys: tuple[str, ...] = ("eval", "ir", "c")) -> dict[str, Outcome]:
    """One case through each pipeline.  A timeout is retried once with twice the
    budget: another agent's build can starve a compile for a few seconds, and a
    transient stall is not a disagreement."""
    out: dict[str, Outcome] = {}
    for k in keys:
        t = max(10.0, min(30.0, ctx.timeout / 3))
        o = run_pipeline(k, [case], ctx, t)
        if o.status == "timeout":
            o = run_pipeline(k, [case], ctx, t * 2)
        out[k] = o
    return out


def classify(outcomes: dict[str, Outcome], case: Case) -> tuple[str, str] | None:
    """The failure class of a single case, or None if it agrees."""
    ev = outcomes.get("eval")
    ir = outcomes.get("ir")
    cc = outcomes.get("c")
    for name, o in (("eval", ev), ("ir", ir), ("c", cc)):
        if o is None:
            continue
        if o.status == "timeout":
            return (f"{name}-timeout", f"the {name} pipeline did not finish")
        if o.status == "failed":
            text = o.stderr
            if "PANIC" in text:
                return (f"{name}-panic", first_panic(text))
            if any("error:" in l for l in text.splitlines()):
                return (f"{name}-error", first_error(text))
            return (f"{name}-crash", f"exit {o.exit}: {text.strip().splitlines()[:1]}")
    if ev is not None and ir is not None:
        if len(ev.values) != 1 or len(ir.values) != 1:
            return ("count", f"eval {len(ev.values)} values, ir {len(ir.values)}")
        if ev.values[0] != ir.values[0]:
            return ("eval-vs-ir", f"#eval {ev.values[0]!r}, #run {ir.values[0]!r}")
    if cc is not None and ev is not None:
        if len(cc.values) != len(case.c_exprs):
            return ("c-count", f"expected {len(case.c_exprs)} lines, got {len(cc.values)}")
        for got, which in zip(cc.values, case.c_exprs):
            if got != ev.values[0]:
                return ("c-vs-interpreters", f"C {got!r}, interpreter {ev.values[0]!r} ({which})")
    return None


def first_panic(text: str) -> str:
    for l in text.splitlines():
        if "PANIC" in l:
            return l.strip()
    return "PANIC"


def first_error(text: str) -> str:
    for l in text.splitlines():
        if "error:" in l:
            return l.strip()
    return "error"


def shrink(f: Finding, ctx: Ctx, seed: int, max_tests: int = 40,
           budget: float = 90.0) -> Finding:
    """Delta-debug the choice sequence, keeping a case with the same failure class.
    Bounded by `budget` seconds: a minimiser that never returns is worse than a
    slightly larger program."""
    target = f.kind
    base_choices = list(f.choices)
    calls = 0
    deadline = time.time() + budget

    keys = pipelines_for(target)

    def still(cand: list[int]) -> bool:
        nonlocal calls
        if calls >= max_tests or not cand or time.time() > deadline:
            return False
        calls += 1
        case = make_case(seed, f.index, cand)
        res = classify(single_outcomes(case, ctx, keys), case)
        return res is not None and res[0] == target

    cur = base_choices
    if not still(cur):
        # The finding was found in a batch; a single run may differ (e.g. a name
        # clash).  Keep the batch's source, and say so.
        return f
    chunk = max(1, len(cur) // 2)
    while chunk >= 1:
        i = 0
        while i < len(cur):
            cand = cur[:i] + cur[i + chunk:]
            if still(cand):
                cur = cand
            else:
                zeros = cur[:i] + [0] * min(chunk, len(cur) - i) + cur[i + chunk:]
                if len(zeros) == len(cur) and still(zeros):
                    cur = zeros
                else:
                    i += chunk
        chunk //= 2
    case = make_case(seed, f.index, cur)
    return Finding(f.kind, f.index, f.detail, case, cur,
                   f"shrunk from {len(base_choices)} choices to {len(cur)} ({calls} runs)")


def campaign(args: argparse.Namespace, ctx: Ctx) -> int:
    seed = args.seed
    n = args.programs
    cases = [make_case(seed, i) for i in range(n)]
    mut = sum(1 for c in cases if c.mult == 2)
    if ctx.verbose:
        print(f"diff-fuzz: seed {seed}, {n} programs ({n - mut} pure, {mut} array)")
        hist: dict[str, int] = {}
        for c in cases:
            hist[c.shape] = hist.get(c.shape, 0) + 1
        print("  shapes: " + " ".join(f"{k}={v}" for k, v in sorted(hist.items())))
    findings: list[Finding] = []
    skipped = False
    ran: dict[str, int] = {}
    # Chunk the campaign: a 2000-program batch would be one huge C file, and a
    # crash/timeout in it would cost a bisection over all of it.
    size = max(1, args.batch_size)
    chunks = [cases[i:i + size] for i in range(0, n, size)]
    for ci, chunk in enumerate(chunks):
        ok = {}
        if ctx.verbose and len(chunks) > 1:
            print(f"  chunk {ci + 1}/{len(chunks)} ({len(chunk)} programs)")
        for kind in ("eval", "ir", "c"):
            out = run_pipeline(kind, chunk, ctx, ctx.timeout)
            if out.status == "timeout":
                # a transient stall (a compile starved by another job) is not a
                # finding: give the whole batch one longer retry before bisecting
                out = run_pipeline(kind, chunk, ctx, ctx.timeout * 2)
            if out.status == "ok":
                ok[kind] = out
                ran[kind] = ran.get(kind, 0) + len(out.values)
                continue
            if out.status == "skip":
                skipped = True
                reason = next((l.strip() for l in out.stderr.splitlines() if l.strip()), "no toolchain")
                print(f"  {kind}: SKIPPED ({reason})")
                continue
            if ctx.verbose:
                print(f"  {kind}: batch {out.status}; bisecting")
            bad = bisect(kind, chunk, ctx)
            if not bad:
                # The batch failed but neither half did: non-deterministic (a stall)
                # or a failure that needs the whole batch.  Report it rather than
                # losing it.
                first = chunk[0]
                findings.append(Finding(f"{kind}-batch", first.index,
                                        f"the {kind} batch failed ({out.status}) but neither half reproduced it",
                                        first, first.choices))
            for case in bad:
                res = classify(single_outcomes(case, ctx), case)
                kind_name, detail = res if res else (f"{kind}-batch", "the batch failed, the single case did not")
                findings.append(Finding(kind_name, case.index, detail, case, case.choices))

        for f in compare(chunk, ok.get("eval"), ok.get("ir"), ok.get("c")):
            findings.append(f)

    # Shrink each finding (at most a handful).  A generator error is the harness's
    # fault, not a compiler disagreement: shrinking it would just hide the source.
    if args.shrink and findings:
        findings = [f if f.kind.endswith("-error") else shrink(f, ctx, seed)
                    for f in findings[: args.max_findings]]

    if args.pin and findings:
        pin = Path(args.pin)
        pin.mkdir(parents=True, exist_ok=True)
        rows = []
        for f in findings:
            stem = f"{f.kind}-{f.index}"
            (pin / f"{stem}.eval.wiz").write_text(source_of(f.case, "eval"))
            if f.case.mult == 2:
                (pin / f"{stem}.c.wiz").write_text(source_of(f.case, "c"))
            rows.append(f"{stem}\t{f.kind}\t{seed}\t{f.index}\t{','.join(map(str, f.choices))}\t{f.detail}")
        (pin / "pins.tsv").write_text("name\tkind\tseed\tindex\tchoices\tdetail\n" + "\n".join(rows) + "\n")

    for f in findings:
        print(f"\n=== {f.kind} (program {f.index}) ===")
        print(f.detail)
        if f.shrink_note:
            print(f.shrink_note)
        print(f"choices: {','.join(map(str, f.choices))}")
        print("--- source (interpreter) ---")
        print(source_of(f.case, "eval").rstrip())
        if f.case.mult == 2:
            print("--- source (compiled, with the array) ---")
            print(source_of(f.case, "c").rstrip())
        print("--- end ---")

    print(f"\ndiff-fuzz: seed {seed}, {n} programs, "
          f"pipelines {','.join(sorted(ran)) or 'none'}, findings {len(findings)}")
    if ctx.verbose:
        print("  lines: " + " ".join(f"{k}={v}" for k, v in sorted(ran.items())))
    if skipped and not findings:
        print("  one pipeline was skipped (not a pass): see SKIPPED above")
        return 3
    return 1 if findings else 0


# ---------------------------------------------------------------------------
# Replay
# ---------------------------------------------------------------------------


def self_test(ctx: Ctx) -> int:
    """Prove the detector's three reactions on cases whose verdict is known:
    agreement, a panic in the interpreter, and a timeout in the interpreter."""
    ok = True

    def report(name: str, got: str | tuple[str, str] | None, want: str) -> None:
        nonlocal ok
        g = got[0] if isinstance(got, tuple) else got
        good = g is not None and g.startswith(want)
        ok = ok and good
        print(f"  {name}: {'PASS' if good else 'FAIL'} (got {g}, wanted {want})")

    normal = Case(0, "arith", [], ["def p0_out : Nat := Nat.add 2 3"], "p0_out",
                  ["def p0_out : Nat := Nat.add 2 3"], ["p0_out"], 1)
    res = classify(single_outcomes(normal, ctx), normal)
    report("an agreeing program", "agreement" if res is None else res[0], "agreement")

    # A native in a 0 position: correct erasure drops it, a bug runs it and panics.
    # Here it is *not* in a 0 position, which is the known-bad shape.  (Array has an
    # interpreter model now; UInt64 is still a compiled-only extern.)
    bad = "UInt64.toNat (UInt64.add (UInt64.ofNat 1) (UInt64.ofNat 2))"
    panic = Case(1, "bad-native", [], [f"def p1_out : Nat := {bad}"],
                 "p1_out", [f"def p1_out : Nat := {bad}"],
                 ["p1_out"], 1)
    res = classify(single_outcomes(panic, ctx, ("eval",)), panic)
    report("a native the interpreter must not run", res, "eval-panic")

    # A divergence the harness must turn into a timeout, not a hang.  (No retry:
    # this test only has to exercise the timeout path; 3 s is enough for a loop.)
    spin = Case(2, "bad-spin", [], ["def p2_out : Nat := dfSpinN ()"], "p2_out",
                ["def p2_out : Nat := dfSpinN ()"], ["p2_out"], 1)
    res = classify({"eval": run_pipeline("eval", [spin], ctx, 3.0)}, spin)
    report("a divergence the interpreter runs", res, "eval-timeout")

    # And the comparison itself: two outcomes that disagree must be a finding.
    mk = Case(3, "arith", [], ["def p3_out : Nat := 5"], "p3_out",
              ["def p3_out : Nat := 5"], ["p3_out"], 1)
    ev = Outcome("ok", ["5"])
    cc = Outcome("ok", ["6"])
    res = classify({"eval": ev, "c": cc}, mk)
    report("a value disagreement", res, "c-vs-interpreters")
    return 0 if ok else 1


def replay(args: argparse.Namespace, ctx: Ctx) -> int:
    ch = [int(x) for x in args.choices.split(",") if x != ""]
    case = make_case(args.seed, args.index, ch)
    print(source_of(case, "eval").rstrip())
    if case.mult == 2:
        print(source_of(case, "c").rstrip())
    outcomes = single_outcomes(case, ctx)
    for k, o in outcomes.items():
        print(f"{k}: {o.status} {o.values!r}")
        if o.status != "ok":
            print(o.stderr[-2000:])
    res = classify(outcomes, case)
    print("finding:" if res else "agrees:", res)
    return 1 if res else 0


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--seed", type=int)
    ap.add_argument("--programs", type=int)
    ap.add_argument("--fast", action="store_true", help="the fixed 200-program CI run")
    ap.add_argument("--nightly", action="store_true", help="today's seed, 2000 programs")
    ap.add_argument("--timeout", type=float, default=30.0, help="per batch (seconds)")
    ap.add_argument("--batch-size", type=int, default=200,
                    help="programs per generated file/process (default 200)")
    ap.add_argument("--no-shrink", dest="shrink", action="store_false", default=True)
    ap.add_argument("--max-findings", type=int, default=5)
    ap.add_argument("--wiz", default=os.environ.get("WIZ", str(DEFAULT_WIZ)))
    ap.add_argument("--wiz-arg", action="append", default=[],
                    help="a flag for every wiz invocation (repeatable)")
    ap.add_argument("--cache", default=None, help="elaboration cache (default .lake/diff-fuzz/cache)")
    ap.add_argument("--no-cache", action="store_true")
    ap.add_argument("--pin", default=None,
                    help="write each finding's minimised source under this directory")
    ap.add_argument("--keep", action="store_true", help="keep the temporary work directory")
    ap.add_argument("--verbose", "-v", action="store_true")
    ap.add_argument("--replay", action="store_true")
    ap.add_argument("--self-test", action="store_true",
                    help="check that a panic and a timeout are reported")
    ap.add_argument("--index", type=int, default=0)
    ap.add_argument("--choices", default="")
    args = ap.parse_args(argv)

    if args.fast:
        args.seed = FAST_SEED if args.seed is None else args.seed
        args.programs = FAST_PROGRAMS if args.programs is None else args.programs
    elif args.nightly:
        args.seed = int(time.strftime("%Y%m%d")) if args.seed is None else args.seed
        args.programs = NIGHTLY_PROGRAMS if args.programs is None else args.programs
    else:
        args.seed = 1 if args.seed is None else args.seed
        args.programs = 100 if args.programs is None else args.programs

    wiz = args.wiz.split() if " " in args.wiz else [args.wiz]
    if not Path(wiz[0]).exists():
        print(f"diff-fuzz: wiz not found: {wiz[0]}", file=sys.stderr)
        return 2
    # A toolchain flag with an empty value (`--cflags ""`) is meaningful and `wiz`
    # accepts it; a stray empty argument is not.  Keep the former, drop the latter.
    value_flags = {"--cc", "--cflags", "--ldflags", "--libs", "--gmp", "--llc",
                   "--gc-cflags", "--gc-ldflags", "--cache", "--cache-ro",
                   "--cache-verify", "-I", "--sat-solver", "--smt-solver",
                   "--solver-timeout", "--native-fuel"}
    wiz_args = []
    for a in args.wiz_arg:
        if a == "" and not (wiz_args and wiz_args[-1] in value_flags):
            continue
        wiz_args.append(a)
    scratch = ROOT / ".lake" / "diff-fuzz"
    scratch.mkdir(parents=True, exist_ok=True)
    work = Path(tempfile.mkdtemp(prefix="diff-fuzz-", dir=str(scratch)))
    if args.no_cache:
        wiz_args.append("--no-cache")
    else:
        # A per-run cache by default: a persistent one grows with every campaign and
        # a large `~/.cache/wiz` makes each `wiz` startup slow.  `--cache DIR` keeps
        # one for a series of runs.  A cache the caller already named (the test driver
        # passes the suite's warm `--cache ~/.cache/wiz` through `--wiz-arg`) wins:
        # replacing it with a cold per-run cache made the 200-program batch time out.
        if args.cache:
            cache = Path(args.cache)
        elif any(a == "--cache" for a in wiz_args):
            cache = None
        else:
            cache = work / "cache"
        if cache is not None:
            cache.mkdir(parents=True, exist_ok=True)
            wiz_args += ["--cache", str(cache)]
    ctx = Ctx(wiz, wiz_args, ROOT, work, args.timeout, args.verbose)
    try:
        if args.self_test:
            return self_test(ctx)
        if args.replay:
            return replay(args, ctx)
        return campaign(args, ctx)
    finally:
        if not args.keep:
            shutil.rmtree(work, ignore_errors=True)


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
