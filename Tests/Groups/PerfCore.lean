import Wiz
import Tests.Harness

/-!
# `perf-core`: the core counters, and two scaling cases

CORE-2.1 (`wiz-notes/roadmap/wiz-core-next.md` M2.1). A group that needs no toolchain: it
calls the core evaluator and conversion checker in this process, so it runs anywhere
`tests` runs. Three kinds of case:

* **The counters** (`Wiz.Stats`) are read after a known amount of work: the closed-value
  repeat count for a definition used `n` times, and the head-type rebuilds for `n`
  comparisons at a global-headed neutral type. Both are printed, and bounded loosely.
* **Two scaling cases**, `n` versus `2n`, via `checkScaling` (`Tests/Harness.lean`), which
  subtracts the fixed floor and prints the measured pair.

## The two shapes, and why they are quadratic today

1. **Per-use instantiation of a closed definition.** `Eval.lean`'s `.const` clause builds a
   fresh `memoThunk` per occurrence, and `Term.instValue`'s `instCache` holds only levels
   `0/1/2` and a *non-memoising* `Thunk` (`instCache` stores `Thunk.mk`, not `memoThunk`).
   A nullary definition whose body is `n` `let`s, used `n` times at level `3`, is therefore
   instantiated *and evaluated* `n` times with `n` work each: `O(n²)`. CORE-2.2 (one
   shared closed value per `(name, levels)`) makes the second and later uses `O(1)`.
   The counter `closedEval / closedMiss` is exactly that repeat count.
2. **`headType` re-evaluating a global's type.** `Conv.headType` for `.global n us` runs
   `eval g [] (d.type.instLevels …)` on every call, and conversion asks for a type on every
   `isProp` (`typeSort?` → `inferNe` → `headType`). A local whose type is `H A`, with `H`'s
   declared type a Π-telescope of `n` domains, compared `n` times, pays `n` per comparison:
   `O(n²)`. CORE-2.3 memoises `headType` per `(name, levels)`, making each call `O(1)`.

## Bounds

The bounds are **loose on purpose**: they are pinning the *shape*, not a machine. Measured
on this group before CORE-2.2–2.4 (2026-11-23, node `win2`, best of three, net of the
floor; `tests --run-case perf-core N`):

| case | n | n (ms net) | 2n (ms net) | ratio |
|---|---:|---:|---:|---:|
| closed value, per-use instantiation | 2000 | 580 | 2303 | 3.97× |
| head type, global-headed neutral | 1500 | 70 | 292 | 4.17× |

(The ratios have been 3.2–4.2 across runs; the load on a shared node moves each sample
but not the shape.) The counters for the same shapes (the case output): `closedEval 300,
closedMiss 1` for 300 uses of one definition (repeat 300×), and `headType 600` for 200
comparisons (3 per `conv`: two `isProp` asks and the neutral comparison's local head).

`checkScaling` is therefore called with `bound 6` (and a small slack): it passes the
current quadratic shape (a cubic regression would be ~8×) and, once CORE-2.2/2.3 land,
the same case measures ~2× — CORE-2.5 lowers the bound to 3 then. In-process numbers are
deterministic enough (same allocation profile, best of three) that the noise is a few
percent, far below the 6× headroom.

## What the counters cost when they are off

The caller pays one opaque call per site even with `WIZ_STATS` unset; the case
`off-path cost of a counter call` times that directly (n = 3M): a no-op opaque of the
same shape is **8 ns/call**, `Stats.countedVal` **20 ns**, and reading the cell at the
call site (what a real site writes) **21 ns**. `lib/Nat.wiz` makes **6.2 M** counter
calls (`WIZ_STATS=1 wiz check lib/Nat.wiz | grep stat`), so the direct cost is ~0.12 s.
The whole-file A/B against the base commit 6d065b579 (user CPU, 15 paired rounds,
`lib/Nat.wiz`) is **+3.6 % median** (min +4.1 %); the same-binary A/A control is 1.000,
so that is real, not a protocol artefact. The difference beyond the 8 ns call floor is
the loss of tail calls in `whnf`/`conv` (their result now flows through the wrapper).
If a release budget needs the last 3 %, compile the call sites out (CORE-2.5); the
`WIZ_STATS` mode is a development measurement, per the note's M2.1 risk.
-/

set_option compiler.extract_closed false

open Wiz

namespace Tests.PerfCore

/-! ### Shape 1: a closed definition with an `n`-node body, used `n` times at level 3

`def big.{u} : Type u := let y₁ := Type u; … let yₙ := Type u; yₙ`
(a nullary definition, so a use is one `.const`: no application work to confuse the
measurement). The body has `n` nodes; `instCache` has no entry for level `3`, so each use
instantiates and evaluates it again. -/

/-- The value of `big`: `n` nested `let`s, each value the closed `Type u`, ending in the
innermost binder. Size `2n + 1` nodes. -/
def bigBody (n : Nat) : Term Unit :=
  (List.range n).foldl (fun acc _ =>
    .letE "y" (.qlit ()) (.sort (.param "u")) (.sort (.param "u")) acc) (.var 0)

/-- `Globals` with `big.{u} : Type u` — inserted unchecked (`Globals.insert` does not type
check; the evaluator is what this case measures). -/
def bigGlobals (n : Nat) : Globals Unit :=
  Globals.insert ({} : Globals Unit)
    { name := "big", levelParams := ["u"]
      type := .sort (.succ (.param "u")), value := some (bigBody n) }

/-- `n` occurrences of `big.{3}`, in a right-nested pair. Each occurrence is one
`.const`; the pair chain is `O(n)` to evaluate and quote, which is the floor. -/
def bigUses (n : Nat) : Term Unit :=
  (List.range n).foldr (fun _ acc => .pair (.const "big" [(3 : Level)]) acc) (.sort 0)

/-- Force every glued value in the result: `quote` keeps a definition's name and does not
force its body, so the read-back alone would not count the work. `whnf` is the forcing
step (and is itself counted). -/
partial def forceAll : Val Unit → IO Unit
  | v => match whnf v with
    | .pair a b => do forceAll a; forceAll b
    | _ => pure ()

/-- Force the evaluation of all `n` uses. -/
def runBig (n : Nat) : IO Unit := do
  let g := bigGlobals n
  forceAll (eval g [] (bigUses n))

/-- `big` used `n` times: `closedEval` counts the evaluations of the body, `closedMiss`
the first one per `(name, levels)` (so `closedEval / closedMiss` is the repeat count). -/
def bigCounters (n : Nat) : IO Unit := do
  Wiz.Stats.reset
  Wiz.Stats.enable
  runBig n
  let ev ← Wiz.Stats.get Wiz.Stats.cells.closedEval
  let miss ← Wiz.Stats.get Wiz.Stats.cells.closedMiss
  let cst ← Wiz.Stats.get Wiz.Stats.cells.evalConst
  IO.println s!"  closed value: {n} uses → closedEval {ev}, closedMiss {miss} (repeat {ev / max 1 miss}×), evalConst {cst}"
  -- a use is one `.const`; more than one body evaluation per use is a regression (the
  -- extra work a shared closed value would remove is what the repeat count prints)
  check (miss ≥ 1) "the first closed-value computation is counted"
  check (ev ≤ n) s!"at most one body evaluation per use ({ev} > {n})"

/-! ### Shape 2: `n` comparisons at a global-headed neutral type with an `n`-node type

`H : D → Type 1` where `D` is a type term of `n` `let`s ending in `Type` (a `Π` telescope
would not do: `eval` of a `Π` evaluates only the domain and captures the codomain as a
closure, so a telescope is O(1) to evaluate). A local `x : H A`; comparing `x` with itself
`n` times calls `isProp (H A)` each time, which reaches `headType (.global H [])` and
re-evaluates `H`'s whole type — the `let` chain — `n` nodes per call. -/

/-- A type term of size `n`: `n` nested `let`s, each value `Type`, ending in `Type`.
`eval` walks every `let`, so evaluating the term costs `n`. -/
def bigDomain (n : Nat) : Term Unit :=
  (List.range n).foldl (fun acc _ =>
    .letE "y" (.qlit ()) (.sort 0) (.sort 0) acc) (.sort 0)

/-- `H : D → Type 1`, an axiom (no value: only its type is read). -/
def headGlobals (n : Nat) : Globals Unit :=
  Globals.insert ({} : Globals Unit)
    { name := "H", value := none
      type := .pi "x" .default (.qlit ()) (bigDomain n) (.sort 1) .hole }

/-- `n` conversions of a local at type `H A` with itself. -/
def runHead (n : Nat) : IO Unit := do
  let g := headGlobals n
  let T : Val Unit := vApp g (.neutral (.global "H" []) #[]) (.sort 0)
  let tys : Array (VTy Unit) := #[T]
  let x : Val Unit := .neutral (.local 0) #[]
  for _ in [0:n] do
    unless conv g tys T x x do throw (IO.userError "x ≡ x was false")

/-- The conversion/type counters for `n` such comparisons. -/
def headCounters (n : Nat) : IO Unit := do
  Wiz.Stats.reset
  Wiz.Stats.enable
  runHead n
  let ht ← Wiz.Stats.get Wiz.Stats.cells.headType
  let ip ← Wiz.Stats.get Wiz.Stats.cells.isProp
  let ok ← Wiz.Stats.get Wiz.Stats.cells.convOk
  IO.println s!"  head type: {n} comparisons → convOk {ok}, isProp {ip}, headType {ht}"
  check (ok == n) s!"one conv per comparison ({ok} ≠ {n})"
  -- conversion asks for the sort of `H A` (twice per `conv` today); each such ask
  -- reaches `headType` for the global, which is the work CORE-2.3 removes
  check (ht ≥ n) s!"headType is reached at least once per comparison ({ht} < {n})"

/-! ### The counter's off-path cost

The default path pays one opaque call per counter site. A `/usr/bin/time` A/B on a whole
file mixes that with code layout, so this case times the call itself: `plainVal` is a
no-op with the same shape as `Stats.countedVal` (one `Cell`, one `Val`, returns the
`Val`), and the third loop also reads `Stats.cells.whnf` inside the loop, which is what a
call site writes. -/

/-- The control for `Stats.countedVal`: the same signature, no counter. -/
unsafe def plainValImpl {R : Type} (c : Wiz.Stats.Cell) (x : Val R) : Val R := x
@[implemented_by plainValImpl] opaque plainVal {R : Type} (c : Wiz.Stats.Cell) (x : Val R) : Val R

/-- Call `f` `n` times on a `Val`, feeding the result back so nothing is dropped; returns
nanoseconds per call. -/
def timeCalls (f : Unit → Val Unit) (n : Nat) : IO Nat := do
  let mut x : Val Unit := .sort 0
  let mut i := 0
  let t0 ← IO.monoNanosNow
  while i < n do
    x := f ()
    i := i + 1
  let t1 ← IO.monoNanosNow
  match x with
  | .sort _ => pure ((t1 - t0) / n)
  | _ => throw (IO.userError "unreachable")

/-- `plainVal` and `Stats.countedVal`, both off, on the same loop. -/
def counterCost : IO Unit := do
  Wiz.Stats.reset
  let n := 3000000
  let c := Wiz.Stats.cells.whnf
  let _ ← timeCalls (fun _ => plainVal c (.sort 0)) 200000   -- warm
  let plain ← timeCalls (fun _ => plainVal c (.sort 0)) n
  let counted ← timeCalls (fun _ => Wiz.Stats.countedVal c (.sort 0)) n
  let atSite ← timeCalls (fun _ => Wiz.Stats.countedVal Wiz.Stats.cells.whnf (.sort 0)) n
  IO.println s!"  off-path call: plain {plain} ns, countedVal {counted} ns, call-site cell {atSite} ns (n {n})"
  -- loose: this catches a call that allocates or a cell read that became a thunk force,
  -- not a few nanoseconds either way
  check (atSite ≤ 200) s!"a counter call is far more expensive than a call ({atSite} ns)"

/-! ### The group -/

def group : Group where
  name := "perf-core"
  shard := "scaling"
  exercise := "CORE-2.1: core counters and two scaling cases"
  cases := [
    -- deterministic counters first: they are the M2.1/M2.2/M2.3 numbers, printed
    { name := "closed value: the repeat count is printed (>1 before CORE-2.2, 1 after)",
      run := fun _ => bigCounters 300 },
    { name := "head type: the rebuild count is printed (isProp → inferNe → headType per conv)",
      run := fun _ => headCounters 200 },
    { name := "off-path cost of a counter call is printed (plain vs counted vs call-site cell)",
      run := fun _ => counterCost },
    -- the two shapes, n vs 2n. Bound 6: see the table in the module comment (measured
    -- 3.2–4.2× while quadratic; cubic would be ~8×). Slack 50 ms is noise, not subsidy.
    { name := "n vs 2n uses of one closed definition (quadratic until CORE-2.2)",
      run := fun _ => do
        let _ ← checkScaling "closed value uses" runBig 2000 6 50 },
    { name := "n vs 2n comparisons at a global-headed neutral type (quadratic until CORE-2.3)",
      run := fun _ => do
        let _ ← checkScaling "global-headed head type" runHead 1500 6 50 }
  ]

builtin_initialize registerGroup group

end Tests.PerfCore
