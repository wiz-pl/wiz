import Std.Data.HashMap
import Wiz.Core.Level
import Wiz.Core.Value

/-!
# Core evaluator counters (`--stats`)

A small, always-compiled-in counter layer for the core evaluator, so that the changes of
CORE-2.2–2.4 (a shared closed value, memoised head types, a cheap failure path) have
numbers to move. It is **off by default**: `--stats` on the `wiz` command or the test
driver enables it for that process (they print the counters at exit), and a test may
enable it explicitly (`Wiz.Stats.enable`). Like every other input, it is a flag and not
an environment variable: a program's output must not depend on the process environment.

The counters are measurement, not semantics: nothing here is read by `eval`, `conv`,
`quote` or the checker unless the flag is set, and no result depends on them. Every call
site is a single opaque call (`countedVal`, `convOutcome`, …); the flag test is inside that
call, so the compiled hot path has no branch added at the call site. See
`wiz-notes/roadmap/wiz-core-next.md` M2.1 for why these and not others.

## The counters (one place; this is the list the reports and tests use)

| name | incremented at | what it counts |
|---|---|---|
| `whnf` | `Eval.whnf` | `whnf` calls |
| `inst` | `Eval.Closure.inst`, `Closure.inst2` | closures instantiated (β-redexes evaluated) |
| `evalConst` | `Eval.eval`, the `.const` clause | `const` terms evaluated |
| `closedEval` | `Eval.eval`, the closed-definition thunk | closed definition values *computed* (forced) |
| `closedMiss` | the same | of those, the first computation of a `(name, levels)` pair |
| `convOk` / `convFail` | `Conv.conv` | conversion attempts, by outcome |
| `convTyOk` / `convTyFail` | `Conv.convTy` | type conversion attempts, by outcome |
| `headType` | `Conv.headType` | neutral head types computed (a `.global` one re-evaluates its type) |
| `isProp` / `isPropTrue` | `Conv.isProp` | proposition tests, and those that answered `true` |
| `zonk` | `Elab.zonk` | zonking passes (elaborator only) |

`closedEval / closedMiss` is the "repeat count" of M2.2: before a shared closed value it
is the number of occurrences of a definition at one `(name, levels)` (the work a cache
would save); after it should be 1.

`inferNe` and `typeSort?` are deliberately **not** counted: they are as hot as `isProp`
and only CORE-2.3 needs them; adding a counter there is two lines when it does.

The cache probe behind `closedEval` is a plain hash set of `(name, levels)` held only
while counting; it is not a cache and is not read by the evaluator.
-/

namespace Wiz.Stats

/-- One counter cell. -/
abbrev Cell := IO.Ref UInt64

/-- A cell used only to give `Cells` an `Inhabited` instance. -/
initialize dummy : IO.Ref UInt64 ← IO.mkRef 0

instance : Inhabited Cell := ⟨dummy⟩

initialize enabledRef : IO.Ref Bool ← IO.mkRef false

/-- The named counters. The doc comment on each is the report line's name. -/
structure Cells where
  /-- `whnf` calls. -/
  whnf : Cell
  /-- closures instantiated (`Closure.inst` and `inst2`). -/
  inst : Cell
  /-- `.const` terms evaluated. -/
  evalConst : Cell
  /-- closed definition values computed (forced). -/
  closedEval : Cell
  /-- first computation of a `(name, levels)` pair. -/
  closedMiss : Cell
  /-- `conv` attempts that returned `true`. -/
  convOk : Cell
  /-- `conv` attempts that returned `false`. -/
  convFail : Cell
  /-- `convTy` attempts that returned `true`. -/
  convTyOk : Cell
  /-- `convTy` attempts that returned `false`. -/
  convTyFail : Cell
  /-- neutral head types computed. -/
  headType : Cell
  /-- proposition tests. -/
  isProp : Cell
  /-- proposition tests that answered `true`. -/
  isPropTrue : Cell
  /-- zonking passes. -/
  zonk : Cell
  deriving Inhabited

initialize cells : Cells ← do
  pure { whnf := (← IO.mkRef 0), inst := (← IO.mkRef 0)
         evalConst := (← IO.mkRef 0), closedEval := (← IO.mkRef 0), closedMiss := (← IO.mkRef 0)
         convOk := (← IO.mkRef 0), convFail := (← IO.mkRef 0)
         convTyOk := (← IO.mkRef 0), convTyFail := (← IO.mkRef 0)
         headType := (← IO.mkRef 0), isProp := (← IO.mkRef 0), isPropTrue := (← IO.mkRef 0)
         zonk := (← IO.mkRef 0) }

/-- The `(name, levels)` pairs a closed value has already been computed at. Only touched
while counting; it is a probe, not a cache. -/
initialize closedSeen : IO.Ref (Std.HashMap (Name × List Level) Unit) ← IO.mkRef {}

/-! ### Turning it on and reading it -/

/-- Start counting (the `--stats` flag, or a test that enables it explicitly). -/
def enable : IO Unit := enabledRef.set true

/-- Is counting on? (A caller that wants to turn it on reads this first; nothing in the
evaluator does.) -/
def isEnabled : IO Bool := enabledRef.get

/-- Zero every counter and forget the closed-value probe. -/
def reset : IO Unit := do
  for c in [cells.whnf, cells.inst, cells.evalConst, cells.closedEval,
            cells.closedMiss, cells.convOk, cells.convFail, cells.convTyOk, cells.convTyFail,
            cells.headType, cells.isProp, cells.isPropTrue, cells.zonk] do
    c.set 0
  closedSeen.set {}

/-- One counter's value. -/
def get (c : Cell) : IO Nat := do pure (← c.get).toNat

/-- `(name, value)` for every counter, in the order of the table above. -/
def read : IO (List (String × Nat)) := do
  let one (n : String) (c : Cell) : IO (String × Nat) := do pure (n, ← get c)
  pure [← one "whnf" cells.whnf, ← one "inst" cells.inst,
        ← one "evalConst" cells.evalConst, ← one "closedEval" cells.closedEval,
        ← one "closedMiss" cells.closedMiss, ← one "convOk" cells.convOk,
        ← one "convFail" cells.convFail, ← one "convTyOk" cells.convTyOk,
        ← one "convTyFail" cells.convTyFail, ← one "headType" cells.headType,
        ← one "isProp" cells.isProp, ← one "isPropTrue" cells.isPropTrue,
        ← one "zonk" cells.zonk]

/-- Print every counter as `stat<TAB>name<TAB>value` on stderr, if counting is on. Called
at process exit by `wiz` and by the test driver, so `wiz --stats check f.wiz` prints them
once the file is elaborated. -/
def report : IO Unit := do
  unless (← enabledRef.get) do return
  for (n, v) in ← read do
    IO.eprintln s!"stat\t{n}\t{v}"

/-! ### The call-site primitives

Each takes the cells it bumps as explicit arguments, so
a call site is `Stats.countedVal Stats.cells.whnf (…)` (see `countedVal` for why this
shape and not a `Unit` bump), with no flag test at the call site. -/

/-- Count one call of `c` and return `x`, for a `Val` result (`whnf`, `eval`, `inst`,
a closed value). `opaque` (the compiler has no body to see, so the call cannot be
removed) and **monomorphic**: a `counted {α} [Inhabited α] (x : α) : α` makes every call
site build an `Inhabited α` default (a `Val` allocation per `whnf`, measured +12 % on
`lib/Nat.wiz`), and a `Unit`-returning bump is dropped by the compiler (measured: all
counts 0). This shape costs one call, one flag load, one branch, no allocation; its
`Inhabited` default is resolved once, at declaration. -/
unsafe def countedValImpl {R : Type} (c : Cell) (x : Val R) : Val R := unsafeBaseIO do
  if ← enabledRef.get then c.modify (· + 1)
  pure x
@[implemented_by countedValImpl] opaque countedVal {R : Type} (c : Cell) (x : Val R) : Val R

/-- `countedVal` for an `Option (Val R)` result (`headType`). -/
unsafe def countedOptValImpl {R : Type} (c : Cell) (x : Option (Val R)) : Option (Val R) :=
  unsafeBaseIO do
    if ← enabledRef.get then c.modify (· + 1)
    pure x
@[implemented_by countedOptValImpl] opaque countedOptVal {R : Type} (c : Cell)
    (x : Option (Val R)) : Option (Val R)

/-- `countedVal` for `Term.spine`'s result (`zonk`): `Term`'s `Inhabited` default is
`.var 0`, so this allocates nothing either. -/
unsafe def countedSpineImpl {R : Type} (c : Cell) (x : Term R × List (Term R)) :
    Term R × List (Term R) := unsafeBaseIO do
  if ← enabledRef.get then c.modify (· + 1)
  pure x
@[implemented_by countedSpineImpl] opaque countedSpine {R : Type} (c : Cell)
    (x : Term R × List (Term R)) : Term R × List (Term R)

/-- Count a `conv`/`convTy` attempt in `ok` or `fail` by the result, and return it. -/
unsafe def convOutcomeImpl (ok fail : Cell) (r : Bool) : Bool := unsafeBaseIO do
  if ← enabledRef.get then
    (if r then ok else fail).modify (· + 1)
  pure r
@[implemented_by convOutcomeImpl] opaque convOutcome (ok fail : Cell) (r : Bool) : Bool

/-- Count an `isProp` call, and a `true` answer, and return the answer. -/
unsafe def isPropOutcomeImpl (c ct : Cell) (r : Bool) : Bool := unsafeBaseIO do
  if ← enabledRef.get then
    c.modify (· + 1)
    if r then ct.modify (· + 1)
  pure r
@[implemented_by isPropOutcomeImpl] opaque isPropOutcome (c ct : Cell) (r : Bool) : Bool

/-- Count that a closed definition's value was computed at `(n, us)`: `total` always, and
`miss` on the first time in this process (so `total / miss` is the repeat count of M2.2).
Wraps the thunk's `eval`, so the count is exactly the computations that a shared closed
value would serve (CORE-2.2). -/
unsafe def closedEvalImpl {R : Type} (total miss : Cell) (n : Name) (us : List Level)
    (v : Val R) : Val R := unsafeBaseIO do
  if ← enabledRef.get then
    total.modify (· + 1)
    let key := (n, us)
    let m ← closedSeen.get
    if !m.contains key then
      miss.modify (· + 1)
      closedSeen.set (m.insert key ())
  pure v
@[implemented_by closedEvalImpl] opaque closedEval {R : Type} (total miss : Cell) (n : Name)
    (us : List Level) (v : Val R) : Val R

end Wiz.Stats
