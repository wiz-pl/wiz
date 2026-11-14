import Wiz.Rig.Instances
import Tests.Harness

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

open Wiz

namespace Tests.Rig

/-- Brute-force the `QRig` laws over a finite list of elements. This catches wrong
tables at runtime; Exercise 0.2 proves them once and for all. -/
def lawsHold {R : Type} [QRig R] [DecidableEq R] [ToString R] (elems : List R) : IO Unit := do
  let le := QRig.le (R := R)
  for a in elems do
    check (0 + a == a) s!"0 + {a} ≠ {a}"
    check (1 * a == a && a * 1 == a) s!"1 is not a unit for {a}"
    check (0 * a == 0 && a * 0 == 0) s!"0 does not annihilate {a}"
    check (le a a) s!"le not reflexive at {a}"
    for b in elems do
      check (a + b == b + a) s!"{a} + {b} ≠ {b} + {a}"
      for c in elems do
        check (a + b + c == a + (b + c)) s!"+ not associative at {a} {b} {c}"
        check (a * b * c == a * (b * c)) s!"* not associative at {a} {b} {c}"
        check (a * (b + c) == a * b + a * c) s!"left distributivity fails at {a} {b} {c}"
        check ((a + b) * c == a * c + b * c) s!"right distributivity fails at {a} {b} {c}"
        if le a b && le b c then check (le a c) s!"le not transitive at {a} {b} {c}"
        for d in elems do
          if le a b && le c d then
            check (le (a + c) (b + d)) s!"+ not monotone at {a} {b} {c} {d}"
            check (le (a * c) (b * d)) s!"* not monotone at {a} {b} {c} {d}"

open ZeroOneMany in
def group : Group where
  name := "rig"
  parallel := true
  exercise := "Exercises 0.1, 0.2"
  cases := [
    { name := "Unit laws", run := fun _ => lawsHold [()] },
    { name := "Nat laws (0..4)", run := fun _ => lawsHold (List.range 5) },
    { name := "ZeroOneMany: 1 + 1 = ω", run := fun _ => checkEq many (one + one) },
    { name := "ZeroOneMany: ω * 0 = 0", run := fun _ => checkEq zero (many * zero) },
    { name := "ZeroOneMany: 1 * ω = ω", run := fun _ => checkEq many (one * many) },
    { name := "ZeroOneMany: 0 not ≤ 1 (linear means exactly once)",
      run := fun _ => check (!QRig.le zero one) "a linear variable must not be droppable" },
    { name := "ZeroOneMany: 1 ≤ ω", run := fun _ => check (QRig.le one many) "ω should accept one use" },
    { name := "ZeroOneMany laws", run := fun _ => lawsHold [zero, one, many] }
  ]

/-- This module's test groups, which `Tests/Main.lean` runs: one per line, in sorted
order, so that branches adding groups rarely touch the same lines. A new group also
needs a shard in `.github/test-shards.json` (CI checks). -/
def groups : List Group :=
  group ::
  []

end Tests.Rig
