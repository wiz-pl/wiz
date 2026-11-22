import Wiz
import Tests.Harness
import Tests.Elab

/-!
# The kernel context representation

`Wiz/Core/Check.lean`'s `Ctx` stores its names, quantities and types as arrays indexed
by level (outermost first), and de Bruijn indices read them at `lvl - 1 - ix`;
`Wiz/Core/Usage.lean`'s usage vectors are sparse (they stop after the last variable
used, so `Usage.zeros n = []`). This group pins the representation and the meanings it
must preserve: de Bruijn order, shadowing, quantity checks, and the cases where the
sparse and the interior-zero shapes differ.

The `#eval`-heavy probe and the before/after measurements are in
`docs/notes/kernel-ctx-arrays.md`; they are not run here (the queue lane runs them).
-/

set_option compiler.extract_closed false

open Wiz

namespace Tests.Context

/-! ## Usage vectors -/

def usageTest : IO Unit := do
  let z : Usage ZeroOneMany := Usage.zeros 100
  check z.isEmpty "Usage.zeros 100 is not the empty (sparse) vector"
  let u : Usage ZeroOneMany := Usage.single 100 3
  check (u.length == 4) s!"Usage.single 100 3 has length {u.length}, expected 4"
  check (Usage.getD u 3 == QPoly.const 1) "Usage.single 100 3 does not use index 3 once"
  check (Usage.getD u 0 == []) "Usage.single 100 3 uses an index before 3"
  check (Usage.getD u 4 == []) "Usage.single 100 3 extends past index 3"
  let a : Usage ZeroOneMany := Usage.single 100 0
  let b : Usage ZeroOneMany := Usage.single 100 2
  let s := a + b
  check (s.length == 3) s!"adding usages at 0 and 2 has length {s.length}, expected 3 (an interior zero)"
  check (Usage.getD s 0 == QPoly.const 1) "add lost the usage at 0"
  check (Usage.getD s 1 == []) "add filled the interior index 1"
  check (Usage.getD s 2 == QPoly.const 1) "add lost the usage at 2"
  check ((QPoly.const (0 : ZeroOneMany) • s).isEmpty) "scaling by 0 did not trim the vector"
  check ((([] : Usage ZeroOneMany) + s) == s) "adding the empty usage changed the vector"
  match Usage.join? a a with
  | some j => check (j == a) "join of a usage with itself changed it"
  | none => throw (IO.userError "join of a usage with itself does not exist")
  -- a stopped vector's missing entries are zeros, and a zero still has to pass the
  -- binder's quantity: a linear binder used zero times is an error, not acceptance
  match popUsage "lin" (QPoly.const 1) ([] : Usage ZeroOneMany) with
  | .ok _ => throw (IO.userError "an unused linear binder was accepted (popUsage [] with q = 1)")
  | .error (.quantityMismatch _ _ used) =>
    check (used == "0") s!"the dropped linear binder reported usage {used}, expected 0"
  | .error e => throw (IO.userError s!"the dropped linear binder reported the wrong error: {e}")
  match popUsage "erased" (QPoly.const 0) ([] : Usage ZeroOneMany) with
  | .ok u => check u.isEmpty "popping an unused erased binder did not return []"
  | .error e => throw (IO.userError s!"an unused erased binder was rejected: {e}")
  match popUsage "unrestricted" (QPoly.const ZeroOneMany.many) ([] : Usage ZeroOneMany) with
  | .ok u => check u.isEmpty "popping an unused unrestricted binder did not return []"
  | .error e => throw (IO.userError s!"an unused unrestricted binder was rejected: {e}")
  -- 1 ⊔ 0 = ω in {0, 1, ω}: a case branch that uses a linear variable and one that does
  -- not must join to ω, so the branch agreement check sees it
  match Usage.join? (Usage.single 2 0) (Usage.zeros 2) with
  | some j => check (Usage.getD j 0 == QPoly.const ZeroOneMany.many) s!"join of 1 and a missing entry is {Usage.getD j 0}, expected ω"
  | none => throw (IO.userError "join of 1 and a missing entry does not exist")

/-! ## The context arrays -/

def ctx : Ctx ZeroOneMany :=
  ({ globals := {} } : Ctx ZeroOneMany)
    |>.bind "x" (QPoly.const 1) (.sort 0)
    |>.bind "y" (QPoly.const 0) (.sort 1)

def ctxTest : IO Unit := do
  check (ctx.lvl == 2) s!"context size: {ctx.lvl}, expected 2"
  check (ctx.types.size == ctx.lvl) "the types array and lvl disagree"
  check (ctx.names.size == ctx.lvl) "the names array and lvl disagree"
  check (ctx.qtys.size == ctx.lvl) "the quantities array and lvl disagree"
  check (ctx.nameAt? 0 == some "y") "index 0 is not the innermost binder"
  check (ctx.nameAt? 1 == some "x") "index 1 is not the outermost binder"
  check (ctx.nameAt? 2 == none) "an index past the end is not out of scope"
  check (ctx.prettyNames == ["y", "x"]) s!"prettyNames: {repr ctx.prettyNames}, expected [y, x]"
  check (ctx.qtyAt? 0 == some (QPoly.const 0)) "the innermost quantity is wrong"
  check (ctx.qtyAt? 1 == some (QPoly.const 1)) "the outermost quantity is wrong"
  match ctx.typeAt? 0, ctx.typeAt? 1 with
  | some (.sort 1), some (.sort 0) => pure ()
  | _, _ => throw (IO.userError "the array is not in level order (index 0 should be the outermost type)")
  -- shadowing: the same name at two levels keeps both entries, and de Bruijn order
  let shadowed : Ctx ZeroOneMany :=
    ({ globals := {} } : Ctx ZeroOneMany)
      |>.bind "x" (QPoly.const 0) (.sort 0)
      |>.bind "x" (QPoly.const 1) (.sort 1)
  check (shadowed.nameAt? 0 == some "x" && shadowed.nameAt? 1 == some "x")
    "a shadowing name was dropped"
  check (shadowed.prettyNames == ["x", "x"]) "the shadowed names are not innermost first"
  match shadowed.typeAt? 0 with
  | some (.sort 1) => pure ()
  | _ => throw (IO.userError "the innermost shadowed binder's type is wrong")

/-! ## A deep context, through the frontend -/

def prelude : String := "inductive N where\n  | z\n"

def arrows (n : Nat) : String := " → ".intercalate (List.replicate n "N")

def binders (n : Nat) (q : String) (start : Nat := 0) : String :=
  " ".intercalate ((List.range n).map fun i => s!"({q} x{start + i})")

/-- Every binder `ω`; only the innermost is used: usage is `[1]` at every pop (sparse). -/
def deepLast (n : Nat) : String :=
  s!"def deepLast : {arrows n} → N := fun {binders n "ω"} => x{n - 1}\n"

/-- Every binder `ω`; only the outermost is used: usage is `[0, …, 0, 1]` (interior
zeros, no sparse win, but the de Bruijn order must stay right). -/
def deepFirst (n : Nat) : String :=
  s!"def deepFirst : {arrows n} → N := fun {binders n "ω"} => x0\n"

/-- The outermost binder is linear and used once; every other binder is `ω` and unused. -/
def deepLinear (n : Nat) : String :=
  s!"def deepLinear : (1 x0 : N) → {arrows (n - 1)} → N := fun (1 x0) {binders (n - 1) "ω" 1} => x0\n"

def shadow : String := "def shadow : N → N → N := fun (ω x) => fun (ω x) => x\n"

def dropLin : String := "def dropLin (1 x : N) : N := N.z\n"

def deepTest : IO Unit := do
  Tests.Elab.ok (prelude ++ deepLast 64)
  Tests.Elab.ok (prelude ++ deepFirst 64)
  Tests.Elab.ok (prelude ++ deepLinear 64)
  Tests.Elab.ok (prelude ++ shadow)

def deepRejectTest : IO Unit := do
  Tests.Elab.fails (prelude ++ dropLin) "quantity"

def group : Group where
  name := "context"
  exercise := "the kernel's context representation (arrays + sparse usages)"
  shard := "library"
  cases := [
    { name := "usage vectors are sparse: zeros is empty, add pads, scale 0 trims, join is pointwise",
      run := fun _ => usageTest },
    { name := "Ctx arrays keep de Bruijn order, level order, and shadowing",
      run := fun _ => ctxTest },
    { name := "a deep context checks (innermost used, outermost used, linear outermost)",
      run := fun _ => deepTest },
    { name := "a deep context still rejects a dropped linear variable",
      run := fun _ => deepRejectTest }]

builtin_initialize registerGroup group

end Tests.Context
