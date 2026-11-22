import Wiz.Core.QPoly

/-!
# Usage vectors

The QTT checker computes, for each subterm, how much it uses each variable in scope.
That is a vector of quantities aligned with the context: here a `List` whose head is
the innermost variable (de Bruijn index 0), matching the de Bruijn indices of `Ctx` in
`Wiz.Core.Check`.

The vector is **sparse**: it stops after the last variable the term uses, and the
variables after the end are unused (quantity `0`). `Usage.zeros n` is `[]` for every
`n`, rather than a list as long as the context (`docs/stages/20-selfhost-checks-itself.md`
§20f: a third of the kernel's allocations). A zero *before* a used variable stays as
`[]`: dropping it would shift the indices of everything after it.

Each entry is a quantity *polynomial* (`Wiz.Core.QPoly`). Until stage 4d's quantity
variables they are all constants, so you can read `QPoly R` as "a quantity".

Leaving a binder pops the head and compares it against the binder's declared
quantity -- see `popUsage` in `Wiz.Core.Check`. A vector that has already stopped is
all zeros; popping it checks the missing zero against the declared quantity (so a
linear binder used zero times is still an error) and yields the empty vector.

-/

namespace Wiz

abbrev Usage (R : Type) := List (QPoly R)

namespace Usage

variable {R : Type} [QRig R] [DecidableEq R]

/-- Drop the trailing zeros: the representation keeps no entry after the last variable
used. (Interior zeros stay: dropping one would shift the indices after it.) -/
def trim : Usage R → Usage R
  | [] => []
  | x :: xs =>
    let xs := trim xs
    if xs.isEmpty && x == [] then [] else x :: xs

/-- Nothing used, in a context of `n` variables. The size is not recorded: every
variable after the (empty) end is unused. -/
def zeros (_n : Nat) : Usage R := []

/-- The variable at index `ix` used once, in a context of `n` variables (`[]` when `ix`
is out of scope, as before). -/
def single (n ix : Nat) : Usage R :=
  if ix < n then List.replicate ix [] ++ [QPoly.const 1] else []

/-- The usage at index `ix` (`0`, unused, when the vector stops before it). -/
def getD (u : Usage R) (ix : Nat) : QPoly R := u[ix]?.getD []

private def addAux : Usage R → Usage R → Usage R
  | [], v => v
  | u, [] => u
  | a :: u, b :: v => (a + b) :: addAux u v

/-- Pointwise sum: both subterms run. A vector that stops earlier is extended by zeros. -/
def add (u v : Usage R) : Usage R := trim (addAux u v)

/-- Scale by `q`: the subterm's result is consumed `q` times. -/
def scale (q : QPoly R) (u : Usage R) : Usage R := trim (u.map (q * ·))

instance : Add (Usage R) := ⟨add⟩
instance : HSMul (QPoly R) (Usage R) (Usage R) := ⟨scale⟩

/-- The pointwise least upper bound of two usages, for the branches of a case:
`none` when some variable's two usages have no join. The missing entries of a sparse
vector are `0`, so a join against a stopped vector is a join against explicit zeros (as
the old same-length vectors had): `0 ⊔ 1 = ω` in `{0, 1, ω}`, which is what makes a case
whose branches disagree on a linear variable a quantity error. -/
private def joinAux : Usage R → Usage R → Option (Usage R)
  | [], [] => some []
  | [], b :: v => do
    let j ← QPoly.join? [] b
    let rest ← joinAux [] v
    pure (j :: rest)
  | a :: u, [] => do
    let j ← QPoly.join? a []
    let rest ← joinAux u []
    pure (j :: rest)
  | a :: u, b :: v => do
    let j ← QPoly.join? a b
    let rest ← joinAux u v
    pure (j :: rest)

def join? (u v : Usage R) : Option (Usage R) :=
  match joinAux u v with
  | some j => some (trim j)
  | none => none

end Usage

end Wiz
