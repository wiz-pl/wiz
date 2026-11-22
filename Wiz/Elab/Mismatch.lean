import Wiz.Core.Check

/-!
# Structured mismatches

A failed unification is reported to the user as a type mismatch. The message's two
printed types are enough to recognise *that* something is wrong, but not *where* in a
type the difference is, nor which kind of mistake it is (a missing argument, a binder
that differs, a universe, a hole). This module carries that structure out of unification
without touching `Unify.lean` (its hot path): `unifyAt0` (`Elab/Term.lean`) quotes the
two types after a failed unification and builds a `Mismatch` from them.

`Mismatch` is deliberately non-generic: the terms are printed where the elaborator still
has the context's names, so a message (and the language server's diagnostic data) can be
built without an `R` in hand.
-/

namespace Wiz

/-- The path from a type to the first subterm where expected and inferred differ: the
argument indices along the way (`[]` at the head), the two printed subterms, and what
kind of difference it is (`head`, `argument`, `universe`, `binder`, `arity`, `hole`). -/
structure Mismatch where
  expected : String := ""
  inferred : String := ""
  path : List Nat := []
  expectedAt : String := ""
  inferredAt : String := ""
  kind : String := "head"
  reason : String := ""
  deriving Repr, Inhabited, BEq

/-- `argument 2`, `argument 0 of argument 1`. -/
def Mismatch.pathText (p : List Nat) : String :=
  match p with
  | [] => "the head"
  | ps => "argument " ++ String.intercalate ", of argument " (ps.reverse.map toString)

/-- The first place the two terms differ, as a path of argument positions and the pair.
Applications are compared head first, then argument by argument; other mismatching
terms (a constant vs another, a variable, a sort) are a difference at the current path. -/
partial def termDiff (t u : Term R) : List Nat × Term R × Term R :=
  go [] t u
where
  go (path : List Nat) (t u : Term R) : List Nat × Term R × Term R :=
    if t == u then (path, t, u) else
    match t, u with
    | .app .., .app .. =>
      let (ht, ats) := Term.spine t
      let (hu, aus) := Term.spine u
      if ht != hu then (path, t, u) else
      let rec args (i : Nat) (xs ys : List (Term R)) : List Nat × Term R × Term R :=
        match xs, ys with
        | x :: xs', y :: ys' =>
          if x == y then args (i + 1) xs' ys' else go (path ++ [i]) x y
        | _, _ => (path, t, u)
      args 0 ats aus
    -- `Nat → Nat` vs `Nat → Nat → Nat`: the second component (the codomain) differs
    | .pi _ _ _ a b _, .pi _ _ _ a' b' _ =>
      if a == a' then go (path ++ [1]) b b' else go (path ++ [0]) a a'
    | .sigma _ _ a b _, .sigma _ _ a' b' _ =>
      if a == a' then go (path ++ [1]) b b' else go (path ++ [0]) a a'
    | _, _ => (path, t, u)

/-- The number of a type's tuple components: `Nat × Bool` has 2, `Nat × (Bool × Nat)` 3
(right-nested Σs are flattened, as a tuple pattern is). -/
partial def sigmaLeaves (t : Term R) : Nat :=
  match t with
  | .sigma _ _ _ snd _ => 1 + sigmaLeaves snd
  | _ => 1

/-- The printed type mismatch, with the first differing subterm and its path. -/
def mismatchOf (g : Globals R) (names : List Name) (expected inferred : Term R) (reason : String) : Mismatch :=
  let show (t : Term R) : String := elideLong (t.pretty names (some g)) 400
  let (path, te, ti) := termDiff expected inferred
  let kind :=
    if reason.startsWith "universe level" then "universe"
    else if reason.contains "binder" || reason.contains "quantity" then "binder"
    else if reason.contains "outside the pattern fragment" then "hole"
    else if path.isEmpty then "head" else "argument"
  { expected := show expected, inferred := show inferred, path, expectedAt := show te,
    inferredAt := show ti, kind, reason }

end Wiz
