# Stage 16: data in the self-hosted frontend

## 16a: inductive types

`selfhost/Frontend.wiz` reads `inductive T where | c (x : A) (y : T) …` (no parameters
or indices yet, in `Type`): `T` becomes the constant `μ D tt` for the description

    D := darg (Enum k) (fun t => ecase t [D₁, …, Dₖ])

with one `Dᵢ` per constructor (exercise 16.1, `ctorDesc`: a field `(x : A)` is
`darg A (fun x => …)`, a field of type `T` is `drec tt …`, the end is `dret tt`), and
each constructor `T.c` the constant `fun fields => con (tag, fields…, tt, tt)`. The
Wiz kernel checks all of them.

| #    | Where                   | What                                     |
|------|-------------------------|------------------------------------------|
| 16.1 | `selfhost/Frontend.wiz` | `ctorDesc`: a constructor's description  |

## 16b: pattern matching and structural recursion

`def f (ps) : R := match x with | .c a b => rhs …`, for a parameter `x` of an inductive
type (and `R` not mentioning `x`), becomes induction with the motive `fun i y => R` and
the method

    fun i xs ih => (ecase (fst xs) [b₁, …, bₖ] : convoy) (snd xs) ih

where each branch `bᵢ := fun rest ih => let fields := …; let hyps := …; rhs` (exercise
16.2, `branchTm`) names the payload's fields and the recursive fields' induction
hypotheses; a recursive call `f … y …` on a recursive field `y`, the other arguments
unchanged, is `y`'s hypothesis. A catch-all `x =>` stands for the missing
constructors. The convoy's types apply the `interp` and `All` templates, which the
frontend normalises first (`nfAt`: the kernel can't infer the type of an applied λ).

| #    | Where                   | What                                     |
|------|-------------------------|------------------------------------------|
| 16.2 | `selfhost/Frontend.wiz` | `branchTm` (16e: `specialize`)           |

## 16c: parameters

`inductive List (A : Type) where | nil | cons (head : A) (tail : List A)`: the
description lives under the parameters (`List` is `fun A => μ D[A] tt`), a field of type
`List A` (the type applied to its own parameters) is recursive, and the constructors take
the parameters first (the self-hosted frontend has no implicit arguments yet:
`List.cons Nat x xs`). A match on `l : List A` instantiates the description and the
field types with the scrutinee type's arguments, again by normalising
(`(fun ps => D) args`) rather than substituting.

## 16d: equations

`def f (ps) : A → R | p => rhs …` (one pattern per alternative) is read as
`def f (ps) (x✝ : A) : R := match x✝ with | p => rhs …` (`eqnsToMatch`, on the syntax
tree; `(x : A) → R` names the parameter).

## 16e: several scrutinees and nested patterns

The match compiler now works column by column, as `compileMatch` in `Term.lean`: split on
the first column where the first clause has a constructor pattern (an `ind` with the
constant motive), replacing that column by the constructor's fields in each branch
(exercise 16.2, `specialize`: the clauses that remain, with their sub-patterns); a leaf
binds its variables with `let`s. The first split is on the structural column (the
leftmost one any clause matches): its method runs for the induction hypotheses too, so
the parameters after it are generalised in its motive (and bound again in each branch:
a recursive call may change them), and a variable for the column is the value at hand
(`cur✝ := con (tag, rest)`). Equations take several columns. The Wiz kernel got the
Lean kernel's check rule for `let`.

That last point was also wrong in the Lean elaborator since the scrutinee change above:
a catch-all variable of a recursive definition stood for the original argument in the
kernel's term (only `#eval`, which runs the `casesOn` implementation, was right). Now it
is the constructor at the recursor's split.

| #    | Where                   | What                                     |
|------|-------------------------|------------------------------------------|
| 16.2 | `selfhost/Frontend.wiz` | `specialize`: the clauses for a constructor |

Next: indices, implicit arguments (which need metavariables in the self-hosted
frontend).
