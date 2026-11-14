# Stage 18: more data in the self-hosted frontend

## 18a: indexed families

`inductive Vec (A : Type) : Nat → Type where | nil : Vec A Nat.zero | cons (n : Nat)
(a : A) (v : Vec A n) : Vec A (Nat.succ n)` (one index): the description's index type
is `Nat`, a recursive field `Vec A j` is `drec j`, a constructor ends in `dret i` for
its result's index `i` (exercise 16.1 now takes the index), and its payload ends in the
proof `refl I i`. `Vec` is `fun A i => μ D i`. A match on `v : Vec A n` runs induction at
`v`'s index, with the index type in the method's binders, the convoy's templates and
`cur✝` (whose index is the method's). The motive is still constant, so a match needs a
case (or a catch-all) for every constructor, even one the index rules out.

Elaboration got two things this needed: an application checked against a type unifies
its result type with it before the postponed `.c` arguments are done, and an argument
whose type is still unknown at the end of its application waits in the elaboration state
until the whole definition is elaborated (`drain`).

## 18b: index equations

When the scrutinee's index is closed (`Vec A (Nat.succ Nat.zero)`, or a tag), the motive
also takes the equation `e :0 i = idx` (and the `ind` gets `refl`). A constructor no
clause covers is then ruled out if the index makes it impossible: its payload proves
`i_c = i`, carried along `e` (`subst`) that is `i_c = idx`, which OTT computes to
`False` (or to `False × …`, projected) when the two differ, so the branch is `exfalso`.
A hypothesis for a recursive field with that same index is applied to `refl` already.
The parameter and result types of a match are now elaborated with types too.

## 18c: mutual inductive types

`mutual inductive Tm … inductive Tms … end` (no parameters or indices yet) is one
family `Tm_Tms : Enum 2 → Type` over every member's constructors: a field whose type is
a member is recursive at that member's tag, and a member's constructors end at its tag.
Each member is the constant `Tm := Tm_Tms (tag 0)`, and its constructors `Tm.c` build
the family's values. A match on a `Tm` runs at a closed index, so 18b rules out the
other members' constructors: a match lists only its own type's.

## 18d–e: parameters for mutual types; structures

The members of a mutual block share their parameters (the first member's): the family
is `fun ps i => μ D i`, a member `A := fun ps => A_B ps (tag j)`, a field `A ps` is
recursive, and constructors take the parameters implicitly (`Tree`/`Forest A`).

`structure T (ps) where f : A …` is read, on the syntax tree, as the inductive type
`T (ps) where | mk (f : A) …` and one projection `T.f {ps} (s : T ps) : A` per field,
defined by `match`. `x.f` (and `(e).f`) is `T.f x` for `x : T …`. (A field's type may
not mention an earlier field yet.)

## 18f–g: numerals; `match` as a term

A numeral `n` is `Nat.succ` applied `n` times to `Nat.zero` (the kernel has no number
literals), and in a pattern `0` is `.zero` and `n + 1` is `.succ n`. `match` can now
appear anywhere a term is checked: its scrutinees are `let`-bound and its clauses
compiled against the expected type, by the same compiler (so the elaborator and the
match compiler are now one mutual block). Only a definition's own match recurses, and
a recursive call may change only the parameters after the structural one: `lt m' n'`
inside a nested `match m` under `match n` is rejected, `| succ m, succ n => lt m n`
is fine.
