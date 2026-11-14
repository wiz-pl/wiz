import Wiz.Core.Term
import Wiz.Core.QPoly

/-!
# Values: the semantic domain for normalisation by evaluation

Values are terms that have been evaluated as far as possible:

* binders are represented by **closures** (an environment plus an unevaluated body), so
  instantiating a binder is just "evaluate the body in an extended environment";
* stuck computations are **neutrals**: a head (a local variable, an axiom or a
  metavariable) followed by a **spine** of eliminations waiting on it, such as
  applications `f a`, projections `p.1`, or a `let (x, y) := p; …` split.

Local variables inside values use **de Bruijn levels** (counting from the *outside*:
the first variable ever bound is level 0). Levels don't need shifting when you go under
a binder, which is why NbE uses them for values while terms use indices.

Converting level `x` to an index in a context of size `l`: `ix = l - x - 1`.

Reference: András Kovács, *elaboration-zoo* (github.com/AndrasKovacs/elaboration-zoo),
especially `01-eval-closures-debruijn` and `02-typecheck-closures-debruijn`.
-/

namespace Wiz

abbrev Lvl := Nat

mutual
/-- What a neutral is stuck on. Besides variables, globals and metas, stage 4c adds
stuck observational constructs: an equality or cast whose type is a neutral, and
proofs (`refl`, `transp`), which never compute because proofs are irrelevant. -/
inductive Head (R : Type) where
  | local (lvl : Lvl)
  | global (name : Name) (levels : List Level)
  /-- an unsolved (as far as the kernel knows) metavariable -/
  | mvar (id : Nat)
  | eq (A a b : Val R)
  | eqTy (A B : Val R)
  | cast (A B e t : Val R)
  | refl (A a : Val R)
  | reflTy (X : Val R)
  | transp (A a P p b e : Val R)
  /-- (P2, `Globals.lazyProofs`) a **suspended proof**: the term `t` in `env`, never
  evaluated by the kernel. It comes from a marked proof (`Term.prf`) or from a position
  the syntax marks (`cast`'s equation, `transp`'s two proofs). Outside the kernel it is
  evaluated to be read back (`quote`, unless `quoteErasesProofs`), within a step budget
  (`Budget`). It carries no type: conversion never compares two proofs, and what follows
  an `absurd` is typed by the motive. -/
  | prf (env : List (Val R)) (t : Term R)

inductive Val (R : Type) where
  /-- `head` followed by the eliminations in `spine`, innermost first -/
  | neutral (head : Head R) (spine : Array (Elim R))
  | sort (level : Level)
  | pi (x : Name) (bi : BinderInfo) (q : Val R) (dom : Val R) (cod : Closure R) (σ : BinderSorts)
  | lam (x : Name) (body : Closure R)
  | sigma (x : Name) (q : Val R) (fst : Val R) (snd : Closure R) (σ : BinderSorts)
  | pair (a b : Val R)
  | unit (level : Level)
  | tt
  | empty (level : Level)
  | qty
  | qlit (r : R)
  | enum (labels : List Name)
  | tag (labels : List Name) (i : Nat)
  | desc (l : Level) (I : Val R)
  | dret (i : Val R)
  | darg (q S D : Val R)
  | drec (q j D : Val R)
  | dhrec (q H j D : Val R)
  | mu (l : Level) (I D i : Val R) (sz : Val R) (hint : Option (Name × List Level × List (Val R)))
  | con (x : Val R)
  | nu (l : Level) (I D i : Val R) (sz : Val R) (hint : Option (Name × List Level × List (Val R)))
  | size
  | szInf
  | szSuc (s : Val R)
  | sizeLt (s : Val R)
  | cocon (x : Val R)
  /-- a sized corecursive value, kept lazy until observed with `out` -/
  | scofix (l : Level) (I D A f s i a : Val R)
  /-- an unfolding, kept lazy until observed with `out` -/
  | coit (l : Level) (I D S step i s : Val R)
  /-- a numeral of the `builtin nat` type (see `Term.natLit`) -/
  | natLit (n : Nat)
  /-- `ULift.{l} A` (for `A : Sort k`) and its constructor (Q4) -/
  | ulift (k l : Level) (A : Val R)
  | up (a : Val R)
  /-- **glued**: the global `name` applied to the eliminations `sp`, together with its
  unfolding, computed only when needed (a `Thunk` remembers it). Keeping the head
  lets conversion compare `f a` with `f b` without unfolding `f`, keeps names in error
  messages, and lets type classes see their class and the nominal heads. Use `whnf`
  before matching on a value's shape. -/
  | unfold (name : Name) (levels : List Level) (sp : Array (Elim R)) (val : Thunk (Val R))
  /-- **glued** induction on a numeral, `ind l I D v P m i x`, computed only when needed:
  the induction hypotheses of a numeral (so that `ind` on `1000000` doesn't compute a
  million of them first), applied to the eliminations `sp` (applications and
  projections, which stay lazy). `whnf` forces it; quoting keeps the folded form. -/
  | lazyInd (l : Level) (I D : Val R) (v : Level) (P m i x : Val R) (sp : Array (Elim R)) (val : Thunk (Val R))

/-- An elimination stuck on a neutral. -/
inductive Elim (R : Type) where
  | app (arg : Val R)
  | fst
  | snd
  /-- `motive` is under one binder, `body` under two -/
  | split (q : Val R) (z : Name) (motive : Closure R) (x y : Name) (body : Closure R)
  | absurd (motive : Val R)
  /-- the branches are evaluated in `env` only when the tag is known -/
  | ecase (z : Name) (motive : Closure R) (env : List (Val R)) (branches : List (Term R))
  | delim (v : Level) (P mret marg mrec mhrec : Val R)
  | ind (l : Level) (I D : Val R) (v : Level) (P m i : Val R)
  | sfix (l : Level) (I D : Val R) (v : Level) (P f s i : Val R)
  | scase (l : Level) (q : Val R) (I D : Val R) (v : Level) (P m s i : Val R)
  | out
  /-- `down` (Q4) -/
  | down

/-- A body waiting for the values of its bound variables. `env` gives the values of
the body's free variables, with the most recent binder at the head of the list. -/
inductive Closure (R : Type) where
  | mk (env : List (Val R)) (body : Term R)
end

abbrev Env (R : Type) := List (Val R)
abbrev VTy (R : Type) := Val R

/-- The head of the value that a kernel-internal failure leaves behind. Lean's `panic!`
(an eliminator applied to a value of the wrong shape, `xs[i]!` out of range) prints a
message and goes on with the type's default value. That default was `Sort 0`, a
well-formed type and proposition, which the checker then accepted (audit F2, K6). It is
now a **stuck unknown**: a constant that no declaration has, so nothing computes on it,
and a term read back from it is rejected (`unknown constant`). The batch commands do
not go on at all (`Wiz.exitOnPanic`). See `wiz-notes/kernel-lint.md`. -/
def kernelPanicName : Name := "kernel panic✝"

instance {R : Type} : Inhabited (Val R) := ⟨.neutral (.global kernelPanicName []) #[]⟩

/-- A quantity value as a polynomial: a literal, or a quantity variable. `none` for
anything else (a stuck computation, or an elaborator metavariable). -/
partial def Val.toPoly? {R : Type} [QRig R] [DecidableEq R] : Val R → Option (QPoly R)
  | .unfold _ _ _ v => Val.toPoly? v.get
  | .lazyInd _ _ _ _ _ _ _ _ _ v => Val.toPoly? v.get
  | .qlit r => some (QPoly.const r)
  | .neutral (.local l) #[] => some (QPoly.var l)
  | _ => none

/-- The value of the local variable at level `l`. -/
def Val.var {R : Type} (l : Lvl) : Val R := .neutral (.local l) #[]

/-- Heads are equal if they are the same variable, or the same global at equivalent
levels. (The stage 4c heads contain values, which `convNe` compares.) -/
def Head.equiv {R : Type} : Head R → Head R → Bool
  | .local a, .local b => a == b
  | .global n us, .global m vs =>
    n == m && us.length == vs.length && (us.zip vs).all fun (u, v) => u.equiv v
  | .mvar a, .mvar b => a == b
  | _, _ => false

/-- (13b) A type that is opaque here (`Globals.opaqueTo?`): its head and module. -/
def Globals.opaqueHere? {R : Type} (g : Globals R) : Val R → Option (Name × String)
  | .neutral (.global T _) _ => (g.opaqueTo? T).map (T, ·)
  | _ => none

end Wiz
