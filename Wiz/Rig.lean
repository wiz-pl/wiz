/-!
# Rigs: the algebra of quantities

A *rig* is a ri**n**g without **n**egatives: a commutative monoid `(R, +, 0)` and a
monoid `(R, *, 1)` where `*` distributes over `+` and `0` annihilates.

In Quantitative Type Theory (QTT) every binder carries a quantity `q : R` saying how
many times the bound variable may be used *at runtime*:

* `+` combines the usages of two subterms that are both evaluated
  (`f a` uses everything `f` uses plus everything `a` uses);
* `*` scales usage when a value is passed to a binder of a given quantity
  (passing `a` to an argument of quantity `q` uses `a`'s variables `q` times);
* `0` means "erased": available only in types, gone at runtime;
* `1` is the usage of a single occurrence of a variable.

The kernel is parametric in the rig, so Idris 2's `{0, 1, ω}`, plain Martin-Löf type
theory (the trivial rig `Unit`), exact counting (`Nat`), affine `{0, ≤1, ω}`, and so on
are all instances of the same checker.

`QRig` adds a *compatibility preorder* `le used declared`: may a variable declared with
quantity `declared` be used `used` times? For `{0,1,ω}` this is "`used = declared` or
`declared = ω`" -- note that `0 ≤ 1` is **false** because a linear variable must be
consumed exactly once.

References:
* Conor McBride, *I Got Plenty o' Nuttin'* (2016).
* Robert Atkey, *Syntax and Semantics of Quantitative Type Theory* (LICS 2018).
-/

namespace Wiz

/-- A commutative-addition rig with the laws stated as fields.
We avoid Mathlib to keep the build light (and to keep the eventual self-hosting port
honest about what it depends on). -/
class Rig (R : Type) extends Zero R, One R, Add R, Mul R where
  add_assoc     : ∀ a b c : R, a + b + c = a + (b + c)
  add_comm      : ∀ a b : R, a + b = b + a
  zero_add      : ∀ a : R, 0 + a = a
  mul_assoc     : ∀ a b c : R, a * b * c = a * (b * c)
  /-- Commutativity of `*` lets usage polynomials (stage 4d) use a normal form. -/
  mul_comm      : ∀ a b : R, a * b = b * a
  one_mul       : ∀ a : R, 1 * a = a
  mul_one       : ∀ a : R, a * 1 = a
  zero_mul      : ∀ a : R, 0 * a = 0
  mul_zero      : ∀ a : R, a * 0 = 0
  left_distrib  : ∀ a b c : R, a * (b + c) = a * b + a * c
  right_distrib : ∀ a b c : R, (a + b) * c = a * c + b * c

/-- A rig with a decidable compatibility preorder used by the type checker.

`le used declared = true` means a variable declared at `declared` may be used `used`
times. Monotonicity of `+` and `*` is what makes the checker's usage arithmetic sound. -/
class QRig (R : Type) extends Rig R where
  le         : R → R → Bool
  le_refl    : ∀ a, le a a = true
  le_trans   : ∀ a b c, le a b = true → le b c = true → le a c = true
  add_le_add : ∀ a b c d, le a b = true → le c d = true → le (a + c) (b + d) = true
  mul_le_mul : ∀ a b c d, le a b = true → le c d = true → le (a * c) (b * d) = true
  /-- All the quantities, if there are finitely many. With quantity polymorphism
  (stage 4d), `used ≤ declared` for symbolic quantities is decided by trying every
  assignment, which needs this list. -/
  elements? : Option (List R) := none
  /-- An unrestricted quantity ("many", ω), if the rig has one: a variable declared with it
  may be used any number of times (`le 0 m`, `le 1 m`, `le (m + m) m`). An eliminator's
  methods (`ind`, `Desc.elim`, …) run once per node, so their usage is scaled by it. A rig
  without one (exact counting, `Nat`) can't bound that usage: there, methods may use
  local variables only in erased positions. -/
  many? : Option R := none

/-- A stable name for a rig, used by cache artifacts that hold elaborated terms
(`Cache.ModuleArtifact.rig`, `--region-cache`): two rigs with the same name must mean the
same quantities, and a rig whose meaning changes needs a new name. -/
class RigTag (R : Type) where
  /-- e.g. `"zero-one-many"` -/
  tag : String

/-- How quantities are written in surface syntax and printed back.

Binders without a quantity get a default: Idris 2 uses ω for explicit binders and 0
for implicit ones, since implicit arguments are almost always types or indices that
should be erased. The pretty printer omits a quantity equal to the default. -/
class QuantitySyntax (R : Type) where
  /-- parse a quantity literal such as `0`, `1` or `ω` -/
  ofLiteral : String → Option R
  explicitDefault : R
  implicitDefault : R
  display : R → String

end Wiz
