import Wiz.Rig

/-!
# Rig instances

* `Unit`         -- the trivial rig. Every quantity is the same, so QTT collapses to
                    ordinary dependent type theory. Fully implemented as a worked example.
* `Nat`          -- exact counting: a variable declared at `n` is used exactly `n` times.
                    Fully implemented as a second worked example.
* `ZeroOneMany`  -- Idris 2's `{0, 1, ω}`. **Exercises 0.1 and 0.2.**
-/

namespace Wiz

/-! ## `Unit`: plain Martin-Löf type theory -/

instance : QRig Unit where
  zero := ()
  one := ()
  add _ _ := ()
  mul _ _ := ()
  add_assoc _ _ _ := rfl
  add_comm _ _ := rfl
  zero_add _ := rfl
  mul_assoc _ _ _ := rfl
  mul_comm _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl
  zero_mul _ := rfl
  mul_zero _ := rfl
  left_distrib _ _ _ := rfl
  right_distrib _ _ _ := rfl
  le _ _ := true
  le_refl _ := rfl
  le_trans _ _ _ _ _ := rfl
  add_le_add _ _ _ _ _ _ := rfl
  mul_le_mul _ _ _ _ _ _ := rfl
  elements? := some [()]
  many? := some ()

instance : QuantitySyntax Unit where
  ofLiteral _ := some ()
  explicitDefault := ()
  implicitDefault := ()
  display _ := ""

instance : RigTag Unit where
  tag := "unit"

/-! ## `Nat`: exact usage counting -/

instance : QRig Nat where
  add_assoc := Nat.add_assoc
  add_comm := Nat.add_comm
  zero_add := Nat.zero_add
  mul_assoc := Nat.mul_assoc
  mul_comm := Nat.mul_comm
  one_mul := Nat.one_mul
  mul_one := Nat.mul_one
  zero_mul := Nat.zero_mul
  mul_zero := Nat.mul_zero
  left_distrib := Nat.left_distrib
  right_distrib := Nat.right_distrib
  le a b := a == b
  le_refl _ := by simp
  le_trans _ _ _ h₁ h₂ := by simp_all
  add_le_add _ _ _ _ h₁ h₂ := by simp_all
  mul_le_mul _ _ _ _ h₁ h₂ := by simp_all

/-- There is no ω in `Nat`, so explicit binders default to exactly once. -/
instance : QuantitySyntax Nat where
  ofLiteral := String.toNat?
  explicitDefault := 1
  implicitDefault := 0
  display := toString

instance : RigTag Nat where
  tag := "nat"

/-! ## `ZeroOneMany`: Idris 2's quantities -/

/-- `zero` = erased, `one` = linear (exactly once), `many` = unrestricted (ω). -/
inductive ZeroOneMany where
  | zero
  | one
  | many
  deriving DecidableEq, Repr, Inhabited

namespace ZeroOneMany

instance : ToString ZeroOneMany where
  toString
    | zero => "0"
    | one => "1"
    | many => "ω"

/-- **Exercise 0.1a.** Addition: "used in one place, then also used in another".
Think about what `1 + 1` must be when there is no `2` available. -/
--<sol
def add : ZeroOneMany → ZeroOneMany → ZeroOneMany
  | zero, b => b
  | a, zero => a
  | _, _ => many
--|ex
--| def add (a b : ZeroOneMany) : ZeroOneMany :=
--|   sorry
--sol>

/-- **Exercise 0.1b.** Multiplication: "passed `b`-many times to a binder of quantity `a`". -/
--<sol
def mul : ZeroOneMany → ZeroOneMany → ZeroOneMany
  | zero, _ => zero
  | _, zero => zero
  | one, b => b
  | a, one => a
  | many, many => many
--|ex
--| def mul (a b : ZeroOneMany) : ZeroOneMany :=
--|   sorry
--sol>

/-- **Exercise 0.1c.** Compatibility: may a variable declared `declared` be used `used` times?
Hint: an ω variable tolerates any usage; a linear one tolerates exactly one use. -/
def le (used declared : ZeroOneMany) : Bool :=
  --<sol
  used == declared || declared == many
  --sol>

/-- **Exercise 0.2.** Prove the laws. Once 0.1 is done, almost all of these fall to
`intro a b c; cases a <;> cases b <;> cases c <;> rfl` (or `decide` on the
case-split goals). -/
instance : QRig ZeroOneMany where
  zero := zero
  one := one
  add := add
  mul := mul
  le := le
  elements? := some [zero, one, many]
  many? := some many
  --<sol
  add_assoc := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  --|ex
  --| add_assoc := sorry
  --sol>
  --<sol
  add_comm := by intro a b; cases a <;> cases b <;> rfl
  --|ex
  --| add_comm := sorry
  --sol>
  --<sol
  zero_add := by intro a; cases a <;> rfl
  --|ex
  --| zero_add := sorry
  --sol>
  --<sol
  mul_comm := by intro a b; cases a <;> cases b <;> rfl
  --|ex
  --| mul_comm := sorry
  --sol>
  --<sol
  mul_assoc := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  --|ex
  --| mul_assoc := sorry
  --sol>
  --<sol
  one_mul := by intro a; cases a <;> rfl
  --|ex
  --| one_mul := sorry
  --sol>
  --<sol
  mul_one := by intro a; cases a <;> rfl
  --|ex
  --| mul_one := sorry
  --sol>
  --<sol
  zero_mul := by intro a; cases a <;> rfl
  --|ex
  --| zero_mul := sorry
  --sol>
  --<sol
  mul_zero := by intro a; cases a <;> rfl
  --|ex
  --| mul_zero := sorry
  --sol>
  --<sol
  left_distrib := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  --|ex
  --| left_distrib := sorry
  --sol>
  --<sol
  right_distrib := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  --|ex
  --| right_distrib := sorry
  --sol>
  --<sol
  le_refl := by intro a; cases a <;> rfl
  --|ex
  --| le_refl := sorry
  --sol>
  --<sol
  le_trans := by intro a b c; cases a <;> cases b <;> cases c <;> decide
  --|ex
  --| le_trans := sorry
  --sol>
  --<sol
  add_le_add := by intro a b c d; cases a <;> cases b <;> cases c <;> cases d <;> decide
  --|ex
  --| add_le_add := sorry
  --sol>
  --<sol
  mul_le_mul := by intro a b c d; cases a <;> cases b <;> cases c <;> cases d <;> decide
  --|ex
  --| mul_le_mul := sorry
  --sol>

instance : QuantitySyntax ZeroOneMany where
  ofLiteral
    | "0" => some zero
    | "1" => some one
    | "ω" => some many
    | _ => none
  explicitDefault := many
  implicitDefault := zero
  display := toString

instance : RigTag ZeroOneMany where
  tag := "zero-one-many"

end ZeroOneMany

end Wiz
