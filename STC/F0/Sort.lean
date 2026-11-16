/-!
# The three closed sorts of F0

F0 has exactly the three sorts of the design note (`/workspace/wiz-notes/stc-m0-spec.md`
§2): `prop` (`Sort 0`), `u0` (`Sort 1`) and `u1` (`Sort 2`). `Sort 0 : Sort 1 : Sort 2`,
and `Sort 2` is a type but not a term: `Srt.succ? .u1 = none`, so no typing rule forms it.

Levels are not part of F0. `WizMeta/Level.lean` stays for the later level-polymorphic
extension (M5/E2); this file is the closed enum the M0 design asks for.

The side conditions are semantic in `WizMeta` (`∀ ρ, …`, `Lvl.Equiv`, `Lvl.IsZero`,
`Lvl.NeverZero`). With one closed value they collapse to `=`, and the same names are kept
so the rules can be read next to `WizMeta/Spec/`.
-/

namespace STC
namespace F0

/-- The three sorts: `prop = Sort 0`, `u0 = Sort 1`, `u1 = Sort 2`.

`Srt` rather than `Sort`: `Sort` is a Lean keyword. -/
inductive Srt where
  | prop
  | u0
  | u1
  deriving Repr, Inhabited, BEq, DecidableEq

namespace Srt

/-- The successor sort, if there is one. `u1` has none: `Sort 2` is a type but not a
term (there is no `Sort 3`). -/
def succ? : Srt → Option Srt
  | .prop => some .u0
  | .u0 => some .u1
  | .u1 => none

/-- `max i j`: the sort of a `Σ`. `prop` is the bottom. -/
def max : Srt → Srt → Srt
  | .prop, b => b
  | a, .prop => a
  | .u0, .u0 => .u0
  | _, _ => .u1

/-- `imax i j`: the sort of a `Π`; `imax i prop = prop` (impredicative `Prop`). -/
def imax : Srt → Srt → Srt
  | _, .prop => .prop
  | a, b => max a b

/-- The two sorts are the same. -/
def Equiv (a b : Srt) : Prop := a = b
/-- `a = prop`: the sort is `Prop`. -/
def IsZero (a : Srt) : Prop := a = .prop
/-- `a ≠ prop`: the sort is a type sort. -/
def NeverZero (a : Srt) : Prop := a ≠ .prop

instance (a : Srt) : Decidable a.IsZero := inferInstanceAs (Decidable (a = .prop))
instance (a : Srt) : Decidable a.NeverZero := inferInstanceAs (Decidable (a ≠ .prop))
instance (a b : Srt) : Decidable (a.Equiv b) := inferInstanceAs (Decidable (a = b))

@[simp] theorem isZero_iff (a : Srt) : a.IsZero ↔ a = .prop := Iff.rfl
@[simp] theorem neverZero_iff (a : Srt) : a.NeverZero ↔ a ≠ .prop := Iff.rfl
@[simp] theorem equiv_iff (a b : Srt) : a.Equiv b ↔ a = b := Iff.rfl

theorem prop_isZero : Srt.IsZero .prop := rfl
theorem u0_neverZero : Srt.NeverZero .u0 := by decide
theorem u1_neverZero : Srt.NeverZero .u1 := by decide

theorem imax_prop (a : Srt) : imax a .prop = .prop := by cases a <;> rfl
theorem max_prop (a : Srt) : max a .prop = a := by cases a <;> rfl
theorem prop_max (a : Srt) : max .prop a = a := by cases a <;> rfl

end Srt

end F0
end STC
