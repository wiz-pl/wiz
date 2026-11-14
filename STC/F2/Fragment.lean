import STC.F2.Ext0
import STC.F2.Glue
import STC.F2.Closed
/-!
# F2: the fragment `F1 ∪ Ext 0 ∪ Glue ∪ ●`

`F2` is the F1 phase layer (`F0Base ∪ Phase`) plus the three term formers which F1
deferred (`shared-cofib-layer.md` R3/R4, `stc-plan.md` M4b):

* `Ext0`: `Ext 0 A φ a` with `in`/`out` (`F2/Ext0.lean`);
* `Glue`: strict `Glue φ A T f` with `glue`/`unglue` and the two restriction rules
  (`F2/Glue.lean`);
* `Closed`: the closed modality `●_φ A` with `η●`, `⋆●`, a non-dependent eliminator and
  its collapse under `φ` (`F2/Closed.lean`).

The union is left-associated, as in F0/F1, and the `*_in_F2` lemmas name each component's
position once. Like F1, `F2` does **not** include F0's two `Struct` rules
(`eqTyped`, `ctxConv`): their law closure is still the open
`StructRenClosed`/`StructSubClosed`.
-/


namespace STC
namespace F2

open F0
open F0.Spec
open scoped F0.Spec

/-- F1's rule set, named for the union. -/
abbrev F1Rules (sg : Sig) : Rules := _root_.STC.F1.F1 sg

/-- **F2**: F1 plus the three phase term formers. -/
def F2 (sg : Sig) : Rules := ((F1Rules sg ∪ Ext0) ∪ Glue) ∪ Closed

theorem f1_in_F2 {sg : Sig} {r : Rule} (h : F1Rules sg r) : F2 sg r :=
  Or.inl (Or.inl (Or.inl h))

theorem ext0_in_F2 {sg : Sig} {r : Rule} (h : Ext0 r) : F2 sg r :=
  Or.inl (Or.inl (Or.inr h))

theorem glue_in_F2 {sg : Sig} {r : Rule} (h : Glue r) : F2 sg r :=
  Or.inl (Or.inr h)

theorem closed_in_F2 {sg : Sig} {r : Rule} (h : Closed r) : F2 sg r :=
  Or.inr h

theorem core_in_F2 {sg : Sig} {r : Rule} (h : Core r) : F2 sg r :=
  f1_in_F2 (_root_.STC.F1.core_in_F1 h)

theorem phase_in_F2 {sg : Sig} {r : Rule} (h : _root_.STC.F1.Phase r) : F2 sg r :=
  f1_in_F2 (_root_.STC.F1.phase_in_F1 h)

theorem pi_in_F2 {sg : Sig} {r : Rule} (h : Pi r) : F2 sg r :=
  f1_in_F2 (_root_.STC.F1.pi_in_F1 h)

theorem sigma_in_F2 {sg : Sig} {r : Rule} (h : Sigma r) : F2 sg r :=
  f1_in_F2 (_root_.STC.F1.sigma_in_F1 h)

theorem unit_in_F2 {sg : Sig} {r : Rule} (h : Unit r) : F2 sg r :=
  f1_in_F2 (_root_.STC.F1.unit_in_F1 h)

theorem empty_in_F2 {sg : Sig} {r : Rule} (h : Empty r) : F2 sg r :=
  f1_in_F2 (_root_.STC.F1.empty_in_F1 h)

theorem eq_in_F2 {sg : Sig} {r : Rule} (h : Eq r) : F2 sg r :=
  f1_in_F2 (_root_.STC.F1.eq_in_F1 h)

theorem eqTy_in_F2 {sg : Sig} {r : Rule} (h : EqTyLevelled r) : F2 sg r :=
  f1_in_F2 (_root_.STC.F1.eqTy_in_F1 h)

theorem ulift_in_F2 {sg : Sig} {r : Rule} (h : ULift .levelled r) : F2 sg r :=
  f1_in_F2 (_root_.STC.F1.ulift_in_F1 h)

end F2
end STC
