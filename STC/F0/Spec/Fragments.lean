import STC.F0.Spec.Core
import STC.F0.Spec.Pi
import STC.F0.Spec.Sigma
import STC.F0.Spec.Unit
import STC.F0.Spec.Enum
import STC.F0.Spec.Let
import STC.F0.Spec.Global
import STC.F0.Spec.Eq
import STC.F0.Spec.EqTyLevelled
import STC.F0.Spec.EqTyCross
import STC.F0.Spec.ULift
import STC.F0.Spec.Struct
/-!
# F0: the fragment, its two structural conversion rules, and its signature

    F0Rules  Core, Π, Σ, Unit, Empty, Enum, let/letUnit/ann, closed globals,
             observational Eq, the chosen Eq-Π/Eq-Σ variant, ULift
    F0Base   `F0Rules` with **levelled** Eq-Π/Eq-Σ: the fragment the renaming and
             substitution lemmas (`Renaming.lean`, `Substitution.lean`) are proved for
    F0       `F0Base` + `Struct`: the two structural conversion rules (`eqTyped`,
             `ctxConv`) that type the ends of conversions and move a context entry along
             a conversion
    F0Cross  `F0Rules` with the cross-level Eq-Π/Eq-Σ (the kernels' rule) + `Struct`; a
             variant for the divergence table, never used in the obligations

Regularity (`InReg`), descriptions, `μ`, `ν`, sizes and quantities are absent: not
"unproved" but unrepresentable in the term type.

The `Struct` rules sit outside `F0Rules` on purpose: the renaming and substitution lemmas
are proved rule set by rule set, and `ctxConv` needs a relation between contexts whose
entries are merely *convertible*, not a renaming (`Sorting.lean`, "the remaining
obligation"). `F0Base` is therefore the system the proved laws are about; `F0` is the
specification's system, and `F0/Typing.lean` proves what the two extra rules buy. The
concrete laws for `F0` itself are conditional on `StructRenClosed`/`StructSubClosed`
(`Typing.lean`).

The union is left-associative, as in `WizMeta`; the `*_in_F0Rules` lemmas name each
component's position once, so the renaming proof does not spell the `Or.inl` chains. The
`*_in_F0` lemmas are the same for `F0`, where the last component is `Struct sg`.
-/

namespace STC
namespace F0
namespace Spec

def eqTyRules : EqTyVariant → Rules
  | .cross => EqTyCross
  | .levelled => EqTyLevelled

/-- The fragment's rules, in the shape of a union of rule sets (no `Struct`). -/
def F0Rules (sg : Sig) (var : EqTyVariant) : Rules :=
  Core ∪ Pi ∪ Sigma ∪ Unit ∪ Empty ∪ Enum ∪ Let ∪ Global sg ∪ Eq ∪ eqTyRules var ∪ ULift var

/-- **`F0Base`**: `stc-m0-spec.md`'s fragment, levelled `Π`/`Σ` equality, without the two
structural conversion rules. This is the system `F0Base_rename`/`F0Base_subst*` are
proved for. -/
def F0Base (sg : Sig) : Rules := F0Rules sg .levelled

/-- **F0**: the fragment of the design note plus the two structural conversion rules
(`eqTyped`, `ctxConv`), licensed by `Sig.Closed sg`. -/
def F0 (sg : Sig) : Rules := F0Base sg ∪ Struct sg

/-- The cross-level variant (what the kernels implement), for the divergence table. -/
def F0Cross (sg : Sig) : Rules := F0Rules sg .cross ∪ Struct sg

theorem core_in_F0Rules {sg : Sig} {var : EqTyVariant} {r : Rule} (h : Core r) :
    F0Rules sg var r :=
  Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h)))))))))

theorem pi_in_F0Rules {sg : Sig} {var : EqTyVariant} {r : Rule} (h : Pi r) :
    F0Rules sg var r :=
  Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))))))

theorem sigma_in_F0Rules {sg : Sig} {var : EqTyVariant} {r : Rule} (h : Sigma r) :
    F0Rules sg var r :=
  Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))))))

theorem unit_in_F0Rules {sg : Sig} {var : EqTyVariant} {r : Rule} (h : Unit r) :
    F0Rules sg var r :=
  Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))))

theorem empty_in_F0Rules {sg : Sig} {var : EqTyVariant} {r : Rule} (h : Empty r) :
    F0Rules sg var r :=
  Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))))

theorem enum_in_F0Rules {sg : Sig} {var : EqTyVariant} {r : Rule} (h : Enum r) :
    F0Rules sg var r :=
  Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))

theorem let_in_F0Rules {sg : Sig} {var : EqTyVariant} {r : Rule} (h : Let r) :
    F0Rules sg var r :=
  Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))

theorem global_in_F0Rules {sg : Sig} {var : EqTyVariant} {r : Rule} (h : Global sg r) :
    F0Rules sg var r :=
  Or.inl (Or.inl (Or.inl (Or.inr h)))

theorem eq_in_F0Rules {sg : Sig} {var : EqTyVariant} {r : Rule} (h : Eq r) :
    F0Rules sg var r :=
  Or.inl (Or.inl (Or.inr h))

theorem eqTy_in_F0Rules {sg : Sig} {var : EqTyVariant} {r : Rule} (h : eqTyRules var r) :
    F0Rules sg var r :=
  Or.inl (Or.inr h)

theorem ulift_in_F0Rules {sg : Sig} {var : EqTyVariant} {r : Rule} (h : ULift var r) :
    F0Rules sg var r :=
  Or.inr h

/-! ### Membership in `F0` (the fragment plus `Struct`) -/

theorem core_in_F0 {sg : Sig} {r : Rule} (h : Core r) : F0 sg r :=
  Or.inl (core_in_F0Rules h)

theorem pi_in_F0 {sg : Sig} {r : Rule} (h : Pi r) : F0 sg r :=
  Or.inl (pi_in_F0Rules h)

theorem sigma_in_F0 {sg : Sig} {r : Rule} (h : Sigma r) : F0 sg r :=
  Or.inl (sigma_in_F0Rules h)

theorem unit_in_F0 {sg : Sig} {r : Rule} (h : Unit r) : F0 sg r :=
  Or.inl (unit_in_F0Rules h)

theorem empty_in_F0 {sg : Sig} {r : Rule} (h : Empty r) : F0 sg r :=
  Or.inl (empty_in_F0Rules h)

theorem enum_in_F0 {sg : Sig} {r : Rule} (h : Enum r) : F0 sg r :=
  Or.inl (enum_in_F0Rules h)

theorem let_in_F0 {sg : Sig} {r : Rule} (h : Let r) : F0 sg r :=
  Or.inl (let_in_F0Rules h)

theorem global_in_F0 {sg : Sig} {r : Rule} (h : Global sg r) : F0 sg r :=
  Or.inl (global_in_F0Rules h)

theorem eq_in_F0 {sg : Sig} {r : Rule} (h : Eq r) : F0 sg r :=
  Or.inl (eq_in_F0Rules h)

theorem eqTy_in_F0 {sg : Sig} {r : Rule} (h : EqTyLevelled r) : F0 sg r :=
  Or.inl (eqTy_in_F0Rules h)

theorem ulift_in_F0 {sg : Sig} {r : Rule} (h : ULift .levelled r) : F0 sg r :=
  Or.inl (ulift_in_F0Rules h)

/-- The two structural conversion rules are the last component of `F0`. -/
theorem struct_in_F0 {sg : Sig} {r : Rule} (h : Struct sg r) : F0 sg r :=
  Or.inr h

/-- Everything derivable in the fragment is derivable in `F0`. -/
theorem F0Base_le_F0 {sg : Sig} : ∀ r, F0Base sg r → F0 sg r := fun _ h => Or.inl h

theorem F0Base_derivable {sg : Sig} {j : Jdg} (d : Derivable (F0Base sg) j) :
    Derivable (F0 sg) j :=
  d.mono F0Base_le_F0

/-! ## Signatures -/

/-- A well-formed signature for a system `T`: each declaration has a fresh name and is
typed in the signature before it (closed; no level parameters in F0). -/
inductive SigWF (T : Sig → Rules) : Sig → Prop
  | nil : SigWF T []
  | axiom {sg : Sig} {d : Decl} {s : Srt} : SigWF T sg → sg.find? d.name = none → d.value = none →
      Derivable (T sg) (([] : Ctx) ⊢ d.type ∶ .sort s) → SigWF T (d :: sg)
  | defn {sg : Sig} {d : Decl} {s : Srt} {v : Tm} : SigWF T sg → sg.find? d.name = none →
      d.value = some v → Derivable (T sg) (([] : Ctx) ⊢ d.type ∶ .sort s) →
      Derivable (T sg) (([] : Ctx) ⊢ v ∶ d.type) → SigWF T (d :: sg)

/-- No declaration is an axiom: consistency is claimed for such signatures only. -/
def AxiomFree (sg : Sig) : Prop := ∀ d, d ∈ sg → d.value.isSome = true

/-- Weak-head reduction of a relevant term: the relation WHN is about. No proof is
reduced: at a proposition this relation is empty (the sort of `A` is never `prop`). -/
def WhRed (T : Rules) (Γ : Ctx) (t u A : Tm) : Prop :=
  Derivable T (Γ ⊢ t ⟶ u ∶ A) ∧ ∃ s, Derivable T (Γ ⊢ A ∶ .sort s) ∧ s.NeverZero

end Spec
end F0
end STC
