import STC.F0.Spec.Rule
/-!
# Type equations, variant "cross-level" (what both kernels implement)

`A ≡ B` is formed for any two types, and an equation between two `Π` (or `Σ`) types
decomposes **without comparing the sorts of the two domains or of the two codomains**.
So the reduct can ask `A₂ ≡ A₁` for types in different universes, where it is `False`
between a proposition and a type that is not one, and otherwise decided by shape
(`Sort 0 ≡ Sort 1 ⟶ False`).

The kernels' *surface* rule forms `A ≡ B` only at one sort; their computation rules do
not keep to it (model-memo rows T4, T6). This file takes the computation rules at face
value and widens formation so that reduction preserves typing. `EqTyLevelled.lean` is
F0's choice; this is the variant for the divergence table, not part of `F0` (it is
`F0Cross` in `Fragments.lean`).
-/


namespace STC
namespace F0
namespace Spec

inductive EqTyCross : Rules
  | form {Γ : Ctx} {A B : Tm} {s s' : Srt} :
      EqTyCross ⟨[Γ ⊢ A ∶ .sort s, Γ ⊢ B ∶ .sort s'], Γ ⊢ .eqTy A B ∶ .sort .prop⟩
  /-- a proposition and a type that is not one -/
  | propType {Γ : Ctx} {A B : Tm} {s s' : Srt} : s.IsZero → s'.NeverZero →
      EqTyCross ⟨[Γ ⊢ A ∶ .sort s, Γ ⊢ B ∶ .sort s'],
        Γ ⊢ .eqTy A B ⟶ .False' ∶ .sort .prop⟩
  | typeProp {Γ : Ctx} {A B : Tm} {s s' : Srt} : s.NeverZero → s'.IsZero →
      EqTyCross ⟨[Γ ⊢ A ∶ .sort s, Γ ⊢ B ∶ .sort s'],
        Γ ⊢ .eqTy A B ⟶ .False' ∶ .sort .prop⟩
  | pi {Γ : Ctx} {A₁ B₁ A₂ B₂ : Tm} {s₁ s₂ : Srt} : s₁.NeverZero → s₂.NeverZero →
      EqTyCross ⟨[Γ ⊢ .pi s₁ A₁ B₁ ∶ .sort s₁, Γ ⊢ .pi s₂ A₂ B₂ ∶ .sort s₂],
        Γ ⊢ .eqTy (.pi s₁ A₁ B₁) (.pi s₂ A₂ B₂) ⟶ .eqTyPi A₁ B₁ A₂ B₂ ∶ .sort .prop⟩
  | sigma {Γ : Ctx} {A₁ B₁ A₂ B₂ : Tm} {s₁ s₂ : Srt} : s₁.NeverZero → s₂.NeverZero →
      EqTyCross ⟨[Γ ⊢ .sigma s₁ A₁ B₁ ∶ .sort s₁, Γ ⊢ .sigma s₂ A₂ B₂ ∶ .sort s₂],
        Γ ⊢ .eqTy (.sigma s₁ A₁ B₁) (.sigma s₂ A₂ B₂) ⟶ .eqTySigma A₁ B₁ A₂ B₂ ∶ .sort .prop⟩

end Spec
end F0
end STC
