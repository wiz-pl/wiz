import STC.F0.Spec.Rule
/-!
# Type equations, variant "levelled" (CCobs's Eq-Π; **F0's choice**)

`A ≡ B` is formed only between two types of one sort, and an equation between two `Π`
(or `Σ`) types decomposes only when the two domains are in one sort and the two
codomains are in one sort ([PT23] Fig. 4; its model tags `Π` codes with their levels).
Otherwise the equation is stuck: no rule. Every reduct is then again an equation at one
sort, so "a proposition against a type that is not one" never arises.

With F0's closed three sorts this is exactly the design's "component-sort premises on
Π/Σ" (Status §4 D2): cross-sort equations are unformable. `EqTyCross.lean` is the variant
that models the kernels and is used only in the divergence table.
-/


namespace STC
namespace F0
namespace Spec

inductive EqTyLevelled : Rules
  | form {Γ : Ctx} {A B : Tm} {s : Srt} :
      EqTyLevelled ⟨[Γ ⊢ A ∶ .sort s, Γ ⊢ B ∶ .sort s], Γ ⊢ .eqTy A B ∶ .sort .prop⟩
  | pi {Γ : Ctx} {A₁ A₂ B₁ B₂ : Tm} {i j s₁ s₂ : Srt} :
      s₁.NeverZero → s₂.NeverZero → s₁.Equiv (.imax i j) → s₂.Equiv (.imax i j) →
      EqTyLevelled ⟨[Γ ⊢ A₁ ∶ .sort i, Γ ⊢ A₂ ∶ .sort i, (A₁ :: Γ) ⊢ B₁ ∶ .sort j,
          (A₂ :: Γ) ⊢ B₂ ∶ .sort j],
        Γ ⊢ .eqTy (.pi s₁ A₁ B₁) (.pi s₂ A₂ B₂) ⟶ .eqTyPi A₁ B₁ A₂ B₂ ∶ .sort .prop⟩
  | sigma {Γ : Ctx} {A₁ A₂ B₁ B₂ : Tm} {i j s₁ s₂ : Srt} :
      s₁.NeverZero → s₂.NeverZero → s₁.Equiv (.max i j) → s₂.Equiv (.max i j) →
      EqTyLevelled ⟨[Γ ⊢ A₁ ∶ .sort i, Γ ⊢ A₂ ∶ .sort i, (A₁ :: Γ) ⊢ B₁ ∶ .sort j,
          (A₂ :: Γ) ⊢ B₂ ∶ .sort j],
        Γ ⊢ .eqTy (.sigma s₁ A₁ B₁) (.sigma s₂ A₂ B₂) ⟶ .eqTySigma A₁ B₁ A₂ B₂ ∶ .sort .prop⟩

end Spec
end F0
end STC
