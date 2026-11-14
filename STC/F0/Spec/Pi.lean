import STC.F0.Spec.Rule
/-!
# Π

`(x : A) → B` carries its sort `s = imax i j` (mandatory; impredicative at `Prop`). There
are no quantities: all binders are relevant `ω`. λ has no domain. β is a reduction; η is a
conversion rule.

The rule for an equation between two `Π` types is in `EqTyLevelled.lean` (F0) and
`EqTyCross.lean` (the variant that models the kernels).
-/


namespace STC
namespace F0
namespace Spec

inductive Pi : Rules
  | form {Γ : Ctx} {A B : Tm} {i j s : Srt} : s.Equiv (.imax i j) →
      Pi ⟨[Γ ⊢ A ∶ .sort i, (A :: Γ) ⊢ B ∶ .sort j], Γ ⊢ .pi s A B ∶ .sort s⟩
  -- `Γ ⊢ A ∶ Sort i` in the rules with a premise under the binder: the renaming lemma needs
  -- the binder's type typed to extend the target context (it is not reachable from
  -- `Γ ⊢ Π A B ∶ Sort s` without an inversion lemma)
  | lam {Γ : Ctx} {A B b : Tm} {s i : Srt} :
      Pi ⟨[Γ ⊢ .pi s A B ∶ .sort s, Γ ⊢ A ∶ .sort i, (A :: Γ) ⊢ b ∶ B], Γ ⊢ .lam b ∶ .pi s A B⟩
  | app {Γ : Ctx} {f A B a : Tm} {s : Srt} : Pi ⟨[Γ ⊢ f ∶ .pi s A B, Γ ⊢ a ∶ A],
      Γ ⊢ .app f a ∶ B.inst a⟩
  | beta {Γ : Ctx} {A B b a : Tm} {s i : Srt} :
      Pi ⟨[Γ ⊢ .pi s A B ∶ .sort s, Γ ⊢ A ∶ .sort i, (A :: Γ) ⊢ b ∶ B, Γ ⊢ a ∶ A],
        Γ ⊢ .app (.lam b) a ⟶ b.inst a ∶ B.inst a⟩
  | appRed {Γ : Ctx} {f f' A B a : Tm} {s : Srt} :
      Pi ⟨[Γ ⊢ f ⟶ f' ∶ .pi s A B, Γ ⊢ a ∶ A], Γ ⊢ .app f a ⟶ .app f' a ∶ B.inst a⟩
  /-- η, as extensionality -/
  | eta {Γ : Ctx} {f A B g : Tm} {s i : Srt} :
      Pi ⟨[Γ ⊢ f ∶ .pi s A B, Γ ⊢ g ∶ .pi s A B, Γ ⊢ A ∶ .sort i,
          (A :: Γ) ⊢ .app f.shift (.var 0) ≡ .app g.shift (.var 0) ∶ B],
        Γ ⊢ f ≡ g ∶ .pi s A B⟩
  | cong {Γ : Ctx} {A A' B B' : Tm} {i j s s' : Srt} : s.Equiv (.imax i j) → s'.Equiv (.imax i j) →
      Pi ⟨[Γ ⊢ A ∶ .sort i, Γ ⊢ A ≡ A' ∶ .sort i, (A :: Γ) ⊢ B ≡ B' ∶ .sort j],
        Γ ⊢ .pi s A B ≡ .pi s' A' B' ∶ .sort s⟩
  | appCong {Γ : Ctx} {f f' A B a a' : Tm} {s : Srt} :
      Pi ⟨[Γ ⊢ f ≡ f' ∶ .pi s A B, Γ ⊢ a ≡ a' ∶ A], Γ ⊢ .app f a ≡ .app f' a' ∶ B.inst a⟩
  /-- funext: an equation between functions is pointwise -/
  | eq {Γ : Ctx} {A B f g : Tm} {s : Srt} : s.NeverZero →
      Pi ⟨[Γ ⊢ .pi s A B ∶ .sort s, Γ ⊢ f ∶ .pi s A B, Γ ⊢ g ∶ .pi s A B],
        Γ ⊢ .eq (.pi s A B) f g ⟶ .eqPi A B f g ∶ .sort .prop⟩
  /-- a proposition and a type that is not one are different `Π`s: `False` -/
  | eqTyApart {Γ : Ctx} {A₁ B₁ A₂ B₂ : Tm} {s₁ s₂ : Srt} : s₁.NeverZero → s₂.NeverZero →
      Pi ⟨[Γ ⊢ .pi s₁ A₁ B₁ ∶ .sort s₁, Γ ⊢ .pi s₂ A₂ B₂ ∶ .sort s₂],
        Γ ⊢ .eqTy (.pi s₁ A₁ B₁) (.pi s₂ A₂ B₂) ⟶ .False' ∶ .sort .prop⟩
  /-- the reduct casts between the domains and between the codomains, so each pair is in one
  sort (a cast is formed at one sort); otherwise the cast is stuck -/
  | cast {Γ : Ctx} {A₁ B₁ A₂ B₂ e t : Tm} {s₁ s₂ i j : Srt} : s₁.NeverZero → s₂.NeverZero →
      Pi ⟨[Γ ⊢ .pi s₁ A₁ B₁ ∶ .sort s₁, Γ ⊢ .pi s₂ A₂ B₂ ∶ .sort s₂,
          Γ ⊢ A₁ ∶ .sort i, Γ ⊢ A₂ ∶ .sort i, (A₁ :: Γ) ⊢ B₁ ∶ .sort j, (A₂ :: Γ) ⊢ B₂ ∶ .sort j,
          Γ ⊢ e ∶ .eqTy (.pi s₁ A₁ B₁) (.pi s₂ A₂ B₂), Γ ⊢ t ∶ .pi s₁ A₁ B₁],
        Γ ⊢ .cast (.pi s₁ A₁ B₁) (.pi s₂ A₂ B₂) e t ⟶ .castPi A₁ B₁ A₂ B₂ e t
          ∶ .pi s₂ A₂ B₂⟩

end Spec
end F0
end STC
