import STC.F0.Spec.Rule
/-!
# Σ

`(x : A) × B` in `Sort s`, `s = max i j` (so a `Σ` of two propositions is one). Pairs,
projections, β as reductions, η as a conversion rule. No `split` (it is `Σ`-η plus
`let`), and no quantities.

The rule for an equation between two such types is in `EqTyLevelled.lean` (F0) and
`EqTyCross.lean` (the variant that models the kernels).
-/


namespace STC
namespace F0
namespace Spec

inductive Sigma : Rules
  | form {Γ : Ctx} {A B : Tm} {i j s : Srt} : s.Equiv (.max i j) →
      Sigma ⟨[Γ ⊢ A ∶ .sort i, (A :: Γ) ⊢ B ∶ .sort j], Γ ⊢ .sigma s A B ∶ .sort s⟩
  | pair {Γ : Ctx} {A B a b : Tm} {s : Srt} :
      Sigma ⟨[Γ ⊢ .sigma s A B ∶ .sort s, Γ ⊢ a ∶ A, Γ ⊢ b ∶ B.inst a],
        Γ ⊢ .pair a b ∶ .sigma s A B⟩
  | fst {Γ : Ctx} {p A B : Tm} {s : Srt} : Sigma ⟨[Γ ⊢ p ∶ .sigma s A B], Γ ⊢ .fst p ∶ A⟩
  | snd {Γ : Ctx} {p A B : Tm} {s : Srt} :
      Sigma ⟨[Γ ⊢ p ∶ .sigma s A B], Γ ⊢ .snd p ∶ B.inst (.fst p)⟩
  | fstBeta {Γ : Ctx} {A B a b : Tm} {s : Srt} :
      Sigma ⟨[Γ ⊢ .sigma s A B ∶ .sort s, Γ ⊢ a ∶ A, Γ ⊢ b ∶ B.inst a],
        Γ ⊢ .fst (.pair a b) ⟶ a ∶ A⟩
  | sndBeta {Γ : Ctx} {A B a b : Tm} {s : Srt} :
      Sigma ⟨[Γ ⊢ .sigma s A B ∶ .sort s, Γ ⊢ a ∶ A, Γ ⊢ b ∶ B.inst a],
        Γ ⊢ .snd (.pair a b) ⟶ b ∶ B.inst a⟩
  | fstRed {Γ : Ctx} {p p' A B : Tm} {s : Srt} :
      Sigma ⟨[Γ ⊢ p ⟶ p' ∶ .sigma s A B], Γ ⊢ .fst p ⟶ .fst p' ∶ A⟩
  | sndRed {Γ : Ctx} {p p' A B : Tm} {s : Srt} :
      Sigma ⟨[Γ ⊢ p ⟶ p' ∶ .sigma s A B], Γ ⊢ .snd p ⟶ .snd p' ∶ B.inst (.fst p)⟩
  /-- η, as extensionality -/
  | eta {Γ : Ctx} {p A B p' : Tm} {s : Srt} :
      Sigma ⟨[Γ ⊢ p ∶ .sigma s A B, Γ ⊢ p' ∶ .sigma s A B,
          Γ ⊢ .fst p ≡ .fst p' ∶ A, Γ ⊢ .snd p ≡ .snd p' ∶ B.inst (.fst p)],
        Γ ⊢ p ≡ p' ∶ .sigma s A B⟩
  | cong {Γ : Ctx} {A A' B B' : Tm} {i j s s' : Srt} : s.Equiv (.max i j) → s'.Equiv (.max i j) →
      Sigma ⟨[Γ ⊢ A ∶ .sort i, Γ ⊢ A ≡ A' ∶ .sort i, (A :: Γ) ⊢ B ≡ B' ∶ .sort j],
        Γ ⊢ .sigma s A B ≡ .sigma s' A' B' ∶ .sort s⟩
  | fstCong {Γ : Ctx} {p p' A B : Tm} {s : Srt} :
      Sigma ⟨[Γ ⊢ p ≡ p' ∶ .sigma s A B], Γ ⊢ .fst p ≡ .fst p' ∶ A⟩
  | sndCong {Γ : Ctx} {p p' A B : Tm} {s : Srt} :
      Sigma ⟨[Γ ⊢ p ≡ p' ∶ .sigma s A B], Γ ⊢ .snd p ≡ .snd p' ∶ B.inst (.fst p)⟩
  /-- an equation between pairs: the first components, and the second ones along a cast
  whose proof transports along the first components' equation -/
  | eq {Γ : Ctx} {A B a b : Tm} {s i : Srt} : s.NeverZero → ¬ i.IsZero →
      Sigma ⟨[Γ ⊢ .sigma s A B ∶ .sort s, Γ ⊢ A ∶ .sort i, Γ ⊢ a ∶ .sigma s A B,
          Γ ⊢ b ∶ .sigma s A B],
        Γ ⊢ .eq (.sigma s A B) a b ⟶ .eqSigma A B a b ∶ .sort .prop⟩
  /-- the same at a proof first component: `a.1 ≡ b.1` by irrelevance, so the cast's proof
  is `reflTy (B a.1)`; the kernels do not form `transp` along a proposition -/
  | eqProof {Γ : Ctx} {A B a b : Tm} {s i : Srt} : s.NeverZero → i.IsZero →
      Sigma ⟨[Γ ⊢ .sigma s A B ∶ .sort s, Γ ⊢ A ∶ .sort i, Γ ⊢ a ∶ .sigma s A B,
          Γ ⊢ b ∶ .sigma s A B],
        Γ ⊢ .eq (.sigma s A B) a b ⟶ .eqSigmaProof A B a b ∶ .sort .prop⟩
  | eqTyApart {Γ : Ctx} {A₁ B₁ A₂ B₂ : Tm} {s₁ s₂ : Srt} : s₁.NeverZero → s₂.NeverZero →
      Sigma ⟨[Γ ⊢ .sigma s₁ A₁ B₁ ∶ .sort s₁, Γ ⊢ .sigma s₂ A₂ B₂ ∶ .sort s₂],
        Γ ⊢ .eqTy (.sigma s₁ A₁ B₁) (.sigma s₂ A₂ B₂) ⟶ .False' ∶ .sort .prop⟩
  /-- as for `Π`: the components pairwise in one sort -/
  | cast {Γ : Ctx} {A₁ B₁ A₂ B₂ e t : Tm} {s₁ s₂ i j : Srt} : s₁.NeverZero → s₂.NeverZero →
      Sigma ⟨[Γ ⊢ .sigma s₁ A₁ B₁ ∶ .sort s₁, Γ ⊢ .sigma s₂ A₂ B₂ ∶ .sort s₂,
          Γ ⊢ A₁ ∶ .sort i, Γ ⊢ A₂ ∶ .sort i, (A₁ :: Γ) ⊢ B₁ ∶ .sort j, (A₂ :: Γ) ⊢ B₂ ∶ .sort j,
          Γ ⊢ e ∶ .eqTy (.sigma s₁ A₁ B₁) (.sigma s₂ A₂ B₂), Γ ⊢ t ∶ .sigma s₁ A₁ B₁],
        Γ ⊢ .cast (.sigma s₁ A₁ B₁) (.sigma s₂ A₂ B₂) e t ⟶ .castSigma A₁ B₁ A₂ B₂ e t
          ∶ .sigma s₂ A₂ B₂⟩

end Spec
end F0
end STC
