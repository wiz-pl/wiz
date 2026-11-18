import STC.F0.Spec.Rule
/-!
# Observational equality: formation, proofs, and the rules that do not belong to a former

`a =_A b` and `A ≡ B` are propositions that compute: by the type `A` (each former's file
has its rule), and here

* at a proposition `A`, `a =_A b ⟶ True`;
* two propositions are equal when equivalent: `P ≡ Q ⟶ (P → Q) × (Q → P)`;
* two different canonical formers (neither type a proposition) are not equal.

`refl`, `reflTy`, `transp` are proofs and have no rules. `cast` is the one operation with
a relevant result; its rules are in the formers' files, and here its congruence, which
does **not** compare the proofs.

**Formation.** `a =_A b` is formed at any sort (D6): the reducts of the rules contain
equations at propositions (the `Σ` rule at a proof component), so with a "never `Prop`"
restriction a reduct of a well-formed type would not be well formed.
-/


namespace STC
namespace F0
namespace Spec

inductive Eq : Rules
  | eq {Γ : Ctx} {A a b : Tm} {s : Srt} :
      Eq ⟨[Γ ⊢ A ∶ .sort s, Γ ⊢ a ∶ A, Γ ⊢ b ∶ A], Γ ⊢ .eq A a b ∶ .sort .prop⟩
  | refl {Γ : Ctx} {A a : Tm} {s : Srt} :
      Eq ⟨[Γ ⊢ A ∶ .sort s, Γ ⊢ a ∶ A], Γ ⊢ .refl A a ∶ .eq A a a⟩
  | reflTy {Γ : Ctx} {A : Tm} {s : Srt} :
      Eq ⟨[Γ ⊢ A ∶ .sort s], Γ ⊢ .reflTy A ∶ .eqTy A A⟩
  /-- transport into a `Prop`-valued family; with `cast` it gives J -/
  | transp {Γ : Ctx} {A a b P p e : Tm} {s : Srt} :
      Eq ⟨[Γ ⊢ A ∶ .sort s, Γ ⊢ a ∶ A, Γ ⊢ b ∶ A, Γ ⊢ P ∶ .transpMotiveTy s A a,
          Γ ⊢ p ∶ .app (.app P a) (.refl A a), Γ ⊢ e ∶ .eq A a b],
        Γ ⊢ .transp A a P p b e ∶ .app (.app P b) e⟩
  | cast {Γ : Ctx} {A B e t : Tm} {s : Srt} :
      Eq ⟨[Γ ⊢ A ∶ .sort s, Γ ⊢ B ∶ .sort s, Γ ⊢ e ∶ .eqTy A B, Γ ⊢ t ∶ A],
        Γ ⊢ .cast A B e t ∶ B⟩
  | eqCong {Γ : Ctx} {A A' a a' b b' : Tm} {s : Srt} :
      Eq ⟨[Γ ⊢ A ≡ A' ∶ .sort s, Γ ⊢ a ≡ a' ∶ A, Γ ⊢ b ≡ b' ∶ A],
        Γ ⊢ .eq A a b ≡ .eq A' a' b' ∶ .sort .prop⟩
  | eqTyCong {Γ : Ctx} {A A' B B' : Tm} {s s' : Srt} :
      Eq ⟨[Γ ⊢ A ≡ A' ∶ .sort s, Γ ⊢ B ≡ B' ∶ .sort s'],
        Γ ⊢ .eqTy A B ≡ .eqTy A' B' ∶ .sort .prop⟩
  /-- the proofs `e`, `e'` are not compared -/
  | castCong {Γ : Ctx} {A A' B B' e e' t t' : Tm} {s : Srt} :
      Eq ⟨[Γ ⊢ A ≡ A' ∶ .sort s, Γ ⊢ B ≡ B' ∶ .sort s, Γ ⊢ e ∶ .eqTy A B,
          Γ ⊢ e' ∶ .eqTy A' B', Γ ⊢ t ≡ t' ∶ A],
        Γ ⊢ .cast A B e t ≡ .cast A' B' e' t' ∶ B⟩
  -- weak-head reduction looks at the type of an equation, and at the two types of a cast
  | eqRed {Γ : Ctx} {A A' a b : Tm} {s : Srt} :
      Eq ⟨[Γ ⊢ A ⟶ A' ∶ .sort s, Γ ⊢ a ∶ A, Γ ⊢ b ∶ A],
        Γ ⊢ .eq A a b ⟶ .eq A' a b ∶ .sort .prop⟩
  | eqTyRedL {Γ : Ctx} {A A' B : Tm} {s s' : Srt} :
      Eq ⟨[Γ ⊢ A ⟶ A' ∶ .sort s, Γ ⊢ B ∶ .sort s'],
        Γ ⊢ .eqTy A B ⟶ .eqTy A' B ∶ .sort .prop⟩
  | eqTyRedR {Γ : Ctx} {A B B' : Tm} {s s' : Srt} :
      Eq ⟨[Γ ⊢ A ∶ .sort s, Γ ⊢ B ⟶ B' ∶ .sort s'],
        Γ ⊢ .eqTy A B ⟶ .eqTy A B' ∶ .sort .prop⟩
  | castRedL {Γ : Ctx} {A A' B e t : Tm} {s : Srt} :
      Eq ⟨[Γ ⊢ A ⟶ A' ∶ .sort s, Γ ⊢ B ∶ .sort s, Γ ⊢ e ∶ .eqTy A B, Γ ⊢ t ∶ A],
        Γ ⊢ .cast A B e t ⟶ .cast A' B e t ∶ B⟩
  | castRedR {Γ : Ctx} {A B B' e t : Tm} {s : Srt} :
      Eq ⟨[Γ ⊢ A ∶ .sort s, Γ ⊢ B ⟶ B' ∶ .sort s, Γ ⊢ e ∶ .eqTy A B, Γ ⊢ t ∶ A],
        Γ ⊢ .cast A B e t ⟶ .cast A B' e t ∶ B⟩
  /-- an equation between two proofs -/
  | eqAtProp {Γ : Ctx} {A a b : Tm} {s : Srt} : s.IsZero →
      Eq ⟨[Γ ⊢ A ∶ .sort s, Γ ⊢ a ∶ A, Γ ⊢ b ∶ A],
        Γ ⊢ .eq A a b ⟶ .True' ∶ .sort .prop⟩
  /-- two propositions are equal when equivalent, whatever their shapes -/
  | eqTyProps {Γ : Ctx} {A B : Tm} {s s' : Srt} : s.IsZero → s'.IsZero →
      Eq ⟨[Γ ⊢ A ∶ .sort s, Γ ⊢ B ∶ .sort s'],
        Γ ⊢ .eqTy A B ⟶ .iff A B ∶ .sort .prop⟩
  /-- no confusion of type formers -/
  | eqTyFormers {Γ : Ctx} {A B : Tm} {s s' : Srt} {f f' : Tm.Former} :
      s.NeverZero → s'.NeverZero → A.former? = some f → B.former? = some f' → f ≠ f' →
      Eq ⟨[Γ ⊢ A ∶ .sort s, Γ ⊢ B ∶ .sort s'],
        Γ ⊢ .eqTy A B ⟶ .False' ∶ .sort .prop⟩

end Spec
end F0
end STC
