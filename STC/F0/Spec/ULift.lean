import STC.F0.Spec.Rule
/-!
# ULift

`ULift_s A : Sort s` for `A : Sort k`, `max k s = s` (so `k ≤ s`): a one-field record with
η. Its observational rules go through the field. A lifted proposition above `Prop` is not
a proposition, but has one inhabitant up to conversion (η and irrelevance), so equations
at it are `True`.

F0 takes it at `s ∈ {u0, u1}` (`s.NeverZero`), which replaces `WizMeta`'s `u.NeverZero`
and removes T10's level-substitution wrinkle. There is no `Qty`/`qlit`: F0 has no
quantities, so `Desc.elim`'s quantity-generic methods are absent too.
-/


namespace STC
namespace F0
namespace Spec

/-- `var`: in the levelled variant `A ≡ B` is formed only at one sort, so `ULift A ≡ ULift B`
decomposes only when `A` and `B` are in one sort. -/
inductive ULift (var : EqTyVariant) : Rules
  | form {Γ : Ctx} {A : Tm} {k l : Srt} : (Srt.max k l).Equiv l →
      ULift var ⟨[Γ ⊢ A ∶ .sort k], Γ ⊢ .ulift l A ∶ .sort l⟩
  | up {Γ : Ctx} {A a : Tm} {l : Srt} :
      ULift var ⟨[Γ ⊢ .ulift l A ∶ .sort l, Γ ⊢ a ∶ A], Γ ⊢ .up a ∶ .ulift l A⟩
  | down {Γ : Ctx} {t A : Tm} {l : Srt} :
      ULift var ⟨[Γ ⊢ t ∶ .ulift l A], Γ ⊢ .down t ∶ A⟩
  | beta {Γ : Ctx} {A a : Tm} {l : Srt} :
      ULift var ⟨[Γ ⊢ .ulift l A ∶ .sort l, Γ ⊢ a ∶ A], Γ ⊢ .down (.up a) ⟶ a ∶ A⟩
  | downRed {Γ : Ctx} {t t' A : Tm} {l : Srt} :
      ULift var ⟨[Γ ⊢ t ⟶ t' ∶ .ulift l A], Γ ⊢ .down t ⟶ .down t' ∶ A⟩
  | eta {Γ : Ctx} {t A t' : Tm} {l : Srt} :
      ULift var ⟨[Γ ⊢ t ∶ .ulift l A, Γ ⊢ t' ∶ .ulift l A, Γ ⊢ .down t ≡ .down t' ∶ A],
        Γ ⊢ t ≡ t' ∶ .ulift l A⟩
  | cong {Γ : Ctx} {A A' : Tm} {l k l' : Srt} : l.Equiv l' →
      ULift var ⟨[Γ ⊢ .ulift l A ∶ .sort l, Γ ⊢ A ≡ A' ∶ .sort k],
        Γ ⊢ .ulift l A ≡ .ulift l' A' ∶ .sort l⟩
  | downCong {Γ : Ctx} {t t' A : Tm} {l : Srt} :
      ULift var ⟨[Γ ⊢ t ≡ t' ∶ .ulift l A], Γ ⊢ .down t ≡ .down t' ∶ A⟩
  /-- boxed proofs are all equal -/
  | eqProp {Γ : Ctx} {A a b : Tm} {k l : Srt} : l.NeverZero → k.IsZero →
      ULift var ⟨[Γ ⊢ A ∶ .sort k, Γ ⊢ a ∶ .ulift l A, Γ ⊢ b ∶ .ulift l A],
        Γ ⊢ .eq (.ulift l A) a b ⟶ .True' ∶ .sort .prop⟩
  | eq {Γ : Ctx} {A a b : Tm} {k l : Srt} : l.NeverZero → k.NeverZero →
      ULift var ⟨[Γ ⊢ A ∶ .sort k, Γ ⊢ a ∶ .ulift l A, Γ ⊢ b ∶ .ulift l A],
        Γ ⊢ .eq (.ulift l A) a b ⟶ .eq A (.down a) (.down b) ∶ .sort .prop⟩
  | eqTy {Γ : Ctx} {A B : Tm} {u w k k' : Srt} : u.NeverZero → u.Equiv w →
      (var = .levelled → k.Equiv k') →
      ULift var ⟨[Γ ⊢ .ulift u A ∶ .sort u, Γ ⊢ .ulift w B ∶ .sort w, Γ ⊢ A ∶ .sort k,
          Γ ⊢ B ∶ .sort k'],
        Γ ⊢ .eqTy (.ulift u A) (.ulift w B) ⟶ .eqTy A B ∶ .sort .prop⟩
  | eqTyApart {Γ : Ctx} {A B : Tm} {u w : Srt} : u.NeverZero → w.NeverZero → ¬ u.Equiv w →
      ULift var ⟨[Γ ⊢ .ulift u A ∶ .sort u, Γ ⊢ .ulift w B ∶ .sort w],
        Γ ⊢ .eqTy (.ulift u A) (.ulift w B) ⟶ .False' ∶ .sort .prop⟩
  /-- the reduct casts between the contents, so they are in one sort (in both variants) -/
  | cast {Γ : Ctx} {A B e t : Tm} {u w k : Srt} : u.NeverZero → u.Equiv w →
      ULift var ⟨[Γ ⊢ .ulift u A ∶ .sort u, Γ ⊢ .ulift w B ∶ .sort w, Γ ⊢ A ∶ .sort k,
          Γ ⊢ B ∶ .sort k, Γ ⊢ e ∶ .eqTy (.ulift u A) (.ulift w B),
          Γ ⊢ t ∶ .ulift u A],
        Γ ⊢ .cast (.ulift u A) (.ulift w B) e t ⟶ .up (.cast A B e (.down t)) ∶ .ulift w B⟩

end Spec
end F0
end STC
