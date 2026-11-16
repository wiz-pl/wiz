import STC.F0.Spec.Rule
/-!
# Unit and Empty

`Unit_s` and `Empty_s` at every sort; `True = Unit_prop`, `False = Empty_prop`. η for
`Unit` (all elements are convertible). `absurd` never computes.
-/


namespace STC
namespace F0
namespace Spec

inductive Unit : Rules
  | form {Γ : Ctx} {s : Srt} : Unit ⟨[.wf Γ], Γ ⊢ .unit s ∶ .sort s⟩
  | tt {Γ : Ctx} {s : Srt} : Unit ⟨[.wf Γ], Γ ⊢ .tt ∶ .unit s⟩
  | eta {Γ : Ctx} {t u : Tm} {s : Srt} :
      Unit ⟨[Γ ⊢ t ∶ .unit s, Γ ⊢ u ∶ .unit s], Γ ⊢ t ≡ u ∶ .unit s⟩
  | cong {Γ : Ctx} {s s' : Srt} : s.Equiv s' →
      Unit ⟨[.wf Γ], Γ ⊢ .unit s ≡ .unit s' ∶ .sort s⟩
  | eq {Γ : Ctx} {a b : Tm} {s : Srt} : s.NeverZero →
      Unit ⟨[Γ ⊢ a ∶ .unit s, Γ ⊢ b ∶ .unit s], Γ ⊢ .eq (.unit s) a b ⟶ .True' ∶ .sort .prop⟩
  | eqTy {Γ : Ctx} {u w : Srt} : u.NeverZero → w.NeverZero → u.Equiv w →
      Unit ⟨[.wf Γ], Γ ⊢ .eqTy (.unit u) (.unit w) ⟶ .True' ∶ .sort .prop⟩
  | eqTyApart {Γ : Ctx} {u w : Srt} : u.NeverZero → w.NeverZero → ¬ u.Equiv w →
      Unit ⟨[.wf Γ], Γ ⊢ .eqTy (.unit u) (.unit w) ⟶ .False' ∶ .sort .prop⟩
  | cast {Γ : Ctx} {e t : Tm} {u w : Srt} : u.NeverZero → u.Equiv w →
      Unit ⟨[Γ ⊢ e ∶ .eqTy (.unit u) (.unit w), Γ ⊢ t ∶ .unit u],
        Γ ⊢ .cast (.unit u) (.unit w) e t ⟶ .tt ∶ .unit w⟩

inductive Empty : Rules
  | form {Γ : Ctx} {s : Srt} : Empty ⟨[.wf Γ], Γ ⊢ .empty s ∶ .sort s⟩
  | absurd {Γ : Ctx} {M t : Tm} {k s : Srt} :
      Empty ⟨[Γ ⊢ M ∶ .sort k, Γ ⊢ t ∶ .empty s], Γ ⊢ .absurd M t ∶ M⟩
  | cong {Γ : Ctx} {s s' : Srt} : s.Equiv s' →
      Empty ⟨[.wf Γ], Γ ⊢ .empty s ≡ .empty s' ∶ .sort s⟩
  | absurdCong {Γ : Ctx} {M M' t t' : Tm} {k s : Srt} :
      Empty ⟨[Γ ⊢ M ≡ M' ∶ .sort k, Γ ⊢ t ≡ t' ∶ .empty s], Γ ⊢ .absurd M t ≡ .absurd M' t' ∶ M⟩
  | eq {Γ : Ctx} {a b : Tm} {s : Srt} : s.NeverZero →
      Empty ⟨[Γ ⊢ a ∶ .empty s, Γ ⊢ b ∶ .empty s], Γ ⊢ .eq (.empty s) a b ⟶ .True' ∶ .sort .prop⟩
  | eqTy {Γ : Ctx} {u w : Srt} : u.NeverZero → w.NeverZero → u.Equiv w →
      Empty ⟨[.wf Γ], Γ ⊢ .eqTy (.empty u) (.empty w) ⟶ .True' ∶ .sort .prop⟩
  | eqTyApart {Γ : Ctx} {u w : Srt} : u.NeverZero → w.NeverZero → ¬ u.Equiv w →
      Empty ⟨[.wf Γ], Γ ⊢ .eqTy (.empty u) (.empty w) ⟶ .False' ∶ .sort .prop⟩
  | cast {Γ : Ctx} {e t : Tm} {u w : Srt} : u.NeverZero → u.Equiv w →
      Empty ⟨[Γ ⊢ e ∶ .eqTy (.empty u) (.empty w), Γ ⊢ t ∶ .empty u],
        Γ ⊢ .cast (.empty u) (.empty w) e t ⟶ t ∶ .empty w⟩

end Spec
end F0
end STC
