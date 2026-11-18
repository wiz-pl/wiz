import STC.F0.Spec.Rule
/-!
# Structural rules, universes, proof irrelevance

`Sort s : Sort (s+1)` for `s ∈ {prop, u0}`; `Sort u1` is a type but not a term (no
`Sort 3`). Non-cumulative, as in Wiz. Level side conditions are closed equalities
(`Srt.Equiv`, `Srt.IsZero`, `Srt.NeverZero`), decidable by `rfl`/`decide`.

F0 has no regularity (`InReg`): `cast A A e t` does not reduce to `t` in conversion. That
is the design decision that keeps the Abel–Coquand loop out (§4, D1).
-/


namespace STC
namespace F0
namespace Spec

inductive Core : Rules
  | wfNil : Core ⟨[], .wf []⟩
  | wfCons {Γ : Ctx} {A : Tm} {s : Srt} : Core ⟨[.wf Γ, Γ ⊢ A ∶ .sort s], .wf (A :: Γ)⟩
  | var {Γ : Ctx} {A : Tm} {i : Nat} : Γ.lookup i = some A → Core ⟨[.wf Γ], Γ ⊢ .var i ∶ A⟩
  | sort {Γ : Ctx} {s s' : Srt} : s.succ? = some s' →
      Core ⟨[.wf Γ], Γ ⊢ .sort s ∶ .sort s'⟩
  /-- conversion -/
  | conv {Γ : Ctx} {t A B : Tm} {s : Srt} : Core ⟨[Γ ⊢ t ∶ A, Γ ⊢ A ≡ B ∶ .sort s], Γ ⊢ t ∶ B⟩
  | eqConv {Γ : Ctx} {t u A B : Tm} {s : Srt} :
      Core ⟨[Γ ⊢ t ≡ u ∶ A, Γ ⊢ A ≡ B ∶ .sort s], Γ ⊢ t ≡ u ∶ B⟩
  | redConv {Γ : Ctx} {t u A B : Tm} {s : Srt} :
      Core ⟨[Γ ⊢ t ⟶ u ∶ A, Γ ⊢ A ≡ B ∶ .sort s], Γ ⊢ t ⟶ u ∶ B⟩
  | refl {Γ : Ctx} {t A : Tm} : Core ⟨[Γ ⊢ t ∶ A], Γ ⊢ t ≡ t ∶ A⟩
  | symm {Γ : Ctx} {t u A : Tm} : Core ⟨[Γ ⊢ t ≡ u ∶ A], Γ ⊢ u ≡ t ∶ A⟩
  | trans {Γ : Ctx} {t u A w : Tm} : Core ⟨[Γ ⊢ t ≡ u ∶ A, Γ ⊢ u ≡ w ∶ A], Γ ⊢ t ≡ w ∶ A⟩
  /-- a reduction step is a conversion -/
  | redEq {Γ : Ctx} {t u A : Tm} : Core ⟨[Γ ⊢ t ⟶ u ∶ A], Γ ⊢ t ≡ u ∶ A⟩
  /-- definitional proof irrelevance: at a proposition any two terms are convertible -/
  | irrel {Γ : Ctx} {A t u : Tm} {s : Srt} : s.IsZero →
      Core ⟨[Γ ⊢ A ∶ .sort s, Γ ⊢ t ∶ A, Γ ⊢ u ∶ A], Γ ⊢ t ≡ u ∶ A⟩
  /-- equality of universes: propext at `Prop`, type equality above it -/
  | eqProp {Γ : Ctx} {a b : Tm} {s : Srt} : s.IsZero →
      Core ⟨[Γ ⊢ a ∶ .sort s, Γ ⊢ b ∶ .sort s], Γ ⊢ .eq (.sort s) a b ⟶ .iff a b ∶ .sort .prop⟩
  | eqType {Γ : Ctx} {a b : Tm} {s : Srt} : s.NeverZero →
      Core ⟨[Γ ⊢ a ∶ .sort s, Γ ⊢ b ∶ .sort s], Γ ⊢ .eq (.sort s) a b ⟶ .eqTy a b ∶ .sort .prop⟩
  | eqTySort {Γ : Ctx} {u w : Srt} : u.Equiv w →
      Core ⟨[.wf Γ], Γ ⊢ .eqTy (.sort u) (.sort w) ⟶ .True' ∶ .sort .prop⟩
  /-- two different closed sorts: no level substitution to worry about any more -/
  | eqTySortApart {Γ : Ctx} {u w : Srt} : ¬ u.Equiv w →
      Core ⟨[.wf Γ], Γ ⊢ .eqTy (.sort u) (.sort w) ⟶ .False' ∶ .sort .prop⟩
  /-- the identity cast at a universe -/
  | castSort {Γ : Ctx} {e t : Tm} {u w : Srt} : u.Equiv w →
      Core ⟨[Γ ⊢ e ∶ .eqTy (.sort u) (.sort w), Γ ⊢ t ∶ .sort u],
        Γ ⊢ .cast (.sort u) (.sort w) e t ⟶ t ∶ .sort w⟩

end Spec
end F0
end STC
