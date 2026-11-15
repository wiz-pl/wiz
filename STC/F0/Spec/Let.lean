import STC.F0.Spec.Rule
/-!
# `let`, `letUnit` and ascription

`let` is transparent: its body is typed with the variable replaced by the value, which is
what the kernels' "the body sees `x := v`" amounts to. `letUnit u b` (the kernel's and the
elaborator's unit binder) is typed with `u ∶ Unit s` and `b ∶ B` and reduces to `b`; the
binder has no usage (there are no quantities in F0). Both formers reduce away, as does
`ann`.
-/


namespace STC
namespace F0
namespace Spec

inductive Let : Rules
  | letE {Γ : Ctx} {A v B b : Tm} {s : Srt} :
      Let ⟨[Γ ⊢ A ∶ .sort s, Γ ⊢ v ∶ A, Γ ⊢ b.inst v ∶ B], Γ ⊢ .letE A v b ∶ B⟩
  | zeta {Γ : Ctx} {A v B b : Tm} {s : Srt} :
      Let ⟨[Γ ⊢ A ∶ .sort s, Γ ⊢ v ∶ A, Γ ⊢ b.inst v ∶ B], Γ ⊢ .letE A v b ⟶ b.inst v ∶ B⟩
  | letUnit {Γ : Ctx} {u B b : Tm} {s : Srt} :
      Let ⟨[Γ ⊢ u ∶ .unit s, Γ ⊢ b ∶ B], Γ ⊢ .letUnit u b ∶ B⟩
  | letUnitRed {Γ : Ctx} {u B b : Tm} {s : Srt} :
      Let ⟨[Γ ⊢ u ∶ .unit s, Γ ⊢ b ∶ B], Γ ⊢ .letUnit u b ⟶ b ∶ B⟩
  | ann {Γ : Ctx} {A t : Tm} {s : Srt} :
      Let ⟨[Γ ⊢ A ∶ .sort s, Γ ⊢ t ∶ A], Γ ⊢ .ann t A ∶ A⟩
  | annRed {Γ : Ctx} {A t : Tm} {s : Srt} :
      Let ⟨[Γ ⊢ A ∶ .sort s, Γ ⊢ t ∶ A], Γ ⊢ .ann t A ⟶ t ∶ A⟩

end Spec
end F0
end STC
