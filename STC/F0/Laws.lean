import STC.F0.Spec.Fragments
/-!
# The renaming and substitution calculus on F0 terms

These are the routine lemmas every later proof starts from: identity and composition of
renamings, the interaction of renaming with substitution, that substitution by variables
is the identity, and that the reducts of the rules commute with renaming. They are the
`WizMeta/Spec/{Laws,Weakening}.lean` calculus, restricted to F0 (no quantities, levels,
descriptions or payloads).

The judgment-level renaming lemma is in `Renaming.lean`.
-/


namespace STC
namespace F0
namespace Tm

theorem upRen_id : upRen id = id := by
  funext i; cases i <;> rfl

theorem upRen_comp (ρ ρ' : Nat → Nat) : upRen (ρ' ∘ ρ) = upRen ρ' ∘ upRen ρ := by
  funext i; cases i <;> rfl

theorem ren_id (t : Tm) : t.ren id = t := by
  induction t <;> simp_all [ren, upRen_id]

theorem ren_ren (t : Tm) : ∀ (ρ ρ' : Nat → Nat), (t.ren ρ).ren ρ' = t.ren (ρ' ∘ ρ) := by
  induction t <;> intro ρ ρ' <;> simp_all [ren, upRen_comp]

theorem upSub_var : upSub Tm.var = Tm.var := by
  funext i; cases i <;> rfl

theorem sub_var (t : Tm) : t.sub Tm.var = t := by
  induction t <;> simp_all [sub, upSub_var]

/-- Weakening twice is weakening by two. -/
theorem shift_shift (t : Tm) : t.shift.shift = t.shiftN 2 := by
  simp only [shift, shiftN, ren_ren]
  rfl

theorem upSub_upRen (σ : Nat → Tm) (ρ : Nat → Nat) : upSub σ ∘ upRen ρ = upSub (σ ∘ ρ) := by
  funext i; cases i <;> rfl

theorem sub_ren (t : Tm) : ∀ (σ : Nat → Tm) (ρ : Nat → Nat), (t.ren ρ).sub σ = t.sub (σ ∘ ρ) := by
  induction t <;> intro σ ρ <;> simp_all [ren, sub, upSub_upRen]

theorem ren_upSub (ρ : Nat → Nat) (σ : Nat → Tm) :
    (fun i => (upSub σ i).ren (upRen ρ)) = upSub (fun i => (σ i).ren ρ) := by
  funext i; cases i with
  | zero => rfl
  | succ n => simp only [upSub, shift, ren_ren]; rfl

theorem ren_sub (t : Tm) : ∀ (ρ : Nat → Nat) (σ : Nat → Tm), (t.sub σ).ren ρ = t.sub (fun i => (σ i).ren ρ) := by
  induction t <;> intro ρ σ <;> simp_all [ren, sub, ← ren_upSub]

theorem sub_upSub (σ τ : Nat → Tm) :
    (fun i => (upSub σ i).sub (upSub τ)) = upSub (fun i => (σ i).sub τ) := by
  funext i; cases i with
  | zero => rfl
  | succ n =>
    simp only [upSub, shift, sub_ren, ren_sub]
    rfl

theorem sub_sub (t : Tm) : ∀ (σ τ : Nat → Tm), (t.sub σ).sub τ = t.sub (fun i => (σ i).sub τ) := by
  induction t <;> intro σ τ <;> simp_all [sub, ← sub_upSub]

theorem ren_eq_sub (t : Tm) (ρ : Nat → Nat) : t.ren ρ = t.sub (fun i => .var (ρ i)) := by
  have h := sub_ren t Tm.var ρ
  rw [sub_var] at h
  exact h

/-- Renaming commutes with instantiating the innermost variable. -/
theorem ren_inst (b a : Tm) (ρ : Nat → Nat) : (b.inst a).ren ρ = (b.ren (upRen ρ)).inst (a.ren ρ) := by
  simp only [inst, ren_sub, sub_ren]
  congr 1; funext i; cases i <;> rfl

theorem ren_shift (t : Tm) (ρ : Nat → Nat) : t.shift.ren (upRen ρ) = (t.ren ρ).shift := by
  simp only [shift, ren_ren]; rfl

/-! ### The reducts commute with renaming -/

theorem ren_True' (ρ : Nat → Nat) : True'.ren ρ = True' := rfl
theorem ren_False' (ρ : Nat → Nat) : False'.ren ρ = False' := rfl

theorem upRen_succ (ρ : Nat → Nat) : upRen ρ ∘ Nat.succ = Nat.succ ∘ ρ := rfl

theorem ren_shift2 (t : Tm) (ρ : Nat → Nat) : (t.shiftN 2).ren (upRen (upRen ρ)) = (t.ren ρ).shiftN 2 := by
  simp only [shiftN, ren_ren]; rfl

theorem ren_iff (a b : Tm) (ρ : Nat → Nat) : (iff a b).ren ρ = iff (a.ren ρ) (b.ren ρ) := by
  simp only [iff, ren, ren_shift, ren_shift2]

theorem ren_eqPi (A B f g : Tm) (ρ : Nat → Nat) :
    (eqPi A B f g).ren ρ = eqPi (A.ren ρ) (B.ren (upRen ρ)) (f.ren ρ) (g.ren ρ) := by
  simp only [eqPi, ren, ren_shift]; rfl

theorem ren_under1 (B : Tm) (ρ : Nat → Nat) : (B.under 1).ren (upRen (upRen ρ)) = (B.ren (upRen ρ)).under 1 := by
  simp only [under, ren_ren]; congr 1; funext i; cases i <;> rfl

theorem ren_castPi (A₁ B₁ A₂ B₂ e t : Tm) (ρ : Nat → Nat) :
    (castPi A₁ B₁ A₂ B₂ e t).ren ρ =
      castPi (A₁.ren ρ) (B₁.ren (upRen ρ)) (A₂.ren ρ) (B₂.ren (upRen ρ)) (e.ren ρ) (t.ren ρ) := by
  simp only [castPi, ren, ren_inst, ren_under1, ren_shift]; rfl

theorem ren_under2 (B : Tm) (ρ : Nat → Nat) :
    (B.under 2).ren (upRen (upRen (upRen ρ))) = (B.ren (upRen ρ)).under 2 := by
  simp only [under, ren_ren]; congr 1; funext i; rcases i with _ | _ | _ | i <;> rfl

theorem ren_eqSigmaTransport (A B a b : Tm) (ρ : Nat → Nat) :
    (eqSigmaTransport A B a b).ren (upRen ρ) =
      eqSigmaTransport (A.ren ρ) (B.ren (upRen ρ)) (a.ren ρ) (b.ren ρ) := by
  simp only [eqSigmaTransport, ren, ren_shift, ren_shift2, ren_inst, ren_under2]; rfl

theorem ren_eqSigma (A B a b : Tm) (ρ : Nat → Nat) :
    (eqSigma A B a b).ren ρ = eqSigma (A.ren ρ) (B.ren (upRen ρ)) (a.ren ρ) (b.ren ρ) := by
  simp only [eqSigma, ren, ren_shift, ren_inst, ren_eqSigmaTransport]

theorem ren_eqSigmaProof (A B a b : Tm) (ρ : Nat → Nat) :
    (eqSigmaProof A B a b).ren ρ = eqSigmaProof (A.ren ρ) (B.ren (upRen ρ)) (a.ren ρ) (b.ren ρ) := by
  simp only [eqSigmaProof, ren, ren_shift, ren_inst]

theorem ren_eqTyPi (A₁ B₁ A₂ B₂ : Tm) (ρ : Nat → Nat) :
    (eqTyPi A₁ B₁ A₂ B₂).ren ρ = eqTyPi (A₁.ren ρ) (B₁.ren (upRen ρ)) (A₂.ren ρ) (B₂.ren (upRen ρ)) := by
  simp only [eqTyPi, ren, ren_shift, ren_shift2, ren_inst, ren_under1, ren_under2]; rfl

theorem ren_eqTySigma (A₁ B₁ A₂ B₂ : Tm) (ρ : Nat → Nat) :
    (eqTySigma A₁ B₁ A₂ B₂).ren ρ = eqTySigma (A₁.ren ρ) (B₁.ren (upRen ρ)) (A₂.ren ρ) (B₂.ren (upRen ρ)) := by
  simp only [eqTySigma, ren, ren_shift, ren_shift2, ren_inst, ren_under1, ren_under2]; rfl

theorem ren_castSigma (A₁ B₁ A₂ B₂ e t : Tm) (ρ : Nat → Nat) :
    (castSigma A₁ B₁ A₂ B₂ e t).ren ρ =
      castSigma (A₁.ren ρ) (B₁.ren (upRen ρ)) (A₂.ren ρ) (B₂.ren (upRen ρ)) (e.ren ρ) (t.ren ρ) := by
  simp only [castSigma, ren, ren_inst]

theorem ren_transpMotiveTy (s : Srt) (A a : Tm) (ρ : Nat → Nat) :
    (transpMotiveTy s A a).ren ρ = transpMotiveTy s (A.ren ρ) (a.ren ρ) := by
  simp only [transpMotiveTy, ren, ren_shift]; rfl

theorem ren_branches (bl : List Tm) (ρ : Nat → Nat) : (branches bl).ren ρ = branches (bl.map (ren ρ)) := by
  induction bl with
  | nil => rfl
  | cons b bl ih => simp only [branches, ren, ih, List.map_cons]

theorem former_ren (t : Tm) (ρ : Nat → Nat) : (t.ren ρ).former? = t.former? := by
  cases t <;> rfl

end Tm

namespace Spec

/-- The action of a renaming on a judgment whose context becomes `Δ`. -/
def Jdg.ren (ρ : Nat → Nat) (Δ : Ctx) : Jdg → Jdg
  | .wf _ => .wf Δ
  | .ty _ t A => .ty Δ (t.ren ρ) (A.ren ρ)
  | .eq _ t u A => .eq Δ (t.ren ρ) (u.ren ρ) (A.ren ρ)
  | .red _ t u A => .red Δ (t.ren ρ) (u.ren ρ) (A.ren ρ)

/-- `ρ` maps the variables of `Γ` to variables of `Δ` of the renamed types. -/
def RenOK (ρ : Nat → Nat) (Γ Δ : Ctx) : Prop :=
  ∀ i A, Γ.lookup i = some A → Δ.lookup (ρ i) = some (A.ren ρ)

theorem Ctx.lookup_zero (A : Tm) (Γ : Ctx) : Ctx.lookup (A :: Γ) 0 = some A.shift := rfl

theorem Ctx.lookup_succ (A : Tm) (Γ : Ctx) (i : Nat) :
    Ctx.lookup (A :: Γ) (i + 1) = (Ctx.lookup Γ i).map Tm.shift := by
  simp only [Ctx.lookup, List.getElem?_cons_succ, Option.map_map]
  congr 1; funext t; simp only [Function.comp, Tm.shift, Tm.shiftN, Tm.ren_ren]; rfl

theorem RenOK.up {ρ : Nat → Nat} {Γ Δ : Ctx} (h : RenOK ρ Γ Δ) (A : Tm) :
    RenOK (Tm.upRen ρ) (A :: Γ) (A.ren ρ :: Δ) := by
  intro i B hB
  cases i with
  | zero =>
    rw [Ctx.lookup_zero] at hB; cases hB
    rw [Tm.ren_shift]; rfl
  | succ i =>
    rw [Ctx.lookup_succ] at hB
    cases hΓ : Ctx.lookup Γ i with
    | none => rw [hΓ] at hB; cases hB
    | some C =>
      rw [hΓ] at hB; cases hB
      show Ctx.lookup (A.ren ρ :: Δ) (ρ i + 1) = _
      rw [Ctx.lookup_succ, h i C hΓ, Tm.ren_shift]; rfl

theorem RenOK.succ (Γ : Ctx) (B : Tm) : RenOK Nat.succ Γ (B :: Γ) := by
  intro i A h
  show Ctx.lookup (B :: Γ) (i + 1) = _
  rw [Ctx.lookup_succ, h]; rfl

end Spec
end F0
end STC
