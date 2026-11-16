import STC.F0.Renaming
/-!
# The substitution lemma for F0

The companion of `Renaming.lean`, in the same architecture (which is
`WizMeta/Spec/Substitution.lean`'s): a substitution sending each variable of `Γ` to a term
of `Δ` at the substituted type (`SubOK`), a closure property per rule set (`SubClosed`),
and the lemma for `F0Base` (the fragment without the two `Struct` rules; their closure is
`StructSubClosed`, `F0/Typing.lean`). Lifting a substitution under a binder needs the renaming lemma
(`F0Base_rename`): the variables of `Γ`, weakened into the extended context, are renamed.

The rule-level work is the same as for renaming, with `sub` in place of `ren`: a rule
with a premise under a binder has the binder's type among its premises (`Pi.lam`,
`Pi.beta`, `Pi.eta`, `Pi.cong`, `Sigma.cong`, `EqTyLevelled.pi/sigma`), and the signature
is closed (`Sig.Closed`).

The concrete companions (`F0Base_subst`, `F0Base_subst_eq`, `F0Base_subst_red`) instantiate the
substitution at `[a/0]`. The well-formedness of `Γ` that `F0Base_weakening` takes as a
hypothesis is not needed: context validity (`F0Base_ctx`, `Γ ⊢ J → ⊢ Γ`) is proved below from
the rules, so the companions have the shape of the implementation note.
-/


namespace STC
namespace F0
namespace Tm

/-! ### The term-level substitution laws

`Laws.lean` has identity/composition of renamings and the interaction of renaming with
substitution; here are substitution's own laws and the reducts' stability under it. -/

theorem sub_congr (t : Tm) {σ τ : Nat → Tm} (h : ∀ i, σ i = τ i) : t.sub σ = t.sub τ := by
  have : σ = τ := funext h
  rw [this]

theorem sub_inst (b a : Tm) (σ : Nat → Tm) : (b.inst a).sub σ = (b.sub (upSub σ)).inst (a.sub σ) := by
  simp only [inst, sub_sub]
  apply sub_congr; intro i; cases i with
  | zero => rfl
  | succ n => simp only [one, sub, upSub, shift, sub_ren]; exact (sub_var _).symm.trans (sub_congr _ fun _ => rfl)

theorem sub_shift (t : Tm) (σ : Nat → Tm) : t.shift.sub (upSub σ) = (t.sub σ).shift := by
  simp only [shift, sub_ren, ren_sub]; rfl

theorem sub_shift2 (t : Tm) (σ : Nat → Tm) : (t.shiftN 2).sub (upSub (upSub σ)) = (t.sub σ).shiftN 2 := by
  simp only [shiftN, sub_ren, ren_sub]
  apply sub_congr; intro i
  simp only [Function.comp, upSub, shift, ren_ren]; rfl

theorem sub_under1 (B : Tm) (σ : Nat → Tm) : (B.under 1).sub (upSub (upSub σ)) = (B.sub (upSub σ)).under 1 := by
  simp only [under, sub_ren, ren_sub]
  apply sub_congr; intro i; rcases i with _ | i
  · rfl
  · simp only [Function.comp, upRen, upSub, shift, ren_ren]; rfl

theorem sub_under2 (B : Tm) (σ : Nat → Tm) :
    (B.under 2).sub (upSub (upSub (upSub σ))) = (B.sub (upSub σ)).under 2 := by
  simp only [under, sub_ren, ren_sub]
  apply sub_congr; intro i; rcases i with _ | i
  · rfl
  · simp only [Function.comp, upRen, upSub, shift, ren_ren]; rfl

theorem sub_iff (a b : Tm) (σ : Nat → Tm) : (iff a b).sub σ = iff (a.sub σ) (b.sub σ) := by
  simp only [iff, sub, sub_shift, sub_shift2]

theorem sub_eqPi (A B f g : Tm) (σ : Nat → Tm) :
    (eqPi A B f g).sub σ = eqPi (A.sub σ) (B.sub (upSub σ)) (f.sub σ) (g.sub σ) := by
  simp only [eqPi, sub, sub_shift]; rfl

theorem sub_castPi (A₁ B₁ A₂ B₂ e t : Tm) (σ : Nat → Tm) :
    (castPi A₁ B₁ A₂ B₂ e t).sub σ =
      castPi (A₁.sub σ) (B₁.sub (upSub σ)) (A₂.sub σ) (B₂.sub (upSub σ)) (e.sub σ) (t.sub σ) := by
  simp only [castPi, sub, sub_inst, sub_under1, sub_shift]; rfl

theorem sub_eqSigmaTransport (A B a b : Tm) (σ : Nat → Tm) :
    (eqSigmaTransport A B a b).sub (upSub σ) =
      eqSigmaTransport (A.sub σ) (B.sub (upSub σ)) (a.sub σ) (b.sub σ) := by
  simp only [eqSigmaTransport, sub, sub_shift, sub_shift2, sub_inst, sub_under2]; rfl

theorem sub_eqSigma (A B a b : Tm) (σ : Nat → Tm) :
    (eqSigma A B a b).sub σ = eqSigma (A.sub σ) (B.sub (upSub σ)) (a.sub σ) (b.sub σ) := by
  simp only [eqSigma, sub, sub_shift, sub_inst, sub_eqSigmaTransport]

theorem sub_eqSigmaProof (A B a b : Tm) (σ : Nat → Tm) :
    (eqSigmaProof A B a b).sub σ = eqSigmaProof (A.sub σ) (B.sub (upSub σ)) (a.sub σ) (b.sub σ) := by
  simp only [eqSigmaProof, sub, sub_shift, sub_inst]

theorem sub_eqTyPi (A₁ B₁ A₂ B₂ : Tm) (σ : Nat → Tm) :
    (eqTyPi A₁ B₁ A₂ B₂).sub σ = eqTyPi (A₁.sub σ) (B₁.sub (upSub σ)) (A₂.sub σ) (B₂.sub (upSub σ)) := by
  simp only [eqTyPi, sub, sub_shift, sub_shift2, sub_inst, sub_under1, sub_under2]; rfl

theorem sub_eqTySigma (A₁ B₁ A₂ B₂ : Tm) (σ : Nat → Tm) :
    (eqTySigma A₁ B₁ A₂ B₂).sub σ = eqTySigma (A₁.sub σ) (B₁.sub (upSub σ)) (A₂.sub σ) (B₂.sub (upSub σ)) := by
  simp only [eqTySigma, sub, sub_shift, sub_shift2, sub_inst, sub_under1, sub_under2]; rfl

theorem sub_castSigma (A₁ B₁ A₂ B₂ e t : Tm) (σ : Nat → Tm) :
    (castSigma A₁ B₁ A₂ B₂ e t).sub σ =
      castSigma (A₁.sub σ) (B₁.sub (upSub σ)) (A₂.sub σ) (B₂.sub (upSub σ)) (e.sub σ) (t.sub σ) := by
  simp only [castSigma, sub, sub_inst]

theorem sub_transpMotiveTy (s : Srt) (A a : Tm) (σ : Nat → Tm) :
    (transpMotiveTy s A a).sub σ = transpMotiveTy s (A.sub σ) (a.sub σ) := by
  simp only [transpMotiveTy, sub, sub_shift]; rfl

theorem sub_branches (bl : List Tm) (σ : Nat → Tm) : (branches bl).sub σ = branches (bl.map (sub σ)) := by
  induction bl with
  | nil => rfl
  | cons b bl ih => simp only [branches, sub, ih, List.map_cons]

theorem former_sub (t : Tm) (σ : Nat → Tm) {f : Former} (h : t.former? = some f) : (t.sub σ).former? = some f := by
  cases t <;> simp_all [former?, sub]

end Tm
namespace Spec

/-- The action of a substitution on a judgment whose context becomes `Δ`. -/
def Jdg.sub (σ : Nat → Tm) (Δ : Ctx) : Jdg → Jdg
  | .wf _ => .wf Δ
  | .ty _ t A => .ty Δ (t.sub σ) (A.sub σ)
  | .eq _ t u A => .eq Δ (t.sub σ) (u.sub σ) (A.sub σ)
  | .red _ t u A => .red Δ (t.sub σ) (u.sub σ) (A.sub σ)

/-- `σ` sends each variable of `Γ` to a term of `Δ` at the substituted type. -/
def SubOK (R : Rules) (σ : Nat → Tm) (Γ Δ : Ctx) : Prop :=
  ∀ i A, Γ.lookup i = some A → Derivable R (Δ ⊢ σ i ∶ A.sub σ)

/-- The substitution lemma at one judgment, for a system `R`. -/
def Substs (R : Rules) (j : Jdg) : Prop :=
  ∀ σ Δ, SubOK R σ (Jdg.ctx j) Δ → Derivable R (.wf Δ) → Derivable R (Jdg.sub σ Δ j)

/-- Every rule of `S`, substituted, is derivable in `R` from its substituted premises. -/
def SubClosed (S R : Rules) : Prop :=
  ∀ r, S r → (∀ p, p ∈ r.prems → Substs R p) → Substs R r.concl

theorem subst_of_closed {R : Rules} (h : SubClosed R R) {j : Jdg} (d : Derivable R j) : Substs R j := by
  induction d with
  | intro r hr _ ih => exact h r hr ih

theorem SubClosed.union {S S' R : Rules} (h : SubClosed S R) (h' : SubClosed S' R) : SubClosed (S ∪ S') R :=
  fun r hr ih => hr.elim (fun hs => h r hs ih) (fun hs => h' r hs ih)

/-- Extending a well-formed context by a type of it. -/
theorem wfExt {R : Rules} (hc : ∀ r, Core r → R r) {Δ : Ctx} {A : Tm} {s : Srt}
    (hΔ : Derivable R (.wf Δ)) (hA : Derivable R (Δ ⊢ A ∶ .sort s)) : Derivable R (.wf (A :: Δ)) :=
  ofRule (hc _ (.wfCons (s := s))) (by
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hΔ, hA⟩)

/-- Lifting a substitution under a binder: the variables of `Γ` are weakened into the
extended context, which is the renaming lemma. -/
theorem SubOK.up {R : Rules} (hren : ∀ j, Derivable R j → Renames R j) (hc : ∀ r, Core r → R r)
    {σ : Nat → Tm} {Γ Δ : Ctx} {A : Tm} {s : Srt} (h : SubOK R σ Γ Δ) (hΔ : Derivable R (.wf Δ))
    (hA : Derivable R (Δ ⊢ A.sub σ ∶ .sort s)) : SubOK R (Tm.upSub σ) (A :: Γ) (A.sub σ :: Δ) := by
  intro i B hB
  cases i with
  | zero =>
    rw [Ctx.lookup_zero] at hB; cases hB
    rw [Tm.sub_shift]
    exact ofRule (hc _ (.var (Ctx.lookup_zero _ _))) (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
      exact wfExt hc hΔ hA)
  | succ i =>
    rw [Ctx.lookup_succ] at hB
    cases hΓ : Ctx.lookup Γ i with
    | none => rw [hΓ] at hB; cases hB
    | some C =>
      rw [hΓ] at hB; cases hB
      rw [Tm.sub_shift]
      exact hren _ (h i C hΓ) Nat.succ _ (RenOK.succ Δ _) (wfExt hc hΔ hA)

theorem Substs.under {R : Rules} (hren : ∀ j, Derivable R j → Renames R j) (hc : ∀ r, Core r → R r)
    {Γ Δ : Ctx} {A : Tm} {s : Srt} {σ : Nat → Tm}
    {j : Jdg} (hj : Substs R j) (hctx : Jdg.ctx j = A :: Γ)
    (hA : Substs R (Γ ⊢ A ∶ .sort s)) (hσ : SubOK R σ Γ Δ) (hΔ : Derivable R (.wf Δ)) :
    Derivable R (Jdg.sub (Tm.upSub σ) (A.sub σ :: Δ) j) :=
  have hA' := hA σ Δ hσ hΔ
  hj _ _ (hctx ▸ hσ.up hren hc hΔ hA') (wfExt hc hΔ hA')

theorem Substs.underD {R : Rules} (hren : ∀ j, Derivable R j → Renames R j) (hc : ∀ r, Core r → R r)
    {Γ Δ : Ctx} {A : Tm} {s : Srt} {σ : Nat → Tm}
    {j : Jdg} (hj : Substs R j) (hctx : Jdg.ctx j = A :: Γ)
    (hA : Derivable R (Δ ⊢ A.sub σ ∶ .sort s)) (hσ : SubOK R σ Γ Δ) (hΔ : Derivable R (.wf Δ)) :
    Derivable R (Jdg.sub (Tm.upSub σ) (A.sub σ :: Δ) j) :=
  hj _ _ (hctx ▸ hσ.up hren hc hΔ hA) (wfExt hc hΔ hA)

theorem core_subClosed {R : Rules} (hc : ∀ r, Core r → R r) : SubClosed Core R := by
  intro r hr ih σ Δ hσ hΔ
  cases hr with
  | wfNil => exact hΔ
  | wfCons => exact hΔ
  | var h => exact hσ _ _ h
  | sort h => exact ofRule (hc _ (.sort h)) (by fromIH ih σ Δ hσ hΔ)
  | conv => exact ofRule (hc _ .conv) (by fromIH ih σ Δ hσ hΔ)
  | eqConv => exact ofRule (hc _ .eqConv) (by fromIH ih σ Δ hσ hΔ)
  | redConv => exact ofRule (hc _ .redConv) (by fromIH ih σ Δ hσ hΔ)
  | refl => exact ofRule (hc _ .refl) (by fromIH ih σ Δ hσ hΔ)
  | symm => exact ofRule (hc _ .symm) (by fromIH ih σ Δ hσ hΔ)
  | trans => exact ofRule (hc _ .trans) (by fromIH ih σ Δ hσ hΔ)
  | redEq => exact ofRule (hc _ .redEq) (by fromIH ih σ Δ hσ hΔ)
  | irrel h => exact ofRule (hc _ (.irrel h)) (by fromIH ih σ Δ hσ hΔ)
  | eqProp h =>
    simp only [Jdg.sub, Tm.sub, Tm.sub_iff]
    exact ofRule (hc _ (.eqProp h)) (by fromIH ih σ Δ hσ hΔ)
  | eqType h => exact ofRule (hc _ (.eqType h)) (by fromIH ih σ Δ hσ hΔ)
  | eqTySort h => exact ofRule (hc _ (.eqTySort h)) (by fromIH ih σ Δ hσ hΔ)
  | eqTySortApart h => exact ofRule (hc _ (.eqTySortApart h)) (by fromIH ih σ Δ hσ hΔ)
  | castSort h => exact ofRule (hc _ (.castSort h)) (by fromIH ih σ Δ hσ hΔ)

theorem pi_subClosed {R : Rules} (hren : ∀ j, Derivable R j → Renames R j) (hc : ∀ r, Core r → R r)
    (hp : ∀ r, Pi r → R r) : SubClosed Pi R := by
  intro r hr ih σ Δ hσ hΔ
  cases hr with
  | form h =>
    exact ofRule (hp _ (.form h)) (by
      fromIH ih σ Δ hσ hΔ
      exact Substs.under hren hc ih.2 rfl ih.1 hσ hΔ)
  | lam =>
    exact ofRule (hp _ .lam) (by
      fromIH ih σ Δ hσ hΔ
      exact Substs.under hren hc ih.2.2 rfl ih.2.1 hσ hΔ)
  | app =>
    simp only [Jdg.sub, Tm.sub, Tm.sub_inst]
    exact ofRule (hp _ .app) (by fromIH ih σ Δ hσ hΔ)
  | beta =>
    simp only [Jdg.sub, Tm.sub, Tm.sub_inst]
    exact ofRule (hp _ .beta) (by
      fromIH ih σ Δ hσ hΔ
      exact Substs.under hren hc ih.2.2.1 rfl ih.2.1 hσ hΔ)
  | appRed =>
    simp only [Jdg.sub, Tm.sub, Tm.sub_inst]
    exact ofRule (hp _ .appRed) (by fromIH ih σ Δ hσ hΔ)
  | eta =>
    exact ofRule (hp _ .eta) (by
      fromIH ih σ Δ hσ hΔ
      have h := Substs.under hren hc ih.2.2.2 rfl ih.2.2.1 hσ hΔ
      simp only [Jdg.sub, Tm.sub, Tm.sub_shift] at h
      exact h)
  | cong h h' =>
    exact ofRule (hp _ (.cong h h')) (by
      fromIH ih σ Δ hσ hΔ
      exact Substs.under hren hc ih.2.2 rfl ih.1 hσ hΔ)
  | appCong =>
    simp only [Jdg.sub, Tm.sub, Tm.sub_inst]
    exact ofRule (hp _ .appCong) (by fromIH ih σ Δ hσ hΔ)
  | eq h =>
    simp only [Jdg.sub, Tm.sub, Tm.sub_eqPi]
    exact ofRule (hp _ (.eq h)) (by fromIH ih σ Δ hσ hΔ)
  | eqTyApart h1 h2 => exact ofRule (hp _ (.eqTyApart h1 h2)) (by fromIH ih σ Δ hσ hΔ)
  | cast h1 h2 =>
    simp only [Jdg.sub, Tm.sub, Tm.sub_castPi]
    exact ofRule (hp _ (.cast h1 h2)) (by
      fromIH ih σ Δ hσ hΔ
      · exact Substs.under hren hc ih.2.2.2.2.1 rfl ih.2.2.1 hσ hΔ
      · exact Substs.under hren hc ih.2.2.2.2.2.1 rfl ih.2.2.2.1 hσ hΔ)

theorem sigma_subClosed {R : Rules} (hren : ∀ j, Derivable R j → Renames R j) (hc : ∀ r, Core r → R r)
    (hs : ∀ r, Sigma r → R r) : SubClosed Sigma R := by
  intro r hr ih σ Δ hσ hΔ
  cases hr with
  | form h =>
    exact ofRule (hs _ (.form h)) (by
      fromIH ih σ Δ hσ hΔ
      exact Substs.under hren hc ih.2 rfl ih.1 hσ hΔ)
  | pair =>
    exact ofRule (hs _ .pair) (by
      fromIH ih σ Δ hσ hΔ
      have h := ih.2.2 σ Δ hσ hΔ
      simp only [Jdg.sub, Tm.sub_inst] at h
      exact h)
  | fst => exact ofRule (hs _ .fst) (by fromIH ih σ Δ hσ hΔ)
  | snd =>
    simp only [Jdg.sub, Tm.sub, Tm.sub_inst]
    exact ofRule (hs _ .snd) (by fromIH ih σ Δ hσ hΔ)
  | fstBeta =>
    exact ofRule (hs _ .fstBeta) (by
      fromIH ih σ Δ hσ hΔ
      have h := ih.2.2 σ Δ hσ hΔ
      simp only [Jdg.sub, Tm.sub_inst] at h
      exact h)
  | sndBeta =>
    simp only [Jdg.sub, Tm.sub, Tm.sub_inst]
    exact ofRule (hs _ .sndBeta) (by
      fromIH ih σ Δ hσ hΔ
      have h := ih.2.2 σ Δ hσ hΔ
      simp only [Jdg.sub, Tm.sub_inst] at h
      exact h)
  | fstRed => exact ofRule (hs _ .fstRed) (by fromIH ih σ Δ hσ hΔ)
  | sndRed =>
    simp only [Jdg.sub, Tm.sub, Tm.sub_inst]
    exact ofRule (hs _ .sndRed) (by fromIH ih σ Δ hσ hΔ)
  | eta =>
    exact ofRule (hs _ .eta) (by
      fromIH ih σ Δ hσ hΔ
      have h := ih.2.2.2 σ Δ hσ hΔ
      simp only [Jdg.sub, Tm.sub, Tm.sub_inst] at h
      exact h)
  | cong h h' =>
    exact ofRule (hs _ (.cong h h')) (by
      fromIH ih σ Δ hσ hΔ
      exact Substs.under hren hc ih.2.2 rfl ih.1 hσ hΔ)
  | fstCong => exact ofRule (hs _ .fstCong) (by fromIH ih σ Δ hσ hΔ)
  | sndCong =>
    simp only [Jdg.sub, Tm.sub, Tm.sub_inst]
    exact ofRule (hs _ .sndCong) (by fromIH ih σ Δ hσ hΔ)
  | eq h h' =>
    simp only [Jdg.sub, Tm.sub, Tm.sub_eqSigma]
    exact ofRule (hs _ (.eq h h')) (by fromIH ih σ Δ hσ hΔ)
  | eqProof h h' =>
    simp only [Jdg.sub, Tm.sub, Tm.sub_eqSigmaProof]
    exact ofRule (hs _ (.eqProof h h')) (by fromIH ih σ Δ hσ hΔ)
  | eqTyApart h1 h2 => exact ofRule (hs _ (.eqTyApart h1 h2)) (by fromIH ih σ Δ hσ hΔ)
  | cast h1 h2 =>
    simp only [Jdg.sub, Tm.sub, Tm.sub_castSigma]
    exact ofRule (hs _ (.cast h1 h2)) (by
      fromIH ih σ Δ hσ hΔ
      · exact Substs.under hren hc ih.2.2.2.2.1 rfl ih.2.2.1 hσ hΔ
      · exact Substs.under hren hc ih.2.2.2.2.2.1 rfl ih.2.2.2.1 hσ hΔ)

theorem unit_subClosed {R : Rules} (hu : ∀ r, Unit r → R r) : SubClosed Unit R := by
  intro r hr ih σ Δ hσ hΔ
  cases hr with
  | form => exact ofRule (hu _ .form) (by fromIH ih σ Δ hσ hΔ)
  | tt => exact ofRule (hu _ .tt) (by fromIH ih σ Δ hσ hΔ)
  | eta => exact ofRule (hu _ .eta) (by fromIH ih σ Δ hσ hΔ)
  | cong h => exact ofRule (hu _ (.cong h)) (by fromIH ih σ Δ hσ hΔ)
  | eq h => exact ofRule (hu _ (.eq h)) (by fromIH ih σ Δ hσ hΔ)
  | eqTy h1 h2 h3 => exact ofRule (hu _ (.eqTy h1 h2 h3)) (by fromIH ih σ Δ hσ hΔ)
  | eqTyApart h1 h2 h3 => exact ofRule (hu _ (.eqTyApart h1 h2 h3)) (by fromIH ih σ Δ hσ hΔ)
  | cast h1 h2 => exact ofRule (hu _ (.cast h1 h2)) (by fromIH ih σ Δ hσ hΔ)

theorem empty_subClosed {R : Rules} (he : ∀ r, Empty r → R r) : SubClosed Empty R := by
  intro r hr ih σ Δ hσ hΔ
  cases hr with
  | form => exact ofRule (he _ .form) (by fromIH ih σ Δ hσ hΔ)
  | absurd => exact ofRule (he _ .absurd) (by fromIH ih σ Δ hσ hΔ)
  | cong h => exact ofRule (he _ (.cong h)) (by fromIH ih σ Δ hσ hΔ)
  | absurdCong => exact ofRule (he _ .absurdCong) (by fromIH ih σ Δ hσ hΔ)
  | eq h => exact ofRule (he _ (.eq h)) (by fromIH ih σ Δ hσ hΔ)
  | eqTy h1 h2 h3 => exact ofRule (he _ (.eqTy h1 h2 h3)) (by fromIH ih σ Δ hσ hΔ)
  | eqTyApart h1 h2 h3 => exact ofRule (he _ (.eqTyApart h1 h2 h3)) (by fromIH ih σ Δ hσ hΔ)
  | cast h1 h2 => exact ofRule (he _ (.cast h1 h2)) (by fromIH ih σ Δ hσ hΔ)

theorem let_subClosed {R : Rules} (hl : ∀ r, Let r → R r) : SubClosed Let R := by
  intro r hr ih σ Δ hσ hΔ
  cases hr with
  | letE =>
    exact ofRule (hl _ .letE) (by
      fromIH ih σ Δ hσ hΔ
      have h := ih.2.2 σ Δ hσ hΔ
      simp only [Jdg.sub, Tm.sub_inst] at h
      exact h)
  | zeta =>
    simp only [Jdg.sub, Tm.sub, Tm.sub_inst]
    exact ofRule (hl _ .zeta) (by
      fromIH ih σ Δ hσ hΔ
      have h := ih.2.2 σ Δ hσ hΔ
      simp only [Jdg.sub, Tm.sub_inst] at h
      exact h)
  | letUnit => exact ofRule (hl _ .letUnit) (by fromIH ih σ Δ hσ hΔ)
  | letUnitRed => exact ofRule (hl _ .letUnitRed) (by fromIH ih σ Δ hσ hΔ)
  | ann => exact ofRule (hl _ .ann) (by fromIH ih σ Δ hσ hΔ)
  | annRed => exact ofRule (hl _ .annRed) (by fromIH ih σ Δ hσ hΔ)

theorem eq_subClosed {R : Rules} (hq : ∀ r, Eq r → R r) : SubClosed Eq R := by
  intro r hr ih σ Δ hσ hΔ
  cases hr with
  | eq => exact ofRule (hq _ .eq) (by fromIH ih σ Δ hσ hΔ)
  | refl => exact ofRule (hq _ .refl) (by fromIH ih σ Δ hσ hΔ)
  | reflTy => exact ofRule (hq _ .reflTy) (by fromIH ih σ Δ hσ hΔ)
  | transp =>
    exact ofRule (hq _ .transp) (by
      fromIH ih σ Δ hσ hΔ
      have h := ih.2.2.2.1 σ Δ hσ hΔ
      simp only [Jdg.sub, Tm.sub_transpMotiveTy] at h
      exact h)
  | cast => exact ofRule (hq _ .cast) (by fromIH ih σ Δ hσ hΔ)
  | eqCong => exact ofRule (hq _ .eqCong) (by fromIH ih σ Δ hσ hΔ)
  | eqTyCong => exact ofRule (hq _ .eqTyCong) (by fromIH ih σ Δ hσ hΔ)
  | castCong => exact ofRule (hq _ .castCong) (by fromIH ih σ Δ hσ hΔ)
  | eqRed => exact ofRule (hq _ .eqRed) (by fromIH ih σ Δ hσ hΔ)
  | eqTyRedL => exact ofRule (hq _ .eqTyRedL) (by fromIH ih σ Δ hσ hΔ)
  | eqTyRedR => exact ofRule (hq _ .eqTyRedR) (by fromIH ih σ Δ hσ hΔ)
  | castRedL => exact ofRule (hq _ .castRedL) (by fromIH ih σ Δ hσ hΔ)
  | castRedR => exact ofRule (hq _ .castRedR) (by fromIH ih σ Δ hσ hΔ)
  | eqAtProp h => exact ofRule (hq _ (.eqAtProp h)) (by fromIH ih σ Δ hσ hΔ)
  | eqTyProps h h' =>
    simp only [Jdg.sub, Tm.sub, Tm.sub_iff]
    exact ofRule (hq _ (.eqTyProps h h')) (by fromIH ih σ Δ hσ hΔ)
  | eqTyFormers h1 h2 h3 h4 h5 =>
    exact ofRule (hq _ (.eqTyFormers h1 h2 (Tm.former_sub _ σ h3) (Tm.former_sub _ σ h4) h5))
      (by fromIH ih σ Δ hσ hΔ)

theorem eqTyCross_subClosed {R : Rules} (hx : ∀ r, EqTyCross r → R r) : SubClosed EqTyCross R := by
  intro r hr ih σ Δ hσ hΔ
  cases hr with
  | form => exact ofRule (hx _ .form) (by fromIH ih σ Δ hσ hΔ)
  | propType h h' => exact ofRule (hx _ (.propType h h')) (by fromIH ih σ Δ hσ hΔ)
  | typeProp h h' => exact ofRule (hx _ (.typeProp h h')) (by fromIH ih σ Δ hσ hΔ)
  | pi h h' =>
    simp only [Jdg.sub, Tm.sub, Tm.sub_eqTyPi]
    exact ofRule (hx _ (.pi h h')) (by fromIH ih σ Δ hσ hΔ)
  | sigma h h' =>
    simp only [Jdg.sub, Tm.sub, Tm.sub_eqTySigma]
    exact ofRule (hx _ (.sigma h h')) (by fromIH ih σ Δ hσ hΔ)

theorem eqTyLevelled_subClosed {R : Rules} (hren : ∀ j, Derivable R j → Renames R j)
    (hc : ∀ r, Core r → R r) (hx : ∀ r, EqTyLevelled r → R r) :
    SubClosed EqTyLevelled R := by
  intro r hr ih σ Δ hσ hΔ
  cases hr with
  | form => exact ofRule (hx _ .form) (by fromIH ih σ Δ hσ hΔ)
  | pi h1 h2 h3 h4 =>
    simp only [Jdg.sub, Tm.sub, Tm.sub_eqTyPi]
    exact ofRule (hx _ (.pi h1 h2 h3 h4)) (by
      fromIH ih σ Δ hσ hΔ
      · exact Substs.under hren hc ih.2.2.1 rfl ih.1 hσ hΔ
      · exact Substs.under hren hc ih.2.2.2 rfl ih.2.1 hσ hΔ)
  | sigma h1 h2 h3 h4 =>
    simp only [Jdg.sub, Tm.sub, Tm.sub_eqTySigma]
    exact ofRule (hx _ (.sigma h1 h2 h3 h4)) (by
      fromIH ih σ Δ hσ hΔ
      · exact Substs.under hren hc ih.2.2.1 rfl ih.1 hσ hΔ
      · exact Substs.under hren hc ih.2.2.2 rfl ih.2.1 hσ hΔ)

theorem branchPrems_sub {R : Rules} {Γ Δ : Ctx} {M : Tm} {n : Nat} {bl : List Tm} {σ : Nat → Tm}
    (h : ∀ p, p ∈ branchPrems Γ M n bl → Substs R p) (hσ : SubOK R σ Γ Δ) (hΔ : Derivable R (.wf Δ)) :
    ∀ p, p ∈ branchPrems Δ (M.sub (Tm.upSub σ)) n (bl.map (Tm.sub σ)) → Derivable R p := by
  intro p hp
  simp only [branchPrems, List.zipIdx_map, List.map_map, List.mem_map] at hp
  obtain ⟨⟨b, k⟩, hm, rfl⟩ := hp
  have := h (Γ ⊢ b ∶ M.inst (.tag n k)) (by simp only [branchPrems, List.mem_map]; exact ⟨(b, k), hm, rfl⟩) σ Δ hσ hΔ
  simpa [Jdg.sub, Tm.sub_inst, Tm.sub] using this

theorem branchEqPrems_sub {R : Rules} {Γ Δ : Ctx} {M : Tm} {n : Nat} {bl bl' : List Tm}
    {σ : Nat → Tm} (h : ∀ p, p ∈ branchEqPrems Γ M n bl bl' → Substs R p)
    (hσ : SubOK R σ Γ Δ) (hΔ : Derivable R (.wf Δ)) :
    ∀ p, p ∈ branchEqPrems Δ (M.sub (Tm.upSub σ)) n (bl.map (Tm.sub σ)) (bl'.map (Tm.sub σ)) →
      Derivable R p := by
  intro p hp
  simp only [branchEqPrems, List.zip_map, List.zipIdx_map, List.map_map, List.mem_map] at hp
  obtain ⟨⟨⟨b, b'⟩, k⟩, hm, rfl⟩ := hp
  have := h (Γ ⊢ b ≡ b' ∶ M.inst (.tag n k)) (by simp only [branchEqPrems, List.mem_map]; exact ⟨((b, b'), k), hm, rfl⟩) σ Δ hσ hΔ
  simpa [Jdg.sub, Tm.sub_inst, Tm.sub] using this

theorem enum_subClosed {R : Rules} (hren : ∀ j, Derivable R j → Renames R j) (hc : ∀ r, Core r → R r)
    (hn : ∀ r, Enum r → R r) : SubClosed Enum R := by
  intro r hr ih σ Δ hσ hΔ
  have hE : ∀ n, Derivable R (Δ ⊢ (Tm.enum n).sub σ ∶ .sort .u0) := fun n =>
    ofRule (hn _ (.form (n := n))) (by fromIH ih σ Δ hσ hΔ)
  cases hr with
  | form => exact ofRule (hn _ .form) (by fromIH ih σ Δ hσ hΔ)
  | tag h => exact ofRule (hn _ (.tag h)) (by fromIH ih σ Δ hσ hΔ)
  | @ecase Γ s M k n bl h =>
    have ih1 := fun p hp => ih p (List.mem_append_left _ hp)
    have ih2 := fun p hp => ih p (List.mem_append_right _ hp)
    simp only [Jdg.sub, Tm.sub, Tm.sub_inst, Tm.sub_branches]
    exact ofRule (hn _ (.ecase (by simpa using h))) (List.forall_mem_append.2 ⟨by
        fromIH ih1 σ Δ hσ hΔ
        exact Substs.underD hren hc ih1.2 rfl (hE n) hσ hΔ, branchPrems_sub ih2 hσ hΔ⟩)
  | @iota Γ b M k n i bl h1 h2 =>
    have ih1 := fun p hp => ih p (List.mem_append_left _ hp)
    have ih2 := fun p hp => ih p (List.mem_append_right _ hp)
    simp only [Jdg.sub, Tm.sub, Tm.sub_inst, Tm.sub_branches]
    exact ofRule (hn _ (.iota (by simpa using h1) (by simp [h2]))) (List.forall_mem_append.2 ⟨by
        fromIH ih1 σ Δ hσ hΔ
        exact Substs.underD hren hc ih1.2 rfl (hE n) hσ hΔ, branchPrems_sub ih2 hσ hΔ⟩)
  | @ecaseRed Γ s s' M k n bl h =>
    have ih1 := fun p hp => ih p (List.mem_append_left _ hp)
    have ih2 := fun p hp => ih p (List.mem_append_right _ hp)
    simp only [Jdg.sub, Tm.sub, Tm.sub_inst, Tm.sub_branches]
    exact ofRule (hn _ (.ecaseRed (by simpa using h))) (List.forall_mem_append.2 ⟨by
        fromIH ih1 σ Δ hσ hΔ
        exact Substs.underD hren hc ih1.2 rfl (hE n) hσ hΔ, branchPrems_sub ih2 hσ hΔ⟩)
  | @ecaseCong Γ s s' M M' k n bl bl' h h' =>
    have ih1 := fun p hp => ih p (List.mem_append_left _ hp)
    have ih2 := fun p hp => ih p (List.mem_append_right _ hp)
    simp only [Jdg.sub, Tm.sub, Tm.sub_inst, Tm.sub_branches]
    exact ofRule (hn _ (.ecaseCong (by simpa using h) (by simpa using h')))
      (List.forall_mem_append.2 ⟨by
        fromIH ih1 σ Δ hσ hΔ
        exact Substs.underD hren hc ih1.2 rfl (hE n) hσ hΔ, branchEqPrems_sub ih2 hσ hΔ⟩)
  | eqSame h => exact ofRule (hn _ (.eqSame h)) (by fromIH ih σ Δ hσ hΔ)
  | eqDiff h1 h2 h3 => exact ofRule (hn _ (.eqDiff h1 h2 h3)) (by fromIH ih σ Δ hσ hΔ)
  | eqRedL => exact ofRule (hn _ .eqRedL) (by fromIH ih σ Δ hσ hΔ)
  | eqRedR => exact ofRule (hn _ .eqRedR) (by fromIH ih σ Δ hσ hΔ)
  | eqTySame => exact ofRule (hn _ .eqTySame) (by fromIH ih σ Δ hσ hΔ)
  | eqTyDiff h => exact ofRule (hn _ (.eqTyDiff h)) (by fromIH ih σ Δ hσ hΔ)
  | cast => exact ofRule (hn _ .cast) (by fromIH ih σ Δ hσ hΔ)

theorem ulift_subClosed {R : Rules} {var : EqTyVariant} (hu : ∀ r, ULift var r → R r) :
    SubClosed (ULift var) R := by
  intro r hr ih σ Δ hσ hΔ
  cases hr with
  | form h => exact ofRule (hu _ (.form h)) (by fromIH ih σ Δ hσ hΔ)
  | up => exact ofRule (hu _ .up) (by fromIH ih σ Δ hσ hΔ)
  | down => exact ofRule (hu _ .down) (by fromIH ih σ Δ hσ hΔ)
  | beta => exact ofRule (hu _ .beta) (by fromIH ih σ Δ hσ hΔ)
  | downRed => exact ofRule (hu _ .downRed) (by fromIH ih σ Δ hσ hΔ)
  | eta => exact ofRule (hu _ .eta) (by fromIH ih σ Δ hσ hΔ)
  | cong h => exact ofRule (hu _ (.cong h)) (by fromIH ih σ Δ hσ hΔ)
  | downCong => exact ofRule (hu _ .downCong) (by fromIH ih σ Δ hσ hΔ)
  | eqProp h h' => exact ofRule (hu _ (.eqProp h h')) (by fromIH ih σ Δ hσ hΔ)
  | eq h h' => exact ofRule (hu _ (.eq h h')) (by fromIH ih σ Δ hσ hΔ)
  | eqTy h1 h2 h3 => exact ofRule (hu _ (.eqTy h1 h2 h3)) (by fromIH ih σ Δ hσ hΔ)
  | eqTyApart h1 h2 h3 => exact ofRule (hu _ (.eqTyApart h1 h2 h3)) (by fromIH ih σ Δ hσ hΔ)
  | cast h1 h2 => exact ofRule (hu _ (.cast h1 h2)) (by fromIH ih σ Δ hσ hΔ)

theorem global_subClosed {R : Rules} {sg : Sig} (hsg : Sig.Closed sg)
    (hg : ∀ r, Global sg r → R r) : SubClosed (Global sg) R := by
  intro r hr ih σ Δ hσ hΔ
  cases hr with
  | @const Γ c d h1 =>
    have hd := (hsg _ (List.mem_of_find?_eq_some h1) σ).1
    simp only [Jdg.sub, Tm.sub, hd]
    exact ofRule (hg _ (.const h1)) (by fromIH ih σ Δ hσ hΔ)
  | @delta Γ v c d h1 h2 =>
    have hd := hsg _ (List.mem_of_find?_eq_some h1) σ
    simp only [Jdg.sub, Tm.sub, hd.1, hd.2 _ h2]
    exact ofRule (hg _ (.delta h1 h2)) (by fromIH ih σ Δ hσ hΔ)

/-- The substitution lemma for `F0Rules`, both `EqTy` variants, read in any system `R`
that contains it. Needs the renaming lemma for `R` to lift under binders. -/
theorem F0Rules_subClosedIn {sg : Sig} (hsg : Sig.Closed sg) {var : EqTyVariant} {R : Rules}
    (hren : ∀ j, Derivable R j → Renames R j)
    (h : ∀ r, F0Rules sg var r → R r) (hc : ∀ r, Core r → R r) :
    SubClosed (F0Rules sg var) R := by
  have h1 : SubClosed (Core ∪ Pi) R :=
    (core_subClosed hc).union (pi_subClosed hren hc (fun r x => h r (pi_in_F0Rules x)))
  have h2 : SubClosed ((Core ∪ Pi) ∪ Sigma) R :=
    h1.union (sigma_subClosed hren hc (fun r x => h r (sigma_in_F0Rules x)))
  have h3 : SubClosed (((Core ∪ Pi) ∪ Sigma) ∪ Unit) R :=
    h2.union (unit_subClosed (fun r x => h r (unit_in_F0Rules x)))
  have h4 : SubClosed ((((Core ∪ Pi) ∪ Sigma) ∪ Unit) ∪ Empty) R :=
    h3.union (empty_subClosed (fun r x => h r (empty_in_F0Rules x)))
  have h5 : SubClosed (((((Core ∪ Pi) ∪ Sigma) ∪ Unit) ∪ Empty) ∪ Enum) R :=
    h4.union (enum_subClosed hren hc (fun r x => h r (enum_in_F0Rules x)))
  have h6 : SubClosed ((((((Core ∪ Pi) ∪ Sigma) ∪ Unit) ∪ Empty) ∪ Enum) ∪ Let) R :=
    h5.union (let_subClosed (fun r x => h r (let_in_F0Rules x)))
  have h7 : SubClosed (((((((Core ∪ Pi) ∪ Sigma) ∪ Unit) ∪ Empty) ∪ Enum) ∪ Let) ∪ Global sg) R :=
    h6.union (global_subClosed hsg (fun r x => h r (global_in_F0Rules x)))
  have h8 : SubClosed ((((((((Core ∪ Pi) ∪ Sigma) ∪ Unit) ∪ Empty) ∪ Enum) ∪ Let) ∪ Global sg) ∪ Eq) R :=
    h7.union (eq_subClosed (fun r x => h r (eq_in_F0Rules x)))
  have h9 : SubClosed (((((((((Core ∪ Pi) ∪ Sigma) ∪ Unit) ∪ Empty) ∪ Enum) ∪ Let) ∪ Global sg) ∪ Eq) ∪ eqTyRules var) R :=
    h8.union (by
      cases var with
      | cross => exact eqTyCross_subClosed (fun r x => h r (eqTy_in_F0Rules x))
      | levelled => exact eqTyLevelled_subClosed hren hc (fun r x => h r (eqTy_in_F0Rules x)))
  exact h9.union (ulift_subClosed (fun r x => h r (ulift_in_F0Rules x)))

theorem F0Rules_subClosed {sg : Sig} {var : EqTyVariant} (hsg : Sig.Closed sg) :
    SubClosed (F0Rules sg var) (F0Rules sg var) :=
  F0Rules_subClosedIn hsg (fun _ d => rename_of_closed (F0Rules_renClosed hsg) d)
    (fun _ x => x) (fun _ x => core_in_F0Rules x)

/-- **The substitution lemma for `F0Rules`** (both `EqTy` variants): every judgment
derivable in `F0Rules` stays derivable under a substitution into a well-formed context
that types its variables at the substituted types. -/
theorem F0Rules_substs {sg : Sig} (hsg : Sig.Closed sg) {var : EqTyVariant} {j : Jdg}
    (d : Derivable (F0Rules sg var) j) : Substs (F0Rules sg var) j :=
  subst_of_closed (F0Rules_subClosed hsg) d

/-- **The substitution lemma for F0**: the levelled variant, the system of `Obligations`. -/
theorem F0Base_substs {sg : Sig} (hsg : Sig.Closed sg) {j : Jdg}
    (d : Derivable (F0Base sg) j) : Substs (F0Base sg) j :=
  F0Rules_substs hsg d

/-! ## Context validity

Every derivable judgment has a well-formed context. This is what lets the concrete
substitution laws below drop the `⊢ Γ` hypothesis that `F0Base_weakening` carries (there is no
inversion lemma, so the proof follows the last rule of the derivation). -/

theorem F0Base_ctx {sg : Sig} {j : Jdg}
    (d : Derivable (F0Base sg) j) : Derivable (F0Base sg) (.wf (Jdg.ctx j)) := by
  induction d with
  | intro r hr hp ih =>
    -- `F0` is a left-associated union chain: peel the components from the right.
    rcases hr with hrest | hulift
    · rcases hrest with hrest | heqty
      · rcases hrest with hrest | heq
        · rcases hrest with hrest | hglobal
          · rcases hrest with hrest | hlet
            · rcases hrest with hrest | henum
              · rcases hrest with hrest | hempty
                · rcases hrest with hrest | hunit
                  · rcases hrest with hrest | hsigma
                    · rcases hrest with hcore | hpi
                      · cases hcore with
                        | wfNil => dsimp only [Jdg.ctx]; exact ofRule (core_in_F0Rules Core.wfNil) (by simp)
                        | @wfCons Γ A sc =>
                          dsimp only [Jdg.ctx]
                          exact wfExt (s := sc) (fun _ x => core_in_F0Rules x)
                            (hp (.wf Γ) (by simp)) (hp (.ty Γ A (.sort sc)) (by simp))
                        | @var Γ A i h => dsimp only [Jdg.ctx]; exact hp (.wf Γ) (by simp)
                        | @sort Γ sc sc' h => dsimp only [Jdg.ctx]; exact hp (.wf Γ) (by simp)
                        | @conv Γ t A B sc => dsimp only [Jdg.ctx]; exact ih (.ty Γ t A) (by simp)
                        | @eqConv Γ t u A B sc =>
                          dsimp only [Jdg.ctx]; exact ih (.eq Γ t u A) (by simp)
                        | @redConv Γ t u A B sc =>
                          dsimp only [Jdg.ctx]; exact ih (.red Γ t u A) (by simp)
                        | @refl Γ t A => dsimp only [Jdg.ctx]; exact ih (.ty Γ t A) (by simp)
                        | @symm Γ t u A => dsimp only [Jdg.ctx]; exact ih (.eq Γ t u A) (by simp)
                        | @trans Γ t u A w =>
                          dsimp only [Jdg.ctx]; exact ih (.eq Γ t u A) (by simp)
                        | @redEq Γ t u A => dsimp only [Jdg.ctx]; exact ih (.red Γ t u A) (by simp)
                        | @irrel Γ A t u sc h =>
                          dsimp only [Jdg.ctx]; exact ih (.ty Γ A (.sort sc)) (by simp)
                        | @eqProp Γ a b sc h =>
                          dsimp only [Jdg.ctx]; exact ih (.ty Γ a (.sort sc)) (by simp)
                        | @eqType Γ a b sc h =>
                          dsimp only [Jdg.ctx]; exact ih (.ty Γ a (.sort sc)) (by simp)
                        | @eqTySort Γ u w h => dsimp only [Jdg.ctx]; exact hp (.wf Γ) (by simp)
                        | @eqTySortApart Γ u w h => dsimp only [Jdg.ctx]; exact hp (.wf Γ) (by simp)
                        | @castSort Γ e t u w h =>
                          dsimp only [Jdg.ctx]; exact ih (.ty Γ t (.sort u)) (by simp)
                      · cases hpi with
                        | @form Γ A B i j sc h =>
                          dsimp only [Jdg.ctx]; exact ih (.ty Γ A (.sort i)) (by simp)
                        | @lam Γ A B b sc i =>
                          dsimp only [Jdg.ctx]; exact ih (.ty Γ (.pi sc A B) (.sort sc)) (by simp)
                        | @app Γ f A B a sc =>
                          dsimp only [Jdg.ctx]; exact ih (.ty Γ f (.pi sc A B)) (by simp)
                        | @beta Γ A B b a sc i =>
                          dsimp only [Jdg.ctx]; exact ih (.ty Γ (.pi sc A B) (.sort sc)) (by simp)
                        | @appRed Γ f f' A B a sc =>
                          dsimp only [Jdg.ctx]; exact ih (.red Γ f f' (.pi sc A B)) (by simp)
                        | @eta Γ f A B g sc i =>
                          dsimp only [Jdg.ctx]; exact ih (.ty Γ f (.pi sc A B)) (by simp)
                        | @cong Γ A A' B B' i j sc sc' h h' =>
                          dsimp only [Jdg.ctx]; exact ih (.ty Γ A (.sort i)) (by simp)
                        | @appCong Γ f f' A B a a' sc =>
                          dsimp only [Jdg.ctx]; exact ih (.eq Γ f f' (.pi sc A B)) (by simp)
                        | @eq Γ A B f g sc h =>
                          dsimp only [Jdg.ctx]; exact ih (.ty Γ (.pi sc A B) (.sort sc)) (by simp)
                        | @eqTyApart Γ A₁ B₁ A₂ B₂ s₁ s₂ h1 h2 =>
                          dsimp only [Jdg.ctx]; exact ih (.ty Γ (.pi s₁ A₁ B₁) (.sort s₁)) (by simp)
                        | @cast Γ A₁ B₁ A₂ B₂ e t s₁ s₂ i j h1 h2 =>
                          dsimp only [Jdg.ctx]; exact ih (.ty Γ (.pi s₁ A₁ B₁) (.sort s₁)) (by simp)
                    · cases hsigma with
                      | @form Γ A B i j sc h =>
                        dsimp only [Jdg.ctx]; exact ih (.ty Γ A (.sort i)) (by simp)
                      | @pair Γ A B a b sc =>
                        dsimp only [Jdg.ctx]; exact ih (.ty Γ (.sigma sc A B) (.sort sc)) (by simp)
                      | @fst Γ p A B sc =>
                        dsimp only [Jdg.ctx]; exact ih (.ty Γ p (.sigma sc A B)) (by simp)
                      | @snd Γ p A B sc =>
                        dsimp only [Jdg.ctx]; exact ih (.ty Γ p (.sigma sc A B)) (by simp)
                      | @fstBeta Γ A B a b sc =>
                        dsimp only [Jdg.ctx]; exact ih (.ty Γ (.sigma sc A B) (.sort sc)) (by simp)
                      | @sndBeta Γ A B a b sc =>
                        dsimp only [Jdg.ctx]; exact ih (.ty Γ (.sigma sc A B) (.sort sc)) (by simp)
                      | @fstRed Γ p p' A B sc =>
                        dsimp only [Jdg.ctx]; exact ih (.red Γ p p' (.sigma sc A B)) (by simp)
                      | @sndRed Γ p p' A B sc =>
                        dsimp only [Jdg.ctx]; exact ih (.red Γ p p' (.sigma sc A B)) (by simp)
                      | @eta Γ p A B p' sc =>
                        dsimp only [Jdg.ctx]; exact ih (.ty Γ p (.sigma sc A B)) (by simp)
                      | @cong Γ A A' B B' i j sc sc' h h' =>
                        dsimp only [Jdg.ctx]; exact ih (.ty Γ A (.sort i)) (by simp)
                      | @fstCong Γ p p' A B sc =>
                        dsimp only [Jdg.ctx]; exact ih (.eq Γ p p' (.sigma sc A B)) (by simp)
                      | @sndCong Γ p p' A B sc =>
                        dsimp only [Jdg.ctx]; exact ih (.eq Γ p p' (.sigma sc A B)) (by simp)
                      | @eq Γ A B a b sc i h1 h2 =>
                        dsimp only [Jdg.ctx]; exact ih (.ty Γ (.sigma sc A B) (.sort sc)) (by simp)
                      | @eqProof Γ A B a b sc i h1 h2 =>
                        dsimp only [Jdg.ctx]; exact ih (.ty Γ (.sigma sc A B) (.sort sc)) (by simp)
                      | @eqTyApart Γ A₁ B₁ A₂ B₂ s₁ s₂ h1 h2 =>
                        dsimp only [Jdg.ctx]; exact ih (.ty Γ (.sigma s₁ A₁ B₁) (.sort s₁)) (by simp)
                      | @cast Γ A₁ B₁ A₂ B₂ e t s₁ s₂ i j h1 h2 =>
                        dsimp only [Jdg.ctx]; exact ih (.ty Γ (.sigma s₁ A₁ B₁) (.sort s₁)) (by simp)
                  · cases hunit with
                    | @form Γ sc => dsimp only [Jdg.ctx]; exact hp (.wf Γ) (by simp)
                    | @tt Γ sc => dsimp only [Jdg.ctx]; exact hp (.wf Γ) (by simp)
                    | @eta Γ t u sc => dsimp only [Jdg.ctx]; exact ih (.ty Γ t (.unit sc)) (by simp)
                    | @cong Γ sc sc' h => dsimp only [Jdg.ctx]; exact hp (.wf Γ) (by simp)
                    | @eq Γ a b sc h => dsimp only [Jdg.ctx]; exact ih (.ty Γ a (.unit sc)) (by simp)
                    | @eqTy Γ u w h1 h2 h3 => dsimp only [Jdg.ctx]; exact hp (.wf Γ) (by simp)
                    | @eqTyApart Γ u w h1 h2 h3 => dsimp only [Jdg.ctx]; exact hp (.wf Γ) (by simp)
                    | @cast Γ e t u w h1 h2 =>
                      dsimp only [Jdg.ctx]; exact ih (.ty Γ e (.eqTy (.unit u) (.unit w))) (by simp)
                · cases hempty with
                  | @form Γ sc => dsimp only [Jdg.ctx]; exact hp (.wf Γ) (by simp)
                  | @absurd Γ M t k sc =>
                    dsimp only [Jdg.ctx]; exact ih (.ty Γ M (.sort k)) (by simp)
                  | @cong Γ sc sc' h => dsimp only [Jdg.ctx]; exact hp (.wf Γ) (by simp)
                  | @absurdCong Γ M M' t t' k sc =>
                    dsimp only [Jdg.ctx]; exact ih (.eq Γ M M' (.sort k)) (by simp)
                  | @eq Γ a b sc h => dsimp only [Jdg.ctx]; exact ih (.ty Γ a (.empty sc)) (by simp)
                  | @eqTy Γ u w h1 h2 h3 => dsimp only [Jdg.ctx]; exact hp (.wf Γ) (by simp)
                  | @eqTyApart Γ u w h1 h2 h3 => dsimp only [Jdg.ctx]; exact hp (.wf Γ) (by simp)
                  | @cast Γ e t u w h1 h2 =>
                    dsimp only [Jdg.ctx]; exact ih (.ty Γ e (.eqTy (.empty u) (.empty w))) (by simp)
              · cases henum with
                | @form Γ n => dsimp only [Jdg.ctx]; exact hp (.wf Γ) (by simp)
                | @tag Γ i n h => dsimp only [Jdg.ctx]; exact hp (.wf Γ) (by simp)
                | @ecase Γ sc M k n bl h =>
                  dsimp only [Jdg.ctx]
                  exact ih (.ty Γ sc (.enum n)) (List.mem_append_left _ (by simp))
                | @iota Γ b M k n i bl h1 h2 =>
                  dsimp only [Jdg.ctx]
                  exact hp (.wf Γ) (List.mem_append_left _ (by simp))
                | @ecaseRed Γ sc sc' M k n bl h =>
                  dsimp only [Jdg.ctx]
                  exact ih (.red Γ sc sc' (.enum n)) (List.mem_append_left _ (by simp))
                | @ecaseCong Γ sc sc' M M' k n bl bl' h h' =>
                  dsimp only [Jdg.ctx]
                  exact ih (.eq Γ sc sc' (.enum n)) (List.mem_append_left _ (by simp))
                | @eqSame Γ i n h => dsimp only [Jdg.ctx]; exact hp (.wf Γ) (by simp)
                | @eqDiff Γ i n j h1 h2 h3 => dsimp only [Jdg.ctx]; exact hp (.wf Γ) (by simp)
                | @eqRedL Γ a a' b n =>
                  dsimp only [Jdg.ctx]; exact ih (.red Γ a a' (.enum n)) (by simp)
                | @eqRedR Γ a b b' n =>
                  dsimp only [Jdg.ctx]; exact ih (.red Γ b b' (.enum n)) (by simp)
                | @eqTySame Γ n => dsimp only [Jdg.ctx]; exact hp (.wf Γ) (by simp)
                | @eqTyDiff Γ n m h => dsimp only [Jdg.ctx]; exact hp (.wf Γ) (by simp)
                | @cast Γ e t n =>
                  dsimp only [Jdg.ctx]; exact ih (.ty Γ e (.eqTy (.enum n) (.enum n))) (by simp)
            · cases hlet with
              | @letE Γ A v B b sc =>
                dsimp only [Jdg.ctx]; exact ih (.ty Γ A (.sort sc)) (by simp)
              | @zeta Γ A v B b sc =>
                dsimp only [Jdg.ctx]; exact ih (.ty Γ A (.sort sc)) (by simp)
              | @letUnit Γ u B b sc =>
                dsimp only [Jdg.ctx]; exact ih (.ty Γ u (.unit sc)) (by simp)
              | @letUnitRed Γ u B b sc =>
                dsimp only [Jdg.ctx]; exact ih (.ty Γ u (.unit sc)) (by simp)
              | @ann Γ A t sc => dsimp only [Jdg.ctx]; exact ih (.ty Γ A (.sort sc)) (by simp)
              | @annRed Γ A t sc => dsimp only [Jdg.ctx]; exact ih (.ty Γ A (.sort sc)) (by simp)
          · cases hglobal with
            | @const Γ c d h => dsimp only [Jdg.ctx]; exact hp (.wf Γ) (by simp)
            | @delta Γ v c d h1 h2 => dsimp only [Jdg.ctx]; exact hp (.wf Γ) (by simp)
        · cases heq with
          | @eq Γ A a b sc => dsimp only [Jdg.ctx]; exact ih (.ty Γ A (.sort sc)) (by simp)
          | @refl Γ A a sc => dsimp only [Jdg.ctx]; exact ih (.ty Γ A (.sort sc)) (by simp)
          | @reflTy Γ A sc => dsimp only [Jdg.ctx]; exact ih (.ty Γ A (.sort sc)) (by simp)
          | @transp Γ A a b P p e sc =>
            dsimp only [Jdg.ctx]; exact ih (.ty Γ A (.sort sc)) (by simp)
          | @cast Γ A B e t sc => dsimp only [Jdg.ctx]; exact ih (.ty Γ A (.sort sc)) (by simp)
          | @eqCong Γ A A' a a' b b' sc =>
            dsimp only [Jdg.ctx]; exact ih (.eq Γ A A' (.sort sc)) (by simp)
          | @eqTyCong Γ A A' B B' sc sc' =>
            dsimp only [Jdg.ctx]; exact ih (.eq Γ A A' (.sort sc)) (by simp)
          | @castCong Γ A A' B B' e e' t t' sc =>
            dsimp only [Jdg.ctx]; exact ih (.eq Γ A A' (.sort sc)) (by simp)
          | @eqRed Γ A A' a b sc =>
            dsimp only [Jdg.ctx]; exact ih (.red Γ A A' (.sort sc)) (by simp)
          | @eqTyRedL Γ A A' B sc sc' =>
            dsimp only [Jdg.ctx]; exact ih (.red Γ A A' (.sort sc)) (by simp)
          | @eqTyRedR Γ A B B' sc sc' =>
            dsimp only [Jdg.ctx]; exact ih (.ty Γ A (.sort sc)) (by simp)
          | @castRedL Γ A A' B e t sc =>
            dsimp only [Jdg.ctx]; exact ih (.red Γ A A' (.sort sc)) (by simp)
          | @castRedR Γ A B B' e t sc =>
            dsimp only [Jdg.ctx]; exact ih (.ty Γ A (.sort sc)) (by simp)
          | @eqAtProp Γ A a b sc h =>
            dsimp only [Jdg.ctx]; exact ih (.ty Γ A (.sort sc)) (by simp)
          | @eqTyProps Γ A B sc sc' h h' =>
            dsimp only [Jdg.ctx]; exact ih (.ty Γ A (.sort sc)) (by simp)
          | @eqTyFormers Γ A B sc sc' f f' h1 h2 h3 h4 h5 =>
            dsimp only [Jdg.ctx]; exact ih (.ty Γ A (.sort sc)) (by simp)
      · change EqTyLevelled r at heqty
        cases heqty with
        | @form Γ A B sc =>
          dsimp only [Jdg.ctx]; exact ih (.ty Γ A (.sort sc)) (by simp)
        | @pi Γ A₁ A₂ B₁ B₂ i j s₁ s₂ h1 h2 h3 h4 =>
          dsimp only [Jdg.ctx]; exact ih (.ty Γ A₁ (.sort i)) (by simp)
        | @sigma Γ A₁ A₂ B₁ B₂ i j s₁ s₂ h1 h2 h3 h4 =>
          dsimp only [Jdg.ctx]; exact ih (.ty Γ A₁ (.sort i)) (by simp)
    · cases hulift with
      | @form Γ A k l h => dsimp only [Jdg.ctx]; exact ih (.ty Γ A (.sort k)) (by simp)
      | @up Γ A a l => dsimp only [Jdg.ctx]; exact ih (.ty Γ (.ulift l A) (.sort l)) (by simp)
      | @down Γ t A l => dsimp only [Jdg.ctx]; exact ih (.ty Γ t (.ulift l A)) (by simp)
      | @beta Γ A a l => dsimp only [Jdg.ctx]; exact ih (.ty Γ (.ulift l A) (.sort l)) (by simp)
      | @downRed Γ t t' A l => dsimp only [Jdg.ctx]; exact ih (.red Γ t t' (.ulift l A)) (by simp)
      | @eta Γ t A t' l =>
        dsimp only [Jdg.ctx]; exact ih (.ty Γ t (.ulift l A)) (by simp)
      | @cong Γ A A' l k l' h =>
        dsimp only [Jdg.ctx]; exact ih (.ty Γ (.ulift l A) (.sort l)) (by simp)
      | @downCong Γ t t' A l => dsimp only [Jdg.ctx]; exact ih (.eq Γ t t' (.ulift l A)) (by simp)
      | @eqProp Γ A a b k l h1 h2 =>
        dsimp only [Jdg.ctx]; exact ih (.ty Γ A (.sort k)) (by simp)
      | @eq Γ A a b k l h1 h2 =>
        dsimp only [Jdg.ctx]; exact ih (.ty Γ A (.sort k)) (by simp)
      | @eqTy Γ A B u w k k' h1 h2 h3 =>
        dsimp only [Jdg.ctx]; exact ih (.ty Γ (.ulift u A) (.sort u)) (by simp)
      | @eqTyApart Γ A B u w h1 h2 h3 =>
        dsimp only [Jdg.ctx]; exact ih (.ty Γ (.ulift u A) (.sort u)) (by simp)
      | @cast Γ A B e t u w k h1 h2 =>
        dsimp only [Jdg.ctx]; exact ih (.ty Γ (.ulift u A) (.sort u)) (by simp)

/-- Dropping the head variable of a well-formed context: `⊢ A :: Γ` gives `⊢ Γ`. (The
`wf` judgment has no term position, so this is the only nontrivial `wf` inversion; the
rule's other premises are not needed.) -/
theorem F0Base_wf_tail {sg : Sig} {Γ : Ctx} {A : Tm}
    (h : Derivable (F0Base sg) (.wf (A :: Γ))) : Derivable (F0Base sg) (.wf Γ) := by
  have aux : ∀ j, Derivable (F0Base sg) j → j = .wf (A :: Γ) → Derivable (F0Base sg) (.wf Γ) := by
    intro j dj
    induction dj with
    | intro r hr hp ih =>
      intro heq
      rcases hr with hrest | hulift
      · rcases hrest with hrest | heqty
        · rcases hrest with hrest | heqset
          · rcases hrest with hrest | hglobal
            · rcases hrest with hrest | hlet
              · rcases hrest with hrest | henum
                · rcases hrest with hrest | hempty
                  · rcases hrest with hrest | hunit
                    · rcases hrest with hrest | hsigma
                      · rcases hrest with hcore | hpi
                        · cases hcore with
                          | wfNil => cases heq
                          | wfCons => cases heq; exact hp (.wf Γ) (by simp)
                          | var => cases heq
                          | sort => cases heq
                          | conv => cases heq
                          | eqConv => cases heq
                          | redConv => cases heq
                          | refl => cases heq
                          | symm => cases heq
                          | trans => cases heq
                          | redEq => cases heq
                          | irrel => cases heq
                          | eqProp => cases heq
                          | eqType => cases heq
                          | eqTySort => cases heq
                          | eqTySortApart => cases heq
                          | castSort => cases heq
                        · cases hpi <;> cases heq
                      · cases hsigma <;> cases heq
                    · cases hunit <;> cases heq
                  · cases hempty <;> cases heq
                · cases henum <;> cases heq
              · cases hlet <;> cases heq
            · cases hglobal <;> cases heq
          · cases heqset <;> cases heq
        · change EqTyLevelled r at heqty
          cases heqty <;> cases heq
      · cases hulift <;> cases heq
  exact aux _ h rfl

/-! ## The concrete companions at `[a/0]` -/

/-- The substitution `[a/0]` is `SubOK` from `A :: Γ` to `Γ`, given a well-formed `Γ`. -/
theorem subOK_one {sg : Sig} {Γ : Ctx} {A a : Tm}
    (hΓ : Derivable (F0Base sg) (.wf Γ)) (ha : Derivable (F0Base sg) (Γ ⊢ a ∶ A)) :
    SubOK (F0Base sg) (Tm.one a) (A :: Γ) Γ := by
  intro i C hC
  cases i with
  | zero =>
    rw [Ctx.lookup_zero] at hC; cases hC
    simp only [Tm.shift, Tm.one, Tm.sub_ren]
    rw [show (Tm.one a ∘ (· + 1)) = Tm.var from rfl, Tm.sub_var]
    exact ha
  | succ i =>
    rw [Ctx.lookup_succ] at hC
    cases hΓi : Ctx.lookup Γ i with
    | none => rw [hΓi] at hC; cases hC
    | some D =>
      rw [hΓi] at hC; cases hC
      simp only [Tm.shift, Tm.one, Tm.sub_ren]
      rw [show (Tm.one a ∘ (· + 1)) = Tm.var from rfl, Tm.sub_var]
      exact ofRule (core_in_F0Rules (Core.var hΓi)) (by
        simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
        exact hΓ)

/-- **Substitution for F0 typing**, the companion of `F0Base_rename`: `t[a/0]` has the
substituted type. Needs a closed signature; the well-formedness of `Γ` follows from the
term's typing by `F0Base_ctx`. -/
theorem F0Base_subst {sg : Sig} (hsg : Sig.Closed sg) {Γ : Ctx} {A t B a : Tm}
    (ht : Derivable (F0Base sg) ((A :: Γ) ⊢ t ∶ B))
    (ha : Derivable (F0Base sg) (Γ ⊢ a ∶ A)) :
    Derivable (F0Base sg) (Γ ⊢ t.inst a ∶ B.inst a) := by
  have hΓ := F0Base_ctx ha
  have := F0Base_substs hsg ht (Tm.one a) Γ (subOK_one hΓ ha) hΓ
  simpa [Jdg.sub, Tm.inst] using this

/-- **Substitution for F0 conversion**: the companion of `F0Base_subst` at the `≡` judgment. -/
theorem F0Base_subst_eq {sg : Sig} (hsg : Sig.Closed sg) {Γ : Ctx} {A t u B a : Tm}
    (ht : Derivable (F0Base sg) ((A :: Γ) ⊢ t ≡ u ∶ B))
    (ha : Derivable (F0Base sg) (Γ ⊢ a ∶ A)) :
    Derivable (F0Base sg) (Γ ⊢ t.inst a ≡ u.inst a ∶ B.inst a) := by
  have hΓ := F0Base_ctx ha
  have := F0Base_substs hsg ht (Tm.one a) Γ (subOK_one hΓ ha) hΓ
  simpa [Jdg.sub, Tm.inst] using this

/-- **Substitution for F0 reduction**: the companion of `F0Base_subst` at the `⟶` judgment. -/
theorem F0Base_subst_red {sg : Sig} (hsg : Sig.Closed sg) {Γ : Ctx} {A t u B a : Tm}
    (ht : Derivable (F0Base sg) ((A :: Γ) ⊢ t ⟶ u ∶ B))
    (ha : Derivable (F0Base sg) (Γ ⊢ a ∶ A)) :
    Derivable (F0Base sg) (Γ ⊢ t.inst a ⟶ u.inst a ∶ B.inst a) := by
  have hΓ := F0Base_ctx ha
  have := F0Base_substs hsg ht (Tm.one a) Γ (subOK_one hΓ ha) hΓ
  simpa [Jdg.sub, Tm.inst] using this

/-- **Substitution for F0 well-formedness**: the `.wf` companion. The wf judgment has no
term position; substituting the head variable away (`⊢ A :: Γ`) leaves `Γ` well formed. -/
theorem F0Base_subst_wf {sg : Sig} {Γ : Ctx} {A : Tm}
    (h : Derivable (F0Base sg) (.wf (A :: Γ))) :
    Derivable (F0Base sg) (.wf Γ) :=
  F0Base_wf_tail h
