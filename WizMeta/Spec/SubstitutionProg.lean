import WizMeta.Spec.Substitution
import WizMeta.Spec.DescCommute

/-!
# Tprog is closed under renaming and substitution

`Substitution.lean` proves both laws for T0 and T1. Here are the rule sets Tprog adds —
`ULift`, `Desc`, `Mu`, `DescEq` and the stable payload variants — and then the two laws for
Tprog itself (O4 `Tprog_rename`, O5 `Tprog_subst`).

The descriptions' rules mention the term formers of `DescCommute.lean`
(`argContTy`, `delimMethodTys`, `muFamily`, …), so the induction hypothesis has to be
normalised with those commutation lemmas before it can be applied; hence the local
`fromIHc` macro, which is `Weakening.lean`'s `fromIH` with that extra simp set.

**The payload variant matters.** `PayloadKernel` is *not* closed under substitution
(CoreSpec §8.4b, "The payload equation is not shape-stable"): a field type that is a
variable becomes an `Enum` under a substitution, and the rule that fires changes from the
`Σ` rule to the tag rule, with an equivalent but not convertible result. So the laws below
are stated for `PayloadStuck` and `PayloadUniform`, and for an arbitrary rule set with the
closure property as a hypothesis; `Tprog_subst` is *not* true for the kernel's variant.
-/

namespace WizMeta
namespace Spec

/-- `fromIH`, with the description formers normalised: the induction hypothesis of a rule
set whose rules mention `argContTy`, `delimMethodTys`, … must be rewritten too. -/
macro "fromIHc " ih:ident ρ:ident Δ:ident hρ:ident hΔ:ident : tactic => `(tactic| (
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq,
    Renames, Substs, Jdg.ren, Jdg.sub, Tm.ren, Tm.ren_shift, Tm.ren_shift2, Tm.ren_inst,
    Tm.ren_argContTy, Tm.ren_hrecIndexTy, Tm.ren_familyTy, Tm.ren_delimMotiveTy,
    Tm.ren_delimMethodTys1, Tm.ren_delimMethodTys2, Tm.ren_delimMethodTys3,
    Tm.ren_delimMethodTys4, Tm.ren_muFamily, Tm.ren_indMotiveTy, Tm.ren_predTy,
    Tm.ren_sectionTy, Tm.ren_indMethodTy, Tm.ren_indHyps, Tm.ren_apps,
    Tm.sub, Tm.sub_shift, Tm.sub_shift2, Tm.sub_inst,
    Tm.sub_argContTy, Tm.sub_hrecIndexTy, Tm.sub_familyTy, Tm.sub_delimMotiveTy,
    Tm.sub_delimMethodTys1, Tm.sub_delimMethodTys2, Tm.sub_delimMethodTys3,
    Tm.sub_delimMethodTys4, Tm.sub_muFamily, Tm.sub_indMotiveTy, Tm.sub_predTy,
    Tm.sub_sectionTy, Tm.sub_indMethodTy, Tm.sub_indHyps, Tm.sub_apps] at $ih:ident ⊢
  repeat' apply And.intro
  all_goals try first | exact $hΔ | exact $ih $ρ $Δ $hρ $hΔ | exact $ih.1 $ρ $Δ $hρ $hΔ | exact $ih.2.1 $ρ $Δ $hρ $hΔ | exact $ih.2.2.1 $ρ $Δ $hρ $hΔ | exact $ih.2.2.2.1 $ρ $Δ $hρ $hΔ | exact $ih.2.2.2.2.1 $ρ $Δ $hρ $hΔ | exact $ih.2.2.2.2.2.1 $ρ $Δ $hρ $hΔ | exact $ih.2.2.2.2.2.2.1 $ρ $Δ $hρ $hΔ | exact $ih.2.2.2.2.2.2.2.1 $ρ $Δ $hρ $hΔ | exact $ih.2.2.2.2.2.2.2.2.1 $ρ $Δ $hρ $hΔ | exact $ih.2 $ρ $Δ $hρ $hΔ | exact $ih.2.2 $ρ $Δ $hρ $hΔ | exact $ih.2.2.2 $ρ $Δ $hρ $hΔ | exact $ih.2.2.2.2 $ρ $Δ $hρ $hΔ | exact $ih.2.2.2.2.2 $ρ $Δ $hρ $hΔ | exact $ih.2.2.2.2.2.2 $ρ $Δ $hρ $hΔ | exact $ih.2.2.2.2.2.2.2 $ρ $Δ $hρ $hΔ | exact $ih.2.2.2.2.2.2.2.2 $ρ $Δ $hρ $hΔ | exact $ih.2.2.2.2.2.2.2.2.2 $ρ $Δ $hρ $hΔ))


macro "renGoal" : tactic => `(tactic| simp only [Jdg.ren, Tm.ren,Tm.ren_shift,Tm.ren_shift2,Tm.ren_inst,Tm.ren_interpRet,Tm.ren_interpArg,Tm.ren_interpRec,Tm.ren_interpHrec,Tm.ren_allArg,Tm.ren_allRec,Tm.ren_allHrec,Tm.ren_hypsArg,Tm.ren_hypsRec,Tm.ren_hypsHrec,Tm.ren_delimArg,Tm.ren_delimRec,Tm.ren_delimHrec,Tm.ren_indCon,Tm.ren_hrecFieldTy,Tm.ren_argContTy,Tm.ren_hrecIndexTy,Tm.ren_familyTy,Tm.ren_famCodeTy,Tm.ren_code,Tm.ren_eqAlong,Tm.ren_eqDescArg,Tm.ren_eqDescRec,Tm.ren_eqDescHrec,Tm.ren_castDescArg,Tm.ren_castDescHrec,Tm.ren_muPayloadEq,Tm.ren_castMuCon,Tm.ren_delimMotiveTy,Tm.ren_delimMethodTys1,Tm.ren_delimMethodTys2,Tm.ren_delimMethodTys3,Tm.ren_delimMethodTys4,Tm.ren_muFamily,Tm.ren_indMotiveTy,Tm.ren_predTy,Tm.ren_sectionTy,Tm.ren_indMethodTy,Tm.ren_indHyps,Tm.ren_apps])
macro "subGoal" : tactic => `(tactic| simp only [Jdg.sub, Tm.sub,Tm.sub_shift,Tm.sub_shift2,Tm.sub_inst,Tm.sub_interpRet,Tm.sub_interpArg,Tm.sub_interpRec,Tm.sub_interpHrec,Tm.sub_allArg,Tm.sub_allRec,Tm.sub_allHrec,Tm.sub_hypsArg,Tm.sub_hypsRec,Tm.sub_hypsHrec,Tm.sub_delimArg,Tm.sub_delimRec,Tm.sub_delimHrec,Tm.sub_indCon,Tm.sub_hrecFieldTy,Tm.sub_argContTy,Tm.sub_hrecIndexTy,Tm.sub_familyTy,Tm.sub_famCodeTy,Tm.sub_code,Tm.sub_eqAlong,Tm.sub_eqDescArg,Tm.sub_eqDescRec,Tm.sub_eqDescHrec,Tm.sub_castDescArg,Tm.sub_castDescHrec,Tm.sub_muPayloadEq,Tm.sub_castMuCon,Tm.sub_delimMotiveTy,Tm.sub_delimMethodTys1,Tm.sub_delimMethodTys2,Tm.sub_delimMethodTys3,Tm.sub_delimMethodTys4,Tm.sub_muFamily,Tm.sub_indMotiveTy,Tm.sub_predTy,Tm.sub_sectionTy,Tm.sub_indMethodTy,Tm.sub_indHyps,Tm.sub_apps])

theorem ulift_renClosed {R : Rules} {var : EqTyVariant} (hu : ∀ r, ULift var r → R r) :
    RenClosed (ULift var) R := by
  intro r hr ih ρ Δ hρ hΔ
  cases hr with
  | form h => exact ofRule (hu _ (.form h)) (by fromIH ih ρ Δ hρ hΔ)
  | up => exact ofRule (hu _ .up) (by fromIH ih ρ Δ hρ hΔ)
  | down => exact ofRule (hu _ .down) (by fromIH ih ρ Δ hρ hΔ)
  | beta => exact ofRule (hu _ .beta) (by fromIH ih ρ Δ hρ hΔ)
  | downRed => exact ofRule (hu _ .downRed) (by fromIH ih ρ Δ hρ hΔ)
  | eta => exact ofRule (hu _ .eta) (by fromIH ih ρ Δ hρ hΔ)
  | cong h => exact ofRule (hu _ (.cong h)) (by fromIH ih ρ Δ hρ hΔ)
  | downCong => exact ofRule (hu _ .downCong) (by fromIH ih ρ Δ hρ hΔ)
  | eqProp h1 h2 => exact ofRule (hu _ (.eqProp h1 h2)) (by fromIH ih ρ Δ hρ hΔ)
  | eq h1 h2 => exact ofRule (hu _ (.eq h1 h2)) (by fromIH ih ρ Δ hρ hΔ)
  | eqTy h1 h2 h3 => exact ofRule (hu _ (.eqTy h1 h2 h3)) (by fromIH ih ρ Δ hρ hΔ)
  | eqTyApart h1 h2 h3 => exact ofRule (hu _ (.eqTyApart h1 h2 h3)) (by fromIH ih ρ Δ hρ hΔ)
  | cast h1 h2 => exact ofRule (hu _ (.cast h1 h2)) (by fromIH ih ρ Δ hρ hΔ)
  | qty => exact ofRule (hu _ .qty) (by fromIH ih ρ Δ hρ hΔ)
  | qlit => exact ofRule (hu _ .qlit) (by fromIH ih ρ Δ hρ hΔ)

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
  | eqProp h1 h2 => exact ofRule (hu _ (.eqProp h1 h2)) (by fromIH ih σ Δ hσ hΔ)
  | eq h1 h2 => exact ofRule (hu _ (.eq h1 h2)) (by fromIH ih σ Δ hσ hΔ)
  | eqTy h1 h2 h3 => exact ofRule (hu _ (.eqTy h1 h2 h3)) (by fromIH ih σ Δ hσ hΔ)
  | eqTyApart h1 h2 h3 => exact ofRule (hu _ (.eqTyApart h1 h2 h3)) (by fromIH ih σ Δ hσ hΔ)
  | cast h1 h2 => exact ofRule (hu _ (.cast h1 h2)) (by fromIH ih σ Δ hσ hΔ)
  | qty => exact ofRule (hu _ .qty) (by fromIH ih σ Δ hσ hΔ)
  | qlit => exact ofRule (hu _ .qlit) (by fromIH ih σ Δ hσ hΔ)


theorem delimPrems_ren {R : Rules} {Γ Δ : Ctx} {l v : Lvl} {I P mret marg mrec mhrec : Tm}
    {ρ : Nat → Nat}
    (h : ∀ p, p ∈ delimPrems Γ l v I P mret marg mrec mhrec → Renames R p)
    (hρ : RenOK ρ Γ Δ) (hΔ : Derivable R (.wf Δ)) :
    ∀ p, p ∈ delimPrems Δ l v (I.ren ρ) (P.ren ρ) (mret.ren ρ) (marg.ren ρ) (mrec.ren ρ)
      (mhrec.ren ρ) → Derivable R p := by
  simp only [delimPrems, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at h ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Jdg.ren, Tm.ren, Tm.ren_delimMotiveTy] using h.1 ρ Δ hρ hΔ
  · simpa only [Jdg.ren, Tm.ren, Tm.ren_delimMethodTys1] using h.2.1 ρ Δ hρ hΔ
  · simpa only [Jdg.ren, Tm.ren, Tm.ren_delimMethodTys2] using h.2.2.1 ρ Δ hρ hΔ
  · simpa only [Jdg.ren, Tm.ren, Tm.ren_delimMethodTys3] using h.2.2.2.1 ρ Δ hρ hΔ
  · simpa only [Jdg.ren, Tm.ren, Tm.ren_delimMethodTys4] using h.2.2.2.2 ρ Δ hρ hΔ

theorem delimPrems_sub {R : Rules} {Γ Δ : Ctx} {l v : Lvl} {I P mret marg mrec mhrec : Tm}
    {σ : Nat → Tm}
    (h : ∀ p, p ∈ delimPrems Γ l v I P mret marg mrec mhrec → Substs R p)
    (hσ : SubOK R σ Γ Δ) (hΔ : Derivable R (.wf Δ)) :
    ∀ p, p ∈ delimPrems Δ l v (I.sub σ) (P.sub σ) (mret.sub σ) (marg.sub σ) (mrec.sub σ)
      (mhrec.sub σ) → Derivable R p := by
  simp only [delimPrems, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at h ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Jdg.sub, Tm.sub, Tm.sub_delimMotiveTy] using h.1 σ Δ hσ hΔ
  · simpa only [Jdg.sub, Tm.sub, Tm.sub_delimMethodTys1] using h.2.1 σ Δ hσ hΔ
  · simpa only [Jdg.sub, Tm.sub, Tm.sub_delimMethodTys2] using h.2.2.1 σ Δ hσ hΔ
  · simpa only [Jdg.sub, Tm.sub, Tm.sub_delimMethodTys3] using h.2.2.2.1 σ Δ hσ hΔ
  · simpa only [Jdg.sub, Tm.sub, Tm.sub_delimMethodTys4] using h.2.2.2.2 σ Δ hσ hΔ

theorem desc_renClosed {R : Rules} (hd : ∀ r, Desc r → R r) : RenClosed Desc R := by
  intro r hr ih ρ Δ hρ hΔ
  cases hr with
  | form => renGoal; apply ofRule (hd _ .form); fromIHc ih ρ Δ hρ hΔ
  | ret => renGoal; apply ofRule (hd _ .ret); fromIHc ih ρ Δ hρ hΔ
  | arg => renGoal; apply ofRule (hd _ .arg); fromIHc ih ρ Δ hρ hΔ
  | drec => renGoal; apply ofRule (hd _ .drec); fromIHc ih ρ Δ hρ hΔ
  | hrec => renGoal; apply ofRule (hd _ .hrec); fromIHc ih ρ Δ hρ hΔ
  | cong h => renGoal; apply ofRule (hd _ (.cong h)); fromIHc ih ρ Δ hρ hΔ
  | retCong => renGoal; apply ofRule (hd _ .retCong); fromIHc ih ρ Δ hρ hΔ
  | argCong => renGoal; apply ofRule (hd _ .argCong); fromIHc ih ρ Δ hρ hΔ
  | recCong => renGoal; apply ofRule (hd _ .recCong); fromIHc ih ρ Δ hρ hΔ
  | hrecCong => renGoal; apply ofRule (hd _ .hrecCong); fromIHc ih ρ Δ hρ hΔ
  | elim =>
      renGoal
      apply ofRule (hd _ .elim)
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at ih
      refine List.forall_mem_cons.2 ⟨?_, ?_⟩
      · exact ih.1 ρ Δ hρ hΔ
      · exact delimPrems_ren (ρ := ρ) ih.2 hρ hΔ
  | elimRet =>
      renGoal
      apply ofRule (hd _ .elimRet)
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at ih
      refine List.forall_mem_cons.2 ⟨?_, ?_⟩
      · exact ih.1 ρ Δ hρ hΔ
      · exact delimPrems_ren (ρ := ρ) ih.2 hρ hΔ
  | elimArg =>
      renGoal
      apply ofRule (hd _ .elimArg)
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at ih
      refine List.forall_mem_cons.2 ⟨?_, ?_⟩
      · exact ih.1 ρ Δ hρ hΔ
      · exact delimPrems_ren (ρ := ρ) ih.2 hρ hΔ
  | elimRec =>
      renGoal
      apply ofRule (hd _ .elimRec)
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at ih
      refine List.forall_mem_cons.2 ⟨?_, ?_⟩
      · exact ih.1 ρ Δ hρ hΔ
      · exact delimPrems_ren (ρ := ρ) ih.2 hρ hΔ
  | elimHrec =>
      renGoal
      apply ofRule (hd _ .elimHrec)
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at ih
      refine List.forall_mem_cons.2 ⟨?_, ?_⟩
      · exact ih.1 ρ Δ hρ hΔ
      · exact delimPrems_ren (ρ := ρ) ih.2 hρ hΔ
  | elimRed =>
      renGoal
      apply ofRule (hd _ .elimRed)
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at ih
      refine List.forall_mem_cons.2 ⟨?_, ?_⟩
      · exact ih.1 ρ Δ hρ hΔ
      · exact delimPrems_ren (ρ := ρ) ih.2 hρ hΔ
  | elimCong h => renGoal; apply ofRule (hd _ (.elimCong h)); fromIHc ih ρ Δ hρ hΔ
  | interp => renGoal; apply ofRule (hd _ .interp); fromIHc ih ρ Δ hρ hΔ
  | interpRet => renGoal; apply ofRule (hd _ .interpRet); fromIHc ih ρ Δ hρ hΔ
  | interpArg => renGoal; apply ofRule (hd _ .interpArg); fromIHc ih ρ Δ hρ hΔ
  | interpRec => renGoal; apply ofRule (hd _ .interpRec); fromIHc ih ρ Δ hρ hΔ
  | interpHrec => renGoal; apply ofRule (hd _ .interpHrec); fromIHc ih ρ Δ hρ hΔ
  | interpRed => renGoal; apply ofRule (hd _ .interpRed); fromIHc ih ρ Δ hρ hΔ
  | interpCong h => renGoal; apply ofRule (hd _ (.interpCong h)); fromIHc ih ρ Δ hρ hΔ
  | all => renGoal; apply ofRule (hd _ .all); fromIHc ih ρ Δ hρ hΔ
  | hyps => renGoal; apply ofRule (hd _ .hyps); fromIHc ih ρ Δ hρ hΔ
  | allRet => renGoal; apply ofRule (hd _ .allRet); fromIHc ih ρ Δ hρ hΔ
  | allArg => renGoal; apply ofRule (hd _ .allArg); fromIHc ih ρ Δ hρ hΔ
  | allRec => renGoal; apply ofRule (hd _ .allRec); fromIHc ih ρ Δ hρ hΔ
  | allHrec => renGoal; apply ofRule (hd _ .allHrec); fromIHc ih ρ Δ hρ hΔ
  | allRed => renGoal; apply ofRule (hd _ .allRed); fromIHc ih ρ Δ hρ hΔ
  | hypsRet => renGoal; apply ofRule (hd _ .hypsRet); fromIHc ih ρ Δ hρ hΔ
  | hypsArg => renGoal; apply ofRule (hd _ .hypsArg); fromIHc ih ρ Δ hρ hΔ
  | hypsRec => renGoal; apply ofRule (hd _ .hypsRec); fromIHc ih ρ Δ hρ hΔ
  | hypsHrec => renGoal; apply ofRule (hd _ .hypsHrec); fromIHc ih ρ Δ hρ hΔ
  | hypsRed => renGoal; apply ofRule (hd _ .hypsRed); fromIHc ih ρ Δ hρ hΔ
  | allCong h1 h2 => renGoal; apply ofRule (hd _ (.allCong h1 h2)); fromIHc ih ρ Δ hρ hΔ
  | hypsCong => renGoal; apply ofRule (hd _ .hypsCong); fromIHc ih ρ Δ hρ hΔ
  | eqTy h => renGoal; apply ofRule (hd _ (.eqTy h)); fromIHc ih ρ Δ hρ hΔ

theorem desc_subClosed {R : Rules} (hd : ∀ r, Desc r → R r) : SubClosed Desc R := by
  intro r hr ih σ Δ hσ hΔ
  cases hr with
  | form => subGoal; apply ofRule (hd _ .form); fromIHc ih σ Δ hσ hΔ
  | ret => subGoal; apply ofRule (hd _ .ret); fromIHc ih σ Δ hσ hΔ
  | arg => subGoal; apply ofRule (hd _ .arg); fromIHc ih σ Δ hσ hΔ
  | drec => subGoal; apply ofRule (hd _ .drec); fromIHc ih σ Δ hσ hΔ
  | hrec => subGoal; apply ofRule (hd _ .hrec); fromIHc ih σ Δ hσ hΔ
  | cong h => subGoal; apply ofRule (hd _ (.cong h)); fromIHc ih σ Δ hσ hΔ
  | retCong => subGoal; apply ofRule (hd _ .retCong); fromIHc ih σ Δ hσ hΔ
  | argCong => subGoal; apply ofRule (hd _ .argCong); fromIHc ih σ Δ hσ hΔ
  | recCong => subGoal; apply ofRule (hd _ .recCong); fromIHc ih σ Δ hσ hΔ
  | hrecCong => subGoal; apply ofRule (hd _ .hrecCong); fromIHc ih σ Δ hσ hΔ
  | elim =>
      subGoal
      apply ofRule (hd _ .elim)
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at ih
      refine List.forall_mem_cons.2 ⟨?_, ?_⟩
      · exact ih.1 σ Δ hσ hΔ
      · exact delimPrems_sub (σ := σ) ih.2 hσ hΔ
  | elimRet =>
      subGoal
      apply ofRule (hd _ .elimRet)
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at ih
      refine List.forall_mem_cons.2 ⟨?_, ?_⟩
      · exact ih.1 σ Δ hσ hΔ
      · exact delimPrems_sub (σ := σ) ih.2 hσ hΔ
  | elimArg =>
      subGoal
      apply ofRule (hd _ .elimArg)
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at ih
      refine List.forall_mem_cons.2 ⟨?_, ?_⟩
      · exact ih.1 σ Δ hσ hΔ
      · exact delimPrems_sub (σ := σ) ih.2 hσ hΔ
  | elimRec =>
      subGoal
      apply ofRule (hd _ .elimRec)
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at ih
      refine List.forall_mem_cons.2 ⟨?_, ?_⟩
      · exact ih.1 σ Δ hσ hΔ
      · exact delimPrems_sub (σ := σ) ih.2 hσ hΔ
  | elimHrec =>
      subGoal
      apply ofRule (hd _ .elimHrec)
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at ih
      refine List.forall_mem_cons.2 ⟨?_, ?_⟩
      · exact ih.1 σ Δ hσ hΔ
      · exact delimPrems_sub (σ := σ) ih.2 hσ hΔ
  | elimRed =>
      subGoal
      apply ofRule (hd _ .elimRed)
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at ih
      refine List.forall_mem_cons.2 ⟨?_, ?_⟩
      · exact ih.1 σ Δ hσ hΔ
      · exact delimPrems_sub (σ := σ) ih.2 hσ hΔ
  | elimCong h => subGoal; apply ofRule (hd _ (.elimCong h)); fromIHc ih σ Δ hσ hΔ
  | interp => subGoal; apply ofRule (hd _ .interp); fromIHc ih σ Δ hσ hΔ
  | interpRet => subGoal; apply ofRule (hd _ .interpRet); fromIHc ih σ Δ hσ hΔ
  | interpArg => subGoal; apply ofRule (hd _ .interpArg); fromIHc ih σ Δ hσ hΔ
  | interpRec => subGoal; apply ofRule (hd _ .interpRec); fromIHc ih σ Δ hσ hΔ
  | interpHrec => subGoal; apply ofRule (hd _ .interpHrec); fromIHc ih σ Δ hσ hΔ
  | interpRed => subGoal; apply ofRule (hd _ .interpRed); fromIHc ih σ Δ hσ hΔ
  | interpCong h => subGoal; apply ofRule (hd _ (.interpCong h)); fromIHc ih σ Δ hσ hΔ
  | all => subGoal; apply ofRule (hd _ .all); fromIHc ih σ Δ hσ hΔ
  | hyps => subGoal; apply ofRule (hd _ .hyps); fromIHc ih σ Δ hσ hΔ
  | allRet => subGoal; apply ofRule (hd _ .allRet); fromIHc ih σ Δ hσ hΔ
  | allArg => subGoal; apply ofRule (hd _ .allArg); fromIHc ih σ Δ hσ hΔ
  | allRec => subGoal; apply ofRule (hd _ .allRec); fromIHc ih σ Δ hσ hΔ
  | allHrec => subGoal; apply ofRule (hd _ .allHrec); fromIHc ih σ Δ hσ hΔ
  | allRed => subGoal; apply ofRule (hd _ .allRed); fromIHc ih σ Δ hσ hΔ
  | hypsRet => subGoal; apply ofRule (hd _ .hypsRet); fromIHc ih σ Δ hσ hΔ
  | hypsArg => subGoal; apply ofRule (hd _ .hypsArg); fromIHc ih σ Δ hσ hΔ
  | hypsRec => subGoal; apply ofRule (hd _ .hypsRec); fromIHc ih σ Δ hσ hΔ
  | hypsHrec => subGoal; apply ofRule (hd _ .hypsHrec); fromIHc ih σ Δ hσ hΔ
  | hypsRed => subGoal; apply ofRule (hd _ .hypsRed); fromIHc ih σ Δ hσ hΔ
  | allCong h1 h2 => subGoal; apply ofRule (hd _ (.allCong h1 h2)); fromIHc ih σ Δ hσ hΔ
  | hypsCong => subGoal; apply ofRule (hd _ .hypsCong); fromIHc ih σ Δ hσ hΔ
  | eqTy h => subGoal; apply ofRule (hd _ (.eqTy h)); fromIHc ih σ Δ hσ hΔ

theorem mu_renClosed {R : Rules} (hm : ∀ r, Mu r → R r) : RenClosed Mu R := by
  intro r hr ih ρ Δ hρ hΔ
  cases hr with
  | form => renGoal; apply ofRule (hm _ .form); fromIHc ih ρ Δ hρ hΔ
  | con => renGoal; apply ofRule (hm _ .con); fromIHc ih ρ Δ hρ hΔ
  | ind => renGoal; apply ofRule (hm _ .ind); fromIHc ih ρ Δ hρ hΔ
  | iota => renGoal; apply ofRule (hm _ .iota); fromIHc ih ρ Δ hρ hΔ
  | indRed => renGoal; apply ofRule (hm _ .indRed); fromIHc ih ρ Δ hρ hΔ
  | cong h => renGoal; apply ofRule (hm _ (.cong h)); fromIHc ih ρ Δ hρ hΔ
  | conCong => renGoal; apply ofRule (hm _ .conCong); fromIHc ih ρ Δ hρ hΔ
  | indCong h1 h2 => renGoal; apply ofRule (hm _ (.indCong h1 h2)); fromIHc ih ρ Δ hρ hΔ

theorem mu_subClosed {R : Rules} (hm : ∀ r, Mu r → R r) : SubClosed Mu R := by
  intro r hr ih σ Δ hσ hΔ
  cases hr with
  | form => subGoal; apply ofRule (hm _ .form); fromIHc ih σ Δ hσ hΔ
  | con => subGoal; apply ofRule (hm _ .con); fromIHc ih σ Δ hσ hΔ
  | ind => subGoal; apply ofRule (hm _ .ind); fromIHc ih σ Δ hσ hΔ
  | iota => subGoal; apply ofRule (hm _ .iota); fromIHc ih σ Δ hσ hΔ
  | indRed => subGoal; apply ofRule (hm _ .indRed); fromIHc ih σ Δ hσ hΔ
  | cong h => subGoal; apply ofRule (hm _ (.cong h)); fromIHc ih σ Δ hσ hΔ
  | conCong => subGoal; apply ofRule (hm _ .conCong); fromIHc ih σ Δ hσ hΔ
  | indCong h1 h2 => subGoal; apply ofRule (hm _ (.indCong h1 h2)); fromIHc ih σ Δ hσ hΔ


theorem descEq_renClosed {R : Rules} (he : ∀ r, DescEq r → R r) : RenClosed DescEq R := by
  intro r hr ih ρ Δ hρ hΔ
  cases hr with
  | eqRet => renGoal; apply ofRule (he _ .eqRet); fromIHc ih ρ Δ hρ hΔ
  | eqArg => renGoal; apply ofRule (he _ .eqArg); fromIHc ih ρ Δ hρ hΔ
  | eqRec => renGoal; apply ofRule (he _ .eqRec); fromIHc ih ρ Δ hρ hΔ
  | eqHrec => renGoal; apply ofRule (he _ .eqHrec); fromIHc ih ρ Δ hρ hΔ
  | @eqQtyApart Γ I D D' l q q' c h1 h2 h3 h4 h5 =>
      renGoal
      apply ofRule (he _ (.eqQtyApart (by simpa only [Tm.dctor_ren] using h1)
        (by simpa only [Tm.dctor_ren] using h2) (Tm.dqty_ren_qlit h3 ρ) (Tm.dqty_ren_qlit h4 ρ) h5))
      fromIHc ih ρ Δ hρ hΔ
  | @eqCtors Γ I D D' l c c' h1 h2 h3 =>
      renGoal
      apply ofRule (he _ (.eqCtors (by simpa only [Tm.dctor_ren] using h1)
        (by simpa only [Tm.dctor_ren] using h2) h3))
      fromIHc ih ρ Δ hρ hΔ
  | eqRedL => renGoal; apply ofRule (he _ .eqRedL); fromIHc ih ρ Δ hρ hΔ
  | eqRedR => renGoal; apply ofRule (he _ .eqRedR); fromIHc ih ρ Δ hρ hΔ
  | eqTyMu h => renGoal; apply ofRule (he _ (.eqTyMu h)); fromIHc ih ρ Δ hρ hΔ
  | castRet h => renGoal; apply ofRule (he _ (.castRet h)); fromIHc ih ρ Δ hρ hΔ
  | castArg h => renGoal; apply ofRule (he _ (.castArg h)); fromIHc ih ρ Δ hρ hΔ
  | castRec h => renGoal; apply ofRule (he _ (.castRec h)); fromIHc ih ρ Δ hρ hΔ
  | castHrec h => renGoal; apply ofRule (he _ (.castHrec h)); fromIHc ih ρ Δ hρ hΔ
  | castMu h => renGoal; apply ofRule (he _ (.castMu h)); fromIHc ih ρ Δ hρ hΔ
  | castRedArg h =>
      renGoal
      apply ofRule (he _ (.castRedArg (Tm.former_desc_mu_ren h ρ)))
      fromIHc ih ρ Δ hρ hΔ

theorem descEq_subClosed {R : Rules} (he : ∀ r, DescEq r → R r) : SubClosed DescEq R := by
  intro r hr ih σ Δ hσ hΔ
  cases hr with
  | eqRet => subGoal; apply ofRule (he _ .eqRet); fromIHc ih σ Δ hσ hΔ
  | eqArg => subGoal; apply ofRule (he _ .eqArg); fromIHc ih σ Δ hσ hΔ
  | eqRec => subGoal; apply ofRule (he _ .eqRec); fromIHc ih σ Δ hσ hΔ
  | eqHrec => subGoal; apply ofRule (he _ .eqHrec); fromIHc ih σ Δ hσ hΔ
  | @eqQtyApart Γ I D D' l q q' c h1 h2 h3 h4 h5 =>
      subGoal
      apply ofRule (he _ (.eqQtyApart (Tm.dctor_sub h1 σ) (Tm.dctor_sub h2 σ)
        (Tm.dqty_sub_qlit h3 σ) (Tm.dqty_sub_qlit h4 σ) h5))
      fromIHc ih σ Δ hσ hΔ
  | @eqCtors Γ I D D' l c c' h1 h2 h3 =>
      subGoal
      apply ofRule (he _ (.eqCtors (Tm.dctor_sub h1 σ) (Tm.dctor_sub h2 σ) h3))
      fromIHc ih σ Δ hσ hΔ
  | eqRedL => subGoal; apply ofRule (he _ .eqRedL); fromIHc ih σ Δ hσ hΔ
  | eqRedR => subGoal; apply ofRule (he _ .eqRedR); fromIHc ih σ Δ hσ hΔ
  | eqTyMu h => subGoal; apply ofRule (he _ (.eqTyMu h)); fromIHc ih σ Δ hσ hΔ
  | castRet h => subGoal; apply ofRule (he _ (.castRet h)); fromIHc ih σ Δ hσ hΔ
  | castArg h => subGoal; apply ofRule (he _ (.castArg h)); fromIHc ih σ Δ hσ hΔ
  | castRec h => subGoal; apply ofRule (he _ (.castRec h)); fromIHc ih σ Δ hσ hΔ
  | castHrec h => subGoal; apply ofRule (he _ (.castHrec h)); fromIHc ih σ Δ hσ hΔ
  | castMu h => subGoal; apply ofRule (he _ (.castMu h)); fromIHc ih σ Δ hσ hΔ
  | castRedArg h =>
      subGoal
      apply ofRule (he _ (.castRedArg (Tm.former_desc_mu_sub h σ)))
      fromIHc ih σ Δ hσ hΔ

theorem payloadUniform_renClosed {R : Rules} (hp : ∀ r, PayloadUniform r → R r) :
    RenClosed PayloadUniform R := by
  intro r hr ih ρ Δ hρ hΔ
  cases hr with
  | eq => renGoal; apply ofRule (hp _ .eq); fromIHc ih ρ Δ hρ hΔ
  | eqRedL => renGoal; apply ofRule (hp _ .eqRedL); fromIHc ih ρ Δ hρ hΔ
  | eqRedR => renGoal; apply ofRule (hp _ .eqRedR); fromIHc ih ρ Δ hρ hΔ

theorem payloadUniform_subClosed {R : Rules} (hp : ∀ r, PayloadUniform r → R r) :
    SubClosed PayloadUniform R := by
  intro r hr ih σ Δ hσ hΔ
  cases hr with
  | eq => subGoal; apply ofRule (hp _ .eq); fromIHc ih σ Δ hσ hΔ
  | eqRedL => subGoal; apply ofRule (hp _ .eqRedL); fromIHc ih σ Δ hσ hΔ
  | eqRedR => subGoal; apply ofRule (hp _ .eqRedR); fromIHc ih σ Δ hσ hΔ

theorem payloadStuck_renClosed {R : Rules} (hp : ∀ r, PayloadStuck r → R r) :
    RenClosed PayloadStuck R := by
  intro r hr ih ρ Δ hρ hΔ
  cases hr with
  | eq => renGoal; apply ofRule (hp _ .eq); fromIHc ih ρ Δ hρ hΔ
  | eqRedL => renGoal; apply ofRule (hp _ .eqRedL); fromIHc ih ρ Δ hρ hΔ
  | eqRedR => renGoal; apply ofRule (hp _ .eqRedR); fromIHc ih ρ Δ hρ hΔ
  | peqRet => renGoal; apply ofRule (hp _ .peqRet); fromIHc ih ρ Δ hρ hΔ
  | peqTag => renGoal; apply ofRule (hp _ .peqTag); fromIHc ih ρ Δ hρ hΔ
  | peqTagLifted => renGoal; apply ofRule (hp _ .peqTagLifted); fromIHc ih ρ Δ hρ hΔ
  | peqTagDiff h => renGoal; apply ofRule (hp _ (.peqTagDiff h)); fromIHc ih ρ Δ hρ hΔ
  | peqTagLiftedDiff h => renGoal; apply ofRule (hp _ (.peqTagLiftedDiff h)); fromIHc ih ρ Δ hρ hΔ
  | peqField h => renGoal; apply ofRule (hp _ (.peqField (NonTag.ren h ρ))); fromIHc ih ρ Δ hρ hΔ
  | peqRecLast => renGoal; apply ofRule (hp _ .peqRecLast); fromIHc ih ρ Δ hρ hΔ
  | peqRec h => renGoal; apply ofRule (hp _ (.peqRec (NonRet.ren h ρ))); fromIHc ih ρ Δ hρ hΔ
  | peqHrecLast => renGoal; apply ofRule (hp _ .peqHrecLast); fromIHc ih ρ Δ hρ hΔ
  | peqHrec h => renGoal; apply ofRule (hp _ (.peqHrec (NonRet.ren h ρ))); fromIHc ih ρ Δ hρ hΔ

theorem payloadStuck_subClosed {R : Rules} (hp : ∀ r, PayloadStuck r → R r) :
    SubClosed PayloadStuck R := by
  intro r hr ih σ Δ hσ hΔ
  cases hr with
  | eq => subGoal; apply ofRule (hp _ .eq); fromIHc ih σ Δ hσ hΔ
  | eqRedL => subGoal; apply ofRule (hp _ .eqRedL); fromIHc ih σ Δ hσ hΔ
  | eqRedR => subGoal; apply ofRule (hp _ .eqRedR); fromIHc ih σ Δ hσ hΔ
  | peqRet => subGoal; apply ofRule (hp _ .peqRet); fromIHc ih σ Δ hσ hΔ
  | peqTag => subGoal; apply ofRule (hp _ .peqTag); fromIHc ih σ Δ hσ hΔ
  | peqTagLifted => subGoal; apply ofRule (hp _ .peqTagLifted); fromIHc ih σ Δ hσ hΔ
  | peqTagDiff h => subGoal; apply ofRule (hp _ (.peqTagDiff h)); fromIHc ih σ Δ hσ hΔ
  | peqTagLiftedDiff h => subGoal; apply ofRule (hp _ (.peqTagLiftedDiff h)); fromIHc ih σ Δ hσ hΔ
  | peqField h => subGoal; apply ofRule (hp _ (.peqField (NonTag.sub h σ))); fromIHc ih σ Δ hσ hΔ
  | peqRecLast => subGoal; apply ofRule (hp _ .peqRecLast); fromIHc ih σ Δ hσ hΔ
  | peqRec h => subGoal; apply ofRule (hp _ (.peqRec (NonRet.sub h σ))); fromIHc ih σ Δ hσ hΔ
  | peqHrecLast => subGoal; apply ofRule (hp _ .peqHrecLast); fromIHc ih σ Δ hσ hΔ
  | peqHrec h => subGoal; apply ofRule (hp _ (.peqHrec (NonRet.sub h σ))); fromIHc ih σ Δ hσ hΔ


theorem T1_renClosedIn {sg : Sig} (hsg : Sig.Closed sg) (var : EqTyVariant) {R : Rules}
    (h : ∀ r, T1 sg var r → R r) (hc : ∀ r, Core r → R r) : RenClosed (T1 sg var) R :=
  (T0_renClosedIn hsg var (fun _ x => h _ (.inl x)) hc).union
    (inReg_renClosed hc (fun _ x => h _ (.inr x)))

theorem T1_subClosedIn {sg : Sig} (hsg : Sig.Closed sg) (var : EqTyVariant) {R : Rules}
    (hren : ∀ j, Derivable R j → Renames R j)
    (h : ∀ r, T1 sg var r → R r) (hc : ∀ r, Core r → R r) : SubClosed (T1 sg var) R :=
  (T0_subClosedIn hsg var hren (fun _ x => h _ (.inl x)) hc).union
    (inReg_subClosed hren hc (fun _ x => h _ (.inr x)))

/-- `Tprog` is closed under renaming, for any payload rule set that is. -/
theorem Tprog_renClosedIn {sg : Sig} (hsg : Sig.Closed sg) (var : EqTyVariant)
    {payload R : Rules}
    (h1 : ∀ r, T1 sg var r → R r) (hu : ∀ r, ULift var r → R r)
    (hd : ∀ r, Desc r → R r) (hm : ∀ r, Mu r → R r) (he : ∀ r, DescEq r → R r)
    (hp : RenClosed payload R) (hc : ∀ r, Core r → R r) :
    RenClosed (Tprog sg var payload) R :=
  (((((T1_renClosedIn hsg var h1 hc).union (ulift_renClosed hu)).union (desc_renClosed hd)).union
    (mu_renClosed hm)).union (descEq_renClosed he)).union hp

/-- `Tprog` is closed under substitution, for any payload rule set that is. The kernel's
payload rule set is *not* closed (see the module comment), so the payload closure is a
hypothesis. -/
theorem Tprog_subClosedIn {sg : Sig} (hsg : Sig.Closed sg) (var : EqTyVariant)
    {payload R : Rules}
    (h1 : ∀ r, T1 sg var r → R r) (hu : ∀ r, ULift var r → R r)
    (hd : ∀ r, Desc r → R r) (hm : ∀ r, Mu r → R r) (he : ∀ r, DescEq r → R r)
    (hp : SubClosed payload R) (hren : ∀ j, Derivable R j → Renames R j)
    (hc : ∀ r, Core r → R r) :
    SubClosed (Tprog sg var payload) R :=
  (((((T1_subClosedIn hsg var hren h1 hc).union (ulift_subClosed hu)).union (desc_subClosed hd)).union
    (mu_subClosed hm)).union (descEq_subClosed he)).union hp

/-- The Core rules are in Tprog (the innermost fragment). -/
theorem core_in_Tprog {sg : Sig} {var : EqTyVariant} {payload : Rules} {r : Rule} (h : Core r) :
    Tprog sg var payload r := by
  unfold Tprog T1 T0
  repeat' apply Or.inl
  exact h

theorem T1_in_Tprog {sg : Sig} {var : EqTyVariant} {payload : Rules} {r : Rule}
    (h : T1 sg var r) : Tprog sg var payload r :=
  Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h))))

theorem ulift_in_Tprog {sg : Sig} {var : EqTyVariant} {payload : Rules} {r : Rule}
    (h : ULift var r) : Tprog sg var payload r := by
  unfold Tprog
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))

theorem desc_in_Tprog {sg : Sig} {var : EqTyVariant} {payload : Rules} {r : Rule}
    (h : Desc r) : Tprog sg var payload r := by
  unfold Tprog
  exact Or.inl (Or.inl (Or.inl (Or.inr h)))

theorem mu_in_Tprog {sg : Sig} {var : EqTyVariant} {payload : Rules} {r : Rule}
    (h : Mu r) : Tprog sg var payload r := by
  unfold Tprog
  exact Or.inl (Or.inl (Or.inr h))

theorem descEq_in_Tprog {sg : Sig} {var : EqTyVariant} {payload : Rules} {r : Rule}
    (h : DescEq r) : Tprog sg var payload r := by
  unfold Tprog
  exact Or.inl (Or.inr h)

theorem payload_in_Tprog {sg : Sig} {var : EqTyVariant} {payload : Rules} {r : Rule}
    (h : payload r) : Tprog sg var payload r := by
  unfold Tprog
  exact Or.inr h

theorem Tprog_renClosed {sg : Sig} (hsg : Sig.Closed sg) (var : EqTyVariant) :
    RenClosed (Tprog sg var PayloadStuck) (Tprog sg var PayloadStuck) := by
  exact Tprog_renClosedIn hsg var (R := Tprog sg var PayloadStuck)
    (fun _ h => T1_in_Tprog h) (fun _ h => ulift_in_Tprog h) (fun _ h => desc_in_Tprog h)
    (fun _ h => mu_in_Tprog h) (fun _ h => descEq_in_Tprog h)
    (payloadStuck_renClosed (fun _ h => payload_in_Tprog h)) (fun _ h => core_in_Tprog h)

theorem Tprog_rename {sg : Sig} (hsg : Sig.Closed sg) {var : EqTyVariant} {j : Jdg}
    (d : Derivable (Tprog sg var PayloadStuck) j) : Renames (Tprog sg var PayloadStuck) j :=
  rename_of_closed (Tprog_renClosed hsg var) d

theorem Tprog_subClosed {sg : Sig} (hsg : Sig.Closed sg) (var : EqTyVariant) :
    SubClosed (Tprog sg var PayloadStuck) (Tprog sg var PayloadStuck) := by
  exact Tprog_subClosedIn hsg var (R := Tprog sg var PayloadStuck)
    (fun _ h => T1_in_Tprog h) (fun _ h => ulift_in_Tprog h) (fun _ h => desc_in_Tprog h)
    (fun _ h => mu_in_Tprog h) (fun _ h => descEq_in_Tprog h)
    (payloadStuck_subClosed (fun _ h => payload_in_Tprog h))
    (fun _ d => Tprog_rename hsg d) (fun _ h => core_in_Tprog h)

/-- **`Tprog_subst` (plan O5).** Tprog with the stable payload rule set is closed under
term substitution, for every judgment form. -/
theorem Tprog_subst {sg : Sig} (hsg : Sig.Closed sg) {var : EqTyVariant} {j : Jdg}
    (d : Derivable (Tprog sg var PayloadStuck) j) : Substs (Tprog sg var PayloadStuck) j :=
  subst_of_closed (Tprog_subClosed hsg var) d

/-- Substitution as the plan states it. -/
theorem Tprog_substitution {sg : Sig} (hsg : Sig.Closed sg) {var : EqTyVariant} {Γ : Ctx}
    {A t B a : Tm} (hΓ : Derivable (Tprog sg var PayloadStuck) (.wf Γ))
    (ht : Derivable (Tprog sg var PayloadStuck) ((A :: Γ) ⊢ t ∶ B))
    (ha : Derivable (Tprog sg var PayloadStuck) (Γ ⊢ a ∶ A)) :
    Derivable (Tprog sg var PayloadStuck) (Γ ⊢ t.inst a ∶ B.inst a) := by
  refine Tprog_subst hsg ht (Tm.one a) Γ ?_ hΓ
  intro i C hC
  simp only [Jdg.ctx] at hC
  cases i with
  | zero =>
    rw [Ctx.lookup_zero] at hC; cases hC
    simp only [Tm.shift, Tm.sub_ren]
    rw [show (Tm.one a ∘ (· + 1)) = Tm.var from rfl, Tm.sub_var]
    exact ha
  | succ i =>
    rw [Ctx.lookup_succ] at hC
    cases hΓi : Ctx.lookup Γ i with
    | none => rw [hΓi] at hC; cases hC
    | some D =>
      rw [hΓi] at hC; cases hC
      simp only [Tm.shift, Tm.sub_ren]
      rw [show (Tm.one a ∘ (· + 1)) = Tm.var from rfl, Tm.sub_var]
      exact ofRule (core_in_Tprog (Core.var hΓi)) (by
        simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]; exact hΓ)

theorem TprogUniform_renClosed {sg : Sig} (hsg : Sig.Closed sg) (var : EqTyVariant) :
    RenClosed (Tprog sg var PayloadUniform) (Tprog sg var PayloadUniform) := by
  exact Tprog_renClosedIn hsg var (R := Tprog sg var PayloadUniform)
    (fun _ h => T1_in_Tprog h) (fun _ h => ulift_in_Tprog h) (fun _ h => desc_in_Tprog h)
    (fun _ h => mu_in_Tprog h) (fun _ h => descEq_in_Tprog h)
    (payloadUniform_renClosed (fun _ h => payload_in_Tprog h)) (fun _ h => core_in_Tprog h)

theorem TprogUniform_subClosed {sg : Sig} (hsg : Sig.Closed sg) (var : EqTyVariant) :
    SubClosed (Tprog sg var PayloadUniform) (Tprog sg var PayloadUniform) := by
  exact Tprog_subClosedIn hsg var (R := Tprog sg var PayloadUniform)
    (fun _ h => T1_in_Tprog h) (fun _ h => ulift_in_Tprog h) (fun _ h => desc_in_Tprog h)
    (fun _ h => mu_in_Tprog h) (fun _ h => descEq_in_Tprog h)
    (payloadUniform_subClosed (fun _ h => payload_in_Tprog h))
    (fun _ d => rename_of_closed (TprogUniform_renClosed hsg var) d) (fun _ h => core_in_Tprog h)

theorem TprogUniform_subst {sg : Sig} (hsg : Sig.Closed sg) {var : EqTyVariant} {j : Jdg}
    (d : Derivable (Tprog sg var PayloadUniform) j) : Substs (Tprog sg var PayloadUniform) j :=
  subst_of_closed (TprogUniform_subClosed hsg var) d


end Spec
end WizMeta
