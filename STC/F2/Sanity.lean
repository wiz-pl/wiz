import STC.F2.Ctx
/-!
# F2: sanity derivations

Small derivations that witness the new rules are inhabited. The examples use
`A = Unit prop` and `φ = ⊤`, so every boundary and proof premise is discharged from `tt`
and the phase rules. They exercise all three term formers: `Ext 0` formation, `η●`/`⋆●`
and the two methods of the `●` eliminator, and strict `Glue` formation with a
non-identity `T` family.
-/


namespace STC
namespace F2

open F0
open F0.Spec
open scoped F0.Spec

/-- `Unit prop`, written once. -/
abbrev U : Tm := .unit .prop

/-- The always-true phase. -/
abbrev topφ : F1.Cof := .top

theorem wf_nil : Derivable (F2 ([] : Sig)) (.wf ([] : Ctx)) :=
  ofRule (core_in_F2 Core.wfNil) (by simp)

theorem ph_top_form : Derivable (F2 ([] : Sig)) ([] ⊢ ph topφ ∶ .sort .prop) :=
  phase_form_R (fun _ x => phase_in_F2 x) wf_nil topφ

theorem wf_ph : Derivable (F2 ([] : Sig)) (.wf (ph topφ :: ([] : Ctx))) :=
  wfExt (fun _ x => core_in_F2 x) wf_nil ph_top_form

theorem u_form : Derivable (F2 ([] : Sig)) ([] ⊢ U ∶ .sort .prop) :=
  ofRule (unit_in_F2 (Unit.form (s := .prop))) (by
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
    exact wf_nil)

theorem wf_U : Derivable (F2 ([] : Sig)) (.wf (U :: ([] : Ctx))) :=
  wfExt (fun _ x => core_in_F2 x) wf_nil u_form

theorem tt_u : Derivable (F2 ([] : Sig)) ([] ⊢ .tt ∶ U) :=
  ofRule (unit_in_F2 (Unit.tt (s := .prop))) (by
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
    exact wf_nil)

theorem prf_top : Derivable (F2 ([] : Sig)) ([] ⊢ prf topφ ∶ ph topφ) := by
  have h1 : Derivable (STC.F1.F1 ([] : Sig)) ([] ⊢ .tt ∶ ph topφ) :=
    STC.F1.phase_top_intro (ofRule (STC.F1.core_in_F1 Core.wfNil) (by simp))
  have h2 := STC.F1.phase_intro (sg := ([] : Sig)) (h := _root_.STC.F1.Cof.le_refl topφ)
    (he := h1)
  exact Derivable.mono (fun _ x => f1_in_F2 x) h2

/-- `○_⊤ (Unit prop) = (z : [⊤]) → Unit prop` is a type. -/
theorem circ_top_U_form : Derivable (F2 ([] : Sig))
    ([] ⊢ circ .prop topφ U ∶ .sort .prop) := by
  refine ofRule (pi_in_F2 (Pi.form (i := .prop) (j := .prop) (s := .prop) rfl)) ?_
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
  refine ⟨ph_top_form, ?_⟩
  exact ofRule (unit_in_F2 (Unit.form (s := .prop))) (by
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
    exact wf_ph)

/-- The boundary `λ _. tt : ○_⊤ (Unit prop)`. -/
theorem a_top : Derivable (F2 ([] : Sig)) ([] ⊢ .lam .tt ∶ circ .prop topφ U) := by
  refine ofRule (pi_in_F2 (Pi.lam (s := .prop) (i := .prop) (A := ph topφ)
    (B := U.shift) (b := .tt))) ?_
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
  refine ⟨circ_top_U_form, ph_top_form, ?_⟩
  exact ofRule (unit_in_F2 (Unit.tt (s := .prop))) (by
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
    exact wf_ph)

/-- `Ext 0` formation. -/
theorem ext_form : Derivable (F2 ([] : Sig)) ([] ⊢ Ext U topφ (.lam .tt) ∶ .sort .prop) :=
  ofRule (ext0_in_F2 (Ext0.form (s := .prop))) (by
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨u_form, a_top⟩)

/-- `●_⊤ (Unit prop)` formation. -/
theorem closed_form : Derivable (F2 ([] : Sig))
    ([] ⊢ ClosedTy topφ U ∶ .sort .prop) :=
  ofRule (closed_in_F2 (Closed.form (s := .prop))) (by
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
    exact u_form)

/-- `η● tt : ●_⊤ (Unit prop)`. -/
theorem closed_intro : Derivable (F2 ([] : Sig))
    ([] ⊢ .closedIn topφ .tt ∶ ClosedTy topφ U) :=
  ofRule (closed_in_F2 (Closed.intro (s := .prop))) (by
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨closed_form, tt_u⟩)

/-- `⋆● : ●_⊤ (Unit prop)`. -/
theorem closed_star : Derivable (F2 ([] : Sig))
    ([] ⊢ .closedStar topφ U ∶ ClosedTy topφ U) :=
  ofRule (closed_in_F2 (Closed.star (s := .prop))) (by
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨closed_form, prf_top⟩)

/-- The eliminator's `η`-method `λ _. tt : U → U`. -/
theorem mEta : Derivable (F2 ([] : Sig))
    ([] ⊢ .lam .tt ∶ .pi (.imax .prop .prop) U U.shift) := by
  refine ofRule (pi_in_F2 (Pi.lam (s := .prop) (i := .prop) (A := U) (B := U.shift)
    (b := .tt))) ?_
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
  refine ⟨?_, u_form, ?_⟩
  · refine ofRule (pi_in_F2 (Pi.form (i := .prop) (j := .prop) (s := .prop) rfl)) ?_
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
    refine ⟨u_form, ?_⟩
    exact ofRule (unit_in_F2 (Unit.form (s := .prop))) (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
      exact wf_U)
  · exact ofRule (unit_in_F2 (Unit.tt (s := .prop))) (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
      exact wf_U)

/-- The eliminator's `⋆`-method `λ _. tt : [⊤] → U`. -/
theorem mStar : Derivable (F2 ([] : Sig))
    ([] ⊢ .lam .tt ∶ .pi .prop (ph topφ) U.shift) := by
  refine ofRule (pi_in_F2 (Pi.lam (s := .prop) (i := .prop) (A := ph topφ)
    (B := U.shift) (b := .tt))) ?_
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
  refine ⟨circ_top_U_form, ph_top_form, ?_⟩
  exact ofRule (unit_in_F2 (Unit.tt (s := .prop))) (by
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
    exact wf_ph)

/-- Eliminating `η● tt`. -/
theorem closed_elim_in : Derivable (F2 ([] : Sig))
    ([] ⊢ .closedElim topφ U U (.lam .tt) (.lam .tt) (.closedIn topφ .tt) ∶ U) := by
  refine ofRule (closed_in_F2 (Closed.elim (sA := .prop) (sB := .prop))) ?_
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨u_form, u_form, mEta, mStar, closed_intro⟩

/-- `η● tt` computes to `mη tt`. -/
theorem closed_beta_in : Derivable (F2 ([] : Sig))
    ([] ⊢ .closedElim topφ U U (.lam .tt) (.lam .tt) (.closedIn topφ .tt) ⟶ .app (.lam .tt) .tt ∶ U) := by
  refine ofRule (closed_in_F2 (Closed.betaIn (sA := .prop) (sB := .prop))) ?_
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨u_form, u_form, mEta, tt_u⟩


end F2
end STC
