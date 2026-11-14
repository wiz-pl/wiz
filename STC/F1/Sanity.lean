import STC.F1.Phase
/-!
# F1 sanity cases

Small witnesses that the F1 phase layer is inhabited and that the decision procedure
behaves on the cases the design note names. These are compile-time checks: the `example`s
must elaborate and the `#eval`s print the expected values (run
`lake build STC.F1.Sanity`; the `#eval` output is a build-time check because the file
fails to build if an `example` stops checking).
-/


namespace STC
namespace F1

open F0
open F0.Spec
open scoped F0.Spec

/-- The empty signature is closed, so the F1 laws apply to it. -/
theorem sigClosed_nil : Sig.Closed ([] : Sig) := by
  intro d hd
  simp at hd

/-- The empty context is well formed (in F1, via F0Base's `wfNil`). -/
theorem wfNil_F1 (sg : Sig) : Derivable (F1 sg) (Jdg.wf ([] : Ctx)) :=
  ofRule (core_in_F1 Core.wfNil) (by simp)

/-- `Unit s` is a type in F1 (a convenience for the examples). -/
theorem unit_form_F1 {sg : Sig} {Γ : Ctx} {s : Srt}
    (hΓ : Derivable (F1 sg) (.wf Γ)) : Derivable (F1 sg) (Γ ⊢ .unit s ∶ .sort s) :=
  ofRule (unit_in_F1 (Unit.form (s := s))) (by
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
    exact hΓ)

/-- `tt : Unit s` in F1. -/
theorem unit_tt_F1 {sg : Sig} {Γ : Ctx} {s : Srt}
    (hΓ : Derivable (F1 sg) (.wf Γ)) : Derivable (F1 sg) (Γ ⊢ .tt ∶ .unit s) :=
  ofRule (unit_in_F1 (Unit.tt (s := s))) (by
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
    exact hΓ)

/-- `[φ]` is a proposition for every cofibration. -/
example : Derivable (F1 ([] : Sig)) (Jdg.ty [] (ph (Cof.atom 0)) (Tm.sort .prop)) :=
  phase_form (wfNil_F1 _) _

/-- `[⊤]` is inhabited (`tt`). -/
example : Derivable (F1 ([] : Sig)) (Jdg.ty [] Tm.tt (ph .top)) :=
  phase_top_intro (wfNil_F1 _)

/-- `[⊤ ∧ ⊤]` is inhabited (`(tt, tt)`). -/
example : Derivable (F1 ([] : Sig)) (Jdg.ty [] (.pair Tm.tt Tm.tt) (ph (.and .top .top))) :=
  phase_and_intro (wfNil_F1 _)
    (phase_top_intro (wfNil_F1 _)) (phase_top_intro (wfNil_F1 _))

/-- The first projection of that pair. -/
example : Derivable (F1 ([] : Sig))
    (Jdg.ty [] (.fst (.pair Tm.tt Tm.tt)) (ph .top)) :=
  phase_and_fst (wfNil_F1 _)
    (phase_and_intro (wfNil_F1 _)
      (phase_top_intro (wfNil_F1 _)) (phase_top_intro (wfNil_F1 _)))

/-- Entailment introduction: `[atoms 0] ⊢ [atom 0 ∨ atom 1]`. -/
example (e : Tm) (he : Derivable (F1 ([] : Sig)) (Jdg.ty [] e (ph (.atom 0)))) :
    Derivable (F1 ([] : Sig))
      (Jdg.ty [] (prf (.or (.atom 0) (.atom 1)))
        (ph (.or (.atom 0) (.atom 1)))) :=
  phase_or_inl he

/-- `○_φ (Unit u0)` is a type in `u0` (the modality preserves the universe). -/
example : Derivable (F1 ([] : Sig))
    (Jdg.ty [] (circ .u0 (.atom 0) (.unit .u0)) (Tm.sort .u0)) :=
  circ_form sigClosed_nil (wfNil_F1 _)
    (unit_form_F1 (wfNil_F1 _)) _

/-- Introduction and elimination at `○`. -/
example :
    Derivable (F1 ([] : Sig))
      (Jdg.ty [] (.app (.lam Tm.tt.shift) Tm.tt) (.unit .u0)) := by
  have hΓ : Derivable (F1 ([] : Sig)) (Jdg.wf ([] : Ctx)) := wfNil_F1 _
  have hA : Derivable (F1 ([] : Sig)) (Jdg.ty [] (.unit .u0) (Tm.sort .u0)) :=
    unit_form_F1 (wfNil_F1 _)
  have htt : Derivable (F1 ([] : Sig)) (Jdg.ty [] Tm.tt (.unit .u0)) :=
    unit_tt_F1 (wfNil_F1 _)
  exact circ_elim (circ_intro sigClosed_nil hΓ hA htt .top) (phase_top_intro hΓ)

/-- **Restriction**: `○_{atom 0 ∨ atom 1}` gives `○_{atom 0}`. -/
example :
    Derivable (F1 ([] : Sig))
      (Jdg.ty []
        (Tm.lam (Tm.app (Tm.lam Tm.tt.shift).shift (prf (.or (.atom 0) (.atom 1)))))
        (circ .u0 (.atom 0) (.unit .u0))) := by
  have hΓ : Derivable (F1 ([] : Sig)) (Jdg.wf ([] : Ctx)) := wfNil_F1 _
  have hA : Derivable (F1 ([] : Sig)) (Jdg.ty [] (.unit .u0) (Tm.sort .u0)) :=
    unit_form_F1 (wfNil_F1 _)
  have htt : Derivable (F1 ([] : Sig)) (Jdg.ty [] Tm.tt (.unit .u0)) :=
    unit_tt_F1 (wfNil_F1 _)
  have hf := circ_intro sigClosed_nil hΓ hA htt (.or (.atom 0) (.atom 1))
  exact circ_restrict sigClosed_nil hΓ hA (Cof.le_or_left (.atom 0) (.atom 1)) hf

/-! ## Decision-procedure checks -/

#eval Cof.le (Cof.and (Cof.atom 0) (Cof.atom 1)) (Cof.atom 0)        -- true
#eval Cof.le (Cof.atom 0) (Cof.or (Cof.atom 0) (Cof.atom 1))          -- true
#eval Cof.le (Cof.atom 0) (Cof.atom 1)                                -- false
#eval Cof.le Cof.bot (Cof.atom 3)                                     -- true
#eval Cof.le Cof.top (Cof.or (Cof.atom 0) (Cof.atom 1))               -- false
#eval Cof.le (Cof.and (Cof.atom 0) (Cof.or (Cof.atom 1) (Cof.atom 2)))
  (Cof.or (Cof.and (Cof.atom 0) (Cof.atom 1)) (Cof.and (Cof.atom 0) (Cof.atom 2))) -- true

/-- Distinct atoms are incomparable, as a checked theorem (not just `#eval`). -/
example : Cof.le (Cof.atom 0) (Cof.atom 1) = false := by
  have h : ¬ (Cof.le (Cof.atom 0) (Cof.atom 1) = true) := by
    intro h
    exact absurd ((Cof.atom_le_atom_iff 0 1).mp h) (by decide)
  simpa using h

/-- `⊥` entails everything. -/
example : Cof.le Cof.bot (Cof.atom 0) = true := Cof.bot_le _

end F1
end STC
