import STC.F0.Obligations
/-!
# Sanity derivations

Small derivations that witness that the F0 rules are inhabited: the sorts, `Unit`/`tt`, a
`λ` (so the binder and the context lookup), `letUnit`, `refl`, an enumeration tag. They
also pin down the rule indices (the sort arguments of `Π`, `Σ`, `Eq`), so a later change
that shifts an index breaks here first. This is M0c's first instalment (§6); the full
corpus and the translation filter are the next commit.
-/


namespace STC
namespace F0
namespace Spec

theorem wf_nil {sg : Sig} : Derivable (F0 sg) (.wf ([] : Ctx)) :=
  ofRule (core_in_F0 Core.wfNil) (by simp)

theorem wf_cons {sg : Sig} {Γ : Ctx} {A : Tm} {s : Srt}
    (hΓ : Derivable (F0 sg) (.wf Γ)) (hA : Derivable (F0 sg) (Γ ⊢ A ∶ .sort s)) :
    Derivable (F0 sg) (.wf (A :: Γ)) :=
  ofRule (core_in_F0 (Core.wfCons (s := s))) (by
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hΓ, hA⟩)

theorem unit_form {sg : Sig} {Γ : Ctx} {s : Srt} (hΓ : Derivable (F0 sg) (.wf Γ)) :
    Derivable (F0 sg) (Γ ⊢ .unit s ∶ .sort s) :=
  ofRule (unit_in_F0 (Unit.form (s := s))) (by
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
    exact hΓ)

/-- `Sort prop ∶ Sort u0` (`Prop : U₀`). -/
theorem sort_prop {sg : Sig} :
    Derivable (F0 sg) (([] : Ctx) ⊢ .sort .prop ∶ .sort .u0) :=
  ofRule (core_in_F0 (Core.sort (s := .prop) (s' := .u0) rfl)) (by
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
    exact wf_nil)

/-- `tt ∶ Unit prop`. -/
theorem tt_prop {sg : Sig} :
    Derivable (F0 sg) (([] : Ctx) ⊢ .tt ∶ .unit .prop) :=
  ofRule (unit_in_F0 (Unit.tt (s := .prop))) (by
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
    exact wf_nil)

/-- `let () := tt; tt ∶ Unit prop`: the `letUnit` former. -/
theorem letUnit_prop {sg : Sig} :
    Derivable (F0 sg) (([] : Ctx) ⊢ .letUnit .tt .tt ∶ .unit .prop) :=
  ofRule (let_in_F0 (Let.letUnit (s := .prop))) (by
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨tt_prop, tt_prop⟩)

/-- `refl tt ∶ tt =_(Unit prop) tt`. -/
theorem refl_prop {sg : Sig} :
    Derivable (F0 sg)
      (([] : Ctx) ⊢ .refl (.unit .prop) .tt ∶ .eq (.unit .prop) .tt .tt) :=
  ofRule (eq_in_F0 (Eq.refl (s := .prop))) (by
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨unit_form wf_nil, tt_prop⟩)

/-- `tag 2 0 ∶ Enum 2`. -/
theorem tag_two_zero {sg : Sig} :
    Derivable (F0 sg) (([] : Ctx) ⊢ .tag 2 0 ∶ .enum 2) :=
  ofRule (enum_in_F0 (Enum.tag (n := 2) (i := 0) (by decide))) (by
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
    exact wf_nil)

/-- `λ x. x ∶ (x : Unit prop) → Unit prop`: a binder, a context lookup and `Pi.lam`. -/
theorem lam_id_unit {sg : Sig} :
    Derivable (F0 sg)
      (([] : Ctx) ⊢ .lam (.var 0) ∶ .pi .prop (.unit .prop) (.unit .prop)) := by
  have hctx : Derivable (F0 sg) (.wf ([.unit .prop] : Ctx)) := wf_cons wf_nil (unit_form wf_nil)
  have hpi : Derivable (F0 sg)
      (([] : Ctx) ⊢ .pi .prop (.unit .prop) (.unit .prop) ∶ .sort .prop) :=
    ofRule (pi_in_F0 (Pi.form (i := .prop) (j := .prop) (s := .prop) rfl)) (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨unit_form wf_nil, unit_form hctx⟩)
  have hvar : Derivable (F0 sg) (([.unit .prop] : Ctx) ⊢ .var 0 ∶ .unit .prop) :=
    ofRule (core_in_F0 (Core.var (Γ := [.unit .prop]) (A := .unit .prop) (i := 0) rfl)) (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
      exact hctx)
  exact ofRule (pi_in_F0 (Pi.lam (s := .prop) (i := .prop))) (by
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hpi, unit_form wf_nil, hvar⟩)

end Spec
end F0
end STC
