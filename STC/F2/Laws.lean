import STC.F2.Fragment
/-!
# F2: renaming, substitution and weakening for the new term formers

This is the F2 companion of `F1/Phase.lean`'s `F1_rename`/`F1_subst*`. The phase layer's
rules are `Struct`-free and do not move a context entry, so the closure properties compose:

* `phase_renClosedIn` / `phase_subClosedIn`: F1's phase rules, read in any system `R`
  that contains them (F1's own versions are the special case `R = F1 sg`);
* `ext0_renClosed` / `ext0_subClosed`, `glue_renClosed` / `glue_subClosed`,
  `closed_renClosed` / `closed_subClosed`: the three term formers. `Ext` and `Closed` are
  non-binding, so their rules commute with renaming/substitution by `rfl`-level facts;
  `Glue`'s boundary premise (`f z (t z) ≡ a` under `z : [φ]`) is the only one under a
  binder, and it lifts with `Renames.under`/`Substs.under` and the phase formation rule;
* **`F2_rename`, `F2_substs`, `F2_weakening`, `F2_subst`, `F2_subst_eq`, `F2_subst_red`**:
  the laws for `F2 = F1 ∪ Ext0 ∪ Glue ∪ Closed`. They keep F1's shape: the concrete
  substitution companions take `⊢ Γ` explicitly; `F2/Ctx.lean` removes that hypothesis.

Everything is proved for `Sig.Closed` signatures, as in F0/F1.
-/


namespace STC
namespace F2

open F0
open F0.Spec
open scoped F0.Spec

/-! ## Renaming and substitution of the new type-forming expressions

The rule premises are written with `circ`, `tTy`, `fTy`; `Jdg.ren`/`Jdg.sub` push the
operation inside them, so these lemmas put the results back into the same shape. -/

@[simp] theorem circ_ren (s : Srt) (φ : F1.Cof) (A : Tm) (ρ : Nat → Nat) :
    (circ s φ A).ren ρ = circ s φ (A.ren ρ) := by
  simp [circ, STC.F1.circ, STC.F1.ph, Tm.ren, Tm.ren_shift]

@[simp] theorem circ_sub (s : Srt) (φ : F1.Cof) (A : Tm) (σ : Nat → Tm) :
    (circ s φ A).sub σ = circ s φ (A.sub σ) := by
  simp [circ, STC.F1.circ, STC.F1.ph, Tm.sub, Tm.sub_shift]

@[simp] theorem tTy_ren (φ : F1.Cof) (T : Tm) (ρ : Nat → Nat) :
    (tTy φ T).ren ρ = tTy φ (T.ren ρ) := by
  simp [tTy, STC.F1.ph, Tm.ren, Tm.ren_shift, Tm.upRen]

@[simp] theorem tTy_sub (φ : F1.Cof) (T : Tm) (σ : Nat → Tm) :
    (tTy φ T).sub σ = tTy φ (T.sub σ) := by
  simp [tTy, STC.F1.ph, Tm.sub, Tm.sub_shift, Tm.upSub]

@[simp] theorem fTy_ren (s : Srt) (φ : F1.Cof) (A T : Tm) (ρ : Nat → Nat) :
    (fTy s φ A T).ren ρ = fTy s φ (A.ren ρ) (T.ren ρ) := by
  simp [fTy, STC.F1.ph, Tm.ren, Tm.ren_shift, Tm.ren_shift2, Tm.upRen, Tm.ren_shift]

@[simp] theorem fTy_sub (s : Srt) (φ : F1.Cof) (A T : Tm) (σ : Nat → Tm) :
    (fTy s φ A T).sub σ = fTy s φ (A.sub σ) (T.sub σ) := by
  simp [fTy, STC.F1.ph, Tm.sub, Tm.sub_shift, Tm.sub_shift2, Tm.upSub, Tm.sub_shift]

/-- Simplify a closure goal (and the induction hypothesis) down to its component
`Renames`/`Substs` facts. -/
macro "simpPrem" : tactic => `(tactic| (
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq,
    Renames, Substs, Jdg.ren, Jdg.sub, Tm.ren, Tm.sub, ph, prf, STC.F1.ph,
    circ_ren, circ_sub, tTy_ren, tTy_sub, fTy_ren, fTy_sub,
    STC.F1.tm_ren_const, STC.F1.tm_sub_const,
    STC.F1.tm_ren_sort, STC.F1.tm_sub_sort,
    STC.F1.tm_ren_unit, STC.F1.tm_sub_unit,
    STC.F1.tm_ren_empty, STC.F1.tm_sub_empty,
    Tm.ren_shift, Tm.sub_shift] at *))

/-! ## The phase rules, generically -/

theorem phase_renClosedIn {R : Rules} (h : ∀ r, STC.F1.Phase r → R r) :
    RenClosed STC.F1.Phase R := by
  intro r hr ih ρ Δ hρ hΔ
  cases hr with
  | form =>
    rename_i Γ φ
    exact ofRule (h _ (.form (Γ := Δ) (φ := φ))) (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
      exact hΔ)
  | intro hle =>
    rename_i Γ e φ ψ
    exact ofRule (h _ (.intro (Γ := Δ) (e := e.ren ρ) (φ := φ) (ψ := ψ) hle)) (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
      exact ih (.ty Γ e (ph φ)) (by simp) ρ Δ hρ hΔ)
  | botRed =>
    rename_i Γ
    exact ofRule (h _ (.botRed (Γ := Δ))) (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
      exact hΔ)
  | topRed =>
    rename_i Γ
    exact ofRule (h _ (.topRed (Γ := Δ))) (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
      exact hΔ)
  | andRed =>
    rename_i Γ φ ψ
    exact ofRule (h _ (.andRed (Γ := Δ) (φ := φ) (ψ := ψ))) (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
      exact hΔ)

theorem phase_subClosedIn {R : Rules} (h : ∀ r, STC.F1.Phase r → R r) :
    SubClosed STC.F1.Phase R := by
  intro r hr ih σ Δ hσ hΔ
  cases hr with
  | form =>
    rename_i Γ φ
    exact ofRule (h _ (.form (Γ := Δ) (φ := φ))) (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
      exact hΔ)
  | intro hle =>
    rename_i Γ e φ ψ
    exact ofRule (h _ (.intro (Γ := Δ) (e := e.sub σ) (φ := φ) (ψ := ψ) hle)) (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
      exact ih (.ty Γ e (ph φ)) (by simp) σ Δ hσ hΔ)
  | botRed =>
    rename_i Γ
    exact ofRule (h _ (.botRed (Γ := Δ))) (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
      exact hΔ)
  | topRed =>
    rename_i Γ
    exact ofRule (h _ (.topRed (Γ := Δ))) (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
      exact hΔ)
  | andRed =>
    rename_i Γ φ ψ
    exact ofRule (h _ (.andRed (Γ := Δ) (φ := φ) (ψ := ψ))) (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
      exact hΔ)

/-- `[φ]` is a proposition, in any system containing the phase rules. -/
theorem phase_form_R {R : Rules} (h : ∀ r, STC.F1.Phase r → R r) {Γ : Ctx}
    (hΓ : Derivable R (.wf Γ)) (φ : F1.Cof) :
    Derivable R (Γ ⊢ ph φ ∶ .sort .prop) :=
  ofRule (h _ (.form (Γ := Γ) (φ := φ))) (by
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
    exact hΓ)

/-- `Renames` of the binder type `[φ]`, used to lift a premise under `z : [φ]`. -/
theorem phase_form_renames {R : Rules} (h : ∀ r, STC.F1.Phase r → R r) {Γ : Ctx}
    (φ : F1.Cof) : Renames R (.ty Γ (ph φ) (.sort .prop)) := by
  intro ρ Δ hρ hΔ
  simpa [Jdg.ren, ph, STC.F1.ph, Tm.ren] using phase_form_R h hΔ φ

/-- `Substs` of the binder type `[φ]`, used to lift a premise under `z : [φ]`. -/
theorem phase_form_substs {R : Rules} (h : ∀ r, STC.F1.Phase r → R r) {Γ : Ctx}
    (φ : F1.Cof) : Substs R (.ty Γ (ph φ) (.sort .prop)) := by
  intro σ Δ hσ hΔ
  simpa [Jdg.sub, ph, STC.F1.ph, Tm.sub] using phase_form_R h hΔ φ

/-! ## `Ext 0` -/

theorem ext0_renClosed {sg : Sig} (hc : ∀ r, Core r → F2 sg r) :
    RenClosed Ext0 (F2 sg) := by
  intro r hr ih ρ Δ hρ hΔ
  cases hr with
  | form =>
    rename_i Γ A a φ s
    refine ofRule (ext0_in_F2 (.form (Γ := Δ) (A := A.ren ρ) (a := a.ren ρ)
      (φ := φ) (s := s))) ?_
    simpPrem
    exact ⟨ih.1 ρ Δ hρ hΔ, ih.2 ρ Δ hρ hΔ⟩
  | intro =>
    rename_i Γ A a t φ s
    refine ofRule (ext0_in_F2 (.intro (Γ := Δ) (A := A.ren ρ) (a := a.ren ρ)
      (t := t.ren ρ) (φ := φ) (s := s))) ?_
    simpPrem
    refine ⟨ih.1 ρ Δ hρ hΔ, ih.2.1 ρ Δ hρ hΔ, ?_⟩
    have hb := Renames.under hc ih.2.2 rfl (phase_form_renames (fun _ x => phase_in_F2 x) φ) hρ hΔ
    simpa [Jdg.ren, ph, STC.F1.ph, prf, STC.F1.prf, STC.F1.tm_ren_const, Tm.ren, Tm.ren_shift, Tm.upRen] using hb
  | elim =>
    rename_i Γ A a x φ s
    refine ofRule (ext0_in_F2 (.elim (Γ := Δ) (A := A.ren ρ) (a := a.ren ρ)
      (x := x.ren ρ) (φ := φ) (s := s))) ?_
    simpPrem
    exact ⟨ih.1 ρ Δ hρ hΔ, ih.2 ρ Δ hρ hΔ⟩
  | beta =>
    rename_i Γ A a t φ s
    refine ofRule (ext0_in_F2 (.beta (Γ := Δ) (A := A.ren ρ) (a := a.ren ρ)
      (t := t.ren ρ) (φ := φ) (s := s))) ?_
    simpPrem
    exact ⟨ih.1 ρ Δ hρ hΔ, ih.2 ρ Δ hρ hΔ⟩
  | eta =>
    rename_i Γ A a x φ s
    refine ofRule (ext0_in_F2 (.eta (Γ := Δ) (A := A.ren ρ) (a := a.ren ρ)
      (x := x.ren ρ) (φ := φ) (s := s))) ?_
    simpPrem
    exact ⟨ih.1 ρ Δ hρ hΔ, ih.2 ρ Δ hρ hΔ⟩

theorem ext0_subClosed {sg : Sig}
    (hren : ∀ j, Derivable (F2 sg) j → Renames (F2 sg) j)
    (hc : ∀ r, Core r → F2 sg r) : SubClosed Ext0 (F2 sg) := by
  intro r hr ih σ Δ hσ hΔ
  cases hr with
  | form =>
    rename_i Γ A a φ s
    refine ofRule (ext0_in_F2 (.form (Γ := Δ) (A := A.sub σ) (a := a.sub σ)
      (φ := φ) (s := s))) ?_
    simpPrem
    exact ⟨ih.1 σ Δ hσ hΔ, ih.2 σ Δ hσ hΔ⟩
  | intro =>
    rename_i Γ A a t φ s
    refine ofRule (ext0_in_F2 (.intro (Γ := Δ) (A := A.sub σ) (a := a.sub σ)
      (t := t.sub σ) (φ := φ) (s := s))) ?_
    simpPrem
    refine ⟨ih.1 σ Δ hσ hΔ, ih.2.1 σ Δ hσ hΔ, ?_⟩
    have hb := Substs.under hren hc ih.2.2 rfl (phase_form_substs (fun _ x => phase_in_F2 x) φ) hσ hΔ
    simpa [Jdg.sub, ph, STC.F1.ph, prf, STC.F1.prf, STC.F1.tm_sub_const, Tm.sub, Tm.sub_shift, Tm.upSub] using hb
  | elim =>
    rename_i Γ A a x φ s
    refine ofRule (ext0_in_F2 (.elim (Γ := Δ) (A := A.sub σ) (a := a.sub σ)
      (x := x.sub σ) (φ := φ) (s := s))) ?_
    simpPrem
    exact ⟨ih.1 σ Δ hσ hΔ, ih.2 σ Δ hσ hΔ⟩
  | beta =>
    rename_i Γ A a t φ s
    refine ofRule (ext0_in_F2 (.beta (Γ := Δ) (A := A.sub σ) (a := a.sub σ)
      (t := t.sub σ) (φ := φ) (s := s))) ?_
    simpPrem
    exact ⟨ih.1 σ Δ hσ hΔ, ih.2 σ Δ hσ hΔ⟩
  | eta =>
    rename_i Γ A a x φ s
    refine ofRule (ext0_in_F2 (.eta (Γ := Δ) (A := A.sub σ) (a := a.sub σ)
      (x := x.sub σ) (φ := φ) (s := s))) ?_
    simpPrem
    exact ⟨ih.1 σ Δ hσ hΔ, ih.2 σ Δ hσ hΔ⟩

/-! ## strict `Glue` -/

theorem glue_renClosed {sg : Sig} (hc : ∀ r, Core r → F2 sg r) :
    RenClosed Glue (F2 sg) := by
  intro r hr ih ρ Δ hρ hΔ
  cases hr with
  | form hs =>
    rename_i Γ A T f φ s s'
    refine ofRule (glue_in_F2 (.form (Γ := Δ) (A := A.ren ρ) (T := T.ren ρ)
      (f := f.ren ρ) (φ := φ) (s := s) (s' := s') hs)) ?_
    simpPrem
    exact ⟨ih.1 ρ Δ hρ hΔ, ih.2.1 ρ Δ hρ hΔ, ih.2.2 ρ Δ hρ hΔ⟩
  | intro hs =>
    rename_i Γ A T f t a φ s s'
    refine ofRule (glue_in_F2 (.intro (Γ := Δ) (A := A.ren ρ) (T := T.ren ρ)
      (f := f.ren ρ) (t := t.ren ρ) (a := a.ren ρ) (φ := φ) (s := s) (s' := s') hs)) ?_
    simpPrem
    refine ⟨ih.1 ρ Δ hρ hΔ, ih.2.1 ρ Δ hρ hΔ, ih.2.2.1 ρ Δ hρ hΔ, ?_⟩
    have hb := Renames.under hc ih.2.2.2 rfl (phase_form_renames (fun _ x => phase_in_F2 x) φ) hρ hΔ
    simpa [Jdg.ren, ph, STC.F1.ph, prf, STC.F1.prf, STC.F1.tm_ren_const, Tm.ren, Tm.ren_shift, Tm.upRen] using hb
  | elim hs =>
    rename_i Γ A T f x φ s s'
    refine ofRule (glue_in_F2 (.elim (Γ := Δ) (A := A.ren ρ) (T := T.ren ρ)
      (f := f.ren ρ) (x := x.ren ρ) (φ := φ) (s := s) (s' := s') hs)) ?_
    simpPrem
    exact ⟨ih.1 ρ Δ hρ hΔ, ih.2.1 ρ Δ hρ hΔ, ih.2.2.1 ρ Δ hρ hΔ,
      ih.2.2.2 ρ Δ hρ hΔ⟩
  | beta hs =>
    rename_i Γ A T f t a φ s s'
    refine ofRule (glue_in_F2 (.beta (Γ := Δ) (A := A.ren ρ) (T := T.ren ρ)
      (f := f.ren ρ) (t := t.ren ρ) (a := a.ren ρ) (φ := φ) (s := s) (s' := s') hs)) ?_
    simpPrem
    refine ⟨ih.1 ρ Δ hρ hΔ, ih.2.1 ρ Δ hρ hΔ, ih.2.2.1 ρ Δ hρ hΔ,
      ih.2.2.2.1 ρ Δ hρ hΔ, ih.2.2.2.2.1 ρ Δ hρ hΔ, ?_⟩
    have hb := Renames.under hc ih.2.2.2.2.2 rfl (phase_form_renames (fun _ x => phase_in_F2 x) φ) hρ hΔ
    simpa [Jdg.ren, ph, STC.F1.ph, prf, STC.F1.prf, STC.F1.tm_ren_const, Tm.ren, Tm.ren_shift, Tm.upRen] using hb



theorem glue_subClosed {sg : Sig}
    (hren : ∀ j, Derivable (F2 sg) j → Renames (F2 sg) j)
    (hc : ∀ r, Core r → F2 sg r) : SubClosed Glue (F2 sg) := by
  intro r hr ih σ Δ hσ hΔ
  cases hr with
  | form hs =>
    rename_i Γ A T f φ s s'
    refine ofRule (glue_in_F2 (.form (Γ := Δ) (A := A.sub σ) (T := T.sub σ)
      (f := f.sub σ) (φ := φ) (s := s) (s' := s') hs)) ?_
    simpPrem
    exact ⟨ih.1 σ Δ hσ hΔ, ih.2.1 σ Δ hσ hΔ, ih.2.2 σ Δ hσ hΔ⟩
  | intro hs =>
    rename_i Γ A T f t a φ s s'
    refine ofRule (glue_in_F2 (.intro (Γ := Δ) (A := A.sub σ) (T := T.sub σ)
      (f := f.sub σ) (t := t.sub σ) (a := a.sub σ) (φ := φ) (s := s) (s' := s') hs)) ?_
    simpPrem
    refine ⟨ih.1 σ Δ hσ hΔ, ih.2.1 σ Δ hσ hΔ, ih.2.2.1 σ Δ hσ hΔ, ?_⟩
    have hb := Substs.under hren hc ih.2.2.2 rfl (phase_form_substs (fun _ x => phase_in_F2 x) φ) hσ hΔ
    simpa [Jdg.sub, ph, STC.F1.ph, prf, STC.F1.prf, STC.F1.tm_sub_const, Tm.sub, Tm.sub_shift, Tm.upSub] using hb
  | elim hs =>
    rename_i Γ A T f x φ s s'
    refine ofRule (glue_in_F2 (.elim (Γ := Δ) (A := A.sub σ) (T := T.sub σ)
      (f := f.sub σ) (x := x.sub σ) (φ := φ) (s := s) (s' := s') hs)) ?_
    simpPrem
    exact ⟨ih.1 σ Δ hσ hΔ, ih.2.1 σ Δ hσ hΔ, ih.2.2.1 σ Δ hσ hΔ,
      ih.2.2.2 σ Δ hσ hΔ⟩
  | beta hs =>
    rename_i Γ A T f t a φ s s'
    refine ofRule (glue_in_F2 (.beta (Γ := Δ) (A := A.sub σ) (T := T.sub σ)
      (f := f.sub σ) (t := t.sub σ) (a := a.sub σ) (φ := φ) (s := s) (s' := s') hs)) ?_
    simpPrem
    refine ⟨ih.1 σ Δ hσ hΔ, ih.2.1 σ Δ hσ hΔ, ih.2.2.1 σ Δ hσ hΔ,
      ih.2.2.2.1 σ Δ hσ hΔ, ih.2.2.2.2.1 σ Δ hσ hΔ, ?_⟩
    have hb := Substs.under hren hc ih.2.2.2.2.2 rfl (phase_form_substs (fun _ x => phase_in_F2 x) φ) hσ hΔ
    simpa [Jdg.sub, ph, STC.F1.ph, prf, STC.F1.prf, STC.F1.tm_sub_const, Tm.sub, Tm.sub_shift, Tm.upSub] using hb


/-! ## the closed modality `●` -/

theorem closed_renClosed {sg : Sig} (_hc : ∀ r, Core r → F2 sg r) :
    RenClosed Closed (F2 sg) := by
  intro r hr ih ρ Δ hρ hΔ
  cases hr with
  | form =>
    rename_i Γ A φ s
    refine ofRule (closed_in_F2 (.form (Γ := Δ) (A := A.ren ρ) (φ := φ) (s := s))) ?_
    simpPrem
    exact ih ρ Δ hρ hΔ
  | intro =>
    rename_i Γ A a φ s
    refine ofRule (closed_in_F2 (.intro (Γ := Δ) (A := A.ren ρ) (a := a.ren ρ)
      (φ := φ) (s := s))) ?_
    simpPrem
    exact ⟨ih.1 ρ Δ hρ hΔ, ih.2 ρ Δ hρ hΔ⟩
  | star =>
    rename_i Γ A φ s
    refine ofRule (closed_in_F2 (.star (Γ := Δ) (A := A.ren ρ) (φ := φ) (s := s))) ?_
    simpPrem
    exact ⟨ih.1 ρ Δ hρ hΔ, ih.2 ρ Δ hρ hΔ⟩
  | elim =>
    rename_i Γ A B mEta mStar x φ sA sB
    refine ofRule (closed_in_F2 (.elim (Γ := Δ) (A := A.ren ρ) (B := B.ren ρ)
      (mEta := mEta.ren ρ) (mStar := mStar.ren ρ) (x := x.ren ρ)
      (φ := φ) (sA := sA) (sB := sB))) ?_
    simpPrem
    exact ⟨ih.1 ρ Δ hρ hΔ, ih.2.1 ρ Δ hρ hΔ, ih.2.2.1 ρ Δ hρ hΔ,
      ih.2.2.2.1 ρ Δ hρ hΔ, ih.2.2.2.2 ρ Δ hρ hΔ⟩
  | betaIn =>
    rename_i Γ A B mEta mStar a φ sA sB
    refine ofRule (closed_in_F2 (.betaIn (Γ := Δ) (A := A.ren ρ) (B := B.ren ρ)
      (mEta := mEta.ren ρ) (mStar := mStar.ren ρ) (a := a.ren ρ)
      (φ := φ) (sA := sA) (sB := sB))) ?_
    simpPrem
    exact ⟨ih.1 ρ Δ hρ hΔ, ih.2.1 ρ Δ hρ hΔ, ih.2.2.1 ρ Δ hρ hΔ,
      ih.2.2.2 ρ Δ hρ hΔ⟩
  | betaStar =>
    rename_i Γ A B mEta mStar φ sA sB
    refine ofRule (closed_in_F2 (.betaStar (Γ := Δ) (A := A.ren ρ) (B := B.ren ρ)
      (mEta := mEta.ren ρ) (mStar := mStar.ren ρ) (φ := φ) (sA := sA) (sB := sB))) ?_
    simpPrem
    exact ⟨ih.1 ρ Δ hρ hΔ, ih.2.1 ρ Δ hρ hΔ, ih.2.2.1 ρ Δ hρ hΔ,
      ih.2.2.2 ρ Δ hρ hΔ⟩


theorem closed_subClosed {sg : Sig}
    (_hren : ∀ j, Derivable (F2 sg) j → Renames (F2 sg) j)
    (_hc : ∀ r, Core r → F2 sg r) : SubClosed Closed (F2 sg) := by
  intro r hr ih σ Δ hσ hΔ
  cases hr with
  | form =>
    rename_i Γ A φ s
    refine ofRule (closed_in_F2 (.form (Γ := Δ) (A := A.sub σ) (φ := φ) (s := s))) ?_
    simpPrem
    exact ih σ Δ hσ hΔ
  | intro =>
    rename_i Γ A a φ s
    refine ofRule (closed_in_F2 (.intro (Γ := Δ) (A := A.sub σ) (a := a.sub σ)
      (φ := φ) (s := s))) ?_
    simpPrem
    exact ⟨ih.1 σ Δ hσ hΔ, ih.2 σ Δ hσ hΔ⟩
  | star =>
    rename_i Γ A φ s
    refine ofRule (closed_in_F2 (.star (Γ := Δ) (A := A.sub σ) (φ := φ) (s := s))) ?_
    simpPrem
    exact ⟨ih.1 σ Δ hσ hΔ, ih.2 σ Δ hσ hΔ⟩
  | elim =>
    rename_i Γ A B mEta mStar x φ sA sB
    refine ofRule (closed_in_F2 (.elim (Γ := Δ) (A := A.sub σ) (B := B.sub σ)
      (mEta := mEta.sub σ) (mStar := mStar.sub σ) (x := x.sub σ)
      (φ := φ) (sA := sA) (sB := sB))) ?_
    simpPrem
    exact ⟨ih.1 σ Δ hσ hΔ, ih.2.1 σ Δ hσ hΔ, ih.2.2.1 σ Δ hσ hΔ,
      ih.2.2.2.1 σ Δ hσ hΔ, ih.2.2.2.2 σ Δ hσ hΔ⟩
  | betaIn =>
    rename_i Γ A B mEta mStar a φ sA sB
    refine ofRule (closed_in_F2 (.betaIn (Γ := Δ) (A := A.sub σ) (B := B.sub σ)
      (mEta := mEta.sub σ) (mStar := mStar.sub σ) (a := a.sub σ)
      (φ := φ) (sA := sA) (sB := sB))) ?_
    simpPrem
    exact ⟨ih.1 σ Δ hσ hΔ, ih.2.1 σ Δ hσ hΔ, ih.2.2.1 σ Δ hσ hΔ,
      ih.2.2.2 σ Δ hσ hΔ⟩
  | betaStar =>
    rename_i Γ A B mEta mStar φ sA sB
    refine ofRule (closed_in_F2 (.betaStar (Γ := Δ) (A := A.sub σ) (B := B.sub σ)
      (mEta := mEta.sub σ) (mStar := mStar.sub σ) (φ := φ) (sA := sA) (sB := sB))) ?_
    simpPrem
    exact ⟨ih.1 σ Δ hσ hΔ, ih.2.1 σ Δ hσ hΔ, ih.2.2.1 σ Δ hσ hΔ,
      ih.2.2.2 σ Δ hσ hΔ⟩

/-! ## The laws for `F2` -/

/-- **The renaming lemma for F2**. -/
theorem F2_rename {sg : Sig} (hsg : Sig.Closed sg) {j : Jdg}
    (d : Derivable (F2 sg) j) : Renames (F2 sg) j :=
  rename_of_closed
    (RenClosed.union
      (RenClosed.union
        (RenClosed.union
          (RenClosed.union
            (F0Rules_renClosedIn (sg := sg) (var := .levelled) (R := F2 sg) hsg
              (fun _ x => f1_in_F2 (Or.inl x)) (fun _ x => core_in_F2 x))
            (phase_renClosedIn (fun _ x => f1_in_F2 (Or.inr x))))
          (ext0_renClosed (fun _ x => core_in_F2 x)))
        (glue_renClosed (fun _ x => core_in_F2 x)))
      (closed_renClosed (fun _ x => core_in_F2 x))) d

/-- **The substitution lemma for F2**. -/
theorem F2_substs {sg : Sig} (hsg : Sig.Closed sg) {j : Jdg}
    (d : Derivable (F2 sg) j) : Substs (F2 sg) j :=
  subst_of_closed
    (SubClosed.union
      (SubClosed.union
        (SubClosed.union
          (SubClosed.union
            (F0Rules_subClosedIn (sg := sg) (var := .levelled) (R := F2 sg) hsg
              (fun _ d => F2_rename hsg d) (fun _ x => f1_in_F2 (Or.inl x))
              (fun _ x => core_in_F2 x))
            (phase_subClosedIn (fun _ x => f1_in_F2 (Or.inr x))))
          (ext0_subClosed (fun _ d => F2_rename hsg d) (fun _ x => core_in_F2 x)))
        (glue_subClosed (fun _ d => F2_rename hsg d) (fun _ x => core_in_F2 x)))
      (closed_subClosed (fun _ d => F2_rename hsg d) (fun _ x => core_in_F2 x))) d

/-- Weakening for F2. -/
theorem F2_weakening {sg : Sig} (hsg : Sig.Closed sg) {Γ : Ctx} {t A B : Tm} {s : Srt}
    (hΓ : Derivable (F2 sg) (.wf Γ))
    (ht : Derivable (F2 sg) (Γ ⊢ t ∶ A))
    (hB : Derivable (F2 sg) (Γ ⊢ B ∶ .sort s)) :
    Derivable (F2 sg) ((B :: Γ) ⊢ t.shift ∶ A.shift) :=
  F2_rename hsg ht Nat.succ (B :: Γ) (RenOK.succ Γ B)
    (ofRule (core_in_F2 (Core.wfCons (s := s))) (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨hΓ, hB⟩))

/-- F2's typing companion at `[a/0]` (the `⊢ Γ` hypothesis is removed in `F2/Ctx.lean`). -/
theorem F2_subst {sg : Sig} (hsg : Sig.Closed sg) {Γ : Ctx} {A t B a : Tm}
    (hΓ : Derivable (F2 sg) (.wf Γ))
    (ht : Derivable (F2 sg) ((A :: Γ) ⊢ t ∶ B))
    (ha : Derivable (F2 sg) (Γ ⊢ a ∶ A)) :
    Derivable (F2 sg) (Γ ⊢ t.inst a ∶ B.inst a) := by
  have hsub : SubOK (F2 sg) (Tm.one a) (A :: Γ) Γ := by
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
        exact ofRule (core_in_F2 (Core.var hΓi)) (by
          simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
          exact hΓ)
  have := F2_substs hsg ht (Tm.one a) Γ hsub hΓ
  simpa [Jdg.sub, Tm.inst] using this

/-- F2's conversion companion at `[a/0]`. -/
theorem F2_subst_eq {sg : Sig} (hsg : Sig.Closed sg) {Γ : Ctx} {A t u B a : Tm}
    (hΓ : Derivable (F2 sg) (.wf Γ))
    (ht : Derivable (F2 sg) ((A :: Γ) ⊢ t ≡ u ∶ B))
    (ha : Derivable (F2 sg) (Γ ⊢ a ∶ A)) :
    Derivable (F2 sg) (Γ ⊢ t.inst a ≡ u.inst a ∶ B.inst a) := by
  have hsub : SubOK (F2 sg) (Tm.one a) (A :: Γ) Γ := by
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
        exact ofRule (core_in_F2 (Core.var hΓi)) (by
          simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
          exact hΓ)
  have := F2_substs hsg ht (Tm.one a) Γ hsub hΓ
  simpa [Jdg.sub, Tm.inst] using this

/-- F2's reduction companion at `[a/0]`. -/
theorem F2_subst_red {sg : Sig} (hsg : Sig.Closed sg) {Γ : Ctx} {A t u B a : Tm}
    (hΓ : Derivable (F2 sg) (.wf Γ))
    (ht : Derivable (F2 sg) ((A :: Γ) ⊢ t ⟶ u ∶ B))
    (ha : Derivable (F2 sg) (Γ ⊢ a ∶ A)) :
    Derivable (F2 sg) (Γ ⊢ t.inst a ⟶ u.inst a ∶ B.inst a) := by
  have hsub : SubOK (F2 sg) (Tm.one a) (A :: Γ) Γ := by
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
        exact ofRule (core_in_F2 (Core.var hΓi)) (by
          simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
          exact hΓ)
  have := F2_substs hsg ht (Tm.one a) Γ hsub hΓ
  simpa [Jdg.sub, Tm.inst] using this

end F2
end STC
