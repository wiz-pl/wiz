import STC.F0.Laws
/-!
# The renaming lemma for F0

The lemma is stated for any renaming between contexts that respects the variables' types
(`RenOK`), not only weakening at the head: a rule with a premise under a binder needs the
lemma at `upRen ρ`, so "weakening by one variable at the head" is not an inductive
statement.

It is proved for a rule set `S` as a closure property `RenClosed S R`: every rule of `S`,
renamed, is derivable in `R` from the renamed premises. Then `Derivable R` is closed under
renaming when each of the sets `R` is made of is (`rename_of_closed`). This is the same
architecture as `WizMeta/Spec/Weakening.lean`, for `F0Rules` (both `EqTy` variants; the
concrete `F0Base_*` theorems instantiate the levelled one).

What the proof needs from the rules: a rule with a premise under a binder has the
binder's type among its premises (`Pi.lam`, `Pi.beta`, `Pi.eta`, `Pi.cong`,
`Sigma.cong`, `EqTyLevelled.pi/sigma`, `ULift` has no binder), and the signature is
closed (`Sig.Closed`; otherwise `Γ ⊢ c ∶ var 5` is derivable and its weakening is not).
-/


namespace STC
namespace F0
namespace Spec

/-- The renaming lemma at one judgment, for a system `R`. -/
def Renames (R : Rules) (j : Jdg) : Prop :=
  ∀ ρ Δ, RenOK ρ (Jdg.ctx j) Δ → Derivable R (.wf Δ) → Derivable R (Jdg.ren ρ Δ j)

/-- Every rule of `S`, renamed, is derivable in `R` from its renamed premises. -/
def RenClosed (S R : Rules) : Prop :=
  ∀ r, S r → (∀ p, p ∈ r.prems → Renames R p) → Renames R r.concl

theorem rename_of_closed {R : Rules} (h : RenClosed R R) {j : Jdg} (d : Derivable R j) : Renames R j := by
  induction d with
  | intro r hr _ ih => exact h r hr ih

theorem RenClosed.union {S S' R : Rules} (h : RenClosed S R) (h' : RenClosed S' R) :
    RenClosed (S ∪ S') R :=
  fun r hr ih => hr.elim (fun hs => h r hs ih) (fun hs => h' r hs ih)

theorem ofRule {R : Rules} {ps : List Jdg} {c : Jdg} (h : R ⟨ps, c⟩)
    (hp : ∀ p, p ∈ ps → Derivable R p) : Derivable R c := .intro ⟨ps, c⟩ h hp

/-- Extending both contexts by a type of the source context. -/
theorem Renames.wfCons {R : Rules} (hc : ∀ r, Core r → R r) {Γ Δ : Ctx} {A : Tm} {s : Srt}
    {ρ : Nat → Nat} (hA : Renames R (Γ ⊢ A ∶ .sort s)) (hρ : RenOK ρ Γ Δ)
    (hΔ : Derivable R (.wf Δ)) : Derivable R (.wf (A.ren ρ :: Δ)) :=
  ofRule (hc _ (.wfCons (s := s))) (by
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hΔ, hA ρ Δ hρ hΔ⟩)

/-- Close the premise goal `∀ p ∈ ps, Derivable R p` from the renamed premises `I` (same
context) and the well-formed target context `hΔ`. -/
macro "fromIH " ih:ident ρ:ident Δ:ident hρ:ident hΔ:ident : tactic => `(tactic| (
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at $ih:ident ⊢
  repeat' apply And.intro
  all_goals try first | exact $hΔ | exact $ih $ρ $Δ $hρ $hΔ | exact $ih.1 $ρ $Δ $hρ $hΔ | exact $ih.2.1 $ρ $Δ $hρ $hΔ | exact $ih.2.2.1 $ρ $Δ $hρ $hΔ | exact $ih.2.2.2.1 $ρ $Δ $hρ $hΔ | exact $ih.2.2.2.2.1 $ρ $Δ $hρ $hΔ | exact $ih.2.2.2.2.2.1 $ρ $Δ $hρ $hΔ | exact $ih.2.2.2.2.2.2.1 $ρ $Δ $hρ $hΔ | exact $ih.2.2.2.2.2.2.2.1 $ρ $Δ $hρ $hΔ | exact $ih.2.2.2.2.2.2.2.2.1 $ρ $Δ $hρ $hΔ | exact $ih.2.2.2.2.2.2.2.2.2.1 $ρ $Δ $hρ $hΔ | exact $ih.2 $ρ $Δ $hρ $hΔ | exact $ih.2.2 $ρ $Δ $hρ $hΔ | exact $ih.2.2.2 $ρ $Δ $hρ $hΔ | exact $ih.2.2.2.2 $ρ $Δ $hρ $hΔ | exact $ih.2.2.2.2.2 $ρ $Δ $hρ $hΔ | exact $ih.2.2.2.2.2.2 $ρ $Δ $hρ $hΔ | exact $ih.2.2.2.2.2.2.2 $ρ $Δ $hρ $hΔ | exact $ih.2.2.2.2.2.2.2.2 $ρ $Δ $hρ $hΔ | exact $ih.2.2.2.2.2.2.2.2.2 $ρ $Δ $hρ $hΔ))

theorem core_renClosed {R : Rules} (hc : ∀ r, Core r → R r) : RenClosed Core R := by
  intro r hr ih ρ Δ hρ hΔ
  cases hr with
  | wfNil => exact hΔ
  | wfCons => exact hΔ
  | var h => exact ofRule (hc _ (.var (hρ _ _ h))) (by fromIH ih ρ Δ hρ hΔ)
  | sort h => exact ofRule (hc _ (.sort h)) (by fromIH ih ρ Δ hρ hΔ)
  | conv => exact ofRule (hc _ .conv) (by fromIH ih ρ Δ hρ hΔ)
  | eqConv => exact ofRule (hc _ .eqConv) (by fromIH ih ρ Δ hρ hΔ)
  | redConv => exact ofRule (hc _ .redConv) (by fromIH ih ρ Δ hρ hΔ)
  | refl => exact ofRule (hc _ .refl) (by fromIH ih ρ Δ hρ hΔ)
  | symm => exact ofRule (hc _ .symm) (by fromIH ih ρ Δ hρ hΔ)
  | trans => exact ofRule (hc _ .trans) (by fromIH ih ρ Δ hρ hΔ)
  | redEq => exact ofRule (hc _ .redEq) (by fromIH ih ρ Δ hρ hΔ)
  | irrel h => exact ofRule (hc _ (.irrel h)) (by fromIH ih ρ Δ hρ hΔ)
  | eqProp h =>
    simp only [Jdg.ren, Tm.ren, Tm.ren_iff]
    exact ofRule (hc _ (.eqProp h)) (by fromIH ih ρ Δ hρ hΔ)
  | eqType h => exact ofRule (hc _ (.eqType h)) (by fromIH ih ρ Δ hρ hΔ)
  | eqTySort h => exact ofRule (hc _ (.eqTySort h)) (by fromIH ih ρ Δ hρ hΔ)
  | eqTySortApart h => exact ofRule (hc _ (.eqTySortApart h)) (by fromIH ih ρ Δ hρ hΔ)
  | castSort h => exact ofRule (hc _ (.castSort h)) (by fromIH ih ρ Δ hρ hΔ)

/-- A premise under one binder, whose binder type is typed by another premise. -/
theorem Renames.under {R : Rules} (hc : ∀ r, Core r → R r) {Γ Δ : Ctx} {A : Tm} {s : Srt}
    {ρ : Nat → Nat} {j : Jdg} (hj : Renames R j) (hctx : Jdg.ctx j = A :: Γ)
    (hA : Renames R (Γ ⊢ A ∶ .sort s)) (hρ : RenOK ρ Γ Δ) (hΔ : Derivable R (.wf Δ)) :
    Derivable R (Jdg.ren (Tm.upRen ρ) (A.ren ρ :: Δ) j) :=
  hj _ _ (hctx ▸ hρ.up A) (Renames.wfCons hc hA hρ hΔ)

theorem pi_renClosed {R : Rules} (hc : ∀ r, Core r → R r) (hp : ∀ r, Pi r → R r) : RenClosed Pi R := by
  intro r hr ih ρ Δ hρ hΔ
  cases hr with
  | form h =>
    exact ofRule (hp _ (.form h)) (by
      fromIH ih ρ Δ hρ hΔ
      exact Renames.under hc ih.2 rfl ih.1 hρ hΔ)
  | lam =>
    exact ofRule (hp _ .lam) (by
      fromIH ih ρ Δ hρ hΔ
      exact Renames.under hc ih.2.2 rfl ih.2.1 hρ hΔ)
  | app =>
    simp only [Jdg.ren, Tm.ren, Tm.ren_inst]
    exact ofRule (hp _ .app) (by fromIH ih ρ Δ hρ hΔ)
  | beta =>
    simp only [Jdg.ren, Tm.ren, Tm.ren_inst]
    exact ofRule (hp _ .beta) (by
      fromIH ih ρ Δ hρ hΔ
      exact Renames.under hc ih.2.2.1 rfl ih.2.1 hρ hΔ)
  | appRed =>
    simp only [Jdg.ren, Tm.ren, Tm.ren_inst]
    exact ofRule (hp _ .appRed) (by fromIH ih ρ Δ hρ hΔ)
  | eta =>
    exact ofRule (hp _ .eta) (by
      fromIH ih ρ Δ hρ hΔ
      have h := Renames.under hc ih.2.2.2 rfl ih.2.2.1 hρ hΔ
      simp only [Jdg.ren, Tm.ren, Tm.ren_shift] at h
      exact h)
  | cong h h' =>
    exact ofRule (hp _ (.cong h h')) (by
      fromIH ih ρ Δ hρ hΔ
      exact Renames.under hc ih.2.2 rfl ih.1 hρ hΔ)
  | appCong =>
    simp only [Jdg.ren, Tm.ren, Tm.ren_inst]
    exact ofRule (hp _ .appCong) (by fromIH ih ρ Δ hρ hΔ)
  | eq h =>
    simp only [Jdg.ren, Tm.ren, Tm.ren_eqPi]
    exact ofRule (hp _ (.eq h)) (by fromIH ih ρ Δ hρ hΔ)
  | eqTyApart h1 h2 => exact ofRule (hp _ (.eqTyApart h1 h2)) (by fromIH ih ρ Δ hρ hΔ)
  | cast h1 h2 =>
    simp only [Jdg.ren, Tm.ren, Tm.ren_castPi]
    exact ofRule (hp _ (.cast h1 h2)) (by
      fromIH ih ρ Δ hρ hΔ
      · exact Renames.under hc ih.2.2.2.2.1 rfl ih.2.2.1 hρ hΔ
      · exact Renames.under hc ih.2.2.2.2.2.1 rfl ih.2.2.2.1 hρ hΔ)

theorem sigma_renClosed {R : Rules} (hc : ∀ r, Core r → R r) (hs : ∀ r, Sigma r → R r) :
    RenClosed Sigma R := by
  intro r hr ih ρ Δ hρ hΔ
  cases hr with
  | form h =>
    exact ofRule (hs _ (.form h)) (by
      fromIH ih ρ Δ hρ hΔ
      exact Renames.under hc ih.2 rfl ih.1 hρ hΔ)
  | pair =>
    exact ofRule (hs _ .pair) (by
      fromIH ih ρ Δ hρ hΔ
      have h := ih.2.2 ρ Δ hρ hΔ
      simp only [Jdg.ren, Tm.ren_inst] at h
      exact h)
  | fst => exact ofRule (hs _ .fst) (by fromIH ih ρ Δ hρ hΔ)
  | snd =>
    simp only [Jdg.ren, Tm.ren, Tm.ren_inst]
    exact ofRule (hs _ .snd) (by fromIH ih ρ Δ hρ hΔ)
  | fstBeta =>
    exact ofRule (hs _ .fstBeta) (by
      fromIH ih ρ Δ hρ hΔ
      have h := ih.2.2 ρ Δ hρ hΔ
      simp only [Jdg.ren, Tm.ren_inst] at h
      exact h)
  | sndBeta =>
    simp only [Jdg.ren, Tm.ren, Tm.ren_inst]
    exact ofRule (hs _ .sndBeta) (by
      fromIH ih ρ Δ hρ hΔ
      have h := ih.2.2 ρ Δ hρ hΔ
      simp only [Jdg.ren, Tm.ren_inst] at h
      exact h)
  | fstRed => exact ofRule (hs _ .fstRed) (by fromIH ih ρ Δ hρ hΔ)
  | sndRed =>
    simp only [Jdg.ren, Tm.ren, Tm.ren_inst]
    exact ofRule (hs _ .sndRed) (by fromIH ih ρ Δ hρ hΔ)
  | eta =>
    exact ofRule (hs _ .eta) (by
      fromIH ih ρ Δ hρ hΔ
      have h := ih.2.2.2 ρ Δ hρ hΔ
      simp only [Jdg.ren, Tm.ren, Tm.ren_inst] at h
      exact h)
  | cong h h' =>
    exact ofRule (hs _ (.cong h h')) (by
      fromIH ih ρ Δ hρ hΔ
      exact Renames.under hc ih.2.2 rfl ih.1 hρ hΔ)
  | fstCong => exact ofRule (hs _ .fstCong) (by fromIH ih ρ Δ hρ hΔ)
  | sndCong =>
    simp only [Jdg.ren, Tm.ren, Tm.ren_inst]
    exact ofRule (hs _ .sndCong) (by fromIH ih ρ Δ hρ hΔ)
  | eq h h' =>
    simp only [Jdg.ren, Tm.ren, Tm.ren_eqSigma]
    exact ofRule (hs _ (.eq h h')) (by fromIH ih ρ Δ hρ hΔ)
  | eqProof h h' =>
    simp only [Jdg.ren, Tm.ren, Tm.ren_eqSigmaProof]
    exact ofRule (hs _ (.eqProof h h')) (by fromIH ih ρ Δ hρ hΔ)
  | eqTyApart h1 h2 => exact ofRule (hs _ (.eqTyApart h1 h2)) (by fromIH ih ρ Δ hρ hΔ)
  | cast h1 h2 =>
    simp only [Jdg.ren, Tm.ren, Tm.ren_castSigma]
    exact ofRule (hs _ (.cast h1 h2)) (by
      fromIH ih ρ Δ hρ hΔ
      · exact Renames.under hc ih.2.2.2.2.1 rfl ih.2.2.1 hρ hΔ
      · exact Renames.under hc ih.2.2.2.2.2.1 rfl ih.2.2.2.1 hρ hΔ)

theorem unit_renClosed {R : Rules} (hu : ∀ r, Unit r → R r) : RenClosed Unit R := by
  intro r hr ih ρ Δ hρ hΔ
  cases hr with
  | form => exact ofRule (hu _ .form) (by fromIH ih ρ Δ hρ hΔ)
  | tt => exact ofRule (hu _ .tt) (by fromIH ih ρ Δ hρ hΔ)
  | eta => exact ofRule (hu _ .eta) (by fromIH ih ρ Δ hρ hΔ)
  | cong h => exact ofRule (hu _ (.cong h)) (by fromIH ih ρ Δ hρ hΔ)
  | eq h => exact ofRule (hu _ (.eq h)) (by fromIH ih ρ Δ hρ hΔ)
  | eqTy h1 h2 h3 => exact ofRule (hu _ (.eqTy h1 h2 h3)) (by fromIH ih ρ Δ hρ hΔ)
  | eqTyApart h1 h2 h3 => exact ofRule (hu _ (.eqTyApart h1 h2 h3)) (by fromIH ih ρ Δ hρ hΔ)
  | cast h1 h2 => exact ofRule (hu _ (.cast h1 h2)) (by fromIH ih ρ Δ hρ hΔ)

theorem empty_renClosed {R : Rules} (he : ∀ r, Empty r → R r) : RenClosed Empty R := by
  intro r hr ih ρ Δ hρ hΔ
  cases hr with
  | form => exact ofRule (he _ .form) (by fromIH ih ρ Δ hρ hΔ)
  | absurd => exact ofRule (he _ .absurd) (by fromIH ih ρ Δ hρ hΔ)
  | cong h => exact ofRule (he _ (.cong h)) (by fromIH ih ρ Δ hρ hΔ)
  | absurdCong => exact ofRule (he _ .absurdCong) (by fromIH ih ρ Δ hρ hΔ)
  | eq h => exact ofRule (he _ (.eq h)) (by fromIH ih ρ Δ hρ hΔ)
  | eqTy h1 h2 h3 => exact ofRule (he _ (.eqTy h1 h2 h3)) (by fromIH ih ρ Δ hρ hΔ)
  | eqTyApart h1 h2 h3 => exact ofRule (he _ (.eqTyApart h1 h2 h3)) (by fromIH ih ρ Δ hρ hΔ)
  | cast h1 h2 => exact ofRule (he _ (.cast h1 h2)) (by fromIH ih ρ Δ hρ hΔ)

theorem let_renClosed {R : Rules} (hl : ∀ r, Let r → R r) : RenClosed Let R := by
  intro r hr ih ρ Δ hρ hΔ
  cases hr with
  | letE =>
    exact ofRule (hl _ .letE) (by
      fromIH ih ρ Δ hρ hΔ
      have h := ih.2.2 ρ Δ hρ hΔ
      simp only [Jdg.ren, Tm.ren_inst] at h
      exact h)
  | zeta =>
    simp only [Jdg.ren, Tm.ren, Tm.ren_inst]
    exact ofRule (hl _ .zeta) (by
      fromIH ih ρ Δ hρ hΔ
      have h := ih.2.2 ρ Δ hρ hΔ
      simp only [Jdg.ren, Tm.ren_inst] at h
      exact h)
  | letUnit => exact ofRule (hl _ .letUnit) (by fromIH ih ρ Δ hρ hΔ)
  | letUnitRed => exact ofRule (hl _ .letUnitRed) (by fromIH ih ρ Δ hρ hΔ)
  | ann => exact ofRule (hl _ .ann) (by fromIH ih ρ Δ hρ hΔ)
  | annRed => exact ofRule (hl _ .annRed) (by fromIH ih ρ Δ hρ hΔ)

theorem eq_renClosed {R : Rules} (hq : ∀ r, Eq r → R r) : RenClosed Eq R := by
  intro r hr ih ρ Δ hρ hΔ
  cases hr with
  | eq => exact ofRule (hq _ .eq) (by fromIH ih ρ Δ hρ hΔ)
  | refl => exact ofRule (hq _ .refl) (by fromIH ih ρ Δ hρ hΔ)
  | reflTy => exact ofRule (hq _ .reflTy) (by fromIH ih ρ Δ hρ hΔ)
  | transp =>
    exact ofRule (hq _ .transp) (by
      fromIH ih ρ Δ hρ hΔ
      have h := ih.2.2.2.1 ρ Δ hρ hΔ
      simp only [Jdg.ren, Tm.ren_transpMotiveTy] at h
      exact h)
  | cast => exact ofRule (hq _ .cast) (by fromIH ih ρ Δ hρ hΔ)
  | eqCong => exact ofRule (hq _ .eqCong) (by fromIH ih ρ Δ hρ hΔ)
  | eqTyCong => exact ofRule (hq _ .eqTyCong) (by fromIH ih ρ Δ hρ hΔ)
  | castCong => exact ofRule (hq _ .castCong) (by fromIH ih ρ Δ hρ hΔ)
  | eqRed => exact ofRule (hq _ .eqRed) (by fromIH ih ρ Δ hρ hΔ)
  | eqTyRedL => exact ofRule (hq _ .eqTyRedL) (by fromIH ih ρ Δ hρ hΔ)
  | eqTyRedR => exact ofRule (hq _ .eqTyRedR) (by fromIH ih ρ Δ hρ hΔ)
  | castRedL => exact ofRule (hq _ .castRedL) (by fromIH ih ρ Δ hρ hΔ)
  | castRedR => exact ofRule (hq _ .castRedR) (by fromIH ih ρ Δ hρ hΔ)
  | eqAtProp h => exact ofRule (hq _ (.eqAtProp h)) (by fromIH ih ρ Δ hρ hΔ)
  | eqTyProps h h' =>
    simp only [Jdg.ren, Tm.ren, Tm.ren_iff]
    exact ofRule (hq _ (.eqTyProps h h')) (by fromIH ih ρ Δ hρ hΔ)
  | eqTyFormers h1 h2 h3 h4 h5 =>
    exact ofRule (hq _ (.eqTyFormers h1 h2 ((Tm.former_ren _ ρ).trans h3)
      ((Tm.former_ren _ ρ).trans h4) h5)) (by fromIH ih ρ Δ hρ hΔ)

theorem eqTyCross_renClosed {R : Rules} (hx : ∀ r, EqTyCross r → R r) : RenClosed EqTyCross R := by
  intro r hr ih ρ Δ hρ hΔ
  cases hr with
  | form => exact ofRule (hx _ .form) (by fromIH ih ρ Δ hρ hΔ)
  | propType h h' => exact ofRule (hx _ (.propType h h')) (by fromIH ih ρ Δ hρ hΔ)
  | typeProp h h' => exact ofRule (hx _ (.typeProp h h')) (by fromIH ih ρ Δ hρ hΔ)
  | pi h h' =>
    simp only [Jdg.ren, Tm.ren, Tm.ren_eqTyPi]
    exact ofRule (hx _ (.pi h h')) (by fromIH ih ρ Δ hρ hΔ)
  | sigma h h' =>
    simp only [Jdg.ren, Tm.ren, Tm.ren_eqTySigma]
    exact ofRule (hx _ (.sigma h h')) (by fromIH ih ρ Δ hρ hΔ)

theorem eqTyLevelled_renClosed {R : Rules} (hc : ∀ r, Core r → R r)
    (hx : ∀ r, EqTyLevelled r → R r) : RenClosed EqTyLevelled R := by
  intro r hr ih ρ Δ hρ hΔ
  cases hr with
  | form => exact ofRule (hx _ .form) (by fromIH ih ρ Δ hρ hΔ)
  | pi h1 h2 h3 h4 =>
    simp only [Jdg.ren, Tm.ren, Tm.ren_eqTyPi]
    exact ofRule (hx _ (.pi h1 h2 h3 h4)) (by
      fromIH ih ρ Δ hρ hΔ
      · exact Renames.under hc ih.2.2.1 rfl ih.1 hρ hΔ
      · exact Renames.under hc ih.2.2.2 rfl ih.2.1 hρ hΔ)
  | sigma h1 h2 h3 h4 =>
    simp only [Jdg.ren, Tm.ren, Tm.ren_eqTySigma]
    exact ofRule (hx _ (.sigma h1 h2 h3 h4)) (by
      fromIH ih ρ Δ hρ hΔ
      · exact Renames.under hc ih.2.2.1 rfl ih.1 hρ hΔ
      · exact Renames.under hc ih.2.2.2 rfl ih.2.1 hρ hΔ)

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
  | eqProp h h' => exact ofRule (hu _ (.eqProp h h')) (by fromIH ih ρ Δ hρ hΔ)
  | eq h h' => exact ofRule (hu _ (.eq h h')) (by fromIH ih ρ Δ hρ hΔ)
  | eqTy h1 h2 h3 => exact ofRule (hu _ (.eqTy h1 h2 h3)) (by fromIH ih ρ Δ hρ hΔ)
  | eqTyApart h1 h2 h3 => exact ofRule (hu _ (.eqTyApart h1 h2 h3)) (by fromIH ih ρ Δ hρ hΔ)
  | cast h1 h2 => exact ofRule (hu _ (.cast h1 h2)) (by fromIH ih ρ Δ hρ hΔ)

/-- A premise under a binder whose renamed type is typed directly. -/
theorem Renames.underD {R : Rules} (hc : ∀ r, Core r → R r) {Γ Δ : Ctx} {A : Tm} {s : Srt}
    {ρ : Nat → Nat} {j : Jdg} (hj : Renames R j) (hctx : Jdg.ctx j = A :: Γ)
    (hA : Derivable R (Δ ⊢ A.ren ρ ∶ .sort s)) (hρ : RenOK ρ Γ Δ) (hΔ : Derivable R (.wf Δ)) :
    Derivable R (Jdg.ren (Tm.upRen ρ) (A.ren ρ :: Δ) j) :=
  hj _ _ (hctx ▸ hρ.up A) (ofRule (hc _ (.wfCons (s := s))) (by
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hΔ, hA⟩))

theorem branchPrems_ren {R : Rules} {Γ Δ : Ctx} {M : Tm} {n : Nat} {bl : List Tm} {ρ : Nat → Nat}
    (h : ∀ p, p ∈ branchPrems Γ M n bl → Renames R p) (hρ : RenOK ρ Γ Δ)
    (hΔ : Derivable R (.wf Δ)) :
    ∀ p, p ∈ branchPrems Δ (M.ren (Tm.upRen ρ)) n (bl.map (Tm.ren ρ)) → Derivable R p := by
  intro p hp
  simp only [branchPrems, List.zipIdx_map, List.map_map, List.mem_map] at hp
  obtain ⟨⟨b, k⟩, hm, rfl⟩ := hp
  have := h (Γ ⊢ b ∶ M.inst (.tag n k)) (by simp only [branchPrems, List.mem_map]; exact ⟨(b, k), hm, rfl⟩) ρ Δ hρ hΔ
  simpa [Jdg.ren, Tm.ren_inst, Tm.ren] using this

theorem branchEqPrems_ren {R : Rules} {Γ Δ : Ctx} {M : Tm} {n : Nat} {bl bl' : List Tm}
    {ρ : Nat → Nat} (h : ∀ p, p ∈ branchEqPrems Γ M n bl bl' → Renames R p) (hρ : RenOK ρ Γ Δ)
    (hΔ : Derivable R (.wf Δ)) :
    ∀ p, p ∈ branchEqPrems Δ (M.ren (Tm.upRen ρ)) n (bl.map (Tm.ren ρ)) (bl'.map (Tm.ren ρ)) →
      Derivable R p := by
  intro p hp
  simp only [branchEqPrems, List.zip_map, List.zipIdx_map, List.map_map, List.mem_map] at hp
  obtain ⟨⟨⟨b, b'⟩, k⟩, hm, rfl⟩ := hp
  have := h (Γ ⊢ b ≡ b' ∶ M.inst (.tag n k)) (by simp only [branchEqPrems, List.mem_map]; exact ⟨((b, b'), k), hm, rfl⟩) ρ Δ hρ hΔ
  simpa [Jdg.ren, Tm.ren_inst, Tm.ren] using this

theorem enum_renClosed {R : Rules} (hc : ∀ r, Core r → R r) (hn : ∀ r, Enum r → R r) :
    RenClosed Enum R := by
  intro r hr ih ρ Δ hρ hΔ
  have hE : ∀ n, Derivable R (Δ ⊢ (Tm.enum n).ren ρ ∶ .sort .u0) := fun n =>
    ofRule (hn _ (.form (n := n))) (by fromIH ih ρ Δ hρ hΔ)
  cases hr with
  | form => exact ofRule (hn _ .form) (by fromIH ih ρ Δ hρ hΔ)
  | tag h => exact ofRule (hn _ (.tag h)) (by fromIH ih ρ Δ hρ hΔ)
  | @ecase Γ s M k n bl h =>
    have ih1 := fun p hp => ih p (List.mem_append_left _ hp)
    have ih2 := fun p hp => ih p (List.mem_append_right _ hp)
    simp only [Jdg.ren, Tm.ren, Tm.ren_inst, Tm.ren_branches]
    exact ofRule (hn _ (.ecase (by simpa using h))) (List.forall_mem_append.2 ⟨by
        fromIH ih1 ρ Δ hρ hΔ
        exact Renames.underD hc ih1.2 rfl (hE n) hρ hΔ, branchPrems_ren ih2 hρ hΔ⟩)
  | @iota Γ b M k n i bl h1 h2 =>
    have ih1 := fun p hp => ih p (List.mem_append_left _ hp)
    have ih2 := fun p hp => ih p (List.mem_append_right _ hp)
    simp only [Jdg.ren, Tm.ren, Tm.ren_inst, Tm.ren_branches]
    exact ofRule (hn _ (.iota (by simpa using h1) (by simp [h2]))) (List.forall_mem_append.2 ⟨by
        fromIH ih1 ρ Δ hρ hΔ
        exact Renames.underD hc ih1.2 rfl (hE n) hρ hΔ, branchPrems_ren ih2 hρ hΔ⟩)
  | @ecaseRed Γ s s' M k n bl h =>
    have ih1 := fun p hp => ih p (List.mem_append_left _ hp)
    have ih2 := fun p hp => ih p (List.mem_append_right _ hp)
    simp only [Jdg.ren, Tm.ren, Tm.ren_inst, Tm.ren_branches]
    exact ofRule (hn _ (.ecaseRed (by simpa using h))) (List.forall_mem_append.2 ⟨by
        fromIH ih1 ρ Δ hρ hΔ
        exact Renames.underD hc ih1.2 rfl (hE n) hρ hΔ, branchPrems_ren ih2 hρ hΔ⟩)
  | @ecaseCong Γ s s' M M' k n bl bl' h h' =>
    have ih1 := fun p hp => ih p (List.mem_append_left _ hp)
    have ih2 := fun p hp => ih p (List.mem_append_right _ hp)
    simp only [Jdg.ren, Tm.ren, Tm.ren_inst, Tm.ren_branches]
    exact ofRule (hn _ (.ecaseCong (by simpa using h) (by simpa using h')))
      (List.forall_mem_append.2 ⟨by
        fromIH ih1 ρ Δ hρ hΔ
        exact Renames.underD hc ih1.2 rfl (hE n) hρ hΔ, branchEqPrems_ren ih2 hρ hΔ⟩)
  | eqSame h => exact ofRule (hn _ (.eqSame h)) (by fromIH ih ρ Δ hρ hΔ)
  | eqDiff h1 h2 h3 => exact ofRule (hn _ (.eqDiff h1 h2 h3)) (by fromIH ih ρ Δ hρ hΔ)
  | eqRedL => exact ofRule (hn _ .eqRedL) (by fromIH ih ρ Δ hρ hΔ)
  | eqRedR => exact ofRule (hn _ .eqRedR) (by fromIH ih ρ Δ hρ hΔ)
  | eqTySame => exact ofRule (hn _ .eqTySame) (by fromIH ih ρ Δ hρ hΔ)
  | eqTyDiff h => exact ofRule (hn _ (.eqTyDiff h)) (by fromIH ih ρ Δ hρ hΔ)
  | cast => exact ofRule (hn _ .cast) (by fromIH ih ρ Δ hρ hΔ)

theorem Sig.Closed.ren {sg : Sig} (h : Sig.Closed sg) {d : Decl} (hd : d ∈ sg) (ρ : Nat → Nat) :
    d.type.ren ρ = d.type ∧ ∀ v, d.value = some v → v.ren ρ = v := by
  simp only [Tm.ren_eq_sub]
  exact ⟨(h d hd _).1, (h d hd _).2⟩

theorem global_renClosed {R : Rules} {sg : Sig} (hsg : Sig.Closed sg)
    (hg : ∀ r, Global sg r → R r) : RenClosed (Global sg) R := by
  intro r hr ih ρ Δ hρ hΔ
  cases hr with
  | const h =>
    have hd := (hsg.ren (List.mem_of_find?_eq_some h) ρ).1
    simp only [Jdg.ren, Tm.ren, hd]
    exact ofRule (hg _ (.const h)) (by fromIH ih ρ Δ hρ hΔ)
  | delta h1 h2 =>
    have hd := hsg.ren (List.mem_of_find?_eq_some h1) ρ
    simp only [Jdg.ren, Tm.ren, hd.1, hd.2 _ h2]
    exact ofRule (hg _ (.delta h1 h2)) (by fromIH ih ρ Δ hρ hΔ)

/-- The renaming lemma for `F0Rules`, both `EqTy` variants, read in any system `R` that
contains it. -/
theorem F0Rules_renClosedIn {sg : Sig} (hsg : Sig.Closed sg) {var : EqTyVariant} {R : Rules}
    (h : ∀ r, F0Rules sg var r → R r) (hc : ∀ r, Core r → R r) :
    RenClosed (F0Rules sg var) R := by
  cases var with
  | levelled =>
    have h1 : RenClosed (Core ∪ Pi) R :=
      (core_renClosed hc).union (pi_renClosed hc (fun r x => h r (pi_in_F0Rules x)))
    have h2 : RenClosed ((Core ∪ Pi) ∪ Sigma) R :=
      h1.union (sigma_renClosed hc (fun r x => h r (sigma_in_F0Rules x)))
    have h3 : RenClosed (((Core ∪ Pi) ∪ Sigma) ∪ Unit) R :=
      h2.union (unit_renClosed (fun r x => h r (unit_in_F0Rules x)))
    have h4 : RenClosed ((((Core ∪ Pi) ∪ Sigma) ∪ Unit) ∪ Empty) R :=
      h3.union (empty_renClosed (fun r x => h r (empty_in_F0Rules x)))
    have h5 : RenClosed (((((Core ∪ Pi) ∪ Sigma) ∪ Unit) ∪ Empty) ∪ Enum) R :=
      h4.union (enum_renClosed hc (fun r x => h r (enum_in_F0Rules x)))
    have h6 : RenClosed ((((((Core ∪ Pi) ∪ Sigma) ∪ Unit) ∪ Empty) ∪ Enum) ∪ Let) R :=
      h5.union (let_renClosed (fun r x => h r (let_in_F0Rules x)))
    have h7 : RenClosed (((((((Core ∪ Pi) ∪ Sigma) ∪ Unit) ∪ Empty) ∪ Enum) ∪ Let) ∪ Global sg) R :=
      h6.union (global_renClosed hsg (fun r x => h r (global_in_F0Rules x)))
    have h8 : RenClosed ((((((((Core ∪ Pi) ∪ Sigma) ∪ Unit) ∪ Empty) ∪ Enum) ∪ Let) ∪ Global sg) ∪ Eq) R :=
      h7.union (eq_renClosed (fun r x => h r (eq_in_F0Rules x)))
    have h9 : RenClosed (((((((((Core ∪ Pi) ∪ Sigma) ∪ Unit) ∪ Empty) ∪ Enum) ∪ Let) ∪ Global sg) ∪ Eq) ∪ EqTyLevelled) R :=
      h8.union (eqTyLevelled_renClosed hc (fun r x => h r (eqTy_in_F0Rules x)))
    exact h9.union (ulift_renClosed (fun r x => h r (ulift_in_F0Rules x)))
  | cross =>
    have h1 : RenClosed (Core ∪ Pi) R :=
      (core_renClosed hc).union (pi_renClosed hc (fun r x => h r (pi_in_F0Rules x)))
    have h2 : RenClosed ((Core ∪ Pi) ∪ Sigma) R :=
      h1.union (sigma_renClosed hc (fun r x => h r (sigma_in_F0Rules x)))
    have h3 : RenClosed (((Core ∪ Pi) ∪ Sigma) ∪ Unit) R :=
      h2.union (unit_renClosed (fun r x => h r (unit_in_F0Rules x)))
    have h4 : RenClosed ((((Core ∪ Pi) ∪ Sigma) ∪ Unit) ∪ Empty) R :=
      h3.union (empty_renClosed (fun r x => h r (empty_in_F0Rules x)))
    have h5 : RenClosed (((((Core ∪ Pi) ∪ Sigma) ∪ Unit) ∪ Empty) ∪ Enum) R :=
      h4.union (enum_renClosed hc (fun r x => h r (enum_in_F0Rules x)))
    have h6 : RenClosed ((((((Core ∪ Pi) ∪ Sigma) ∪ Unit) ∪ Empty) ∪ Enum) ∪ Let) R :=
      h5.union (let_renClosed (fun r x => h r (let_in_F0Rules x)))
    have h7 : RenClosed (((((((Core ∪ Pi) ∪ Sigma) ∪ Unit) ∪ Empty) ∪ Enum) ∪ Let) ∪ Global sg) R :=
      h6.union (global_renClosed hsg (fun r x => h r (global_in_F0Rules x)))
    have h8 : RenClosed ((((((((Core ∪ Pi) ∪ Sigma) ∪ Unit) ∪ Empty) ∪ Enum) ∪ Let) ∪ Global sg) ∪ Eq) R :=
      h7.union (eq_renClosed (fun r x => h r (eq_in_F0Rules x)))
    have h9 : RenClosed (((((((((Core ∪ Pi) ∪ Sigma) ∪ Unit) ∪ Empty) ∪ Enum) ∪ Let) ∪ Global sg) ∪ Eq) ∪ EqTyCross) R :=
      h8.union (eqTyCross_renClosed (fun r x => h r (eqTy_in_F0Rules x)))
    exact h9.union (ulift_renClosed (fun r x => h r (ulift_in_F0Rules x)))

theorem F0Rules_renClosed {sg : Sig} {var : EqTyVariant} (hsg : Sig.Closed sg) :
    RenClosed (F0Rules sg var) (F0Rules sg var) :=
  F0Rules_renClosedIn hsg (fun _ x => x) (fun _ x => core_in_F0Rules x)

/-- **The renaming lemma for the fragment** (`F0Base`, levelled variant): every judgment
derivable in `F0Base` stays derivable under a renaming into a well-formed context that
respects the variables' types. The same statement for `F0` (which adds `Struct sg`) is
conditional on `StructRenClosed` (`F0/Typing.lean`). -/
theorem F0Base_rename {sg : Sig} (hsg : Sig.Closed sg) {j : Jdg} (d : Derivable (F0Base sg) j) :
    Renames (F0Base sg) j :=
  rename_of_closed (F0Rules_renClosed hsg) d

/-- Weakening for `F0Base`: the first consequence of the renaming lemma. Needs a closed
signature and a well-formed context (the latter would follow from context validity,
`Γ ⊢ J → ⊢ Γ`, which is not proved). -/
theorem F0Base_weakening {sg : Sig} (hsg : Sig.Closed sg) {Γ : Ctx} {t A B : Tm} {s : Srt}
    (hΓ : Derivable (F0Base sg) (.wf Γ)) (ht : Derivable (F0Base sg) (Γ ⊢ t ∶ A))
    (hB : Derivable (F0Base sg) (Γ ⊢ B ∶ .sort s)) :
    Derivable (F0Base sg) ((B :: Γ) ⊢ t.shift ∶ A.shift) :=
  F0Base_rename hsg ht Nat.succ (B :: Γ) (RenOK.succ Γ B)
    (ofRule (core_in_F0Rules (Core.wfCons (s := s))) (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨hΓ, hB⟩))

end Spec
end F0
end STC
