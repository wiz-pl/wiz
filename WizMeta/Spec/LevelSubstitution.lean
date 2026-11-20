import WizMeta.Spec.SubstitutionProg


/-!
# Level instantiation of Tprog (plan O6), and `DescEq_subst` (O7)

`Jdg.instL us` substitutes levels for the declaration's level parameters. It leaves the
term structure and the variable indices alone and maps the context `Γ` to `Γ.map (Tm.instL us)`,
so the induction is simpler than renaming: there is no target-context relation and no
binder lifting. What has to be checked is (a) every level side condition survives
(`Lvl.inst_equiv`, `inst_neverZero`, `inst_isZero`, and closed levels' `toNat?`), and (b)
the formers commute, which `DescCommute.lean` and the first block below provide.

The last section is the recommended first lemma, `DescEq_subst`: description equality is
stable under term substitution *and* level instantiation, including the `arg` cast case and
the `q ≡ q'` / `l ≡ l'` / `k ≡ l+1` side conditions. It is a corollary of `Tprog_subst`
and `Tprog_instL`, applied to the judgment `Γ ⊢ D ≡ D' ∶ Desc_l I`.
-/

namespace WizMeta
namespace Tm

theorem instL_inst (b a : Tm) (us : List Lvl) :
    (b.inst a).instL us = (b.instL us).inst (a.instL us) := by
  simp only [inst, sub_instL]
  congr 1
  funext i; cases i <;> rfl

theorem instL_instL (t : Tm) (us' us : List Lvl) :
    (t.instL us').instL us = t.instL (us'.map (Lvl.inst us)) := by
  induction t <;> simp_all [instL, Lvl.inst_inst, List.map_map, Function.comp_def]


theorem instL_under (B : Tm) (n : Nat) (us : List Lvl) :
    (B.under n).instL us = (B.instL us).under n := by
  simp only [under, ← Tm.ren_instL]

theorem Lvl.inst_zero (us : List Lvl) : Lvl.inst us 0 = 0 := rfl
theorem Lvl.inst_one (us : List Lvl) : Lvl.inst us 1 = 1 := rfl

theorem Option.map_inst_some (us : List Lvl) (l : Lvl) :
    (some l).map (Lvl.inst us) = some (l.inst us) := rfl

/-! ## The remaining formers commute with level instantiation -/

theorem instL_iff (a b : Tm) (us : List Lvl) :
    (iff a b).instL us = iff (a.instL us) (b.instL us) := by
  simp only [iff, instL, Tm.shift, ← Tm.ren_instL, Option.map, Lvl.inst, Lvl.ofNat, Tm.shiftN, Tm.Lvl.inst_zero, Tm.Lvl.inst_one, Tm.Option.map_inst_some, Tm.instL_under]

theorem instL_eqPi (A B f g : Tm) (us : List Lvl) :
    (eqPi A B f g).instL us = eqPi (A.instL us) (B.instL us) (f.instL us) (g.instL us) := by
  simp only [eqPi, instL, Tm.shift, ← Tm.ren_instL, Option.map, Lvl.inst, Lvl.ofNat, Tm.shiftN, Tm.Lvl.inst_zero, Tm.Lvl.inst_one, Tm.Option.map_inst_some, Tm.instL_under]

theorem instL_eqSigmaTransport (A B a b : Tm) (us : List Lvl) :
    (eqSigmaTransport A B a b).instL us =
      eqSigmaTransport (A.instL us) (B.instL us) (a.instL us) (b.instL us) := by
  simp only [eqSigmaTransport, instL, Tm.shift, Tm.shiftN, ← Tm.ren_instL, Tm.instL_inst, Option.map, Lvl.inst, Lvl.ofNat, Tm.shiftN, Tm.Lvl.inst_zero, Tm.Lvl.inst_one, Tm.Option.map_inst_some, Tm.instL_under]

theorem instL_eqSigma (A B a b : Tm) (us : List Lvl) :
    (eqSigma A B a b).instL us = eqSigma (A.instL us) (B.instL us) (a.instL us) (b.instL us) := by
  simp only [eqSigma, instL, Tm.shift, ← Tm.ren_instL, Tm.instL_inst, Option.map, Lvl.inst, Lvl.ofNat, Tm.shiftN, Tm.Lvl.inst_zero, Tm.Lvl.inst_one, Tm.Option.map_inst_some, Tm.instL_under, Tm.instL_eqSigmaTransport]

theorem instL_eqSigmaProof (A B a b : Tm) (us : List Lvl) :
    (eqSigmaProof A B a b).instL us =
      eqSigmaProof (A.instL us) (B.instL us) (a.instL us) (b.instL us) := by
  simp only [eqSigmaProof, instL, Tm.shift, ← Tm.ren_instL, Tm.instL_inst, Option.map, Lvl.inst, Lvl.ofNat, Tm.shiftN, Tm.Lvl.inst_zero, Tm.Lvl.inst_one, Tm.Option.map_inst_some, Tm.instL_under, Tm.instL_eqSigmaTransport]

theorem instL_eqTyPi (A₁ B₁ A₂ B₂ : Tm) (us : List Lvl) :
    (eqTyPi A₁ B₁ A₂ B₂).instL us =
      eqTyPi (A₁.instL us) (B₁.instL us) (A₂.instL us) (B₂.instL us) := by
  simp only [eqTyPi, instL, Tm.shift, Tm.shiftN, ← Tm.ren_instL, Tm.instL_inst, Option.map, Lvl.inst, Lvl.ofNat, Tm.shiftN, Tm.Lvl.inst_zero, Tm.Lvl.inst_one, Tm.Option.map_inst_some, Tm.instL_under]

theorem instL_eqTySigma (A₁ B₁ A₂ B₂ : Tm) (us : List Lvl) :
    (eqTySigma A₁ B₁ A₂ B₂).instL us =
      eqTySigma (A₁.instL us) (B₁.instL us) (A₂.instL us) (B₂.instL us) := by
  simp only [eqTySigma, instL, Tm.shift, Tm.shiftN, ← Tm.ren_instL, Tm.instL_inst, Option.map, Lvl.inst, Lvl.ofNat, Tm.shiftN, Tm.Lvl.inst_zero, Tm.Lvl.inst_one, Tm.Option.map_inst_some, Tm.instL_under]

theorem instL_castPi (A₁ B₁ A₂ B₂ e t : Tm) (us : List Lvl) :
    (castPi A₁ B₁ A₂ B₂ e t).instL us =
      castPi (A₁.instL us) (B₁.instL us) (A₂.instL us) (B₂.instL us) (e.instL us) (t.instL us) := by
  simp only [castPi, instL, Tm.shift, ← Tm.ren_instL, Tm.instL_inst, Option.map, Lvl.inst, Lvl.ofNat, Tm.shiftN, Tm.Lvl.inst_zero, Tm.Lvl.inst_one, Tm.Option.map_inst_some, Tm.instL_under]

theorem instL_castSigma (A₁ B₁ A₂ B₂ e t : Tm) (us : List Lvl) :
    (castSigma A₁ B₁ A₂ B₂ e t).instL us =
      castSigma (A₁.instL us) (B₁.instL us) (A₂.instL us) (B₂.instL us) (e.instL us) (t.instL us) := by
  simp only [castSigma, instL, Tm.instL_inst, Option.map, Lvl.inst, Lvl.ofNat, Tm.shiftN, Tm.Lvl.inst_zero, Tm.Lvl.inst_one, Tm.Option.map_inst_some, Tm.instL_under]

theorem instL_transpMotiveTy (l : Lvl) (A a : Tm) (us : List Lvl) :
    (transpMotiveTy l A a).instL us = transpMotiveTy (l.inst us) (A.instL us) (a.instL us) := by
  simp only [transpMotiveTy, instL, Tm.shift, ← Tm.ren_instL, Option.map, Lvl.inst, Lvl.ofNat, Tm.shiftN, Tm.Lvl.inst_zero, Tm.Lvl.inst_one, Tm.Option.map_inst_some, Tm.instL_under]

theorem instL_branches (bl : List Tm) (us : List Lvl) :
    (branches bl).instL us = branches (bl.map (Tm.instL us)) := by
  induction bl with
  | nil => rfl
  | cons b bl ih => simp only [branches, instL, ih, List.map_cons]

end Tm

namespace Spec

/-! ## Level instantiation of judgments -/

/-- Substitute levels for the declaration's level parameters, in the context and the
judgment. -/
def Jdg.instL (us : List Lvl) : Jdg → Jdg
  | .wf Γ => .wf (Γ.map (Tm.instL us))
  | .ty Γ t A => .ty (Γ.map (Tm.instL us)) (t.instL us) (A.instL us)
  | .eq Γ t u A => .eq (Γ.map (Tm.instL us)) (t.instL us) (u.instL us) (A.instL us)
  | .red Γ t u A => .red (Γ.map (Tm.instL us)) (t.instL us) (u.instL us) (A.instL us)
  | .inert Γ A => .inert (Γ.map (Tm.instL us)) (A.instL us)
  | .inertD Γ l I D => .inertD (Γ.map (Tm.instL us)) (l.inst us) (I.instL us) (D.instL us)
  | .peq Γ l I X i D x y r =>
    .peq (Γ.map (Tm.instL us)) (l.inst us) (I.instL us) (X.instL us) (i.instL us) (D.instL us)
      (x.instL us) (y.instL us) (r.instL us)

theorem Ctx.lookup_instL (Γ : Ctx) (i : Nat) (us : List Lvl) :
    Ctx.lookup (Γ.map (Tm.instL us)) i = (Ctx.lookup Γ i).map (Tm.instL us) := by
  simp only [Ctx.lookup, List.getElem?_map, Option.map_map]
  congr 1
  funext t
  simp only [Function.comp, Tm.shiftN, Tm.ren_instL]

/-- A judgment survives every level instantiation. -/
def InstLs (R : Rules) (j : Jdg) : Prop := ∀ us, Lvl.Good us → Derivable R (Jdg.instL us j)

def InstLClosed (S R : Rules) : Prop :=
  ∀ r, S r → (∀ p, p ∈ r.prems → InstLs R p) → InstLs R r.concl

theorem instL_of_closed {R : Rules} (h : InstLClosed R R) {j : Jdg} (d : Derivable R j) :
    InstLs R j := by
  induction d with
  | intro r hr _ ih => exact h r hr ih

theorem InstLClosed.union {S S' R : Rules} (h : InstLClosed S R) (h' : InstLClosed S' R) :
    InstLClosed (S ∪ S') R :=
  fun r hr ih => hr.elim (fun hs => h r hs ih) (fun hs => h' r hs ih)

/-- `fromIH`, for level instantiation: `InstLs` is unfolded and the formers are normalised. -/
macro "fromIHi " ih:ident us:ident hu:ident : tactic => `(tactic| (
  simp only [InstLs, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq,
    Jdg.instL, Tm.instL, Tm.shift, Tm.shiftN, ← Tm.ren_instL, Tm.instL_inst, Tm.instL_instL,
    Tm.instL_iff, Tm.instL_eqPi, Tm.instL_eqSigmaTransport, Tm.instL_eqSigma, Tm.instL_eqSigmaProof,
    Tm.instL_eqTyPi, Tm.instL_eqTySigma, Tm.instL_castPi, Tm.instL_castSigma,
    Tm.instL_transpMotiveTy, Tm.instL_branches, Tm.instL_under,
    Tm.instL_interpRet, Tm.instL_interpArg, Tm.instL_interpRec, Tm.instL_interpHrec,
    Tm.instL_allArg, Tm.instL_allRec, Tm.instL_allHrec, Tm.instL_hypsArg, Tm.instL_hypsRec,
    Tm.instL_hypsHrec, Tm.instL_delimArg, Tm.instL_delimRec, Tm.instL_delimHrec,
    Tm.instL_indCon, Tm.instL_hrecFieldTy, Tm.instL_argContTy, Tm.instL_hrecIndexTy,
    Tm.instL_familyTy, Tm.instL_famCodeTy, Tm.instL_code, Tm.instL_eqAlong,
    Tm.instL_eqDescArg, Tm.instL_eqDescRec, Tm.instL_eqDescHrec, Tm.instL_castDescArg,
    Tm.instL_castDescHrec, Tm.instL_muPayloadEq, Tm.instL_castMuCon, Tm.instL_delimMotiveTy,
    Tm.instL_delimMethodTys1, Tm.instL_delimMethodTys2, Tm.instL_delimMethodTys3,
    Tm.instL_delimMethodTys4, Tm.instL_muFamily, Tm.instL_indMotiveTy, Tm.instL_predTy,
    Tm.instL_sectionTy, Tm.instL_indMethodTy, Tm.instL_indHyps, Tm.instL_apps,
    Option.map, Lvl.inst, Lvl.ofNat, Tm.Lvl.inst_zero, Tm.Lvl.inst_one, Tm.Option.map_inst_some] at $ih:ident ⊢
  repeat' apply And.intro
  all_goals try first | exact $ih $us $hu | exact $ih.1 $us $hu | exact $ih.2.1 $us $hu | exact $ih.2.2.1 $us $hu | exact $ih.2.2.2.1 $us $hu | exact $ih.2.2.2.2.1 $us $hu | exact $ih.2.2.2.2.2.1 $us $hu | exact $ih.2.2.2.2.2.2.1 $us $hu | exact $ih.2.2.2.2.2.2.2.1 $us $hu | exact $ih.2.2.2.2.2.2.2.2.1 $us $hu | exact $ih.2 $us $hu | exact $ih.2.2 $us $hu | exact $ih.2.2.2 $us $hu | exact $ih.2.2.2.2 $us $hu | exact $ih.2.2.2.2.2 $us $hu | exact $ih.2.2.2.2.2.2 $us $hu | exact $ih.2.2.2.2.2.2.2 $us $hu | exact $ih.2.2.2.2.2.2.2.2 $us $hu | exact $ih.2.2.2.2.2.2.2.2.2 $us))

/-- The goal, before `ofRule`: `Jdg.instL` and the formers normalised. -/
macro "instLGoal" : tactic => `(tactic| simp only [
    Jdg.instL, Tm.instL, Tm.shift, Tm.shiftN, ← Tm.ren_instL, Tm.instL_inst, Tm.instL_instL,
    Tm.instL_iff, Tm.instL_eqPi, Tm.instL_eqSigmaTransport, Tm.instL_eqSigma, Tm.instL_eqSigmaProof,
    Tm.instL_eqTyPi, Tm.instL_eqTySigma, Tm.instL_castPi, Tm.instL_castSigma,
    Tm.instL_transpMotiveTy, Tm.instL_branches, Tm.instL_under,
    Tm.instL_interpRet, Tm.instL_interpArg, Tm.instL_interpRec, Tm.instL_interpHrec,
    Tm.instL_allArg, Tm.instL_allRec, Tm.instL_allHrec, Tm.instL_hypsArg, Tm.instL_hypsRec,
    Tm.instL_hypsHrec, Tm.instL_delimArg, Tm.instL_delimRec, Tm.instL_delimHrec,
    Tm.instL_indCon, Tm.instL_hrecFieldTy, Tm.instL_argContTy, Tm.instL_hrecIndexTy,
    Tm.instL_familyTy, Tm.instL_famCodeTy, Tm.instL_code, Tm.instL_eqAlong,
    Tm.instL_eqDescArg, Tm.instL_eqDescRec, Tm.instL_eqDescHrec, Tm.instL_castDescArg,
    Tm.instL_castDescHrec, Tm.instL_muPayloadEq, Tm.instL_castMuCon, Tm.instL_delimMotiveTy,
    Tm.instL_delimMethodTys1, Tm.instL_delimMethodTys2, Tm.instL_delimMethodTys3,
    Tm.instL_delimMethodTys4, Tm.instL_muFamily, Tm.instL_indMotiveTy, Tm.instL_predTy,
    Tm.instL_sectionTy, Tm.instL_indMethodTy, Tm.instL_indHyps, Tm.instL_apps,
    Option.map, Lvl.inst, Lvl.ofNat, Tm.Lvl.inst_zero, Tm.Lvl.inst_one, Tm.Option.map_inst_some])

end Spec

namespace Spec

theorem branchPrems_instL {R : Rules} {Γ : Ctx} {M : Tm} {n : Nat} {bl : List Tm}
    {us : List Lvl}
    (h : ∀ p, p ∈ branchPrems Γ M n bl → InstLs R p) (hu : Lvl.Good us) :
    ∀ p, p ∈ branchPrems (Γ.map (Tm.instL us)) (M.instL us) n (bl.map (Tm.instL us)) →
      Derivable R p := by
  intro p hp
  simp only [branchPrems, List.zipIdx_map, List.map_map, List.mem_map] at hp
  obtain ⟨⟨b, k⟩, hm, rfl⟩ := hp
  have := h (Γ ⊢ b ∶ M.inst (.tag n k)) (by simp only [branchPrems, List.mem_map]; exact ⟨(b, k), hm, rfl⟩) us hu
  simpa only [Function.comp_apply, Prod.map, id_eq, Jdg.instL, Tm.instL, Tm.instL_inst] using this

theorem branchEqPrems_instL {R : Rules} {Γ : Ctx} {M : Tm} {n : Nat} {bl bl' : List Tm}
    {us : List Lvl}
    (h : ∀ p, p ∈ branchEqPrems Γ M n bl bl' → InstLs R p) (hu : Lvl.Good us) :
    ∀ p, p ∈ branchEqPrems (Γ.map (Tm.instL us)) (M.instL us) n (bl.map (Tm.instL us))
      (bl'.map (Tm.instL us)) → Derivable R p := by
  intro p hp
  simp only [branchEqPrems, List.zip_map, List.zipIdx_map, List.map_map, List.mem_map] at hp
  obtain ⟨⟨⟨b, b'⟩, k⟩, hm, rfl⟩ := hp
  have := h (Γ ⊢ b ≡ b' ∶ M.inst (.tag n k)) (by simp only [branchEqPrems, List.mem_map]; exact ⟨((b, b'), k), hm, rfl⟩) us hu
  simpa only [Function.comp_apply, Prod.map, id_eq, Jdg.instL, Tm.instL, Tm.instL_inst] using this

theorem tagPrems_instL {R : Rules} {Γ : Ctx} {l : Lvl} {I D : Tm} {k : Nat} {mk : Tm → Tm}
    {us : List Lvl}
    (h : ∀ p, p ∈ tagPrems Γ l I D k mk → InstLs R p) (hu : Lvl.Good us)
    (hmk : ∀ k a, (mk (Tm.tag k a)).instL us = mk (Tm.tag k a)) :
    ∀ p, p ∈ tagPrems (Γ.map (Tm.instL us)) (l.inst us) (I.instL us) (D.instL us) k mk →
      Derivable R p := by
  intro p hp
  simp only [tagPrems, List.mem_map] at hp
  obtain ⟨a, ha, rfl⟩ := hp
  have := h (.inertD Γ l I (.app D (mk (.tag k a))))
    (List.mem_map.2 ⟨a, ha, rfl⟩) us hu
  simpa only [Jdg.instL, Tm.instL, hmk k a] using this

theorem delimPrems_instL {R : Rules} {Γ : Ctx} {l v : Lvl}
    {I P mret marg mrec mhrec : Tm} {us : List Lvl}
    (h : ∀ p, p ∈ delimPrems Γ l v I P mret marg mrec mhrec → InstLs R p) (hu : Lvl.Good us) :
    ∀ p, p ∈ delimPrems (Γ.map (Tm.instL us)) (l.inst us) (v.inst us) (I.instL us) (P.instL us)
      (mret.instL us) (marg.instL us) (mrec.instL us) (mhrec.instL us) → Derivable R p := by
  simp only [delimPrems, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at h ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Jdg.instL, Tm.instL, Tm.instL_delimMotiveTy] using h.1 us hu
  · simpa only [Jdg.instL, Tm.instL, Tm.instL_delimMethodTys1] using h.2.1 us hu
  · simpa only [Jdg.instL, Tm.instL, Tm.instL_delimMethodTys2] using h.2.2.1 us hu
  · simpa only [Jdg.instL, Tm.instL, Tm.instL_delimMethodTys3] using h.2.2.2.1 us hu
  · simpa only [Jdg.instL, Tm.instL, Tm.instL_delimMethodTys4] using h.2.2.2.2 us hu

theorem core_instLClosed {R : Rules} (hc : ∀ r, Core r → R r) : InstLClosed Core R := by
  intro r hr ih us hu
  cases hr with
  | wfNil => exact ofRule (hc _ .wfNil) (by simp)
  | wfCons => instLGoal; apply ofRule (hc _ .wfCons); fromIHi ih us hu
  | var h =>
      instLGoal
      apply ofRule (hc _ (.var (by rw [Ctx.lookup_instL, h]; rfl)))
      fromIHi ih us hu
  | sort => instLGoal; apply ofRule (hc _ .sort); fromIHi ih us hu
  | sortCong h => instLGoal; apply ofRule (hc _ (.sortCong (Lvl.inst_equiv h us))); fromIHi ih us hu
  | conv => instLGoal; apply ofRule (hc _ .conv); fromIHi ih us hu
  | eqConv => instLGoal; apply ofRule (hc _ .eqConv); fromIHi ih us hu
  | redConv => instLGoal; apply ofRule (hc _ .redConv); fromIHi ih us hu
  | refl => instLGoal; apply ofRule (hc _ .refl); fromIHi ih us hu
  | symm => instLGoal; apply ofRule (hc _ .symm); fromIHi ih us hu
  | trans => instLGoal; apply ofRule (hc _ .trans); fromIHi ih us hu
  | redEq => instLGoal; apply ofRule (hc _ .redEq); fromIHi ih us hu
  | irrel h => instLGoal; apply ofRule (hc _ (.irrel (Lvl.inst_isZero h us))); fromIHi ih us hu
  | eqProp h => instLGoal; apply ofRule (hc _ (.eqProp (Lvl.inst_isZero h us))); fromIHi ih us hu
  | eqType h => instLGoal; apply ofRule (hc _ (.eqType (Lvl.inst_neverZero h us))); fromIHi ih us hu
  | eqTySort h => instLGoal; apply ofRule (hc _ (.eqTySort (Lvl.inst_equiv h us))); fromIHi ih us hu
  | eqTySortApart h1 h2 h3 =>
      instLGoal
      apply ofRule (hc _ (.eqTySortApart (Lvl.toNat?_inst h1 us) (Lvl.toNat?_inst h2 us) h3))
      fromIHi ih us hu
  | castSort h => instLGoal; apply ofRule (hc _ (.castSort (Lvl.inst_equiv h us))); fromIHi ih us hu

theorem pi_instLClosed {R : Rules} (hp : ∀ r, Pi r → R r) : InstLClosed Pi R := by
  intro r hr ih us hu
  cases hr with
  | form h => instLGoal; apply ofRule (hp _ (.form (Lvl.inst_equiv h us))); fromIHi ih us hu
  | lam => instLGoal; apply ofRule (hp _ .lam); fromIHi ih us hu
  | app => instLGoal; apply ofRule (hp _ .app); fromIHi ih us hu
  | beta => instLGoal; apply ofRule (hp _ .beta); fromIHi ih us hu
  | appRed => instLGoal; apply ofRule (hp _ .appRed); fromIHi ih us hu
  | eta => instLGoal; apply ofRule (hp _ .eta); fromIHi ih us hu
  | cong h1 h2 =>
      instLGoal
      apply ofRule (hp _ (.cong (Lvl.inst_equiv h1 us) (Lvl.inst_equiv h2 us)))
      fromIHi ih us hu
  | appCong => instLGoal; apply ofRule (hp _ .appCong); fromIHi ih us hu
  | eq h => instLGoal; apply ofRule (hp _ (.eq (Lvl.inst_neverZero h us))); fromIHi ih us hu
  | eqTyApart h1 h2 h3 =>
      instLGoal
      apply ofRule (hp _ (.eqTyApart (Lvl.inst_neverZero h1 us) (Lvl.inst_neverZero h2 us) h3))
      fromIHi ih us hu
  | cast h1 h2 =>
      instLGoal
      apply ofRule (hp _ (.cast (Lvl.inst_neverZero h1 us) (Lvl.inst_neverZero h2 us)))
      fromIHi ih us hu

theorem sigma_instLClosed {R : Rules} (hs : ∀ r, Sigma r → R r) : InstLClosed Sigma R := by
  intro r hr ih us hu
  cases hr with
  | form h => instLGoal; apply ofRule (hs _ (.form (Lvl.inst_equiv h us))); fromIHi ih us hu
  | pair => instLGoal; apply ofRule (hs _ .pair); fromIHi ih us hu
  | fst => instLGoal; apply ofRule (hs _ .fst); fromIHi ih us hu
  | snd => instLGoal; apply ofRule (hs _ .snd); fromIHi ih us hu
  | fstBeta => instLGoal; apply ofRule (hs _ .fstBeta); fromIHi ih us hu
  | sndBeta => instLGoal; apply ofRule (hs _ .sndBeta); fromIHi ih us hu
  | fstRed => instLGoal; apply ofRule (hs _ .fstRed); fromIHi ih us hu
  | sndRed => instLGoal; apply ofRule (hs _ .sndRed); fromIHi ih us hu
  | eta => instLGoal; apply ofRule (hs _ .eta); fromIHi ih us hu
  | cong h1 h2 =>
      instLGoal
      apply ofRule (hs _ (.cong (Lvl.inst_equiv h1 us) (Lvl.inst_equiv h2 us)))
      fromIHi ih us hu
  | fstCong => instLGoal; apply ofRule (hs _ .fstCong); fromIHi ih us hu
  | sndCong => instLGoal; apply ofRule (hs _ .sndCong); fromIHi ih us hu
  | eq h1 h2 =>
      instLGoal
      apply ofRule (hs _ (.eq (Lvl.inst_neverZero h1 us) (Lvl.not_isZero_inst h2 hu)))
      fromIHi ih us hu
  | eqProof h1 h2 =>
      instLGoal
      apply ofRule (hs _ (.eqProof (Lvl.inst_neverZero h1 us) (Lvl.inst_isZero h2 us)))
      fromIHi ih us hu
  | eqTyApart h1 h2 h3 =>
      instLGoal
      apply ofRule (hs _ (.eqTyApart (Lvl.inst_neverZero h1 us) (Lvl.inst_neverZero h2 us) h3))
      fromIHi ih us hu
  | cast h1 h2 =>
      instLGoal
      apply ofRule (hs _ (.cast (Lvl.inst_neverZero h1 us) (Lvl.inst_neverZero h2 us)))
      fromIHi ih us hu

theorem unit_instLClosed {R : Rules} (hu' : ∀ r, Unit r → R r) : InstLClosed Unit R := by
  intro r hr ih us hu
  cases hr with
  | form => instLGoal; apply ofRule (hu' _ .form); fromIHi ih us hu
  | tt => instLGoal; apply ofRule (hu' _ .tt); fromIHi ih us hu
  | eta => instLGoal; apply ofRule (hu' _ .eta); fromIHi ih us hu
  | cong h => instLGoal; apply ofRule (hu' _ (.cong (Lvl.inst_equiv h us))); fromIHi ih us hu
  | eq h => instLGoal; apply ofRule (hu' _ (.eq (Lvl.inst_neverZero h us))); fromIHi ih us hu
  | eqTy h1 h2 h3 =>
      instLGoal
      apply ofRule (hu' _ (.eqTy (Lvl.inst_neverZero h1 us) (Lvl.inst_neverZero h2 us) (Lvl.inst_equiv h3 us)))
      fromIHi ih us hu
  | eqTyApart h1 h2 h3 =>
      instLGoal
      apply ofRule (hu' _ (.eqTyApart (Lvl.toNat?_inst h1 us) (Lvl.toNat?_inst h2 us) h3))
      fromIHi ih us hu
  | cast h1 h2 =>
      instLGoal
      apply ofRule (hu' _ (.cast (Lvl.inst_neverZero h1 us) (Lvl.inst_equiv h2 us)))
      fromIHi ih us hu

theorem empty_instLClosed {R : Rules} (he : ∀ r, Empty r → R r) : InstLClosed Empty R := by
  intro r hr ih us hu
  cases hr with
  | form => instLGoal; apply ofRule (he _ .form); fromIHi ih us hu
  | absurd => instLGoal; apply ofRule (he _ .absurd); fromIHi ih us hu
  | cong h => instLGoal; apply ofRule (he _ (.cong (Lvl.inst_equiv h us))); fromIHi ih us hu
  | absurdCong => instLGoal; apply ofRule (he _ .absurdCong); fromIHi ih us hu
  | eq h => instLGoal; apply ofRule (he _ (.eq (Lvl.inst_neverZero h us))); fromIHi ih us hu
  | eqTy h1 h2 h3 =>
      instLGoal
      apply ofRule (he _ (.eqTy (Lvl.inst_neverZero h1 us) (Lvl.inst_neverZero h2 us) (Lvl.inst_equiv h3 us)))
      fromIHi ih us hu
  | eqTyApart h1 h2 h3 =>
      instLGoal
      apply ofRule (he _ (.eqTyApart (Lvl.toNat?_inst h1 us) (Lvl.toNat?_inst h2 us) h3))
      fromIHi ih us hu
  | cast h1 h2 =>
      instLGoal
      apply ofRule (he _ (.cast (Lvl.inst_neverZero h1 us) (Lvl.inst_equiv h2 us)))
      fromIHi ih us hu

theorem enum_instLClosed {R : Rules} (hn : ∀ r, Enum r → R r) : InstLClosed Enum R := by
  intro r hr ih us hu
  cases hr with
  | form => instLGoal; apply ofRule (hn _ .form); fromIHi ih us hu
  | tag h => instLGoal; apply ofRule (hn _ (.tag h)); fromIHi ih us hu
  | @ecase Γ s M k n bl h =>
      have ih1 := fun p hp => ih p (List.mem_append_left _ hp)
      have ih2 := fun p hp => ih p (List.mem_append_right _ hp)
      instLGoal
      apply ofRule (hn _ (.ecase (by simpa using h)))
      refine List.forall_mem_append.2 ⟨?_, ?_⟩
      · fromIHi ih1 us hu
      · exact branchPrems_instL ih2 hu
  | @iota Γ b M k n i bl h1 h2 =>
      have ih1 := fun p hp => ih p (List.mem_append_left _ hp)
      have ih2 := fun p hp => ih p (List.mem_append_right _ hp)
      instLGoal
      apply ofRule (hn _ (.iota (by simpa using h1) (by simp [h2])))
      refine List.forall_mem_append.2 ⟨?_, ?_⟩
      · fromIHi ih1 us hu
      · exact branchPrems_instL ih2 hu
  | @ecaseRed Γ s s' M k n bl h =>
      have ih1 := fun p hp => ih p (List.mem_append_left _ hp)
      have ih2 := fun p hp => ih p (List.mem_append_right _ hp)
      instLGoal
      apply ofRule (hn _ (.ecaseRed (by simpa using h)))
      refine List.forall_mem_append.2 ⟨?_, ?_⟩
      · fromIHi ih1 us hu
      · exact branchPrems_instL ih2 hu
  | @ecaseCong Γ s s' M M' k n bl bl' h h' =>
      have ih1 := fun p hp => ih p (List.mem_append_left _ hp)
      have ih2 := fun p hp => ih p (List.mem_append_right _ hp)
      instLGoal
      apply ofRule (hn _ (.ecaseCong (by simpa using h) (by simpa using h')))
      refine List.forall_mem_append.2 ⟨?_, ?_⟩
      · fromIHi ih1 us hu
      · exact branchEqPrems_instL ih2 hu
  | eqSame h => instLGoal; apply ofRule (hn _ (.eqSame h)); fromIHi ih us hu
  | eqDiff h1 h2 h3 => instLGoal; apply ofRule (hn _ (.eqDiff h1 h2 h3)); fromIHi ih us hu
  | eqRedL => instLGoal; apply ofRule (hn _ .eqRedL); fromIHi ih us hu
  | eqRedR => instLGoal; apply ofRule (hn _ .eqRedR); fromIHi ih us hu
  | eqTySame => instLGoal; apply ofRule (hn _ .eqTySame); fromIHi ih us hu
  | eqTyDiff h => instLGoal; apply ofRule (hn _ (.eqTyDiff h)); fromIHi ih us hu
  | cast => instLGoal; apply ofRule (hn _ .cast); fromIHi ih us hu

theorem let_instLClosed {R : Rules} (hl : ∀ r, Let r → R r) : InstLClosed Let R := by
  intro r hr ih us hu
  cases hr with
  | letE => instLGoal; apply ofRule (hl _ .letE); fromIHi ih us hu
  | zeta => instLGoal; apply ofRule (hl _ .zeta); fromIHi ih us hu
  | ann => instLGoal; apply ofRule (hl _ .ann); fromIHi ih us hu
  | annRed => instLGoal; apply ofRule (hl _ .annRed); fromIHi ih us hu

theorem zip_map_instL_equiv {us us' : List Lvl}
    (h : ∀ p, p ∈ us.zip us' → p.1.Equiv p.2) (w : List Lvl) :
    ∀ p, p ∈ (us.map (Lvl.inst w)).zip (us'.map (Lvl.inst w)) → p.1.Equiv p.2 := by
  induction us generalizing us' with
  | nil =>
      intro p hp
      simp only [List.map_nil, List.zip_nil_left, List.not_mem_nil] at hp
  | cons a as ih =>
      cases us' with
      | nil =>
          intro p hp
          simp only [List.map_nil, List.zip_nil_right, List.not_mem_nil] at hp
      | cons b bs =>
          intro p hp
          simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at hp
          rcases hp with rfl | hp
          · exact Lvl.inst_equiv (h (a, b) (by simp)) w
          · exact ih (fun p hp => h p (by simp [hp])) p hp

theorem global_instLClosed {R : Rules} {sg : Sig} (hg : ∀ r, Global sg r → R r) :
    InstLClosed (Global sg) R := by
  intro r hr ih w hu
  cases hr with
  | @const Γ us c d h1 h2 =>
      instLGoal
      apply ofRule (hg _ (.const h1 (by simpa using h2)))
      fromIHi ih w hu
  | @delta Γ v us c d h1 h2 h3 =>
      instLGoal
      apply ofRule (hg _ (.delta h1 (by simpa using h2) h3))
      fromIHi ih w hu
  | @cong Γ us us' c d h1 h2 h3 h4 =>
      instLGoal
      apply ofRule (hg _ (.cong h1 (by simpa using h2) (by simpa using h3)
        (zip_map_instL_equiv h4 w)))
      fromIHi ih w hu

theorem eq_instLClosed {R : Rules} (hq : ∀ r, Eq r → R r) : InstLClosed Eq R := by
  intro r hr ih us hu
  cases hr with
  | eq => instLGoal; apply ofRule (hq _ .eq); fromIHi ih us hu
  | refl => instLGoal; apply ofRule (hq _ .refl); fromIHi ih us hu
  | reflTy => instLGoal; apply ofRule (hq _ .reflTy); fromIHi ih us hu
  | transp => instLGoal; apply ofRule (hq _ .transp); fromIHi ih us hu
  | cast => instLGoal; apply ofRule (hq _ .cast); fromIHi ih us hu
  | eqCong => instLGoal; apply ofRule (hq _ .eqCong); fromIHi ih us hu
  | eqTyCong => instLGoal; apply ofRule (hq _ .eqTyCong); fromIHi ih us hu
  | castCong => instLGoal; apply ofRule (hq _ .castCong); fromIHi ih us hu
  | eqRed => instLGoal; apply ofRule (hq _ .eqRed); fromIHi ih us hu
  | eqTyRedL => instLGoal; apply ofRule (hq _ .eqTyRedL); fromIHi ih us hu
  | eqTyRedR => instLGoal; apply ofRule (hq _ .eqTyRedR); fromIHi ih us hu
  | castRedL => instLGoal; apply ofRule (hq _ .castRedL); fromIHi ih us hu
  | castRedR => instLGoal; apply ofRule (hq _ .castRedR); fromIHi ih us hu
  | eqAtProp h => instLGoal; apply ofRule (hq _ (.eqAtProp (Lvl.inst_isZero h us))); fromIHi ih us hu
  | eqTyProps h1 h2 =>
      instLGoal
      apply ofRule (hq _ (.eqTyProps (Lvl.inst_isZero h1 us) (Lvl.inst_isZero h2 us)))
      fromIHi ih us hu
  | eqTyFormers h1 h2 h3 h4 h5 =>
      instLGoal
      apply ofRule (hq _ (.eqTyFormers (Lvl.inst_neverZero h1 us) (Lvl.inst_neverZero h2 us)
        (by simpa only [Tm.former_instL] using h3) (by simpa only [Tm.former_instL] using h4) h5))
      fromIHi ih us hu

theorem eqTyCross_instLClosed {R : Rules} (hx : ∀ r, EqTyCross r → R r) :
    InstLClosed EqTyCross R := by
  intro r hr ih us hu
  cases hr with
  | form => instLGoal; apply ofRule (hx _ .form); fromIHi ih us hu
  | propType h1 h2 =>
      instLGoal
      apply ofRule (hx _ (.propType (Lvl.inst_isZero h1 us) (Lvl.inst_neverZero h2 us)))
      fromIHi ih us hu
  | typeProp h1 h2 =>
      instLGoal
      apply ofRule (hx _ (.typeProp (Lvl.inst_neverZero h1 us) (Lvl.inst_isZero h2 us)))
      fromIHi ih us hu
  | pi h1 h2 =>
      instLGoal
      apply ofRule (hx _ (.pi (Lvl.inst_neverZero h1 us) (Lvl.inst_neverZero h2 us)))
      fromIHi ih us hu
  | sigma h1 h2 =>
      instLGoal
      apply ofRule (hx _ (.sigma (Lvl.inst_neverZero h1 us) (Lvl.inst_neverZero h2 us)))
      fromIHi ih us hu

theorem eqTyLevelled_instLClosed {R : Rules} (hx : ∀ r, EqTyLevelled r → R r) :
    InstLClosed EqTyLevelled R := by
  intro r hr ih us hu
  cases hr with
  | form => instLGoal; apply ofRule (hx _ .form); fromIHi ih us hu
  | pi h1 h2 h3 h4 =>
      instLGoal
      apply ofRule (hx _ (.pi (Lvl.inst_neverZero h1 us) (Lvl.inst_neverZero h2 us)
        (Lvl.inst_equiv h3 us) (Lvl.inst_equiv h4 us)))
      fromIHi ih us hu
  | sigma h1 h2 h3 h4 =>
      instLGoal
      apply ofRule (hx _ (.sigma (Lvl.inst_neverZero h1 us) (Lvl.inst_neverZero h2 us)
        (Lvl.inst_equiv h3 us) (Lvl.inst_equiv h4 us)))
      fromIHi ih us hu

end Spec

namespace Spec

theorem inReg_instLClosed {R : Rules} (hi : ∀ r, InReg r → R r) : InstLClosed InReg R := by
  intro r hr ih us hu
  cases hr with
  | castRefl => instLGoal; apply ofRule (hi _ .castRefl); fromIHi ih us hu
  | conv => instLGoal; apply ofRule (hi _ .conv); fromIHi ih us hu
  | enum => instLGoal; apply ofRule (hi _ .enum); fromIHi ih us hu
  | unit h => instLGoal; apply ofRule (hi _ (.unit (Lvl.inst_neverZero h us))); fromIHi ih us hu
  | ulift h => instLGoal; apply ofRule (hi _ (.ulift (Lvl.inst_neverZero h us))); fromIHi ih us hu
  | sigma h =>
      instLGoal
      apply ofRule (hi _ (.sigma (Lvl.inst_neverZero h us)))
      fromIHi ih us hu
  | mu => instLGoal; apply ofRule (hi _ .mu); fromIHi ih us hu
  | descConv => instLGoal; apply ofRule (hi _ .descConv); fromIHi ih us hu
  | ret => instLGoal; apply ofRule (hi _ .ret); fromIHi ih us hu
  | drec => instLGoal; apply ofRule (hi _ .drec); fromIHi ih us hu
  | argTag =>
      instLGoal
      apply ofRule (hi _ .argTag)
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at ih
      refine List.forall_mem_cons.2 ⟨?_, ?_⟩
      · exact ih.1 us hu
      · exact tagPrems_instL ih.2 hu (fun k a => rfl)
  | argTagLifted =>
      instLGoal
      apply ofRule (hi _ .argTagLifted)
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at ih
      refine List.forall_mem_cons.2 ⟨?_, ?_⟩
      · exact ih.1 us hu
      · exact tagPrems_instL ih.2 hu (fun k a => rfl)
  | arg => instLGoal; apply ofRule (hi _ .arg); fromIHi ih us hu

theorem ulift_instLClosed {R : Rules} {var : EqTyVariant} (hu' : ∀ r, ULift var r → R r) :
    InstLClosed (ULift var) R := by
  intro r hr ih us hu
  cases hr with
  | form h => instLGoal; apply ofRule (hu' _ (.form (Lvl.inst_equiv h us))); fromIHi ih us hu
  | up => instLGoal; apply ofRule (hu' _ .up); fromIHi ih us hu
  | down => instLGoal; apply ofRule (hu' _ .down); fromIHi ih us hu
  | beta => instLGoal; apply ofRule (hu' _ .beta); fromIHi ih us hu
  | downRed => instLGoal; apply ofRule (hu' _ .downRed); fromIHi ih us hu
  | eta => instLGoal; apply ofRule (hu' _ .eta); fromIHi ih us hu
  | cong h => instLGoal; apply ofRule (hu' _ (.cong (Lvl.inst_equiv h us))); fromIHi ih us hu
  | downCong => instLGoal; apply ofRule (hu' _ .downCong); fromIHi ih us hu
  | eqProp h1 h2 =>
      instLGoal
      apply ofRule (hu' _ (.eqProp (Lvl.inst_neverZero h1 us) (Lvl.inst_isZero h2 us)))
      fromIHi ih us hu
  | eq h1 h2 =>
      instLGoal
      apply ofRule (hu' _ (.eq (Lvl.inst_neverZero h1 us) (Lvl.inst_neverZero h2 us)))
      fromIHi ih us hu
  | eqTy h1 h2 h3 =>
      instLGoal
      apply ofRule (hu' _ (.eqTy (Lvl.inst_neverZero h1 us) (Lvl.inst_equiv h2 us)
        (fun hv => Lvl.inst_equiv (h3 hv) us)))
      fromIHi ih us hu
  | eqTyApart h1 h2 h3 =>
      instLGoal
      apply ofRule (hu' _ (.eqTyApart (Lvl.toNat?_inst h1 us) (Lvl.toNat?_inst h2 us) h3))
      fromIHi ih us hu
  | cast h1 h2 =>
      instLGoal
      apply ofRule (hu' _ (.cast (Lvl.inst_neverZero h1 us) (Lvl.inst_equiv h2 us)))
      fromIHi ih us hu
  | qty => instLGoal; apply ofRule (hu' _ .qty); fromIHi ih us hu
  | qlit => instLGoal; apply ofRule (hu' _ .qlit); fromIHi ih us hu

theorem desc_instLClosed {R : Rules} (hd : ∀ r, Desc r → R r) : InstLClosed Desc R := by
  intro r hr ih us hu
  cases hr with
  | form => instLGoal; apply ofRule (hd _ .form); fromIHi ih us hu
  | ret => instLGoal; apply ofRule (hd _ .ret); fromIHi ih us hu
  | arg => instLGoal; apply ofRule (hd _ .arg); fromIHi ih us hu
  | drec => instLGoal; apply ofRule (hd _ .drec); fromIHi ih us hu
  | hrec => instLGoal; apply ofRule (hd _ .hrec); fromIHi ih us hu
  | cong h => instLGoal; apply ofRule (hd _ (.cong (Lvl.inst_equiv h us))); fromIHi ih us hu
  | retCong => instLGoal; apply ofRule (hd _ .retCong); fromIHi ih us hu
  | argCong => instLGoal; apply ofRule (hd _ .argCong); fromIHi ih us hu
  | recCong => instLGoal; apply ofRule (hd _ .recCong); fromIHi ih us hu
  | hrecCong => instLGoal; apply ofRule (hd _ .hrecCong); fromIHi ih us hu
  | elim =>
      instLGoal
      apply ofRule (hd _ .elim)
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at ih
      refine List.forall_mem_cons.2 ⟨?_, ?_⟩
      · exact ih.1 us hu
      · exact delimPrems_instL ih.2 hu
  | elimRet =>
      instLGoal
      apply ofRule (hd _ .elimRet)
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at ih
      refine List.forall_mem_cons.2 ⟨?_, ?_⟩
      · exact ih.1 us hu
      · exact delimPrems_instL ih.2 hu
  | elimArg =>
      instLGoal
      apply ofRule (hd _ .elimArg)
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at ih
      refine List.forall_mem_cons.2 ⟨?_, ?_⟩
      · exact ih.1 us hu
      · exact delimPrems_instL ih.2 hu
  | elimRec =>
      instLGoal
      apply ofRule (hd _ .elimRec)
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at ih
      refine List.forall_mem_cons.2 ⟨?_, ?_⟩
      · exact ih.1 us hu
      · exact delimPrems_instL ih.2 hu
  | elimHrec =>
      instLGoal
      apply ofRule (hd _ .elimHrec)
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at ih
      refine List.forall_mem_cons.2 ⟨?_, ?_⟩
      · exact ih.1 us hu
      · exact delimPrems_instL ih.2 hu
  | elimRed =>
      instLGoal
      apply ofRule (hd _ .elimRed)
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at ih
      refine List.forall_mem_cons.2 ⟨?_, ?_⟩
      · exact ih.1 us hu
      · exact delimPrems_instL ih.2 hu
  | elimCong h => instLGoal; apply ofRule (hd _ (.elimCong (Lvl.inst_equiv h us))); fromIHi ih us hu
  | interp => instLGoal; apply ofRule (hd _ .interp); fromIHi ih us hu
  | interpRet => instLGoal; apply ofRule (hd _ .interpRet); fromIHi ih us hu
  | interpArg => instLGoal; apply ofRule (hd _ .interpArg); fromIHi ih us hu
  | interpRec => instLGoal; apply ofRule (hd _ .interpRec); fromIHi ih us hu
  | interpHrec => instLGoal; apply ofRule (hd _ .interpHrec); fromIHi ih us hu
  | interpRed => instLGoal; apply ofRule (hd _ .interpRed); fromIHi ih us hu
  | interpCong h => instLGoal; apply ofRule (hd _ (.interpCong (Lvl.inst_equiv h us))); fromIHi ih us hu
  | all => instLGoal; apply ofRule (hd _ .all); fromIHi ih us hu
  | hyps => instLGoal; apply ofRule (hd _ .hyps); fromIHi ih us hu
  | allRet => instLGoal; apply ofRule (hd _ .allRet); fromIHi ih us hu
  | allArg => instLGoal; apply ofRule (hd _ .allArg); fromIHi ih us hu
  | allRec => instLGoal; apply ofRule (hd _ .allRec); fromIHi ih us hu
  | allHrec => instLGoal; apply ofRule (hd _ .allHrec); fromIHi ih us hu
  | allRed => instLGoal; apply ofRule (hd _ .allRed); fromIHi ih us hu
  | hypsRet => instLGoal; apply ofRule (hd _ .hypsRet); fromIHi ih us hu
  | hypsArg => instLGoal; apply ofRule (hd _ .hypsArg); fromIHi ih us hu
  | hypsRec => instLGoal; apply ofRule (hd _ .hypsRec); fromIHi ih us hu
  | hypsHrec => instLGoal; apply ofRule (hd _ .hypsHrec); fromIHi ih us hu
  | hypsRed => instLGoal; apply ofRule (hd _ .hypsRed); fromIHi ih us hu
  | allCong h1 h2 =>
      instLGoal
      apply ofRule (hd _ (.allCong (Lvl.inst_equiv h1 us) (Lvl.inst_equiv h2 us)))
      fromIHi ih us hu
  | hypsCong => instLGoal; apply ofRule (hd _ .hypsCong); fromIHi ih us hu
  | eqTy h => instLGoal; apply ofRule (hd _ (.eqTy (Lvl.inst_equiv h us))); fromIHi ih us hu

theorem mu_instLClosed {R : Rules} (hm : ∀ r, Mu r → R r) : InstLClosed Mu R := by
  intro r hr ih us hu
  cases hr with
  | form => instLGoal; apply ofRule (hm _ .form); fromIHi ih us hu
  | con => instLGoal; apply ofRule (hm _ .con); fromIHi ih us hu
  | ind => instLGoal; apply ofRule (hm _ .ind); fromIHi ih us hu
  | iota => instLGoal; apply ofRule (hm _ .iota); fromIHi ih us hu
  | indRed => instLGoal; apply ofRule (hm _ .indRed); fromIHi ih us hu
  | cong h => instLGoal; apply ofRule (hm _ (.cong (Lvl.inst_equiv h us))); fromIHi ih us hu
  | conCong => instLGoal; apply ofRule (hm _ .conCong); fromIHi ih us hu
  | indCong h1 h2 =>
      instLGoal
      apply ofRule (hm _ (.indCong (Lvl.inst_equiv h1 us) (Lvl.inst_equiv h2 us)))
      fromIHi ih us hu

theorem descEq_instLClosed {R : Rules} (he : ∀ r, DescEq r → R r) : InstLClosed DescEq R := by
  intro r hr ih us hu
  cases hr with
  | eqRet => instLGoal; apply ofRule (he _ .eqRet); fromIHi ih us hu
  | eqArg => instLGoal; apply ofRule (he _ .eqArg); fromIHi ih us hu
  | eqRec => instLGoal; apply ofRule (he _ .eqRec); fromIHi ih us hu
  | eqHrec => instLGoal; apply ofRule (he _ .eqHrec); fromIHi ih us hu
  | @eqQtyApart Γ I D D' l q q' c h1 h2 h3 h4 h5 =>
      instLGoal
      apply ofRule (he _ (.eqQtyApart (by simpa only [Tm.dctor_instL] using h1)
        (by simpa only [Tm.dctor_instL] using h2) (Tm.dqty_instL_qlit h3 us) (Tm.dqty_instL_qlit h4 us) h5))
      fromIHi ih us hu
  | @eqCtors Γ I D D' l c c' h1 h2 h3 =>
      instLGoal
      apply ofRule (he _ (.eqCtors (by simpa only [Tm.dctor_instL] using h1)
        (by simpa only [Tm.dctor_instL] using h2) h3))
      fromIHi ih us hu
  | eqRedL => instLGoal; apply ofRule (he _ .eqRedL); fromIHi ih us hu
  | eqRedR => instLGoal; apply ofRule (he _ .eqRedR); fromIHi ih us hu
  | eqTyMu h => instLGoal; apply ofRule (he _ (.eqTyMu (Lvl.inst_equiv h us))); fromIHi ih us hu
  | castRet h => instLGoal; apply ofRule (he _ (.castRet (Lvl.inst_equiv h us))); fromIHi ih us hu
  | castArg h => instLGoal; apply ofRule (he _ (.castArg (Lvl.inst_equiv h us))); fromIHi ih us hu
  | castRec h => instLGoal; apply ofRule (he _ (.castRec (Lvl.inst_equiv h us))); fromIHi ih us hu
  | castHrec h => instLGoal; apply ofRule (he _ (.castHrec (Lvl.inst_equiv h us))); fromIHi ih us hu
  | castMu h => instLGoal; apply ofRule (he _ (.castMu (Lvl.inst_equiv h us))); fromIHi ih us hu
  | castRedArg h =>
      instLGoal
      apply ofRule (he _ (.castRedArg (Tm.former_desc_mu_instL h us)))
      fromIHi ih us hu

theorem payloadUniform_instLClosed {R : Rules} (hp : ∀ r, PayloadUniform r → R r) :
    InstLClosed PayloadUniform R := by
  intro r hr ih us hu
  cases hr with
  | eq => instLGoal; apply ofRule (hp _ .eq); fromIHi ih us hu
  | eqRedL => instLGoal; apply ofRule (hp _ .eqRedL); fromIHi ih us hu
  | eqRedR => instLGoal; apply ofRule (hp _ .eqRedR); fromIHi ih us hu

theorem payloadStuck_instLClosed {R : Rules} (hp : ∀ r, PayloadStuck r → R r) :
    InstLClosed PayloadStuck R := by
  intro r hr ih us hu
  cases hr with
  | eq => instLGoal; apply ofRule (hp _ .eq); fromIHi ih us hu
  | eqRedL => instLGoal; apply ofRule (hp _ .eqRedL); fromIHi ih us hu
  | eqRedR => instLGoal; apply ofRule (hp _ .eqRedR); fromIHi ih us hu
  | peqRet => instLGoal; apply ofRule (hp _ .peqRet); fromIHi ih us hu
  | peqTag => instLGoal; apply ofRule (hp _ .peqTag); fromIHi ih us hu
  | peqTagLifted => instLGoal; apply ofRule (hp _ .peqTagLifted); fromIHi ih us hu
  | peqTagDiff h => instLGoal; apply ofRule (hp _ (.peqTagDiff h)); fromIHi ih us hu
  | peqTagLiftedDiff h => instLGoal; apply ofRule (hp _ (.peqTagLiftedDiff h)); fromIHi ih us hu
  | peqField h => instLGoal; apply ofRule (hp _ (.peqField (NonTag.instL h us))); fromIHi ih us hu
  | peqRecLast => instLGoal; apply ofRule (hp _ .peqRecLast); fromIHi ih us hu
  | peqRec h => instLGoal; apply ofRule (hp _ (.peqRec (NonRet.instL h us))); fromIHi ih us hu
  | peqHrecLast => instLGoal; apply ofRule (hp _ .peqHrecLast); fromIHi ih us hu
  | peqHrec h => instLGoal; apply ofRule (hp _ (.peqHrec (NonRet.instL h us))); fromIHi ih us hu

end Spec

namespace Spec

theorem core_in_T0 {sg : Sig} {var : EqTyVariant} {r : Rule} (h : Core r) : T0 sg var r := by
  unfold T0
  repeat' apply Or.inl
  exact h

theorem pi_in_T0 {sg : Sig} {var : EqTyVariant} {r : Rule} (h : Pi r) : T0 sg var r := by
  unfold T0
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))))))

theorem sigma_in_T0 {sg : Sig} {var : EqTyVariant} {r : Rule} (h : Sigma r) : T0 sg var r := by
  unfold T0
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))))

theorem unit_in_T0 {sg : Sig} {var : EqTyVariant} {r : Rule} (h : Unit r) : T0 sg var r := by
  unfold T0
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))))

theorem empty_in_T0 {sg : Sig} {var : EqTyVariant} {r : Rule} (h : Empty r) : T0 sg var r := by
  unfold T0
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))

theorem enum_in_T0 {sg : Sig} {var : EqTyVariant} {r : Rule} (h : Enum r) : T0 sg var r := by
  unfold T0
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))

theorem let_in_T0 {sg : Sig} {var : EqTyVariant} {r : Rule} (h : Let r) : T0 sg var r := by
  unfold T0
  exact Or.inl (Or.inl (Or.inl (Or.inr h)))

theorem global_in_T0 {sg : Sig} {var : EqTyVariant} {r : Rule} (h : Global sg r) : T0 sg var r := by
  unfold T0
  exact Or.inl (Or.inl (Or.inr h))

theorem eq_in_T0 {sg : Sig} {var : EqTyVariant} {r : Rule} (h : Eq r) : T0 sg var r := by
  unfold T0
  exact Or.inl (Or.inr h)

theorem eqTy_in_T0 {sg : Sig} {var : EqTyVariant} {r : Rule} (h : eqTyRules var r) : T0 sg var r := by
  unfold T0
  exact Or.inr h

theorem T0_instLClosedIn {sg : Sig} (var : EqTyVariant) {R : Rules}
    (h : ∀ r, T0 sg var r → R r) : InstLClosed (T0 sg var) R := by
  refine ((((((((core_instLClosed (fun _ hr => h _ (core_in_T0 hr))).union
    (pi_instLClosed (fun _ hr => h _ (pi_in_T0 hr)))).union
    (sigma_instLClosed (fun _ hr => h _ (sigma_in_T0 hr)))).union
    (unit_instLClosed (fun _ hr => h _ (unit_in_T0 hr)))).union
    (empty_instLClosed (fun _ hr => h _ (empty_in_T0 hr)))).union
    (enum_instLClosed (fun _ hr => h _ (enum_in_T0 hr)))).union
    (let_instLClosed (fun _ hr => h _ (let_in_T0 hr)))).union
    (global_instLClosed (fun _ hr => h _ (global_in_T0 hr)))).union
    (eq_instLClosed (fun _ hr => h _ (eq_in_T0 hr))) |>.union ?_
  cases var with
  | cross => exact eqTyCross_instLClosed (fun _ hr => h _ (eqTy_in_T0 hr))
  | levelled => exact eqTyLevelled_instLClosed (fun _ hr => h _ (eqTy_in_T0 hr))

theorem T1_instLClosedIn {sg : Sig} (var : EqTyVariant) {R : Rules}
    (h : ∀ r, T1 sg var r → R r) : InstLClosed (T1 sg var) R :=
  (T0_instLClosedIn var (fun _ hr => h _ (.inl hr))).union
    (inReg_instLClosed (fun _ hr => h _ (.inr hr)))

theorem Tprog_instLClosedIn {sg : Sig} (var : EqTyVariant) {payload R : Rules}
    (h1 : ∀ r, T1 sg var r → R r) (hu : ∀ r, ULift var r → R r)
    (hd : ∀ r, Desc r → R r) (hm : ∀ r, Mu r → R r) (he : ∀ r, DescEq r → R r)
    (hp : InstLClosed payload R) (hc : ∀ r, Core r → R r) :
    InstLClosed (Tprog sg var payload) R :=
  (((((T1_instLClosedIn var h1).union (ulift_instLClosed hu)).union (desc_instLClosed hd)).union
    (mu_instLClosed hm)).union (descEq_instLClosed he)).union hp

theorem Tprog_instLClosed {sg : Sig} (var : EqTyVariant) :
    InstLClosed (Tprog sg var PayloadStuck) (Tprog sg var PayloadStuck) :=
  Tprog_instLClosedIn var (fun _ hr => T1_in_Tprog hr) (fun _ hr => ulift_in_Tprog hr)
    (fun _ hr => desc_in_Tprog hr) (fun _ hr => mu_in_Tprog hr) (fun _ hr => descEq_in_Tprog hr)
    (payloadStuck_instLClosed (fun _ hr => payload_in_Tprog hr)) (fun _ hr => core_in_Tprog hr)

/-- **`Tprog_instL` (plan O6).** Tprog is closed under level instantiation, for a *good*
instantiation (`Lvl.Good us`: every parameter is instantiated by a level that is never
zero). The hypothesis is necessary: `Sigma.eq` has the negative side condition `¬ i.IsZero`,
and instantiating `i` by `0` would make it false (see the module note and
`wiz-notes/description-metatheory.md`). -/
theorem Tprog_instL {sg : Sig} {var : EqTyVariant} {j : Jdg}
    (d : Derivable (Tprog sg var PayloadStuck) j) {us : List Lvl} (hu : Lvl.Good us) :
    Derivable (Tprog sg var PayloadStuck) (Jdg.instL us j) :=
  instL_of_closed (Tprog_instLClosed var) d us hu

theorem TprogUniform_instLClosed {sg : Sig} (var : EqTyVariant) :
    InstLClosed (Tprog sg var PayloadUniform) (Tprog sg var PayloadUniform) :=
  Tprog_instLClosedIn var (fun _ hr => T1_in_Tprog hr) (fun _ hr => ulift_in_Tprog hr)
    (fun _ hr => desc_in_Tprog hr) (fun _ hr => mu_in_Tprog hr) (fun _ hr => descEq_in_Tprog hr)
    (payloadUniform_instLClosed (fun _ hr => payload_in_Tprog hr)) (fun _ hr => core_in_Tprog hr)

theorem TprogUniform_instL {sg : Sig} {var : EqTyVariant} {j : Jdg}
    (d : Derivable (Tprog sg var PayloadUniform) j) {us : List Lvl} (hu : Lvl.Good us) :
    Derivable (Tprog sg var PayloadUniform) (Jdg.instL us j) :=
  instL_of_closed (TprogUniform_instLClosed var) d us hu

/-- **`DescEq_subst` (plan O7).** Equality at `Desc_l I` is stable under a term
substitution: from `Γ ⊢ D ≡ D' ∶ Desc_l I` and a substitution `σ` of `Γ`'s variables into
`Δ`, the substituted equation is derivable in `Δ`. This is `Tprog_subst` at the judgment
`D ≡ D'`; it exercises every premise of the `DescEq` rules, including `q ≡ q'` and the
`arg` cast `(0 s : S) → E s = E' (cast S S' e s)`. -/
theorem DescEq_subst {sg : Sig} (hsg : Sig.Closed sg) {var : EqTyVariant}
    {Γ Δ : Ctx} {l : Lvl} {I D D' : Tm} {σ : Nat → Tm}
    (hd : Derivable (Tprog sg var PayloadStuck) (Γ ⊢ D ≡ D' ∶ .desc l I))
    (hσ : SubOK (Tprog sg var PayloadStuck) σ Γ Δ)
    (hΔ : Derivable (Tprog sg var PayloadStuck) (.wf Δ)) :
    Derivable (Tprog sg var PayloadStuck) (Δ ⊢ D.sub σ ≡ D'.sub σ ∶ .desc l (I.sub σ)) :=
  Tprog_subst hsg hd σ Δ hσ hΔ

/-- **`DescEq_instL`.** The level-instantiated form of `DescEq_subst`, under the good
instantiation hypothesis of `Tprog_instL`. -/
theorem DescEq_instL {sg : Sig} {var : EqTyVariant}
    {Γ : Ctx} {l : Lvl} {I D D' : Tm} {us : List Lvl}
    (hd : Derivable (Tprog sg var PayloadStuck) (Γ ⊢ D ≡ D' ∶ .desc l I))
    (hu : Lvl.Good us) :
    Derivable (Tprog sg var PayloadStuck)
      (Γ.map (Tm.instL us) ⊢ D.instL us ≡ D'.instL us ∶ .desc (l.inst us) (I.instL us)) :=
  Tprog_instL hd hu

end Spec

end WizMeta
