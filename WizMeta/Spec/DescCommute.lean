import WizMeta.Spec.Substitution
import WizMeta.Spec.Desc
import WizMeta.Spec.Mu
import WizMeta.Spec.DescEq

/-!
# The description machinery commutes with renaming, substitution and level instantiation

The rule sets of Tprog (`Desc`, `Mu`, `DescEq`, `Payload*`) mention a number of terms
built from the formers (`Tm.interp`, `Tm.dall`, the `Desc.elim` method types, …). The
renaming and substitution lemmas for those rule sets have to rewrite *those terms*, so
this file collects, for every such term former `F`,

    (F x…).ren ρ = F (x.ren ρ)…      (F x…).sub σ = F (x.sub σ)…      (F x…).instL us = F (x.instL us)…

and the same for the syntactic side conditions (`former?`, `dctor?`, `dqty?`, `NonTag`,
`NonRet`). Nothing here changes the rules; it is the bookkeeping the closure proofs in
`SubstitutionProg.lean` and `LevelSubstitution.lean` need.

The `Tm.close`-based method types (`delimMethodTys`, `indMotiveTy`, …) are written over an
environment plus the ambient context. Closing commutes with a renaming or substitution on
the ambient context only up to a change of the environment; `closeTail` states that
generally, and the specific lemmas close the gap with `rfl`, because the method types use
no ambient variable (all their free variables are the environment's).
-/

namespace WizMeta
namespace Tm

/-! ## Closing commutes -/

def closeTail (env : List Tm) (τ : Nat → Tm) (t : Tm) : Tm :=
  t.sub fun i => if h : i < env.length then env[i] else τ (i - env.length)

theorem close_eq_closeTail (env : List Tm) (t : Tm) : close env t = closeTail env Tm.var t := rfl

theorem closeTail_ren (env : List Tm) (τ : Nat → Tm) (t : Tm) (ρ : Nat → Nat) :
    (closeTail env τ t).ren ρ = closeTail (env.map (Tm.ren ρ)) (fun i => (τ i).ren ρ) t := by
  simp only [closeTail, ren_sub]
  apply sub_congr; intro i
  by_cases h : i < env.length
  · have h' : i < (env.map (Tm.ren ρ)).length := by simpa using h
    simp only [dif_pos h, dif_pos h', List.getElem_map]
  · have h' : ¬ i < (env.map (Tm.ren ρ)).length := by simpa using h
    simp only [dif_neg h, List.length_map, dif_neg h']

theorem closeTail_sub (env : List Tm) (τ σ : Nat → Tm) (t : Tm) :
    (closeTail env τ t).sub σ = closeTail (env.map (Tm.sub σ)) (fun i => (τ i).sub σ) t := by
  simp only [closeTail, sub_sub]
  apply sub_congr; intro i
  by_cases h : i < env.length
  · have h' : i < (env.map (Tm.sub σ)).length := by simpa using h
    simp only [dif_pos h, dif_pos h', List.getElem_map]
  · have h' : ¬ i < (env.map (Tm.sub σ)).length := by simpa using h
    simp only [dif_neg h, List.length_map, dif_neg h']

/-- `instL` commutes with a substitution: it substitutes levels only, so it distributes
through `sub` and never touches a variable. -/
theorem upSub_instL (σ : Nat → Tm) (us : List Lvl) :
    (fun i => (upSub σ i).instL us) = upSub (fun i => (σ i).instL us) := by
  funext i
  cases i with
  | zero => rfl
  | succ n => simp only [upSub, shift, ren_instL]

theorem sub_instL (t : Tm) (us : List Lvl) (σ : Nat → Tm) :
    (t.sub σ).instL us = (t.instL us).sub (fun i => (σ i).instL us) := by
  induction t generalizing σ <;> simp_all [instL, sub, upSub_instL, shift, ren_instL]

theorem closeTail_instL (env : List Tm) (τ : Nat → Tm) (t : Tm) (us : List Lvl) :
    (closeTail env τ t).instL us =
      closeTail (env.map (Tm.instL us)) (fun i => (τ i).instL us) (t.instL us) := by
  simp only [closeTail, sub_instL]
  apply sub_congr; intro i
  by_cases h : i < env.length
  · have h' : i < (env.map (Tm.instL us)).length := by simpa using h
    simp only [dif_pos h, dif_pos h', List.getElem_map]
  · have h' : ¬ i < (env.map (Tm.instL us)).length := by simpa using h
    simp only [dif_neg h, List.length_map, dif_neg h']

theorem close_instL (env : List Tm) (t : Tm) (us : List Lvl) :
    (close env t).instL us = close (env.map (Tm.instL us)) (t.instL us) := by
  rw [close_eq_closeTail, close_eq_closeTail]
  rw [closeTail_instL]
  rfl

theorem ren_apps (f : Tm) (as : List Tm) (ρ : Nat → Nat) :
    (apps f as).ren ρ = apps (f.ren ρ) (as.map (Tm.ren ρ)) := by
  induction as generalizing f with
  | nil => rfl
  | cons a as ih => simp only [apps, List.foldl_cons]; exact ih (.app f a)

theorem sub_apps (f : Tm) (as : List Tm) (σ : Nat → Tm) :
    (apps f as).sub σ = apps (f.sub σ) (as.map (Tm.sub σ)) := by
  induction as generalizing f with
  | nil => rfl
  | cons a as ih => simp only [apps, List.foldl_cons]; exact ih (.app f a)

theorem instL_apps (f : Tm) (as : List Tm) (us : List Lvl) :
    (apps f as).instL us = apps (f.instL us) (as.map (Tm.instL us)) := by
  induction as generalizing f with
  | nil => rfl
  | cons a as ih => simp only [apps, List.foldl_cons]; exact ih (.app f a)


theorem ren_muFamily (l : Lvl) (I D : Tm) (ρ : Nat → Nat) :
    (muFamily l I D).ren ρ = muFamily l (I.ren ρ) (D.ren ρ) := by
  simp only [muFamily, ren, ren_shift, upRen] <;> try rfl
theorem sub_muFamily (l : Lvl) (I D : Tm) (σ : Nat → Tm) :
    (muFamily l I D).sub σ = muFamily l (I.sub σ) (D.sub σ) := by
  simp only [muFamily, sub, sub_shift, upSub] <;> try rfl
theorem instL_muFamily (l : Lvl) (I D : Tm) (us : List Lvl) :
    (muFamily l I D).instL us = muFamily (l.inst us) (I.instL us) (D.instL us) := by
  simp only [muFamily, instL, Tm.shift, allSort, ← ren_instL, Option.map, Lvl.inst, Lvl.ofNat, Tm.shiftN] <;> try rfl

theorem ren_indHyps (l v : Lvl) (I D P m i xs : Tm) (ρ : Nat → Nat) :
    (indHyps l v I D P m i xs).ren ρ =
      indHyps l v (I.ren ρ) (D.ren ρ) (P.ren ρ) (m.ren ρ) (i.ren ρ) (xs.ren ρ) := by
  simp only [indHyps, ren, ren_shift, ren_shift2, ren_muFamily, upRen] <;> try rfl

theorem sub_indHyps (l v : Lvl) (I D P m i xs : Tm) (σ : Nat → Tm) :
    (indHyps l v I D P m i xs).sub σ =
      indHyps l v (I.sub σ) (D.sub σ) (P.sub σ) (m.sub σ) (i.sub σ) (xs.sub σ) := by
  simp only [indHyps, sub, sub_shift, sub_shift2, sub_muFamily, upSub] <;> try rfl

theorem instL_indHyps (l v : Lvl) (I D P m i xs : Tm) (us : List Lvl) :
    (indHyps l v I D P m i xs).instL us =
      indHyps (l.inst us) (v.inst us) (I.instL us) (D.instL us) (P.instL us) (m.instL us)
        (i.instL us) (xs.instL us) := by
  simp only [indHyps, instL, Tm.shift, allSort, ← ren_instL, Option.map, Lvl.inst, Lvl.ofNat, Tm.shiftN, instL_muFamily] <;> try rfl


/-! ## Former, constructor and quantity tests -/

theorem former_instL (t : Tm) (us : List Lvl) : (t.instL us).former? = t.former? := by
  cases t <;> rfl

/-- The side condition of `DescEq.castRedArg`: `A` is a description or `μ`. -/
theorem former_desc_mu_ren {A : Tm} (h : A.former? = some .desc ∨ A.former? = some .mu)
    (ρ : Nat → Nat) : (A.ren ρ).former? = some .desc ∨ (A.ren ρ).former? = some .mu := by
  rw [Tm.former_ren]; exact h

theorem former_desc_mu_sub {A : Tm} (h : A.former? = some .desc ∨ A.former? = some .mu)
    (σ : Nat → Tm) : (A.sub σ).former? = some .desc ∨ (A.sub σ).former? = some .mu := by
  rcases h with h | h
  · exact Or.inl (Tm.former_sub _ σ h)
  · exact Or.inr (Tm.former_sub _ σ h)

theorem former_desc_mu_instL {A : Tm} (h : A.former? = some .desc ∨ A.former? = some .mu)
    (us : List Lvl) : (A.instL us).former? = some .desc ∨ (A.instL us).former? = some .mu := by
  rw [Tm.former_instL]; exact h

/-- A term whose constructor is known survives a renaming/substitution/instantiation: the
only term that changes its head is a variable, and `dctor?` is `none` there. -/
theorem dctor_ren (t : Tm) (ρ : Nat → Nat) : (t.ren ρ).dctor? = t.dctor? := by
  cases t <;> rfl

theorem dctor_sub {t : Tm} {c : Nat} (h : t.dctor? = some c) (σ : Nat → Tm) :
    (t.sub σ).dctor? = some c := by
  cases t <;> simp_all [dctor?, Tm.sub]

theorem dctor_instL (t : Tm) (us : List Lvl) : (t.instL us).dctor? = t.dctor? := by
  cases t <;> rfl

theorem dqty_ren (t : Tm) (ρ : Nat → Nat) : (t.ren ρ).dqty? = (t.dqty?).map (Tm.ren ρ) := by
  cases t <;> rfl

theorem dqty_sub {t : Tm} {q : Tm} (h : t.dqty? = some q) (σ : Nat → Tm) :
    (t.sub σ).dqty? = some (q.sub σ) := by
  cases t <;> simp_all [dqty?, Tm.sub]

theorem dqty_instL (t : Tm) (us : List Lvl) : (t.instL us).dqty? = (t.dqty?).map (Tm.instL us) := by
  cases t <;> rfl

theorem dqty_ren_qlit {t : Tm} {q : Q} (h : t.dqty? = some (.qlit q)) (ρ : Nat → Nat) :
    (t.ren ρ).dqty? = some (.qlit q) := by
  rw [dqty_ren t ρ, h]; rfl

theorem dqty_sub_qlit {t : Tm} {q : Q} (h : t.dqty? = some (.qlit q)) (σ : Nat → Tm) :
    (t.sub σ).dqty? = some (.qlit q) := by
  rw [dqty_sub h σ]; rfl

theorem dqty_instL_qlit {t : Tm} {q : Q} (h : t.dqty? = some (.qlit q)) (us : List Lvl) :
    (t.instL us).dqty? = some (.qlit q) := by
  rw [dqty_instL t us, h]; rfl

theorem qlit_ren (q : Q) (ρ : Nat → Nat) : (qlit q).ren ρ = qlit q := rfl
theorem qlit_sub (q : Q) (σ : Nat → Tm) : (qlit q).sub σ = qlit q := rfl
theorem qlit_instL (q : Q) (us : List Lvl) : (qlit q).instL us = qlit q := rfl

/-! ## The `Tm`-level terms of the description rules -/

theorem ren_interpRet (l : Lvl) (I j i : Tm) (ρ : Nat → Nat) :
    (interpRet l I j i).ren ρ = interpRet l (I.ren ρ) (j.ren ρ) (i.ren ρ) := by
  simp only [interpRet, ren] <;> try rfl

theorem sub_interpRet (l : Lvl) (I j i : Tm) (σ : Nat → Tm) :
    (interpRet l I j i).sub σ = interpRet l (I.sub σ) (j.sub σ) (i.sub σ) := by
  simp only [interpRet, sub] <;> try rfl

theorem instL_interpRet (l : Lvl) (I j i : Tm) (us : List Lvl) :
    (interpRet l I j i).instL us = interpRet (l.inst us) (I.instL us) (j.instL us) (i.instL us) := by
  simp only [interpRet, instL, Option.map, Lvl.inst, Lvl.ofNat, Tm.shiftN] <;> try rfl

theorem ren_interpArg (l : Lvl) (q : Q) (I S D X i : Tm) (ρ : Nat → Nat) :
    (interpArg l q I S D X i).ren ρ = interpArg l q (I.ren ρ) (S.ren ρ) (D.ren ρ) (X.ren ρ) (i.ren ρ) := by
  simp only [interpArg, ren, ren_shift, upRen] <;> try rfl

theorem sub_interpArg (l : Lvl) (q : Q) (I S D X i : Tm) (σ : Nat → Tm) :
    (interpArg l q I S D X i).sub σ = interpArg l q (I.sub σ) (S.sub σ) (D.sub σ) (X.sub σ) (i.sub σ) := by
  simp only [interpArg, sub, sub_shift, upSub] <;> try rfl

theorem instL_interpArg (l : Lvl) (q : Q) (I S D X i : Tm) (us : List Lvl) :
    (interpArg l q I S D X i).instL us =
      interpArg (l.inst us) q (I.instL us) (S.instL us) (D.instL us) (X.instL us) (i.instL us) := by
  simp only [interpArg, instL, Tm.shift, allSort, ← ren_instL, Option.map, Lvl.inst, Lvl.ofNat, Tm.shiftN] <;> try rfl

theorem ren_interpRec (l : Lvl) (q : Q) (I j D X i : Tm) (ρ : Nat → Nat) :
    (interpRec l q I j D X i).ren ρ = interpRec l q (I.ren ρ) (j.ren ρ) (D.ren ρ) (X.ren ρ) (i.ren ρ) := by
  simp only [interpRec, ren, ren_shift, upRen] <;> try rfl

theorem sub_interpRec (l : Lvl) (q : Q) (I j D X i : Tm) (σ : Nat → Tm) :
    (interpRec l q I j D X i).sub σ = interpRec l q (I.sub σ) (j.sub σ) (D.sub σ) (X.sub σ) (i.sub σ) := by
  simp only [interpRec, sub, sub_shift, upSub] <;> try rfl

theorem instL_interpRec (l : Lvl) (q : Q) (I j D X i : Tm) (us : List Lvl) :
    (interpRec l q I j D X i).instL us =
      interpRec (l.inst us) q (I.instL us) (j.instL us) (D.instL us) (X.instL us) (i.instL us) := by
  simp only [interpRec, instL, Tm.shift, allSort, ← ren_instL, Option.map, Lvl.inst, Lvl.ofNat, Tm.shiftN] <;> try rfl

theorem ren_interpHrec (l : Lvl) (q : Q) (I H j D X i : Tm) (ρ : Nat → Nat) :
    (interpHrec l q I H j D X i).ren ρ =
      interpHrec l q (I.ren ρ) (H.ren ρ) (j.ren ρ) (D.ren ρ) (X.ren ρ) (i.ren ρ) := by
  simp only [interpHrec, ren, ren_shift, upRen] <;> try rfl

theorem sub_interpHrec (l : Lvl) (q : Q) (I H j D X i : Tm) (σ : Nat → Tm) :
    (interpHrec l q I H j D X i).sub σ =
      interpHrec l q (I.sub σ) (H.sub σ) (j.sub σ) (D.sub σ) (X.sub σ) (i.sub σ) := by
  simp only [interpHrec, sub, sub_shift, upSub] <;> try rfl

theorem instL_interpHrec (l : Lvl) (q : Q) (I H j D X i : Tm) (us : List Lvl) :
    (interpHrec l q I H j D X i).instL us =
      interpHrec (l.inst us) q (I.instL us) (H.instL us) (j.instL us) (D.instL us) (X.instL us)
        (i.instL us) := by
  simp only [interpHrec, instL, Tm.shift, allSort, ← ren_instL, Option.map, Lvl.inst, Lvl.ofNat, Tm.shiftN] <;> try rfl

theorem ren_allArg (l v : Lvl) (I D X P i xs : Tm) (ρ : Nat → Nat) :
    (allArg l v I D X P i xs).ren ρ = allArg l v (I.ren ρ) (D.ren ρ) (X.ren ρ) (P.ren ρ) (i.ren ρ) (xs.ren ρ) := by
  simp only [allArg, ren] <;> try rfl

theorem sub_allArg (l v : Lvl) (I D X P i xs : Tm) (σ : Nat → Tm) :
    (allArg l v I D X P i xs).sub σ = allArg l v (I.sub σ) (D.sub σ) (X.sub σ) (P.sub σ) (i.sub σ) (xs.sub σ) := by
  simp only [allArg, sub] <;> try rfl

theorem instL_allArg (l v : Lvl) (I D X P i xs : Tm) (us : List Lvl) :
    (allArg l v I D X P i xs).instL us =
      allArg (l.inst us) (v.inst us) (I.instL us) (D.instL us) (X.instL us) (P.instL us) (i.instL us)
        (xs.instL us) := by
  simp only [allArg, instL, Option.map, Lvl.inst, Lvl.ofNat, Tm.shiftN] <;> try rfl

theorem ren_allRec (l v : Lvl) (I j D X P i xs : Tm) (ρ : Nat → Nat) :
    (allRec l v I j D X P i xs).ren ρ =
      allRec l v (I.ren ρ) (j.ren ρ) (D.ren ρ) (X.ren ρ) (P.ren ρ) (i.ren ρ) (xs.ren ρ) := by
  simp only [allRec, ren, ren_shift, ren_apps, List.map_cons, List.map_nil, ren, upRen] <;> try rfl

theorem sub_allRec (l v : Lvl) (I j D X P i xs : Tm) (σ : Nat → Tm) :
    (allRec l v I j D X P i xs).sub σ =
      allRec l v (I.sub σ) (j.sub σ) (D.sub σ) (X.sub σ) (P.sub σ) (i.sub σ) (xs.sub σ) := by
  simp only [allRec, sub, sub_shift, sub_apps, List.map_cons, List.map_nil, sub, upSub] <;> try rfl

theorem instL_allRec (l v : Lvl) (I j D X P i xs : Tm) (us : List Lvl) :
    (allRec l v I j D X P i xs).instL us =
      allRec (l.inst us) (v.inst us) (I.instL us) (j.instL us) (D.instL us) (X.instL us) (P.instL us)
        (i.instL us) (xs.instL us) := by
  simp only [allRec, instL, Tm.shift, allSort, ← ren_instL, Option.map, Lvl.inst, Lvl.ofNat, Tm.shiftN, instL_apps, List.map_cons, List.map_nil, instL] <;> try rfl

theorem ren_allHrec (l v : Lvl) (I H j D X P i xs : Tm) (ρ : Nat → Nat) :
    (allHrec l v I H j D X P i xs).ren ρ =
      allHrec l v (I.ren ρ) (H.ren ρ) (j.ren ρ) (D.ren ρ) (X.ren ρ) (P.ren ρ) (i.ren ρ) (xs.ren ρ) := by
  simp only [allHrec, ren, ren_shift, ren_apps, List.map_cons, List.map_nil, ren, upRen] <;> try rfl

theorem sub_allHrec (l v : Lvl) (I H j D X P i xs : Tm) (σ : Nat → Tm) :
    (allHrec l v I H j D X P i xs).sub σ =
      allHrec l v (I.sub σ) (H.sub σ) (j.sub σ) (D.sub σ) (X.sub σ) (P.sub σ) (i.sub σ) (xs.sub σ) := by
  simp only [allHrec, sub, sub_shift, sub_apps, List.map_cons, List.map_nil, sub, upSub] <;> try rfl

theorem instL_allHrec (l v : Lvl) (I H j D X P i xs : Tm) (us : List Lvl) :
    (allHrec l v I H j D X P i xs).instL us =
      allHrec (l.inst us) (v.inst us) (I.instL us) (H.instL us) (j.instL us) (D.instL us) (X.instL us)
        (P.instL us) (i.instL us) (xs.instL us) := by
  simp only [allHrec, instL, Tm.shift, allSort, ← ren_instL, Option.map, Lvl.inst, Lvl.ofNat, Tm.shiftN, instL_apps, List.map_cons, List.map_nil, instL] <;> try rfl

theorem ren_hypsArg (l v : Lvl) (I D X P f i xs : Tm) (ρ : Nat → Nat) :
    (hypsArg l v I D X P f i xs).ren ρ =
      hypsArg l v (I.ren ρ) (D.ren ρ) (X.ren ρ) (P.ren ρ) (f.ren ρ) (i.ren ρ) (xs.ren ρ) := by
  simp only [hypsArg, ren] <;> try rfl

theorem sub_hypsArg (l v : Lvl) (I D X P f i xs : Tm) (σ : Nat → Tm) :
    (hypsArg l v I D X P f i xs).sub σ =
      hypsArg l v (I.sub σ) (D.sub σ) (X.sub σ) (P.sub σ) (f.sub σ) (i.sub σ) (xs.sub σ) := by
  simp only [hypsArg, sub] <;> try rfl

theorem instL_hypsArg (l v : Lvl) (I D X P f i xs : Tm) (us : List Lvl) :
    (hypsArg l v I D X P f i xs).instL us =
      hypsArg (l.inst us) (v.inst us) (I.instL us) (D.instL us) (X.instL us) (P.instL us) (f.instL us)
        (i.instL us) (xs.instL us) := by
  simp only [hypsArg, instL, Option.map, Lvl.inst, Lvl.ofNat, Tm.shiftN] <;> try rfl

theorem ren_hypsRec (l v : Lvl) (I j D X P f i xs : Tm) (ρ : Nat → Nat) :
    (hypsRec l v I j D X P f i xs).ren ρ =
      hypsRec l v (I.ren ρ) (j.ren ρ) (D.ren ρ) (X.ren ρ) (P.ren ρ) (f.ren ρ) (i.ren ρ) (xs.ren ρ) := by
  simp only [hypsRec, ren, ren_apps, List.map_cons, List.map_nil, ren, upRen] <;> try rfl

theorem sub_hypsRec (l v : Lvl) (I j D X P f i xs : Tm) (σ : Nat → Tm) :
    (hypsRec l v I j D X P f i xs).sub σ =
      hypsRec l v (I.sub σ) (j.sub σ) (D.sub σ) (X.sub σ) (P.sub σ) (f.sub σ) (i.sub σ) (xs.sub σ) := by
  simp only [hypsRec, sub, sub_apps, List.map_cons, List.map_nil, sub, upSub] <;> try rfl

theorem instL_hypsRec (l v : Lvl) (I j D X P f i xs : Tm) (us : List Lvl) :
    (hypsRec l v I j D X P f i xs).instL us =
      hypsRec (l.inst us) (v.inst us) (I.instL us) (j.instL us) (D.instL us) (X.instL us) (P.instL us)
        (f.instL us) (i.instL us) (xs.instL us) := by
  simp only [hypsRec, instL, instL_apps, List.map_cons, List.map_nil, instL] <;> try rfl

theorem ren_hypsHrec (l v : Lvl) (I j D X P f i xs : Tm) (ρ : Nat → Nat) :
    (hypsHrec l v I j D X P f i xs).ren ρ =
      hypsHrec l v (I.ren ρ) (j.ren ρ) (D.ren ρ) (X.ren ρ) (P.ren ρ) (f.ren ρ) (i.ren ρ) (xs.ren ρ) := by
  simp only [hypsHrec, ren, ren_shift, ren_apps, List.map_cons, List.map_nil, ren, upRen] <;> try rfl

theorem sub_hypsHrec (l v : Lvl) (I j D X P f i xs : Tm) (σ : Nat → Tm) :
    (hypsHrec l v I j D X P f i xs).sub σ =
      hypsHrec l v (I.sub σ) (j.sub σ) (D.sub σ) (X.sub σ) (P.sub σ) (f.sub σ) (i.sub σ) (xs.sub σ) := by
  simp only [hypsHrec, sub, sub_shift, sub_apps, List.map_cons, List.map_nil, sub, upSub] <;> try rfl

theorem instL_hypsHrec (l v : Lvl) (I j D X P f i xs : Tm) (us : List Lvl) :
    (hypsHrec l v I j D X P f i xs).instL us =
      hypsHrec (l.inst us) (v.inst us) (I.instL us) (j.instL us) (D.instL us) (X.instL us) (P.instL us)
        (f.instL us) (i.instL us) (xs.instL us) := by
  simp only [hypsHrec, instL, Tm.shift, allSort, ← ren_instL, Option.map, Lvl.inst, Lvl.ofNat, Tm.shiftN, instL_apps, List.map_cons, List.map_nil, instL] <;> try rfl

theorem ren_delimArg (v : Lvl) (P mret marg mrec mhrec q S D : Tm) (ρ : Nat → Nat) :
    (delimArg v P mret marg mrec mhrec q S D).ren ρ =
      delimArg v (P.ren ρ) (mret.ren ρ) (marg.ren ρ) (mrec.ren ρ) (mhrec.ren ρ) (q.ren ρ) (S.ren ρ) (D.ren ρ) := by
  simp only [delimArg, ren, ren_shift, ren_apps, List.map_cons, List.map_nil, ren, upRen] <;> try rfl

theorem sub_delimArg (v : Lvl) (P mret marg mrec mhrec q S D : Tm) (σ : Nat → Tm) :
    (delimArg v P mret marg mrec mhrec q S D).sub σ =
      delimArg v (P.sub σ) (mret.sub σ) (marg.sub σ) (mrec.sub σ) (mhrec.sub σ) (q.sub σ) (S.sub σ) (D.sub σ) := by
  simp only [delimArg, sub, sub_shift, sub_apps, List.map_cons, List.map_nil, sub, upSub] <;> try rfl

theorem instL_delimArg (v : Lvl) (P mret marg mrec mhrec q S D : Tm) (us : List Lvl) :
    (delimArg v P mret marg mrec mhrec q S D).instL us =
      delimArg (v.inst us) (P.instL us) (mret.instL us) (marg.instL us) (mrec.instL us) (mhrec.instL us)
        (q.instL us) (S.instL us) (D.instL us) := by
  simp only [delimArg, instL, Tm.shift, allSort, ← ren_instL, Option.map, Lvl.inst, Lvl.ofNat, Tm.shiftN, instL_apps, List.map_cons, List.map_nil, instL] <;> try rfl

theorem ren_delimRec (v : Lvl) (P mret marg mrec mhrec q j D : Tm) (ρ : Nat → Nat) :
    (delimRec v P mret marg mrec mhrec q j D).ren ρ =
      delimRec v (P.ren ρ) (mret.ren ρ) (marg.ren ρ) (mrec.ren ρ) (mhrec.ren ρ) (q.ren ρ) (j.ren ρ) (D.ren ρ) := by
  simp only [delimRec, ren, ren_apps, List.map_cons, List.map_nil, ren, upRen] <;> try rfl

theorem sub_delimRec (v : Lvl) (P mret marg mrec mhrec q j D : Tm) (σ : Nat → Tm) :
    (delimRec v P mret marg mrec mhrec q j D).sub σ =
      delimRec v (P.sub σ) (mret.sub σ) (marg.sub σ) (mrec.sub σ) (mhrec.sub σ) (q.sub σ) (j.sub σ) (D.sub σ) := by
  simp only [delimRec, sub, sub_apps, List.map_cons, List.map_nil, sub, upSub] <;> try rfl

theorem instL_delimRec (v : Lvl) (P mret marg mrec mhrec q j D : Tm) (us : List Lvl) :
    (delimRec v P mret marg mrec mhrec q j D).instL us =
      delimRec (v.inst us) (P.instL us) (mret.instL us) (marg.instL us) (mrec.instL us) (mhrec.instL us)
        (q.instL us) (j.instL us) (D.instL us) := by
  simp only [delimRec, instL, instL_apps, List.map_cons, List.map_nil, instL] <;> try rfl

theorem ren_delimHrec (v : Lvl) (P mret marg mrec mhrec q H j D : Tm) (ρ : Nat → Nat) :
    (delimHrec v P mret marg mrec mhrec q H j D).ren ρ =
      delimHrec v (P.ren ρ) (mret.ren ρ) (marg.ren ρ) (mrec.ren ρ) (mhrec.ren ρ) (q.ren ρ) (H.ren ρ)
        (j.ren ρ) (D.ren ρ) := by
  simp only [delimHrec, ren, ren_apps, List.map_cons, List.map_nil, ren, upRen] <;> try rfl

theorem sub_delimHrec (v : Lvl) (P mret marg mrec mhrec q H j D : Tm) (σ : Nat → Tm) :
    (delimHrec v P mret marg mrec mhrec q H j D).sub σ =
      delimHrec v (P.sub σ) (mret.sub σ) (marg.sub σ) (mrec.sub σ) (mhrec.sub σ) (q.sub σ) (H.sub σ)
        (j.sub σ) (D.sub σ) := by
  simp only [delimHrec, sub, sub_apps, List.map_cons, List.map_nil, sub, upSub] <;> try rfl

theorem instL_delimHrec (v : Lvl) (P mret marg mrec mhrec q H j D : Tm) (us : List Lvl) :
    (delimHrec v P mret marg mrec mhrec q H j D).instL us =
      delimHrec (v.inst us) (P.instL us) (mret.instL us) (marg.instL us) (mrec.instL us) (mhrec.instL us)
        (q.instL us) (H.instL us) (j.instL us) (D.instL us) := by
  simp only [delimHrec, instL, instL_apps, List.map_cons, List.map_nil, instL] <;> try rfl

theorem ren_indCon (l v : Lvl) (I D P m i xs : Tm) (ρ : Nat → Nat) :
    (indCon l v I D P m i xs).ren ρ = indCon l v (I.ren ρ) (D.ren ρ) (P.ren ρ) (m.ren ρ) (i.ren ρ) (xs.ren ρ) := by
  simp only [indCon, ren_apps, List.map_cons, List.map_nil, ren_indHyps, upRen] <;> try rfl

theorem sub_indCon (l v : Lvl) (I D P m i xs : Tm) (σ : Nat → Tm) :
    (indCon l v I D P m i xs).sub σ =
      indCon l v (I.sub σ) (D.sub σ) (P.sub σ) (m.sub σ) (i.sub σ) (xs.sub σ) := by
  simp only [indCon, sub_apps, List.map_cons, List.map_nil, sub_indHyps, upSub] <;> try rfl

theorem instL_indCon (l v : Lvl) (I D P m i xs : Tm) (us : List Lvl) :
    (indCon l v I D P m i xs).instL us =
      indCon (l.inst us) (v.inst us) (I.instL us) (D.instL us) (P.instL us) (m.instL us) (i.instL us)
        (xs.instL us) := by
  simp only [indCon, instL_apps, List.map_cons, List.map_nil, instL_indHyps, instL] <;> try rfl

theorem ren_hrecFieldTy (l : Lvl) (H j X : Tm) (ρ : Nat → Nat) :
    (hrecFieldTy l H j X).ren ρ = hrecFieldTy l (H.ren ρ) (j.ren ρ) (X.ren ρ) := by
  simp only [hrecFieldTy, ren, ren_shift, upRen] <;> try rfl

theorem sub_hrecFieldTy (l : Lvl) (H j X : Tm) (σ : Nat → Tm) :
    (hrecFieldTy l H j X).sub σ = hrecFieldTy l (H.sub σ) (j.sub σ) (X.sub σ) := by
  simp only [hrecFieldTy, sub, sub_shift, upSub] <;> try rfl

theorem instL_hrecFieldTy (l : Lvl) (H j X : Tm) (us : List Lvl) :
    (hrecFieldTy l H j X).instL us = hrecFieldTy (l.inst us) (H.instL us) (j.instL us) (X.instL us) := by
  simp only [hrecFieldTy, instL, Tm.shift, allSort, ← ren_instL, Option.map, Lvl.inst, Lvl.ofNat, Tm.shiftN] <;> try rfl

theorem ren_argContTy (l : Lvl) (I S : Tm) (ρ : Nat → Nat) :
    (argContTy l I S).ren ρ = argContTy l (I.ren ρ) (S.ren ρ) := by
  simp only [argContTy, ren, ren_shift, upRen] <;> try rfl

theorem sub_argContTy (l : Lvl) (I S : Tm) (σ : Nat → Tm) :
    (argContTy l I S).sub σ = argContTy l (I.sub σ) (S.sub σ) := by
  simp only [argContTy, sub, sub_shift, upSub] <;> try rfl

theorem instL_argContTy (l : Lvl) (I S : Tm) (us : List Lvl) :
    (argContTy l I S).instL us = argContTy (l.inst us) (I.instL us) (S.instL us) := by
  simp only [argContTy, instL, Tm.shift, allSort, ← ren_instL, Option.map, Lvl.inst, Lvl.ofNat, Tm.shiftN] <;> try rfl

theorem ren_hrecIndexTy (l : Lvl) (I H : Tm) (ρ : Nat → Nat) :
    (hrecIndexTy l I H).ren ρ = hrecIndexTy l (I.ren ρ) (H.ren ρ) := by
  simp only [hrecIndexTy, ren, ren_shift, upRen] <;> try rfl

theorem sub_hrecIndexTy (l : Lvl) (I H : Tm) (σ : Nat → Tm) :
    (hrecIndexTy l I H).sub σ = hrecIndexTy l (I.sub σ) (H.sub σ) := by
  simp only [hrecIndexTy, sub, sub_shift, upSub] <;> try rfl

theorem instL_hrecIndexTy (l : Lvl) (I H : Tm) (us : List Lvl) :
    (hrecIndexTy l I H).instL us = hrecIndexTy (l.inst us) (I.instL us) (H.instL us) := by
  simp only [hrecIndexTy, instL, Tm.shift, allSort, ← ren_instL, Option.map, Lvl.inst, Lvl.ofNat, Tm.shiftN] <;> try rfl

theorem ren_familyTy (l : Lvl) (I : Tm) (ρ : Nat → Nat) :
    (familyTy l I).ren ρ = familyTy l (I.ren ρ) := by
  simp only [familyTy, ren] <;> try rfl

theorem sub_familyTy (l : Lvl) (I : Tm) (σ : Nat → Tm) :
    (familyTy l I).sub σ = familyTy l (I.sub σ) := by
  simp only [familyTy, sub] <;> try rfl

theorem instL_familyTy (l : Lvl) (I : Tm) (us : List Lvl) :
    (familyTy l I).instL us = familyTy (l.inst us) (I.instL us) := by
  simp only [familyTy, instL, Option.map, Lvl.inst, Lvl.ofNat, Tm.shiftN] <;> try rfl

theorem ren_famCodeTy (l : Lvl) (ρ : Nat → Nat) : (famCodeTy l).ren ρ = famCodeTy l := by
  simp only [famCodeTy, ren] <;> try rfl

theorem sub_famCodeTy (l : Lvl) (σ : Nat → Tm) : (famCodeTy l).sub σ = famCodeTy l := by
  simp only [famCodeTy, sub] <;> try rfl

theorem instL_famCodeTy (l : Lvl) (us : List Lvl) :
    (famCodeTy l).instL us = famCodeTy (l.inst us) := by
  simp only [famCodeTy, instL, Option.map, Lvl.inst, Lvl.ofNat, Tm.shiftN] <;> try rfl

theorem ren_code (I D i : Tm) (ρ : Nat → Nat) :
    (code I D i).ren ρ = code (I.ren ρ) (D.ren ρ) (i.ren ρ) := by
  simp only [code, ren] <;> try rfl

theorem sub_code (I D i : Tm) (σ : Nat → Tm) :
    (code I D i).sub σ = code (I.sub σ) (D.sub σ) (i.sub σ) := by
  simp only [code, sub] <;> try rfl

theorem instL_code (I D i : Tm) (us : List Lvl) :
    (code I D i).instL us = code (I.instL us) (D.instL us) (i.instL us) := by
  simp only [code, instL, Option.map, Lvl.inst, Lvl.ofNat, Tm.shiftN] <;> try rfl

theorem ren_eqAlong (S S' F F' T : Tm) (ρ : Nat → Nat) :
    (eqAlong S S' F F' T).ren ρ = eqAlong (S.ren ρ) (S'.ren ρ) (F.ren ρ) (F'.ren ρ) (T.ren ρ) := by
  simp only [eqAlong, ren, ren_shift, ren_shift2, upRen] <;> try rfl

theorem sub_eqAlong (S S' F F' T : Tm) (σ : Nat → Tm) :
    (eqAlong S S' F F' T).sub σ = eqAlong (S.sub σ) (S'.sub σ) (F.sub σ) (F'.sub σ) (T.sub σ) := by
  simp only [eqAlong, sub, sub_shift, sub_shift2, upSub] <;> try rfl

theorem instL_eqAlong (S S' F F' T : Tm) (us : List Lvl) :
    (eqAlong S S' F F' T).instL us =
      eqAlong (S.instL us) (S'.instL us) (F.instL us) (F'.instL us) (T.instL us) := by
  simp only [eqAlong, instL, Tm.shift, allSort, ← ren_instL, Option.map, Lvl.inst, Lvl.ofNat, Tm.shiftN] <;> try rfl

theorem ren_eqDescArg (l : Lvl) (I S S' E E' : Tm) (ρ : Nat → Nat) :
    (eqDescArg l I S S' E E').ren ρ =
      eqDescArg l (I.ren ρ) (S.ren ρ) (S'.ren ρ) (E.ren ρ) (E'.ren ρ) := by
  simp only [eqDescArg, ren_eqAlong] <;> try rfl

theorem sub_eqDescArg (l : Lvl) (I S S' E E' : Tm) (σ : Nat → Tm) :
    (eqDescArg l I S S' E E').sub σ =
      eqDescArg l (I.sub σ) (S.sub σ) (S'.sub σ) (E.sub σ) (E'.sub σ) := by
  simp only [eqDescArg, sub_eqAlong] <;> try rfl

theorem instL_eqDescArg (l : Lvl) (I S S' E E' : Tm) (us : List Lvl) :
    (eqDescArg l I S S' E E').instL us =
      eqDescArg (l.inst us) (I.instL us) (S.instL us) (S'.instL us) (E.instL us) (E'.instL us) := by
  simp only [eqDescArg, instL_eqAlong] <;> try rfl

theorem ren_eqDescRec (l : Lvl) (I j j' E E' : Tm) (ρ : Nat → Nat) :
    (eqDescRec l I j j' E E').ren ρ =
      eqDescRec l (I.ren ρ) (j.ren ρ) (j'.ren ρ) (E.ren ρ) (E'.ren ρ) := by
  simp only [eqDescRec, ren, ren_shift, upRen] <;> try rfl

theorem sub_eqDescRec (l : Lvl) (I j j' E E' : Tm) (σ : Nat → Tm) :
    (eqDescRec l I j j' E E').sub σ =
      eqDescRec l (I.sub σ) (j.sub σ) (j'.sub σ) (E.sub σ) (E'.sub σ) := by
  simp only [eqDescRec, sub, sub_shift, upSub] <;> try rfl

theorem instL_eqDescRec (l : Lvl) (I j j' E E' : Tm) (us : List Lvl) :
    (eqDescRec l I j j' E E').instL us =
      eqDescRec (l.inst us) (I.instL us) (j.instL us) (j'.instL us) (E.instL us) (E'.instL us) := by
  simp only [eqDescRec, instL, Tm.shift, allSort, ← ren_instL, Option.map, Lvl.inst, Lvl.ofNat, Tm.shiftN] <;> try rfl

theorem ren_eqDescHrec (l : Lvl) (I H H' j j' E E' : Tm) (ρ : Nat → Nat) :
    (eqDescHrec l I H H' j j' E E').ren ρ =
      eqDescHrec l (I.ren ρ) (H.ren ρ) (H'.ren ρ) (j.ren ρ) (j'.ren ρ) (E.ren ρ) (E'.ren ρ) := by
  simp only [eqDescHrec, ren, ren_shift, ren_eqAlong, upRen] <;> try rfl

theorem sub_eqDescHrec (l : Lvl) (I H H' j j' E E' : Tm) (σ : Nat → Tm) :
    (eqDescHrec l I H H' j j' E E').sub σ =
      eqDescHrec l (I.sub σ) (H.sub σ) (H'.sub σ) (j.sub σ) (j'.sub σ) (E.sub σ) (E'.sub σ) := by
  simp only [eqDescHrec, sub, sub_shift, sub_eqAlong, upSub] <;> try rfl

theorem instL_eqDescHrec (l : Lvl) (I H H' j j' E E' : Tm) (us : List Lvl) :
    (eqDescHrec l I H H' j j' E E').instL us =
      eqDescHrec (l.inst us) (I.instL us) (H.instL us) (H'.instL us) (j.instL us) (j'.instL us)
        (E.instL us) (E'.instL us) := by
  simp only [eqDescHrec, instL, Tm.shift, allSort, ← ren_instL, Option.map, Lvl.inst, Lvl.ofNat, Tm.shiftN, instL_eqAlong] <;> try rfl

theorem ren_castDescArg (l : Lvl) (I I' e q S E : Tm) (ρ : Nat → Nat) :
    (castDescArg l I I' e q S E).ren ρ =
      castDescArg l (I.ren ρ) (I'.ren ρ) (e.ren ρ) (q.ren ρ) (S.ren ρ) (E.ren ρ) := by
  simp only [castDescArg, ren, ren_shift, upRen] <;> try rfl

theorem sub_castDescArg (l : Lvl) (I I' e q S E : Tm) (σ : Nat → Tm) :
    (castDescArg l I I' e q S E).sub σ =
      castDescArg l (I.sub σ) (I'.sub σ) (e.sub σ) (q.sub σ) (S.sub σ) (E.sub σ) := by
  simp only [castDescArg, sub, sub_shift, upSub] <;> try rfl

theorem instL_castDescArg (l : Lvl) (I I' e q S E : Tm) (us : List Lvl) :
    (castDescArg l I I' e q S E).instL us =
      castDescArg (l.inst us) (I.instL us) (I'.instL us) (e.instL us) (q.instL us) (S.instL us)
        (E.instL us) := by
  simp only [castDescArg, instL, Tm.shift, allSort, ← ren_instL, Option.map, Lvl.inst, Lvl.ofNat, Tm.shiftN] <;> try rfl

theorem ren_castDescHrec (l l' : Lvl) (I I' e q H j E : Tm) (ρ : Nat → Nat) :
    (castDescHrec l l' I I' e q H j E).ren ρ =
      castDescHrec l l' (I.ren ρ) (I'.ren ρ) (e.ren ρ) (q.ren ρ) (H.ren ρ) (j.ren ρ) (E.ren ρ) := by
  simp only [castDescHrec, ren, ren_shift, upRen] <;> try rfl

theorem sub_castDescHrec (l l' : Lvl) (I I' e q H j E : Tm) (σ : Nat → Tm) :
    (castDescHrec l l' I I' e q H j E).sub σ =
      castDescHrec l l' (I.sub σ) (I'.sub σ) (e.sub σ) (q.sub σ) (H.sub σ) (j.sub σ) (E.sub σ) := by
  simp only [castDescHrec, sub, sub_shift, upSub] <;> try rfl

theorem instL_castDescHrec (l l' : Lvl) (I I' e q H j E : Tm) (us : List Lvl) :
    (castDescHrec l l' I I' e q H j E).instL us =
      castDescHrec (l.inst us) (l'.inst us) (I.instL us) (I'.instL us) (e.instL us) (q.instL us)
        (H.instL us) (j.instL us) (E.instL us) := by
  simp only [castDescHrec, instL, Tm.shift, allSort, ← ren_instL, Option.map, Lvl.inst, Lvl.ofNat, Tm.shiftN] <;> try rfl

theorem ren_muPayloadEq (l : Lvl) (I D i I' D' i' e : Tm) (ρ : Nat → Nat) :
    (muPayloadEq l I D i I' D' i' e).ren ρ =
      muPayloadEq l (I.ren ρ) (D.ren ρ) (i.ren ρ) (I'.ren ρ) (D'.ren ρ) (i'.ren ρ) (e.ren ρ) := by
  simp only [muPayloadEq, ren, ren_shift, ren_shift2, ren_code, ren_famCodeTy, ren_muFamily, upRen] <;> try rfl

theorem sub_muPayloadEq (l : Lvl) (I D i I' D' i' e : Tm) (σ : Nat → Tm) :
    (muPayloadEq l I D i I' D' i' e).sub σ =
      muPayloadEq l (I.sub σ) (D.sub σ) (i.sub σ) (I'.sub σ) (D'.sub σ) (i'.sub σ) (e.sub σ) := by
  simp only [muPayloadEq, sub, sub_shift, sub_shift2, sub_code, sub_famCodeTy, sub_muFamily, upSub] <;> try rfl

theorem instL_muPayloadEq (l : Lvl) (I D i I' D' i' e : Tm) (us : List Lvl) :
    (muPayloadEq l I D i I' D' i' e).instL us =
      muPayloadEq (l.inst us) (I.instL us) (D.instL us) (i.instL us) (I'.instL us) (D'.instL us)
        (i'.instL us) (e.instL us) := by
  simp only [muPayloadEq, instL, Tm.shift, ← ren_instL, Option.map, Lvl.inst, Tm.shiftN, instL_famCodeTy, instL_code, instL_muFamily] <;> try rfl

theorem ren_castMuCon (l l' : Lvl) (I D i I' D' i' e x : Tm) (ρ : Nat → Nat) :
    (castMuCon l l' I D i I' D' i' e x).ren ρ =
      castMuCon l l' (I.ren ρ) (D.ren ρ) (i.ren ρ) (I'.ren ρ) (D'.ren ρ) (i'.ren ρ) (e.ren ρ) (x.ren ρ) := by
  simp only [castMuCon, ren, ren_muPayloadEq, ren_muFamily, upRen] <;> try rfl

theorem sub_castMuCon (l l' : Lvl) (I D i I' D' i' e x : Tm) (σ : Nat → Tm) :
    (castMuCon l l' I D i I' D' i' e x).sub σ =
      castMuCon l l' (I.sub σ) (D.sub σ) (i.sub σ) (I'.sub σ) (D'.sub σ) (i'.sub σ) (e.sub σ) (x.sub σ) := by
  simp only [castMuCon, sub, sub_muPayloadEq, sub_muFamily, upSub] <;> try rfl

theorem instL_castMuCon (l l' : Lvl) (I D i I' D' i' e x : Tm) (us : List Lvl) :
    (castMuCon l l' I D i I' D' i' e x).instL us =
      castMuCon (l.inst us) (l'.inst us) (I.instL us) (D.instL us) (i.instL us) (I'.instL us)
        (D'.instL us) (i'.instL us) (e.instL us) (x.instL us) := by
  simp only [castMuCon, instL, Tm.shift, ← ren_instL, Option.map, Lvl.inst, Tm.shiftN, instL_muFamily, instL_muPayloadEq] <;> try rfl

/-! ## The method types (closed with `close`) -/

theorem ren_delimMotiveTy (l v : Lvl) (I : Tm) (ρ : Nat → Nat) :
    (delimMotiveTy l v I).ren ρ = delimMotiveTy l v (I.ren ρ) := by
  rfl

theorem sub_delimMotiveTy (l v : Lvl) (I : Tm) (σ : Nat → Tm) :
    (delimMotiveTy l v I).sub σ = delimMotiveTy l v (I.sub σ) := by
  rfl

theorem instL_delimMotiveTy (l v : Lvl) (I : Tm) (us : List Lvl) :
    (delimMotiveTy l v I).instL us = delimMotiveTy (l.inst us) (v.inst us) (I.instL us) := by
  rfl

theorem ren_delimMethodTys (l v : Lvl) (I P : Tm) (ρ : Nat → Nat) :
    (delimMethodTys l v I P).1.ren ρ = (delimMethodTys l v (I.ren ρ) (P.ren ρ)).1 ∧
    (delimMethodTys l v I P).2.1.ren ρ = (delimMethodTys l v (I.ren ρ) (P.ren ρ)).2.1 ∧
    (delimMethodTys l v I P).2.2.1.ren ρ = (delimMethodTys l v (I.ren ρ) (P.ren ρ)).2.2.1 ∧
    (delimMethodTys l v I P).2.2.2.ren ρ = (delimMethodTys l v (I.ren ρ) (P.ren ρ)).2.2.2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · simp only [delimMethodTys, close_eq_closeTail]
      rw [closeTail_ren]
      rfl


theorem ren_delimMethodTys1 (l v : Lvl) (I P : Tm) (ρ : Nat → Nat) :
    (delimMethodTys l v I P).1.ren ρ = (delimMethodTys l v (I.ren ρ) (P.ren ρ)).1 :=
  (ren_delimMethodTys l v I P ρ).1

theorem ren_delimMethodTys2 (l v : Lvl) (I P : Tm) (ρ : Nat → Nat) :
    (delimMethodTys l v I P).2.1.ren ρ = (delimMethodTys l v (I.ren ρ) (P.ren ρ)).2.1 :=
  (ren_delimMethodTys l v I P ρ).2.1

theorem ren_delimMethodTys3 (l v : Lvl) (I P : Tm) (ρ : Nat → Nat) :
    (delimMethodTys l v I P).2.2.1.ren ρ = (delimMethodTys l v (I.ren ρ) (P.ren ρ)).2.2.1 :=
  (ren_delimMethodTys l v I P ρ).2.2.1

theorem ren_delimMethodTys4 (l v : Lvl) (I P : Tm) (ρ : Nat → Nat) :
    (delimMethodTys l v I P).2.2.2.ren ρ = (delimMethodTys l v (I.ren ρ) (P.ren ρ)).2.2.2 :=
  (ren_delimMethodTys l v I P ρ).2.2.2

theorem sub_delimMethodTys (l v : Lvl) (I P : Tm) (σ : Nat → Tm) :
    (delimMethodTys l v I P).1.sub σ = (delimMethodTys l v (I.sub σ) (P.sub σ)).1 ∧
    (delimMethodTys l v I P).2.1.sub σ = (delimMethodTys l v (I.sub σ) (P.sub σ)).2.1 ∧
    (delimMethodTys l v I P).2.2.1.sub σ = (delimMethodTys l v (I.sub σ) (P.sub σ)).2.2.1 ∧
    (delimMethodTys l v I P).2.2.2.sub σ = (delimMethodTys l v (I.sub σ) (P.sub σ)).2.2.2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · simp only [delimMethodTys, close_eq_closeTail]
      rw [closeTail_sub]
      rfl


theorem sub_delimMethodTys1 (l v : Lvl) (I P : Tm) (σ : Nat → Tm) :
    (delimMethodTys l v I P).1.sub σ = (delimMethodTys l v (I.sub σ) (P.sub σ)).1 :=
  (sub_delimMethodTys l v I P σ).1

theorem sub_delimMethodTys2 (l v : Lvl) (I P : Tm) (σ : Nat → Tm) :
    (delimMethodTys l v I P).2.1.sub σ = (delimMethodTys l v (I.sub σ) (P.sub σ)).2.1 :=
  (sub_delimMethodTys l v I P σ).2.1

theorem sub_delimMethodTys3 (l v : Lvl) (I P : Tm) (σ : Nat → Tm) :
    (delimMethodTys l v I P).2.2.1.sub σ = (delimMethodTys l v (I.sub σ) (P.sub σ)).2.2.1 :=
  (sub_delimMethodTys l v I P σ).2.2.1

theorem sub_delimMethodTys4 (l v : Lvl) (I P : Tm) (σ : Nat → Tm) :
    (delimMethodTys l v I P).2.2.2.sub σ = (delimMethodTys l v (I.sub σ) (P.sub σ)).2.2.2 :=
  (sub_delimMethodTys l v I P σ).2.2.2

theorem instL_delimMethodTys (l v : Lvl) (I P : Tm) (us : List Lvl) :
    (delimMethodTys l v I P).1.instL us = (delimMethodTys (l.inst us) (v.inst us) (I.instL us) (P.instL us)).1 ∧
    (delimMethodTys l v I P).2.1.instL us = (delimMethodTys (l.inst us) (v.inst us) (I.instL us) (P.instL us)).2.1 ∧
    (delimMethodTys l v I P).2.2.1.instL us = (delimMethodTys (l.inst us) (v.inst us) (I.instL us) (P.instL us)).2.2.1 ∧
    (delimMethodTys l v I P).2.2.2.instL us = (delimMethodTys (l.inst us) (v.inst us) (I.instL us) (P.instL us)).2.2.2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · simp only [delimMethodTys, close_instL]
      rfl

theorem ren_indMotiveTy (l v : Lvl) (I D : Tm) (ρ : Nat → Nat) :
    (indMotiveTy l v I D).ren ρ = indMotiveTy l v (I.ren ρ) (D.ren ρ) := by
  simp only [indMotiveTy, close_eq_closeTail]
  rw [closeTail_ren]
  rfl

theorem sub_indMotiveTy (l v : Lvl) (I D : Tm) (σ : Nat → Tm) :
    (indMotiveTy l v I D).sub σ = indMotiveTy l v (I.sub σ) (D.sub σ) := by
  simp only [indMotiveTy, close_eq_closeTail]
  rw [closeTail_sub]
  rfl

theorem instL_indMotiveTy (l v : Lvl) (I D : Tm) (us : List Lvl) :
    (indMotiveTy l v I D).instL us = indMotiveTy (l.inst us) (v.inst us) (I.instL us) (D.instL us) := by
  simp only [indMotiveTy, close_instL]
  rfl

theorem ren_predTy (l v : Lvl) (I X : Tm) (ρ : Nat → Nat) :
    (predTy l v I X).ren ρ = predTy l v (I.ren ρ) (X.ren ρ) := by
  simp only [predTy, close_eq_closeTail]
  rw [closeTail_ren]
  rfl

theorem sub_predTy (l v : Lvl) (I X : Tm) (σ : Nat → Tm) :
    (predTy l v I X).sub σ = predTy l v (I.sub σ) (X.sub σ) := by
  simp only [predTy, close_eq_closeTail]
  rw [closeTail_sub]
  rfl

theorem instL_predTy (l v : Lvl) (I X : Tm) (us : List Lvl) :
    (predTy l v I X).instL us = predTy (l.inst us) (v.inst us) (I.instL us) (X.instL us) := by
  simp only [predTy, close_instL]
  rfl

theorem ren_sectionTy (l v : Lvl) (I X P : Tm) (ρ : Nat → Nat) :
    (sectionTy l v I X P).ren ρ = sectionTy l v (I.ren ρ) (X.ren ρ) (P.ren ρ) := by
  simp only [sectionTy, close_eq_closeTail]
  rw [closeTail_ren]
  rfl

theorem sub_sectionTy (l v : Lvl) (I X P : Tm) (σ : Nat → Tm) :
    (sectionTy l v I X P).sub σ = sectionTy l v (I.sub σ) (X.sub σ) (P.sub σ) := by
  simp only [sectionTy, close_eq_closeTail]
  rw [closeTail_sub]
  rfl

theorem instL_sectionTy (l v : Lvl) (I X P : Tm) (us : List Lvl) :
    (sectionTy l v I X P).instL us = sectionTy (l.inst us) (v.inst us) (I.instL us) (X.instL us) (P.instL us) := by
  simp only [sectionTy, close_instL]
  rfl

theorem ren_indMethodTy (l v : Lvl) (I D P : Tm) (ρ : Nat → Nat) :
    (indMethodTy l v I D P).ren ρ = indMethodTy l v (I.ren ρ) (D.ren ρ) (P.ren ρ) := by
  simp only [indMethodTy, close_eq_closeTail]
  rw [closeTail_ren]
  rfl

theorem sub_indMethodTy (l v : Lvl) (I D P : Tm) (σ : Nat → Tm) :
    (indMethodTy l v I D P).sub σ = indMethodTy l v (I.sub σ) (D.sub σ) (P.sub σ) := by
  simp only [indMethodTy, close_eq_closeTail]
  rw [closeTail_sub]
  rfl

theorem instL_indMethodTy (l v : Lvl) (I D P : Tm) (us : List Lvl) :
    (indMethodTy l v I D P).instL us =
      indMethodTy (l.inst us) (v.inst us) (I.instL us) (D.instL us) (P.instL us) := by
  simp only [indMethodTy, close_instL]
  rfl

theorem instL_delimMethodTys1 (l v : Lvl) (I P : Tm) (us : List Lvl) :
    (delimMethodTys l v I P).1.instL us = (delimMethodTys (l.inst us) (v.inst us) (I.instL us) (P.instL us)).1 :=
  (instL_delimMethodTys l v I P us).1

theorem instL_delimMethodTys2 (l v : Lvl) (I P : Tm) (us : List Lvl) :
    (delimMethodTys l v I P).2.1.instL us = (delimMethodTys (l.inst us) (v.inst us) (I.instL us) (P.instL us)).2.1 :=
  (instL_delimMethodTys l v I P us).2.1

theorem instL_delimMethodTys3 (l v : Lvl) (I P : Tm) (us : List Lvl) :
    (delimMethodTys l v I P).2.2.1.instL us = (delimMethodTys (l.inst us) (v.inst us) (I.instL us) (P.instL us)).2.2.1 :=
  (instL_delimMethodTys l v I P us).2.2.1

theorem instL_delimMethodTys4 (l v : Lvl) (I P : Tm) (us : List Lvl) :
    (delimMethodTys l v I P).2.2.2.instL us = (delimMethodTys (l.inst us) (v.inst us) (I.instL us) (P.instL us)).2.2.2 :=
  (instL_delimMethodTys l v I P us).2.2.2


end Tm

namespace Spec

/-! ## The side conditions of the payload rules survive -/

theorem NonRet.ren {t : Tm} (h : NonRet t) (ρ : Nat → Nat) : NonRet (t.ren ρ) := by
  cases t <;> simp_all [NonRet, Tm.ren]

theorem NonRet.sub {t : Tm} (h : NonRet t) (σ : Nat → Tm) : NonRet (t.sub σ) := by
  cases t <;> simp_all [NonRet, Tm.sub]

theorem NonRet.instL {t : Tm} (h : NonRet t) (us : List Lvl) : NonRet (t.instL us) := by
  cases t <;> simp_all [NonRet, Tm.instL]

theorem NonTag.ren {S : Tm} (h : NonTag S) (ρ : Nat → Nat) : NonTag (S.ren ρ) := by
  obtain ⟨f, hf, hne, hu⟩ := h
  cases S with
  | ulift u' A' =>
    obtain ⟨g, hg, hge⟩ := hu u' A' rfl
    refine ⟨.ulift, rfl, by decide, ?_⟩
    intro u A hA
    cases hA
    exact ⟨g, by simp only [Tm.former_ren, hg], hge⟩
  | _ => simp_all [NonTag, Tm.former?, Tm.ren]

theorem NonTag.sub {S : Tm} (h : NonTag S) (σ : Nat → Tm) : NonTag (S.sub σ) := by
  obtain ⟨f, hf, hne, hu⟩ := h
  cases S with
  | ulift u' A' =>
    obtain ⟨g, hg, hge⟩ := hu u' A' rfl
    refine ⟨.ulift, rfl, by decide, ?_⟩
    intro u A hA
    cases hA
    exact ⟨g, Tm.former_sub _ σ hg, hge⟩
  | _ => simp_all [NonTag, Tm.former?, Tm.sub]

theorem NonTag.instL {S : Tm} (h : NonTag S) (us : List Lvl) : NonTag (S.instL us) := by
  obtain ⟨f, hf, hne, hu⟩ := h
  cases S with
  | ulift u' A' =>
    obtain ⟨g, hg, hge⟩ := hu u' A' rfl
    refine ⟨.ulift, rfl, by decide, ?_⟩
    intro u A hA
    cases hA
    exact ⟨g, by simp only [Tm.former_instL, hg], hge⟩
  | _ => simp_all [NonTag, Tm.former?, Tm.instL]

end Spec
end WizMeta
