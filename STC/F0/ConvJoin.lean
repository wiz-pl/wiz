import STC.F0.Sorting
import STC.F0.Sanity
/-!
# `ConvJoin` is false: proof irrelevance and η are not reductions

`F0/Sorting.lean` states the canonical-head obligation as `ConvJoin`: every conversion
`Γ ⊢ t ≡ u ∶ A` has a common `RedStar` reduct. That statement **is refuted here** — it is
not the missing ingredient, it is too strong — for the same structural reason as
`TyUnique` at the top universe (`F0/TopSort.lean`): the rules of `≡` are not all generated
by `⟶`.

`Core.irrel` makes any two *proofs* of a proposition convertible, with no reduction
premise for either end. Take the proposition

    propPi = (x : Unit prop) → Unit prop        -- in `Sort prop` (`imax prop prop`)

and its two proofs `λ_. tt` and `λx. x`. Both are values: no rule of `⟶` has a `lam` at
its left endpoint (`red_not_lam`), so a `RedStar` chain from either is constant
(`redStar_of_lam`). `irrel` makes them convertible at `propPi`, so `ConvJoin` would give a
common reduct `v` with `v = λ_. tt` and `v = λx. x` — a contradiction.

The same happens with η (`Pi.eta` is a conversion rule, not a reduction: `f` and its
η-expansion are convertible with no reduct at all), so no side condition on the sort
repairs `ConvJoin`. The correct canonical-head obligation is the *algorithmic* one: the
whnf-interleaved conversion checker `DecConv` (`Obligations.lean`) decides irrelevance and
η by construction, and the sorting lemma's `ConvInjSort` is then read off the algorithm
(which, on two sorts, has no rule that could return `true`), not off a common reduct.
`convInjSort_of_join` (`Sorting.lean`) and `sortUnique_of_join` stay as the conditional
statements they are; their hypothesis is refuted, so they are not the route.

This file only adds the refutation; no statement of `Sorting.lean` or `Obligations.lean`
changes.
-/


namespace STC
namespace F0
namespace Spec

/-- The proposition `(x : Unit prop) → Unit prop`: `imax prop prop = prop`, so it is a
proposition and `irrel` applies to its proofs. -/
def propPi : Tm := .pi .prop (.unit .prop) (.unit .prop)

theorem propPi_ty {sg : Sig} : Derivable (F0 sg) (([] : Ctx) ⊢ propPi ∶ .sort .prop) := by
  have hctx : Derivable (F0 sg) (.wf ([.unit .prop] : Ctx)) := wf_cons wf_nil (unit_form wf_nil)
  exact ofRule (pi_in_F0 (Pi.form (i := .prop) (j := .prop) (s := .prop) rfl)) (by
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨unit_form wf_nil, unit_form hctx⟩)

/-- `λ_. tt ∶ (x : Unit prop) → Unit prop`. -/
theorem lam_tt_propPi {sg : Sig} :
    Derivable (F0 sg) (([] : Ctx) ⊢ .lam .tt ∶ propPi) := by
  have hctx : Derivable (F0 sg) (.wf ([.unit .prop] : Ctx)) := wf_cons wf_nil (unit_form wf_nil)
  have htt : Derivable (F0 sg) (([.unit .prop] : Ctx) ⊢ .tt ∶ .unit .prop) :=
    ofRule (unit_in_F0 (Unit.tt (s := .prop))) (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
      exact hctx)
  exact ofRule (pi_in_F0 (Pi.lam (s := .prop) (i := .prop))) (by
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨propPi_ty, unit_form wf_nil, htt⟩)

/-- `λx. x ∶ (x : Unit prop) → Unit prop`. -/
theorem lam_id_propPi {sg : Sig} :
    Derivable (F0 sg) (([] : Ctx) ⊢ .lam (.var 0) ∶ propPi) :=
  lam_id_unit

/-- **Two proofs of `propPi` are convertible by `irrel`**, and neither `λ` reduces. -/
theorem lam_tt_equiv_lam_id :
    Derivable (F0 ([] : Sig))
      (([] : Ctx) ⊢ .lam .tt ≡ .lam (.var 0) ∶ propPi) :=
  ofRule (core_in_F0 (Core.irrel (s := .prop) (A := propPi) (t := .lam .tt)
    (u := .lam (.var 0)) rfl)) (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨propPi_ty, lam_tt_propPi, lam_id_propPi⟩)

/-- **`ConvJoin` is false.** `irrel` relates the two distinct `λ`-proofs of the proposition
`(x : Unit prop) → Unit prop`; a `λ` has no reduct, so there is no common reduct. -/
theorem convJoin_false : ¬ ConvJoin ([] : Sig) := by
  intro hj
  obtain ⟨v, h1, h2⟩ := hj ([] : Ctx) (Tm.lam Tm.tt) (Tm.lam (Tm.var 0)) propPi
    lam_tt_equiv_lam_id
  have e1 : v = Tm.lam Tm.tt := redStar_of_lam h1
  have e2 : v = Tm.lam (Tm.var 0) := redStar_of_lam h2
  have h : Tm.lam Tm.tt = Tm.lam (Tm.var 0) := e1.symm.trans e2
  have hh : Tm.tt = Tm.var 0 := by injection h
  exact absurd hh (by intro hh; cases hh)

end Spec
end F0
end STC
