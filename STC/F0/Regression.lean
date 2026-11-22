import STC.F0.Obligations
import STC.F0.Sanity
/-!
# Regression: the signature hypotheses on the M0 obligations are load-bearing

`Obligations.lean`'s `Con` used to say "an axiom-free signature has no closed proof of
`Empty prop`", with no hypothesis on the signature. That statement is **false**, and this
file is the checked witness. `Global.const` (`Spec/Global.lean`) types a constant at
`d.type` for any declaration `d` with `sg.find? c = some d`; it does not check that
`d.type` is a sort, and `Global.delta` does not check that `d.value` is at `d.type`. So

    badSig = [{ name := "bad", type := Empty prop, value := some tt }]

is `AxiomFree` (and `Sig.Closed`), and `[] ⊢ const "bad" ∶ Empty prop` holds
(`badSig_derives_empty`). The historical, unrestricted statement is kept here as
`ConUnrestricted` and refuted (`conUnrestricted_false`): it must not be restored.

`SigWF F0` (`Spec/Fragments.lean`) rules `badSig` out for the right reason. Its `defn`
constructor checks a value at the declared type **in the signature before the declaration**,
so `SigWF F0 badSig` would already give `[] ⊢ tt ∶ Empty prop` in `F0 []`
(`badSig_sigWF_gives_empty`). With the repaired `Con` at the empty signature — which is
`SigWF`, closed and axiom-free — that is a contradiction (`badSig_not_sigWF_of_con`). The
hypothesis is therefore not a syntactic filter: it fails exactly when the fragment is
already inconsistent.

The last section checks that the hypotheses are inhabited by a non-empty signature
(`goodSig`), so the repaired obligations are not vacuous.
-/

namespace STC
namespace F0
namespace Spec

/-! ## The counterexample -/

/-- The malformed declaration behind the counterexample: `bad : Empty prop`, with value
`tt`. The value is not a proof of `Empty prop`; `Global.const` does not look. -/
def badDecl : Decl :=
  { name := "bad", type := Tm.empty .prop, value := some Tm.tt }

/-- The one-declaration signature `[bad]`. It is **not** `SigWF`: the `defn` clause would
require `[] ⊢ tt ∶ Empty prop` in the signature before the declaration (`F0 []`). -/
def badSig : Sig := [badDecl]

/-- The lookup `Global.const` uses. For any declaration, a singleton signature finds its
name at its head; `LawfulBEq String` gives `d.name == d.name`. -/
theorem find_singleton (d : Decl) : ([d] : Sig).find? d.name = some d := by
  simp [Sig.find?, List.find?, beq_self_eq_true]

theorem badSig_find : badSig.find? "bad" = some badDecl := by
  simpa [badSig, badDecl] using find_singleton badDecl

/-- `badSig` is axiom-free: its only declaration has a value. -/
theorem badSig_axiomFree : AxiomFree badSig := by
  intro d hd
  simp only [badSig, List.mem_cons, List.mem_nil_iff, or_false] at hd
  subst hd
  rfl

/-- `badSig` is a closed signature: `Empty prop` and `tt` are closed terms. So the only
hypothesis of the repaired `Con` that fails for it is `SigWF`; the counterexample is not
beside the point of the repair. -/
theorem badSig_closed : Sig.Closed badSig := by
  intro d hd σ
  simp only [badSig, List.mem_cons, List.mem_nil_iff, or_false] at hd
  subst hd
  refine ⟨?_, ?_⟩
  · rfl
  · intro v hv
    simp only [badDecl, Option.some.injEq] at hv
    rw [← hv]
    rfl

/-- **The counterexample**: the fragment proves `const "bad" ∶ Empty prop` from a signature
that declares exactly that type and no axiom. This is a derivation, not a model-theoretic
argument: `Global.const` and `Core.wfNil`. -/
theorem badSig_derives_empty :
    Derivable (F0 badSig) (([] : Ctx) ⊢ Tm.const "bad" ∶ Tm.empty .prop) := by
  refine ofRule (global_in_F0 (Global.const (sg := badSig) (c := "bad") (d := badDecl)
    badSig_find)) ?_
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
  exact wf_nil

/-- **The old, unrestricted `Con`** — the statement as it stood in `Obligations.lean` before
the `SigWF` hypothesis was added. Kept only as a refutation target. -/
def ConUnrestricted (sg : Sig) : Prop :=
  AxiomFree sg → ∀ t : Tm, ¬ Derivable (F0 sg) (([] : Ctx) ⊢ t ∶ .empty .prop)

/-- **The old `Con` is false**, refuted by `badSig`: do not weaken the repaired statement
back to this shape. -/
theorem conUnrestricted_false : ¬ ConUnrestricted badSig := by
  intro h
  exact h badSig_axiomFree (Tm.const "bad") badSig_derives_empty

/-- `SigWF`'s `defn` premise for `badSig`, extracted: it is a closed proof of `Empty prop`
in the empty signature. So `badSig` is only well formed if the fragment is already
inconsistent — the hypothesis is the consistency assumption, not a syntactic filter. -/
theorem badSig_sigWF_gives_empty (h : SigWF F0 badSig) :
    Derivable (F0 ([] : Sig)) (([] : Ctx) ⊢ Tm.tt ∶ Tm.empty .prop) := by
  unfold badSig at h
  cases h with
  | axiom _ _ hval _ => simp [badDecl] at hval
  | defn _ _ hval hty _ =>
      simp only [badDecl, Option.some.injEq] at hval
      subst hval
      simpa [badDecl] using hty

/-- **The repaired `Con` excludes the counterexample.** If `Con` holds at the empty
signature (it is `SigWF`, closed and axiom-free), `badSig` cannot be `SigWF`: the extracted
premise `badSig_sigWF_gives_empty` is exactly the judgment `Con []` denies. -/
theorem badSig_not_sigWF_of_con (hcon : Con ([] : Sig)) : ¬ SigWF F0 badSig := by
  intro h
  exact hcon SigWF.nil (by intro d hd; simp at hd) (by intro d hd; simp at hd) Tm.tt
    (badSig_sigWF_gives_empty h)

/-! ## Non-vacuity: the hypotheses are inhabited by a non-empty signature -/

/-- A well-formed definition: `u : Unit prop := tt`. -/
def goodDecl : Decl :=
  { name := "u", type := Tm.unit .prop, value := some Tm.tt }

def goodSig : Sig := [goodDecl]

theorem goodSig_axiomFree : AxiomFree goodSig := by
  intro d hd
  simp only [goodSig, List.mem_cons, List.mem_nil_iff, or_false] at hd
  subst hd
  rfl

theorem goodSig_closed : Sig.Closed goodSig := by
  intro d hd σ
  simp only [goodSig, List.mem_cons, List.mem_nil_iff, or_false] at hd
  subst hd
  refine ⟨?_, ?_⟩
  · rfl
  · intro v hv
    simp only [goodDecl, Option.some.injEq] at hv
    rw [← hv]
    rfl

/-- `goodSig` is `SigWF`: the declared type `Unit prop` is a sort in the empty signature,
and its value `tt` is typed at it. -/
theorem goodSig_sigWF : SigWF F0 goodSig := by
  refine SigWF.defn (T := F0) (sg := ([] : Sig)) (d := goodDecl) (s := .prop) (v := .tt)
    SigWF.nil rfl rfl ?_ ?_
  · exact unit_form (sg := ([] : Sig)) (Γ := []) wf_nil
  · exact tt_prop (sg := ([] : Sig))

/-- The three hypotheses of the repaired obligations are jointly satisfiable, with a
non-empty signature. So `Con`/`SoundF0`/`WHN`/`DecConv`/`DecTC` are not vacuous statements
about a signature class that happens to be empty. -/
theorem sigWF_closed_axiomFree_inhabited :
    ∃ sg : Sig, SigWF F0 sg ∧ Sig.Closed sg ∧ AxiomFree sg :=
  ⟨goodSig, goodSig_sigWF, goodSig_closed, goodSig_axiomFree⟩

end Spec
end F0
end STC
