import STC.F0.Sort
import STC.F0.Syntax
import STC.F0.Reducts
import STC.F0.Spec.Fragments
import STC.F0.Laws
import STC.F0.Renaming
import STC.F0.Substitution
import STC.F0.WhRed
import STC.F0.Obligations
import STC.F0.Sorting
import STC.F0.Typing
import STC.F0.TopSort
import STC.F0.Sanity
import STC.F1.Cof
import STC.F1.Phase
import STC.F1.Sanity
import STC.F2.Sanity

/-!
# STC: the F0 specification, the F1 phase layer, and the F2 term formers

M0.1 of the design note `/workspace/wiz-notes/stc-m0-spec.md`:

* `F0/Sort`, `F0/Syntax`: the closed three sorts and the F0 terms (`letUnit` included);
* `F0/Spec/`: the four judgments and the rules as data, one file per former; `F0` is
  Core, Π, Σ, Unit, Empty, Enum, let, globals, Eq, **levelled** Eq-Π/Eq-Σ, ULift and the
  two structural conversion rules (`Struct`); `F0Base` is the same without `Struct`, and
  is what the laws below are proved for;
* `F0/Laws`: the renaming/substitution calculus on terms;
* `F0/Renaming`: the renaming lemma for `F0Base` (the first law, proved; the `Struct`
  closure is `StructRenClosed` in `F0/Typing`);
* `F0/Substitution`: the substitution lemma for `F0Base` (the second law, proved), with
  context validity (`F0Base_ctx`) and the `ty`/`eq`/`red`/`wf` companions;
* `F0/WhRed`: `WhRed` empty at propositions, modulo the sorting lemma `SortUniqueAt`;
* `F0/Spec/Struct`: the two structural conversion rules (`eqTyped`, `ctxConv`), licensed
  by `Sig.Closed`, that type the ends of conversions and move a context entry along one;
* `F0/Sorting`: `SortUniqueAt` reduced to `TyUnique` + `ConvInjSort`, with the exact gap
  (the `trans` case needs normalisation/confluence, not a rule) written down;
* `F0/Typing`: what the two structural rules buy (both endpoints of any conversion typed,
  both endpoints of a `Pi.cong`/`Sigma.cong` conclusion typed from its own premises), and
  the remaining law obligation (`StructRenClosed`, `StructSubClosed`);
* `F0/TopSort`: the checked refutation of `TyUnique` at the top universe (the obligation
  is the corrected pair `TyUniqueTyped` + `TopSortUnique`);
* `F0/Obligations`: `Sound(F0)`, `Con(F0)`, `WHN`, `DecConv`, `DecTC` as `Prop`s, and the
  sorting lemma's supporting statements (`TyUnique`, `ConvInj*`);
* `F0/Sanity`: small derivations that witness that the rules are inhabited.

## F1 (the phase layer, first slice)

`F1/` is the first piece of M4b beyond F0 — the cofibration/phase layer of
`/workspace/wiz-notes/stc-plan.md` M4b and the STC requirements R1–R3 in
`/workspace/wiz-notes/shared-cofib-layer.md`:

* `F1/Cof`: cofibrations over abstract phase atoms (`⊥`, `⊤`, atom, `∧`, `∨`), their
  valuation semantics, a **decidable entailment** `Cof.le` with soundness and
  completeness (`Cof.le_iff`), the distributive-lattice laws, and the independence
  sanity cases (distinct atoms are incomparable; no negation, so excluded middle
  is not even formable);
* `F1/Phase`: `[φ]` as an opaque proposition (`ph φ`), the phase rule set (`form`,
  `intro` from `φ ⊢ ψ`, and the computations `[⊥] ⟶ Empty`, `[⊤] ⟶ Unit`,
  `[φ ∧ ψ] ⟶ [φ] × [ψ]`), **renaming and substitution for `F1 := F0Base ∪ Phase`**
  (`F1_rename`, `F1_weakening`, `F1_subst`, `F1_subst_eq`, `F1_subst_red`), the derived
  rules (`⊤` intro, `⊥` elim, `∧` intro/elim, `∨` intro), and the open modality
  `○_φ A = (z : [φ]) → A` with `circ_form`, `circ_intro`, `circ_elim` and the
  restriction lemma **`circ_restrict`** (`φ ⊢ ψ ⟹ ○_ψ A ⟹ ○_φ A`);
* `F1/Sanity`: compile-time witnesses and `#eval` checks of the decision procedure.

`F1` is `F0Base ∪ Phase`: it does not include F0's two `Struct` rules, whose law closure
remains the open `StructRenClosed`/`StructSubClosed` of `F0/Typing.lean`. The implementation
note is `/workspace/wiz-notes/agents/stc-f1.md`; the design paragraph is in
`/workspace/wiz-notes/stc-m0-spec.md` §3 (2026-11-14, agent `stc-f1`).

## F2 (the term formers: `Ext 0`, strict `Glue`, `●`)

`F2/` adds the three term formers F1 deferred (`shared-cofib-layer.md` R3/R4,
`stc-plan.md` M4b), with their phase rules:

* `F2/Ext0`: `Ext 0 A φ a` (`{A ∣ φ ↦ a}`, stage 22c) with `extIn`/`extOut`, the
  boundary premise `a z ≡ t` under `z : [φ]`, `β` (`out (in t) ⟶ t`) and `η`
  (`in (out x) ≡ x`);
* `F2/Glue`: strict `Glue φ A T f` (stage 22d, `eqv = none`) with `glue`/`unglue`, the
  boundary premise `f z (t z) ≡ a` under `φ`, and `β`; the two *restriction* rules
  (`Glue ≡ T z`, `glue t a ≡ t z` under `φ`) are stated as `GlueRestr`, outside `F2`
  (see the gap below);
* `F2/Closed`: the closed modality `●_φ A` (stage 22e, R3) with `η●`/`⋆●`, a
  **non-dependent** eliminator and its two computation rules; the collapse
  `η● a ≡ ⋆●` under `φ` is `ClosedRestr`, outside `F2` for the same reason;
* `F2/Fragment`: `F2 = F1 ∪ Ext0 ∪ Glue ∪ Closed` and its membership lemmas;
* `F2/Laws`: **renaming and substitution for all three formers**
  (`ext0_renClosed`/`ext0_subClosed`, `glue_renClosed`/`glue_subClosed`,
  `closed_renClosed`/`closed_subClosed`) and the laws for `F2`
  (`F2_rename`, `F2_substs`, `F2_weakening`, `F2_subst`, `F2_subst_eq`,
  `F2_subst_red`);
* `F2/Ctx`: **context validity** for F1 and F2 (`F1_ctx`, `F2_ctx`), and the concrete
  `[a/0]` companions without the explicit `⊢ Γ` (`F1_subst'`, `F2_subst'`, …);
* `F2/Sanity`: `Ext 0` formation, `η●`/`⋆●`/elimination/computation for `●`.

The F2 syntax lives in `STC/F0/Syntax.lean` (the three formers are new `Tm`
constructors, which F0's rules and proofs do not inspect); `Tm.ren`/`Tm.sub` cover them
without binders. F0's and F1's theorems are untouched and still build.

**Gaps.** The two Glue restriction rules and the `●` collapse rule are not in `F2`:
their conclusions live under `z : [φ]`, and F0/F1's `Renames R j` is stated for `j`'s own
context, so their closure needs a relation between a renaming of `Γ` and one of
`φ :: Γ` — the same restricted-context/hole relation that `StructRenClosed` needs.
They are stated as the separate rule sets `GlueRestr`/`ClosedRestr`. `F2` is also still
`Struct`-free (`F0Base ∪ Phase ∪ …`), and the `●` eliminator is non-dependent; the
dependent one with its coherence premise is the next refinement. The implementation note
is `/workspace/wiz-notes/agents/stc-f2.md`.

Not a default Lake target; nothing imports it yet. The F0 implementation note is
`/workspace/wiz-notes/stc-m0-impl.md`.
-/
