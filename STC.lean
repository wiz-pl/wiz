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

/-!
# STC: the F0 specification and the F1 phase layer of the STC track

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
remains the open `StructRenClosed`/`StructSubClosed` of `F0/Typing.lean`. The F1 *term*
formers `Ext`, strict `Glue` and `●` are not in this slice. The implementation note is
`/workspace/wiz-notes/agents/stc-f1.md`; the design paragraph is in
`/workspace/wiz-notes/stc-m0-spec.md` §3 (2026-11-14, agent `stc-f1`).

Not a default Lake target; nothing imports it yet. The F0 implementation note is
`/workspace/wiz-notes/stc-m0-impl.md`.
-/
