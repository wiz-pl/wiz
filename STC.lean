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
import STC.F0.Context
import STC.F0.ConvJoin
import STC.F0.DecConv
import STC.F0.Sanity

/-!
# STC: the F0 specification of the STC track

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
* `F0/Context`: context validity for `F0` (`Γ ⊢ J → ⊢ Γ`), extending the fragment's
  `F0Base_ctx` by the two `Struct` cases, with `F0_wf_tail` and the sorting reduction at a
  typing (`sortUniqueAt_of_typing`, no `⊢ Γ` hypothesis);
* `F0/ConvJoin`: the checked refutation of `ConvJoin` (proof irrelevance and η are
  conversions, not reductions: two `λ`-proofs of `(x : Unit prop) → Unit prop` are
  `irrel`-convertible and have no reduct), so the canonical-head obligation is the
  algorithmic `DecConv`, not reduction joinability;
* `F0/DecConv`: the algorithmic conversion: the `RedStar` algebra and the sound half of
  joinability, the canonical-head relation `CanonConv` (sound, trans-free, with the η/irrel
  guards), the checked sort case (`canonConv_sort_left`/`_right`/`_inj`: a term related to
  `Sort u` reduces to it), and the exact remaining gaps (`CanonConvComplete`,
  `SortNotProof`) with `ConvInjSort`/`SortUniqueAt`/`WhRed` reduced to them;
* `F0/Obligations`: `Sound(F0)`, `Con(F0)`, `WHN`, `DecConv`, `DecTC` as `Prop`s, and the
  sorting lemma's supporting statements (`TyUnique`, `ConvInj*`);
* `F0/Sanity`: small derivations that witness that the rules are inhabited.

Not a default Lake target; nothing imports it yet. The implementation note is
`/workspace/wiz-notes/stc-m0-impl.md`.
-/
