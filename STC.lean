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
import STC.F0.ConvJoin
import STC.F0.Typing
import STC.F0.TopSort
import STC.F0.Sanity

/-!
# STC: the F0 specification of the STC track

F0 is the fragment the first metatheory milestone (M0) is about: T0's rules plus `ULift`,
with regularity off and nothing of T1/T2. That is Core (contexts, universes, conversion,
definitional proof irrelevance), Π, Σ, Unit, Empty, Enum, `let`/annotation, closed
globals, observational `Eq`/`cast`/`transp`, and `ULift`. It keeps T0's hard content
(impredicative `Prop`, observational equality, η at Π/Σ/Unit/ULift) and leaves out what
adds risk without being needed for M0: regularity and `Desc`/`μ`. Its deliberate choices:

* **three closed sorts** `Sort 0 : Sort 1 : Sort 2` (no level variables, no level
  arguments on globals), `Sort 2` a type but not a term;
* **no quantities** (every binder is `ω`), sizes, `ν`, `Qty`, `split`, numerals, natives;
* **levelled** Π/Σ type equality: `A ≡ B` forms only between types of one sort, the
  formation that has a published model and normalisation proof; the kernels'
  cross-level rule is kept as a variant (`F0Cross`) for comparison;
* `ULift` and `letUnit` are in (the elaborator emits `letUnit`);
* four judgments: context formation, typing, conversion, one step of weak-head
  reduction.

M0 **states** the metatheory as `Prop`s (`F0/Obligations`) rather than proving it:
soundness/completeness/totality of a checker, consistency for an axiom-free signature,
weak-head normalisation, and decidability of conversion and typing. Not claimed:
consistency of full Wiz, soundness of the kernels themselves, strong normalisation.

The files:

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
* `F0/ConvJoin`: `ConvJoin` ("conversion has a common reduct") is **refuted** — `irrel`/`η`
  are conversions, not reductions, and the counterexample is strongly normalising
  (`convJoin_false`). The true conditional form of the reduction fragment is proved from
  strong normalisation + local confluence (Newman's lemma), and the sort-endpoint repair
  `ConvHead` — implied by `ConvJoin`, and enough for `ConvInjSort`/`SortUniqueAt`/
  `WhRed.empty_at_prop` — is recorded as the algorithmic obligation M1 proves;
* `F0/Typing`: what the two structural rules buy (both endpoints of any conversion typed,
  both endpoints of a `Pi.cong`/`Sigma.cong` conclusion typed from its own premises), and
  the remaining law obligation (`StructRenClosed`, `StructSubClosed`);
* `F0/TopSort`: the checked refutation of `TyUnique` at the top universe (the obligation
  is the corrected pair `TyUniqueTyped` + `TopSortUnique`);
* `F0/Obligations`: `Sound(F0)`, `Con(F0)`, `WHN`, `DecConv`, `DecTC` as `Prop`s, and the
  sorting lemma's supporting statements (`TyUnique`, `ConvInj*`);
* `F0/Sanity`: small derivations that witness that the rules are inhabited.

Not a default Lake target (`lake build STC` builds it); nothing imports it yet.
-/
