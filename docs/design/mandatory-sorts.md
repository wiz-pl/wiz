# Mandatory component sorts

Every `Π` and `Σ` in the Wiz core carries the sorts of its two components, and every
`ULift` carries the sort of its content. The sorts are written in the term, never
recovered by evaluation, and both kernels check each one against the sort they infer for
its own component. Evaluation reads them to decide whether a type is a proposition and
whether a `cast` computes. This closes three issues of the [soundness ledger](../Status.md):
U5 (a `Π`/`Σ` without its sort made type equality stuck), U5b (a `cast` at such a type
computed to an ill-typed term) and the meta-review's D2 (the structural casts at
`Π`/`Σ`/`ULift` computed across sorts, so subject reduction failed). The change merged as
PR #203 (2026-11-14). The specification is in [CoreSpec §2](../CoreSpec.md) ("Mandatory
sorts"), §8.3 and §8.4.

## The problem

Before this change a `Π`/`Σ` carried an optional annotation `s : Option Level`, its
combined sort (`imax i j` for a `Π`, `max i j` for a `Σ`). Three things went wrong.

* **U5: incompleteness.** `propSort?` decides whether a type is a proposition. For a
  `Π`/`Σ` it could only read the annotation, because a neutral component carries no type.
  An unannotated `(Unit → Unit) = (Unit → Unit)` was stuck where the annotated copy
  computed. Conversion did not compare annotations, so two convertible types could take
  different branches of `vEqType` and `vCast`. Conversion was then not a congruence.
* **U5b: an ill-typed reduct.** `cast` at a `Π`/`Σ` of unknown sort applied its
  structural rule, which projects the equation `e.1`, while the equation itself was stuck
  (`vEqType` had no sort to decide on). The result projected a `reflTy` and was rejected
  when checked again.
* **D2 (meta-review): subject reduction.** The `Π`, `Σ` and `ULift` casts computed
  whatever the sorts of the components. The reduct casts between the domains (or the
  contents), so it could form `cast` between types in different universes, which the
  typing rule for `cast` does not allow. An accepted term could have a normal form that
  the kernel rejects.

A combined annotation is not enough to fix D2. `imax 2 2` passed as the sort of
`X → Type` with `X : Sort 1`, because the check compared only the combination, while
splitting it would claim the domain is in `Sort 2`. A normalised level cannot be split
at all.

## The rule

The term change (`Wiz/Core/Term.lean`, `Wiz/Core/Value.lean`):

```
structure BinderSorts where dom : Level; cod : Level
| pi (x) (bi) (q) (dom cod : Term) (σ : BinderSorts)
| sigma (x) (q) (fst snd : Term) (σ : BinderSorts)
| ulift (k l : Level) (A : Term)          -- A : Sort k, ULift A : Sort l
```

`BinderSorts.piSort σ` is `imax σ.dom σ.cod` and `BinderSorts.sigmaSort σ` is
`max σ.dom σ.cod`. In `selfhost/Kernel.wiz` the former constructors `pi`, `piq`, `sigma`,
`sigmaq` and the `sorted` wrapper are folded into `pi (q) (i j : Lvl) (dom cod)` and
`sigma (q) (i j : Lvl) (fst snd)`, and the values into `vpi q i j …`, `vsigma q i j …` and
`vulift k l A`. "Unsorted" cannot be represented after the frontend.

**Formation, component by component** (both kernels):

```
Γ ⊢ A ⇒ Sort i'   i ≡ i'   Γ, x:A ⊢ B ⇒ Sort j'   j ≡ j'   no hole in ⟨i, j⟩
────────────────────────────────────────────────────────────────────────────
Γ ⊢ (q x : A) →^⟨i,j⟩ B ⇒ Sort (imax i j)            (Σ: Sort (max i j))

Γ ⊢ A ⇒ Sort k'   k ≡ k'
──────────────────────────
Γ ⊢ ULift.{k,l} A ⇒ Sort l
```

`≡` on levels is `Level.equiv`, with a fast path when the two are syntactically equal.
The Lean kernel does this in `checkComponentSort` (`Wiz/Core/Check.lean`), the
self-hosted kernel in `componentSort` and `former` (`selfhost/Kernel.wiz`).

**Conversion compares the sorts.** `convTy` and `subTy` compare `σ` componentwise
(`sameSorts` in `Wiz/Core/Conv.lean` and in `Kernel.wiz`). On well-typed types this is
redundant: convertible components have equivalent sorts. It is kept so that
"convertible types get the same `propSort?`, hence the same `vEqType` and `vCast`
decision" holds by construction.

**What evaluation reads** (`sortProp?` and `propSort?` in `Wiz/Core/Eval.lean`;
`sortProp` and `propSort` in `Kernel.wiz`):

* a `Π` is a proposition iff `σ.cod` is `0`, and is known not to be one iff `σ.cod` is
  never `0`;
* a `Σ` is a proposition iff both components are `0`, and not one iff either is never `0`;
* otherwise the answer is unknown. With the sorts mandatory, "unknown" means only "depends
  on a level parameter that may be `0`".

**The casts** (`vCast` in `Eval.lean`, `castComputes` and `vCastW` in `Kernel.wiz`; CoreSpec
§8.4):

```
cast (Π^⟨i₁,j₁⟩ q A₁ B₁) (Π^⟨i₂,j₂⟩ q' A₂ B₂) e f  computes iff
    q ≡ q', both sides are known non-propositions, i₁ ≡ i₂ and j₁ ≡ j₂     (Σ: the same)
cast (ULift.{k,l} A) (ULift.{k',l'} B) e t  computes iff
    l is never 0, l ≡ l' and k ≡ k'
otherwise the cast is stuck
```

Every test here is stable under level substitution: `equiv`, `isZero` and `isNeverZero`
hold at every instance when they hold generically. An unknown sort is stuck generically
and may compute at an instance, which is the allowed direction (stuck becomes a reduct).
The U5b gate stays for that case: at a `Π`/`Σ` whose sort depends on a level variable the
cast is stuck exactly when the equation it goes along is.

The same information lets `vEq`'s `Σ` rule see a neutral proposition. It reads whether a
component is a proposition off `σ` instead of the component's head, so an equation at
`(x : A) × P x` with `P x` a neutral proposition now computes (CoreSpec §8.2; this closes
the neutral case of Status F13).

## Who writes the sorts

* **The kernels' own templates** write them from levels they already have: the
  description templates (`interpTm`, `allTm`, `hypsTm`, `mapTm` in
  `Wiz/Core/Templates.lean`), the motive and method types of the eliminators
  (`indMotiveTy`, `indMethodTy`, `delimMotiveTy`, `delimMethodTys`, `sfixFunTy`,
  `scaseMethodTy`, `coitStateTy`, `coitStepTy`, `scofixFunTy` in `Conv.lean`), the
  equality templates in `Eval.lean` (`vIff`, `vEq`, `vEqType`) and `transp`'s motive type
  in `Check.lean`. `Kernel.wiz` writes the same templates with closed numerals (its `TS`
  and `tpi` helpers). Because each component's sort is written on its own, a numeral
  needs no decomposition, and the two kernels agree.
* **The elaborator** writes the sorts it knows (a surface `(x : A) → B` gets them from the
  levels that elaborating `A` and `B` returns) and a hole, `Level.hole`, for the others.
  `Zonk` turns a sort with an unsolved level metavariable into a hole. Unification ignores
  `σ`.
* **The sorts pass** fills every hole before the kernel sees the declaration. It is the
  marking pass of the [proof marker](prf-marker.md) in a mode that places no markers
  (`Ctx.sortsOnly`; `Decl.withSorts` in `Wiz/Elab/Mark.lean`). It is total: it goes inside
  proofs and under every `fun`, in the type, the value, the implementation and the
  witness, and it skips subterms with no hole. In the self-hosted toolchain the same pass
  runs at `TCtx.pm` 4 and 5 (`sortsTy`, `sortsClosed`, `sortsInfer`, `sortsTyIn`, guarded
  by `tmHasHole`).
* **The kernels reject a hole** (`checkComponentSort`, `componentSort`, and
  `checkHeader`'s "without its sorts"). The pass is untrusted: a sort it fills wrongly is
  a kernel error, never an acceptance.

The pass has to be total in one step. An earlier version filled the sorts it could see and
left proofs alone. Then `cast (U0 → U0) (U0 → U0) (reflTy (U0 → U0)) (fun x => x)` was
rejected: the endpoints were sorted and computed to a `Σ` of equations, while the type of
`reflTy`'s argument, inside the proof, stayed stuck. Partial filling was worse than none.

## Alternatives considered

* **Keep one combined annotation and make it mandatory.** It closes U5 but not D2: the
  domain's sort cannot be recovered from `imax i j`.
* **Read the components' sorts off their heads when the cast fires.** Evaluation has no
  context, and a type variable's sort is unknown. The payload casts of `lib/Vec.wiz`
  (`(x : A) × …` with `A : Type u`) became stuck, and lemmas such as `Vec.get_cons_zero`
  failed.
* **Compute unless the sorts are known and different.** Unstable under substitution: a
  cast at type variables computes, and after substituting closed types of different sorts
  the same cast is stuck.
* **Form `cast` across sorts instead of getting stuck** (the meta-review's other option
  for D2). Not taken: stuck matches the rule of the specification checker in `WizMeta/`.
* **Keep a `sorted` wrapper in `Kernel.wiz` and reject a bare `Π`.** The value would still
  need an optional sort. Folding the sorts into the constructor makes the bad state
  unrepresentable.
* **A reserved metavariable as the hole** instead of a new `Level.hole` constructor. The
  constructor was chosen (`Lvl.lhole` in `Kernel.wiz`).

The `Π`/`Σ` type-equality rule stays **Cross** (CoreSpec §8.3): `A ≡ B` at two `Π` types
decomposes whatever their sorts are, so a reduct can relate domains in different sorts. The
**Levelled** variant (decompose only when `i ≡ i'` and `j ≡ j'`, as in CCobs [PT23]) needs
the component sorts and is now implementable. It exists in the specification checker as an
option (`eqTyLevelled`) and is tested there, but neither kernel uses it.

## Limits and what remains open

* **`Level.equiv` is incomplete.** It splits on parameters under `imax` with a fuel of 8.
  The structural check could reject a valid term whose sort is a deep `imax` tower over
  many parameters. Making `equiv` complete was not part of this change.
* **The elaborator sees holes until the pass runs.** While elaborating, a `Π`/`Σ` with a
  hole has an unknown `propSort?`, so an equation at it stays stuck, as before. No new
  elaboration failures, and no new successes, until builders write more sorts eagerly.
* **`λ` does not carry its domain's sort.** Relevance marks on binders are a later step
  (see [the proof marker](prf-marker.md)).
* **The specification checker** (`WizMeta/`) keeps a single optional sort per `Π`/`Σ`;
  the kernels' terms are translated with `imax`/`max` of the two components, and
  `Opts.sortsOptional` is off by default.
* [Status.md](../Status.md) §4 still lists U5, U5b and D2 (meta-review) as open; its
  header records that #203 merged and that those rows are awaiting a refresh.

## Tests

* Group `selfhost` (`Tests/Groups/SelfHost.lean`): "D2 (closed by mandatory sorts): a
  Π/Σ/ULift cast across components of different sorts is stuck, and its normal form is
  accepted (both kernels)"; "U5b: a cast at a Π/Σ whose sort depends on a level variable
  is stuck, as the equation it goes along is; a Π without its sorts is rejected (both
  kernels)"; and the differential test "the Wiz kernel agrees with the Lean kernel (400
  random terms)", in which each side fills holes with its own sorts pass.
* Group `check: structural types` (`Tests/Check.lean`): "mandatory sorts: every
  description template is a well-typed term of its type, its written sorts included" and
  "mandatory sorts: a declaration with a sort hole is rejected, even with sortHolesOk set".
* Group `observational equality` (`Tests/Groups/Ott.lean`): "an equation at a Σ with a
  neutral proof component (nu-transp; closed by mandatory sorts)", and the cases "a
  definition's type carries its sort" and "a constructor's type carries its sort".
* Group `scaling` (`Tests/Scaling.lean`): "erasure believes a Π's sort, and the kernel
  rejects a wrong one wherever erasure could read it" and "a wrong sort note on a Π into an
  equation is rejected by the kernel".
* Group `meta` (`Tests/Meta.lean`): "the spec's own rules: a Π/Σ carries its sort, and it
  is checked"; "review: a structural cast whose components are in different sorts is stuck
  (its reduct would cast across universes)"; and the Cross/Levelled comparison cases.
