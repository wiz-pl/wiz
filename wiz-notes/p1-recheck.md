# P1 recheck: glued equations against master 627b48f6

agent p1-recheck, 2026-11-15. Worktree `/workspace/wt/p1-recheck`, branch
`agent/p1-recheck`, from `origin/master` `627b48f6`. Assessment only; no implementation.
Probes used the `wiz` built at exactly this commit in `/workspace/wt/hdl-stream`
(`.lake/build/bin/wiz`, 17:37) in the light slot (2 GB cap, below the 3 GB budget).
Here **P1** means *glued equations* (`kernel-eval.md` §4, `glued-eq.md`), not the
regularity side-condition P1 of `p1-stable.md`.

## 0. Verdict in one paragraph

**Still wanted, but narrower than the wishful entry says.** P1 is not superseded by the
`rfl`/`Thunk` work: #256 fixed `rfl` *after* an equation has computed at a data type, and
#286 fixed η-splitting at Σ/Π; neither shares an equation *type* between uses. On master a
closed equation reused N times still costs one full evaluation per use (measured: 8.56 s /
13.45 s / 23.12 s for 1 / 2 / 4 uses of a 200 000-step equation), and composing two
already-checked ranges costs 17.2 s against 4.4 s for the two ranges alone. `#257`
(`Eq.trans h e1`) still fails; that one has a cheaper possible fix, but the first two are
P1-shaped and real. P1 is **not** a fix for G11's memory (`F6`: glued history) or for one
long run; the UART still needs ranges + a cheap composition (P1) or `native_refl`. Do **not** reopen #155 as
it stands (1072 commits behind, and its `rflWritten?`/quote choices predate #256/#286);
reimplement the revised slice on master.

**No site was found where P1 as designed is unsound.** Six places must be *redesigned*
(text/ordering, not the congruence argument): the memoisation premise, the quote rule
under `quoteErasesProofs`, the `rfl` sub-plan (`markDataEq` now does it), the selfhost
`memo` (still identity), the extra mandatory-sorts/marking forcing sites, and the
unifier's "both sides are glued" assumption (a glued equation must also meet a *stuck*
one, or the elaborator must never force the expected equation). Details in §5.

## 1. What P1 is, precisely

### 1.1 A glued equation

An equation is built by `eval (.eq A a b)`. Today this calls `vEq g A a b` immediately.
`vEq` may compute (True/False, a Π for funext, a Σ for the Σ rule, `vIff` at `Sort 0`),
or stay stuck as `.neutral (.eq A a b)`. Type evaluation therefore *is* equation
computation: `eval (.pi …)` evaluates the domain, `Closure.inst` of a codomain that is an
equation, `headType` of a global whose type is an equation, and `Sorts.type` all reach
`vEq` (F5 of `kernel-eval.md`).

P1 makes `eval (.eq A a b)` build a new value

```lean
| lazyEq (A a b : Val R) (val : Thunk (Val R))
```

with the sides evaluated (cheap: glued `unfold`s) and `vEq` in the thunk. `whnf` forces
it. `vEq` itself, and its rules (#111, #123, the Σ/proof and ULift rules), do not change.
An equation stays strict (no `lazyEq`) at a proposition known from `propSort?`, under
`g.eager` (`nf`/`#reduce`), and under `!g.lazyProofs` (`--eager-proofs`; a new
`--eager-eqs`/`Globals.lazyEqs` also turns it off for the differential test).

There are three ways to use it without forcing:

1. **Sort.** An equation is always a proposition: `propSort?`, `typeSort?`, `isProp`,
   `Ctx.sortOf?`, erasure answer Prop/Sort 0 without running `vEq`.
2. **Sides.** Conversion and unification compare two equations side by side
   (congruence of `=`): `convGlued` on two `lazyEq`s compares `A`, `a`, `b`; `subTy`
   tries that first; `unifyGlued` unifies the three components.
3. **Read-back.** `quote` writes the equation as written, `.eq A a b` (see §5.2), which
   evaluates back to the same `lazyEq`.

### 1.2 Where it lands

* `Sigma`: the `Val` *type* former is unchanged. What changes is that the equation
  former's *result* no longer has to be a computed `Val.sigma`/`Val.unit`/`Val.empty`;
  it is a `lazyEq`. `Val.lazyEq` carries no spine (types are not applied or projected).
  The computed value of a forced equation at a data type still gets #256's
  `markDataEq` marker (`Eval.lean:239-248, 846-848`).
* `conv`: a new case in `convGlued` (`Conv.lean:479-492`) for
  `lazyEq A a b` vs `lazyEq A' a' b'`:
  `convTy A A' && conv A a a' && conv A b b'`. Every "no" falls through to the existing
  `r || conv … (whnf a) (whnf b)` (or `subTy`'s old path, or `unify`'s force).
* `quote`: folded `.eq (quote A) (quote a) (quote b)`; #256's `quoteEqs` path already
  reads a *computed data* equation back as `.eq` (`Eval.lean:1431-1434`), so folded and
  computed read-backs agree in the elaborator.
* `check`/`Mark`: only introduction forms (`fun`, a pair, `()`) need to see what an
  equation computes to; the catch-all goes to `infer` + `subTy` with the type still glued.

### 1.3 The soundness invariant

The only new "equal" answer is **congruence of `=`**: if `A ≡ A'`, `a ≡ a'`, `b ≡ b'`,
then `(a =_A b) ≡ (a' =_A' b')`. That is admissible in the declarative system (it is the
congruence rule of the `=` former, already implemented for *stuck* equations by
`convNe`'s `.eq` case, `Conv.lean:537`). The algorithm's obligation is:

> (S) `vEq` is a function of `(A,a,b)` up to conversion: convertible inputs give
> convertible results.

Given (S), folding before/after forcing cannot change an answer, because every "no" from
the glued path falls back to the forced comparison, and every "yes" is either the same
forced answer or the congruence instance. (S) holds because `vEq` decides by `whnf`
shapes, numerals and `propSort?`, all invariant under conversion; the mandatory-sorts
work now *enforces* the `propSort?` half (`convTy` compares the `BinderSorts`,
`Conv.lean:423-432`). The one known yes-flip is `conv`'s `unCast` (InReg_conv,
`Conv.lean:321, 469-475`), where a stuck cast is convertible to its argument; that is the
congruence instance of (S), not an unsoundness.

Two side conditions are not about congruence:
* **Read-back well-formedness.** A folded `.eq P x y` with `P : Prop` is rejected by the
  kernel's formation rule (`inferCore .eq` requires a type in `Type u`,
  `Check.lean:823-826`). Therefore `vEqL` must stay strict whenever `propSort?` *sees* a
  proposition (`some true`), as designed (`glued-eq.md` §2). At a sort parameter or a
  neutral proposition that `propSort?` cannot see, the situation is more delicate: today
  `vEq` may still compute by shape (a Π/Σ) or stay stuck, whereas a folded `.eq A a b`
  is ill-typed if `A` later instantiates to a proposition. That is the design's known
  sort-parameter caveat (`glued-eq-review.md`, "Folded read-back at a sort parameter"):
  a completeness/read-back issue, not a new `False`; the strict-at-`some true` rule must
  not be weakened to paper over it.
* **Purity/memoisation.** Forcing gives `vEq`'s value for the sides captured at build
  time. Purity alone makes that sound; memoisation is needed only for the cost (§5.1).

## 2. Audit of the current tree

Numbers: `Value.lean`, `Eval.lean`, `Conv.lean`, `Check.lean`, `Unify.lean`,
`Elab/Term.lean`, `Elab/Mark.lean`, `Elab/Basic.lean`, `Compiler/Erase.lean`,
`selfhost/Kernel.wiz`, `selfhost/Frontend.wiz` at 627b48f6.

| # | site (file:line) | what changed since the design | verdict |
|---|---|---|---|
| 1 | `Value.lean:29-56` `memoThunk`; uses `Eval.lean:68,80,93,288,443-444,703-705` | Lean's `Thunk` is **not** memoising; #256 added an `unsafe` memo cell. The design's `lazyEq … (Thunk.mk …)` and its "the thunk is memoised" sentence are wrong. | **helps** (the primitive exists) / **design conflict** (use `memoThunk`; rewrite §4.2(4) and termination) |
| 2 | `Eval.lean:214-248, 838-848` `eqSigmaSides?` / `eqDataMark` / `markDataEq`; `Eval.lean:1431-1434` `quoteEqs`; `Term.lean:619-624`; `Basic.lean:447-449` | #256 keeps a *computed data* equation's original sides in the outermost payload Σ and reads it back as `.eq` in the elaborator; `rfl` recovers it. | **partly supersedes P1's `rfl` sub-plan**; **neutral** for soundness; the quote/`rfl` design must be rewritten |
| 3 | `Value.lean:73-79` `Head.prf`; `Eval.lean:278-280, 312-323, 422-430`; `Conv.lean:296-301, 514-548`; `Check.lean:400-430` | proofs are suspended and never evaluated; `cast`'s equation and `transp`'s proofs are suspended; proof irrelevance comes first in `conv`. | **helps** (equations at Prop stay cheap; proofs never force them); **neutral** soundness |
| 4 | `Eval.lean:795-857` `vEq`; `175-184` `propSort?`; `Conv.lean:35-43` `headType` | `vEq` at a proposition returns `True` (`819`); ULift prop rule (`809-813`); Σ rule carries `eqReductMark` (`838-841`); `#123` uses `reflTy` for a proof component. | **neutral/helps**: `vEqL`'s ULift exception is now subsumed by `propSort?` (`175-184`); the strict-at-Prop rule is still required |
| 5 | `Value.lean:85-88`; `Conv.lean:196-202, 240-260, 423-432`; `Eval.lean:175-184`; `Check.lean:435-444` | mandatory `BinderSorts` on `Π`/`Σ`; `typeSort?`/`propSort?` read annotations; `convTy` compares the sorts. | **helps** (S now enforced for `propSort?`); **needs** a `lazyEq` fast path in `propSort?`, `typeSort?`, `isProp`, `Ctx.sortOf?` |
| 6 | `Check.lean:435-444` `Ctx.sortOf?`; `455` `isPropTy`; `469-470` `isProofTy`; `477-481` `modeAt` | these were added by mandatory sorts (#154) *after* the design: `sortOf?` starts with `match whnf ty`, and `check` calls `isPropTy` before its match. | **new forcing site / conflicts with the design's single kernel-`check` guard**: add `lazyEq => some 0` before `whnf`, or every `check` forces |
| 7 | `Check.lean:532-558` `check`/`checkU`/`checkCore` (`match t, whnf ty`) | the intro-rule list is now `prf`, `up`, `lam`, `letE`, `pair`, `tt`, `letUnit`, `sizeLt`, `dret/darg/drec/dhrec`, `con`, `cocon`; the design's "force only for fun/pair/()" is still the right list (plus `prf` passes through), but the code is different. | **adaptation**: keep `ty` glued except for `lam`/`pair`/`tt`; pass the original `ty` through `letE`, `letUnit` |
| 8 | `Elab/Mark.lean:44-52` `decide`, `90-93` `checkCore`, `402-427` `withSorts` (`ty` Thunk at 414, `needsType` at 421-425) | the marking pass computes a sort before every check; `checkCore` does `match t, whnf ty`. This is the pass that marks every proof term. | **new forcing site / conflicts with the design's list**: `decide` must see `lazyEq` as Prop without forcing; `checkCore` must not force for a non-intro term. #155's refresh did this; the design predates it |
| 9 | `Elab/Basic.lean:470-488` `Sorts.type`; `504-511` `Sorts.value` | `Sorts.type` already answers `some 0` for a syntactic `.eq`/`.eqTy` (`482-484`), so one F1 run is already gone; `Sorts.value` still `match t, whnf ty` (forces). | **helps** (`Sorts.type`); **adaptation** (`Sorts.value` needs a `lazyEq` case before the `whnf`) |
| 10 | `Conv.lean:299-339` `conv` | proof irrelevance first (`300-301`), `convGlued` before `whnf` (`308`), `unCast` before the shape match (`321`), and #286's `neutralsAgree` before η at Π/Σ (`323-339`). | **neutral**: `neutralsAgree` only looks at `.neutral`, so a `lazyEq` is unaffected; the `unCast` yes-flip is the design's known caveat; the proof-irrelevance first line needs `isProp` to see `lazyEq` |
| 11 | `Conv.lean:398-442` `convTy`, `409-419` Cast-Refl at every type while both sides are propositions | new after the design (`b1ee61d9`); `regularity := .full` for two propositions. | **neutral** for P1 soundness (`conv` is trusted; the congruence premise is still `conv`); the `convGlued` call at `399` already runs first, so keep it there for two `lazyEq` types |
| 12 | `Conv.lean:629-645` `subTy` | starts `match whnf A, whnf B`; new size/`sameSorts` cases. | **needs the design's `lazyEq` shortcut**; without it every `subTy` of two equations computes both |
| 13 | `Conv.lean:479-492` `convGlued`; `514-548` `convNe` | `convGlued` handles `unfold`/`lazyInd` only; `convNe` already has the `.eq` congruence (`537`) and proof heads (`518-548`). | **adaptation**: add `lazyEq`/`lazyEq`; consider `lazyEq` vs `.neutral (.eq …)` (see §5.6) |
| 14 | `Check.lean:1329-1338` `checkImplAgrees`; `1329+` | new consumer: compares a value with its compiled impl, starting `sortOf? ty0` and `conv ty0 value impl`. | **helps** (a glued type is cheap); **neutral** soundness (a prop-valued definition is a proof); needs `sortOf?` |
| 15 | `Compiler/Erase.lean:274-280` `erasable` | `match whnf ty` — will force every equation type in every binder type. | **adaptation**: `lazyEq => true` before `whnf`, as designed |
| 16 | `Elab/Unify.lean:86-104` `forceMeta`/`force`; `108-117` `recomputeEq?`; `313-314` `rename`; `512-515` `reevalStale?`; `562-577` `unify`; `706-788` `unifyGlued`; `864-879` `unifyHead` | `force` unfolds `unfold`/`lazyInd`; `recomputeEq?` matches only `.neutral (.eq ..)`; `rename` forces `lazyInd`; `unify` first calls `unifyGlued` on `forceMeta` values; #230/#286 changed lazy delta/failure cache. | **adaptation, with one design gap**: add `lazyEq` to `force`/`rename`/`unifyGlued`/`recomputeEq?`; the `Eq.trans`/`#257` shape needs `lazyEq` vs a *stuck* `.eq` too, or the elaborator must never force the expected equation (§5.6) |
| 17 | `Elab/Term.lean:120-149` `insertImplicits`/`trailingInst`; `1194-1205` `sameDefinition?`; `1219-1237` `check`; `1455-1462` `checkData?` | every identifier goes through `infer` + `insertImplicits`, which starts `force ty`; `check` starts `checkData?`, which forces expected. This was the prototype's first miss (AxUse ~1.3 s/use). | **required for the measured gain**: early return on `lazyEq` in `insertImplicits`/`trailingInst`, and the ident/app/hole/paren shortcut before `checkData?`/`sameDefinition?`; **not optional** if #257 is to be fixed |
| 18 | `Elab/Term.lean:926-995` `sameSides`/`rflProof`; `1323-1362` `term.refl`; `1364-1376` `term.rfl`; `3433-3439` `infer refl`; `Elab/Tactic.lean:590-599` `forceNames` | `rfl` now has #256's `eqSigmaSides?` path; `term.rfl` forces expected first; `infer refl` builds `vEq` (strict). | **adaptation**: `rfl` need not change (the #256 path works; §3), but a `lazyEq` branch before `force` would avoid the last type computation; `infer refl` → `vEqL`; `forceNames` must force (whnf/unfold tactic) |
| 19 | `Elab/Witness.lean:50-58` `headNames`; `Smt/Translate.lean:132-159, 269-276` | a `lazyEq` falls into the wildcard (no names); SMT falls back to `wh A`, forcing. | **neutral/UX**: witness suggestions lose the equation's head until a case is added; SMT forces, which is acceptable |
| 20 | `Frontend/Frontend.lean:75-92` `isoKey`; `Tests/ElabFix.lean:787-794` | every `Globals` setting must be in the isolated-module key; #155 found `lazyEqs` missing here. | **adaptation**: add `Globals.lazyEqs`; the guard will fail until then |
| 21 | `Tests/Lint.lean:511-520` `valCtorName` (no default) | a new `Val` constructor needs a row and a traversal case. | **adaptation** (compile/test-enforced) |
| 22 | `selfhost/Kernel.wiz:1067` `eval .eq`; `1318` `vEq`; `2555` `conv`; `2327` `isProp`; `2229` `sortOf`; `2795` `subTy`; `1879` `quoteM`; `selfhost/Frontend.wiz:6204` `def memo … := f` | the selfhost kernel has no `lazyEq` and **its `memo` is the identity** (no #256, no `markDataEq`, no `quoteEqs`). | **conflict with the design's selfhost plan**: forcing re-runs `vEq`; if P1 is ported without memoising `memo`, the selfhost checker can become exponential/time out; `markDataEq` parity is also absent |
| 23 | `mutual`/`partial`; `Check.lean:1329+` `checkImplAgrees` | `mutual` blocks are axioms/witnesses (no value); `partial` definitions get an impl checked by `checkImplAgrees`. | **neutral**: no equation evaluation change; conv at a glued type is still sound |
| 24 | "trap state" | there is no kernel trap state at this commit. The only traps are `kernelPanicName` (`Value.lean:164`, the stuck-unknown panic) and the runtime's `Rv.trap` in the separate `wiz-rv` repo. | **neutral/unrelated** |
| 25 | typeclass/deriving surface (`Elab/Term.lean` instance search; `Elab/Command.lean` deriving/`addDecl`; `Check.lean:1329+` agreement) | instance search and `headType` go through `whnf`/`force`; a `lazyEq` is a proof, never a class head. Deriving generates `DecidableEq`/`BEq` proofs and equations; P1 only makes their types cheaper. `addDecl`'s type comparisons use `convTy`, where the new congruence can only add a `=` congruence instance. | **neutral** (no new class/deriving rule; P1 composes) |

Level handling (the U2 work) enters only through `sortProp?`/`isNeverZero`: a `lazyEq`
is always level 0, so P1 bypasses levels entirely. There is no interaction with level
instantiation, `Globals.instCache`/`cacheInst`, or the level-parameter caveat beyond the
read-back note in §1.3.

### 2.1 Summary of the labels

* **Helps:** #1 (the memo primitive), #3 (proof suspension), #4 (Prop/ULift), #5
  (mandatory sorts now enforce the invariant), #9 (`Sorts.type`), #14 (agreement check).
* **Neutral:** #10, #11, #19, #23, #24, #25; #2 for soundness (but see supersession).
* **Conflicts/needs redesign (none is an unsoundness):** #1 (use `memoThunk`, rewrite
  the design's memo sentences), #2 (quote/`rfl` plan superseded), #6/#7/#8 (extra forcing
  sites from mandatory sorts and the marking pass), #16 with §5.6 (the "both sides glued"
  assumption), #22 (selfhost `memo`/parity).
* **Adaptation only:** #12, #13, #15, #17, #18, #20, #21.

## 3. Probes on master (627b48f6)

Binary: `/workspace/wt/hdl-stream/.lake/build/bin/wiz`. Its worktree HEAD is exactly
`627b48f6` (verified with `git rev-parse HEAD`) and it has no tracked changes, so this is
a build of the same source as this worktree, not a stale or other-branch kernel. (My own
`lake build wiz` was queued behind a 6 GiB `pslot` fixpoint and the slots did not free
within the probe window; the source is identical, so the numbers are of this commit.)
`wiz check --no-cache`, wall time and max RSS, light slot (2 GB). Numbers are ratios, not
perf-run measurements.

### 3.1 The two wishful entries

* `conv-sigma-eta-neutral` (status **done**, 71b7dc70): the record-η repro now passes at
  the fast time. `slow-selfcontained.wiz` 1.45 s / 99 MB, `fast-selfcontained.wiz`
  1.63 s / 100 MB, `slow-axiom.wiz` 1.25 s. The entry's P1 table (101 s → 30.6 s → 15.4 s)
  is historical: **#286 alone** does what the entry's last row attributed to P1. P1 is no
  longer needed for this entry (and its "remaining ~14 s is the sides" is also gone).
* `kernel-eval-throughput` (status **blocked**): the "no gluing" half still holds.
  * Reuse of a closed equation type, N uses: 8.56 s (N=1), 13.45 s (N=2), 23.12 s (N=4)
    for `it 200000 0`; RSS 381 / 379 / 402 MB. Linear in uses, so the equation type is
    re-evaluated per use. (This is the `AxUse` rung of `kernel-eval.md` §9, in miniature.)
  * Combining two already-checked ranges: `r1`, `r2` alone 4.43 s / 170 MB; adding
    `allBelow_append 2 2 P0 r1 r2` 17.20 s / 170 MB. The composition re-runs both range
    types; the wishful claim ("`allBelow_append` re-runs both ranges") holds.
  * The #256 `rfl` regression (`Tests/data/rfl-shared-run.wiz`) checks in 4.29 s / 87 MB;
    #256 does what P1's `rflWritten?` was for, for data equations. P1's `rfl` win is now
    only avoiding the equation-type computation (roughly the F1 run), not the proof shape.
  * The single-run `Loop.ok 104 1100` and the ~1 MB/cycle figure were **not** re-run
    (they need the icestick copy and minutes/GB); the code still has F6 (`Val.unfold`
    keeps the spine and history, `Value.lean:118-123`, `Eval.lean:442-444`), and P1 does
    not change it.

### 3.2 #257 / the unifier and the flex-flex check

* `unify-computed-equations.md`'s repro (`L`, `L2`, `e1 : L = L2`, `Eq.trans h e1`) still
  fails on 627b48f6: `expected: L = ?m3 y h`, `inferred: (0 e : True) × …` (the computed
  Σ of field equations). So `#257` is still open. P1's side-by-side unify is one fix
  (with the elaborator shortcut of §5.6); the cheaper #256-based unifier case in §4 may
  also fix it and should be probed first.
* The "primary flex-flex" repro is not one of these two entries; it is
  `elab-head-meta-first-order.md`. For completeness: `frame9 {r} [Hw r] (d : r (bits 8)) :
  r (bits 9) := Hw.cat (Hw.lit 1 1) d` **checks** on master (22.3 s / 136 MB, import
  dominated). That entry's remaining half (the converse first-order mis-solve) is a
  different, still-open item; P1 is neutral for it.

## 4. Decision

**P1: still wanted, in a narrowed form.**

* **Real, current problems it solves:** (i) an equation *type* is recomputed at every
  use (`AxUse`/`Combine` above; `native_refl` reuse is the canonical case — the
  `Command.lean:1656` comment says the type is not evaluated at declaration *because*
  F5 would compute it, but every use still does); (ii) a ~25–30 % saving on a single
  heavy `refl` (the F1 run the elaborator still does); (iii) `Eq.trans`/`#257`.
* **But #257 alone is not sufficient to justify the kernel change.** #256 already puts a
  data equation's original sides on the computed Σ (`markDataEq`), and
  `eqSigmaSides?` (`Eval.lean:225-233`) recovers them. A ~10-line unifier case —
  a Σ carrying those sides against a stuck `.neutral (.eq …)` — would likely fix
  `Eq.trans h e1` with no new `Val` constructor (the stored sides contain metavariables;
  `unify`'s `forceMeta` resolves them; `rflProof` already does the analogous thing at
  `Elab/Term.lean:983-987`). **This should be probed first.** P1's unique remaining value
  is the use-time cost of a *closed* equation type (`AxUse`/`Combine`/`native_refl`),
  where the type computes to `True` or a Σ and is re-run by the elaborator and the
  kernel; the unifier case cannot remove that.

* **Not solved by P1:** G11's memory (`F6`), the single 23000-cycle run, and the
  `rfl`-proof-shape problem (both #256 and #286 are independent and already landed).
* **Not superseded:** #256 and #286 remove P1's *examples* from the two wishful entries,
  but not its *mechanism*. If the only goal were the record-η lemma, P1 would be
  unnecessary; it is not the only goal.
* **Do not reopen #155:** branch `agent/glued-eq-impl` is 1072 commits behind (last base
  `2008ced`, 2026-11-12); its `rflWritten?` and `quoteErasesProofs` choices predate
  #256/#286/#154-sorts. Reimplement on 627b48f6 (or a later master) with §5.

## 5. Smallest first slice, risk, and what has to be redesigned

### 5.1 The slice

Lean kernel + elaborator only, behind `Globals.lazyEqs` (default **off** in the first PR;
`--lazy-eqs` turns it on, `--eager-eqs`/`--eager-proofs` off; include the flag in
`isoKey`):

1. `Value.lazyEq A a b (memoThunk …)` (not `Thunk.mk`).
2. `eval .eq` → `vEqL`; `whnf`; `propSort?`; `vEqL` strict at `propSort? = some true`,
   under `g.eager` and `!g.lazyProofs`.
3. `typeSort?`/`isProp`/`Ctx.sortOf?` → 0 for `lazyEq`; `quote` folded; `erasable`.
4. `convGlued` + `subTy` shortcut; `force`/`rename`/`unifyGlued`; `recomputeEq?`.
5. Elaborator: early return in `insertImplicits`/`trailingInst`; the ident/app/hole/paren
   `check` shortcut before `checkData?`/`sameDefinition?`; `infer refl` → `vEqL`.
6. Keep `rfl` as it is (#256's `markDataEq`/`eqSigmaSides?`); do not add `rflWritten?`.
7. Differential test with the flag on/off on lib/, examples/, the corpora; then flip the
   default after the expected-output churn is settled.

This slice alone should make the `AxUse`/`Combine` probes flat and fix #257. It does not
touch `mutual`/`partial`, typeclasses/deriving, or the selfhost.

**Risk.** (a) A new `Val` constructor is a compile-forced sweep of every traversal;
missing a wildcard site is a wrong answer, not a crash (Lint's `valCtorName` and the
"every constructor" tests are the guard). (b) The `quote` mode is the subtle one: if
`lazyEq` forces in one mode and folds in another, `convGlued`'s `lazyInd` syntactic
comparison and `reevalStale?`'s quote-equality can see mixed forms. Fold everywhere
(§5.2); the fallback keeps completeness. (c) Expected-output churn (messages, infoview,
hover) and the `conv`/`check`/`lint` groups. (d) Memory: a glued equation retains `A,a,b`
(and #256's marker retains them again for data equations); measured RSS in the AxUse
probe was flat, but a huge equation's sides stay alive longer. (e) The elaborator
shortcut list is where the *gain* lives; missing one costs time only (the kernel still
checks), like the prototype's first miss.

### 5.2 Redesign: `quote` under `quoteErasesProofs`

The design (§2, §3) says `quote` of a `lazyEq` forces when `quoteErasesProofs` (the
kernel's syntactic comparisons). On current master that flag is also set by `showVal`
(`Check.lean:295`) for *messages*, and `sameVal` is gone. Forcing there would re-run the
very computation P1 avoids every time a large type is printed or a declaration is
rejected. **Fold `lazyEq` in every quote mode** (as #155's refreshed review concluded:
the only remaining syntactic comparison is `convGlued`'s `lazyInd` folded quote, which
has a forced fallback). This is a text/implementation change, not an unsoundness.

### 5.3 Redesign: the `rfl` sub-plan

`rflWritten?`/`sidesOk` (the prototype's `rfl` shortcut) was narrowed in #155 and is not
on master. #256's `markDataEq` + `eqSigmaSides?` already makes a data equation's `rfl`
one `refl` after the equation computes (`Eval.lean:214-248`, `Elab/Term.lean:970-995`);
#286 removes the η cost. P1 should **not** carry the old `rfl` plan: it should leave
`rfl` alone, or (optionally) add a `lazyEq` case *before* `force` that uses the sides,
without changing the elaborated term. The #256 scaling test ("three completions, 30 s
bound") must stay green.

### 5.4 Redesign: the selfhost half

The design's selfhost plan reuses `vglued` with head `heq` and assumes `memo` memoises.
At this commit `selfhost/Frontend.wiz:6204` defines `memo f := f` (identity), and
`Kernel.wiz` has neither `markDataEq` nor `quoteEqs`. Landing P1 in the selfhost without
memoisation leaves a checker that re-runs `vEq` at every `whnf`, which can be exponential
on nested equations and can time out on cases the Lean kernel now accepts. Either
(i) memoise the selfhost `memo` first (a separate, reviewed change; #256 did this for the
Lean kernel only), or (ii) land Lean-only, keep the selfhost strict, and rely on parity
of *verdicts* (the selfhost is slower but accepts the same set), then port the selfhost
with memoisation. If elaborated-term parity is tested, also port `markDataEq`/
`quoteEqs`; otherwise the selfhost's `rfl` proof shape differs (still valid, slower).

### 5.5 Redesign: the forcing-site list

The design lists the kernel's `check` and the elaborator's `check`. Mandatory sorts and
the marking pass added `Ctx.sortOf?`/`isPropTy`/`isProofTy`/`modeAt`
(`Check.lean:435-481`), `Mark.decide`/`Mark.checkCore` (`Mark.lean:44-93`),
`Sorts.value` (`Basic.lean:504-511`), and `checkData?`/`sameDefinition?`
(`Term.lean:1194-1205, 1455-1462`). Each is a place where an equation type is forced
before P1's shortcut. The rule is the same: only intro forms force; everything else
carries the glued type.

### 5.6 Redesign: the unifier's "both sides are glued" assumption

The design's `unifyGlued`/`convGlued` rule is `lazyEq` vs `lazyEq`. `#257`'s shape has
the inferred `e1` type as a `lazyEq` (with P1) but the expected domain can have been
forced to a **stuck** `.neutral (.eq A a b)` by `checkData?`, `force` in `check`, or
`sameDefinition?` before `unifyAt`. In that shape, the design's rule does not fire;
`force` computes the `lazyEq` to a Σ and the comparison fails as it does today. Either
(a) the elaborator shortcut must guarantee the expected equation is still glued (the
design's `check`/`insertImplicits` path), **and** all the forcing sites of §5.5 are
fixed, or (b) add the symmetric rule: a `lazyEq` against a stuck `.neutral (.eq A' a' b')`
compares `A`/`A'` and the three sides. (b) is sound by the same congruence rule and makes
the fix robust; it should be in the first slice. This is the one place where the design's
assumption is too strong for the current elaborator, but it is a missing case, not an
unsoundness.

### 5.7 Obsolete design items

`Val.lvlBound` (`glued-eq.md` §2) no longer exists; `sameVal` is gone; `quote`'s
`quoteErasesProofs` has a different meaning (proofs erased, `showVal`, the `lazyInd`
comparison). The design's §2/§4 tables need these edits.

### 5.8 Unsoundness?

**None found.** The congruence argument survives every change above: the only new "equal"
is the `=` congruence; all "no" answers fall back; `vEq`'s stability (S) is now *better*
enforced by mandatory sorts. The only places where the original *text* is unsafe are
efficiency/termination premises (memoisation, selfhost `memo`), and the read-back
well-formedness rule (strict at a known proposition), which the design already has and
must not weaken. If a future change makes `propSort?`/`typeSort?` lie about `lazyEq`
(e.g. returning `some false` at a proposition) or makes `conv`'s new Cast-Refl apply to
the equation *former* rather than two propositions, that would be the place to re-audit;
at 627b48f6 it does not.

## 6. Follow-ups (not this assessment)

* Update `kernel-eval-throughput.md` status: P1 still wanted, but its "blocked on P1"
  sentence should say *composition/use-time and #257*, not `rfl`/η.
* Update `conv-sigma-eta-neutral.md`: its P1 dependency is gone (#286); no action.
* `unify-computed-equations.md`: P1 is one fix for #257; the cheaper #256-based unifier
  case (§4) should be tried first. If it works, #257 no longer argues for P1.
* If P1 is not funded, the `AxUse`/`Combine` cost needs a different design (an
  elaborator/kernel cache of a declaration's evaluated type, or a lighter lazy-equation
  value); the existing `markDataEq` route covers `Eq.trans` but not the use-time cost.
