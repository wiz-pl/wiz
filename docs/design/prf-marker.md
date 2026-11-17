# The proof marker

Wiz's kernels never evaluate a proof. The syntax shows some proof positions (`cast`'s
equation, `transp`'s two proofs), and the evaluator suspends those. A proof bound by
`let`, passed as an argument or stored in a pair or a constructor sits in a position the
syntax does not mark, and the evaluator, which has no types, used to run it. The proof
marker closes that gap: a term former `prf.{l} t`, where `l` is the sort of `t`'s type,
which the evaluator suspends when `l` is `0`. The kernel **verifies** every marker (its
level must be the sort) and **requires** one wherever a proof could otherwise be evaluated.
This is the second step of P2 in the [soundness ledger](../Status.md) ("the kernel never
evaluates proofs"). The design was decided on 2026-11-10 and merged as PR #128. The specification is [CoreSpec §8.6 and §8.6a](../CoreSpec.md).

## Why

Not evaluating proofs is the algorithm that the published decidability results for
observational type theory are about ([PT23], [PLT25]): conversion never compares two
proofs, and no reduction rule runs on a term of a proposition. With an impredicative
`Prop`, proof-irrelevant equality and regularity, evaluating proofs can diverge [AC20].
Wiz hit this: the `let`-encoded Abel–Coquand term looped in the self-hosted kernel with
regularity on, because its `let`-bound proofs were evaluated (D1 in Status.md).

## The rule

**Term and value.** `Term.prf (l : Level) (t : Term)` in `Wiz/Core/Term.lean`, `Tm.prf (l : Lvl) (t : Tm)`
in `selfhost/Kernel.wiz`. A suspended proof is the neutral head `Head.prf env t`
(`hprf env t`): a term and its environment, with no type and no value.

```
eval env (prf.{l} t) = neutral (prf env t)      if l is 0      (never looks at t)
eval env (prf.{l} t) = eval env t               otherwise
```

"`l` is 0" is `Level.isZero` (`lvlIsZero`): a closed level is computed exactly
(`toNat?`), and a level with parameters is `0` only if `Level.equiv` says so.
Eliminations of a suspended proof (application, projections, `down`, `absurd`) grow its
spine.

**Typing.** The checker has two modes. Proof mode is entered under a marker at level `0`,
and in `cast`'s equation and `transp`'s proofs. Relevant mode is everywhere else,
including a declaration's body.

```
Γ ⊢ T : Sort s    s ≡ l    Γ ⊢ t ⇐ T  (in proof mode if l is 0; else t itself is exempt)
──────────────────────────────────────────────────────────────────────────────────────── Prf
Γ ⊢ prf.{l} t ⇐ T                                           (and the same for ⇒)
```

* **Verified.** A marker whose level is not the sort of the type is rejected
  (`Ctx.underMarker` in `Wiz/Core/Check.lean`; `underMarker` in `Kernel.wiz`). This is
  the soundness-critical direction: a marker at level `0` on a data type would put a
  neutral where a constructor is expected, and conversion takes any two suspended proofs
  as equal. If the sort cannot be computed (`Ctx.sortOf`, `sortOf`) the term is rejected,
  not treated as needing no marker.
* **Required.** In relevant mode, a term whose type is in a sort that *may* be `0` (`Prop`,
  or `Sort u` for a level parameter) must be marked, neutral-shaped, or a stuck proof:

  ```
  marked:          prf.{l} t
  neutral-shaped:  x | c | () | n a | n.1 | n.2 | down n | (n : T)
  a stuck proof:   refl A a | reflTy X | transp A a P p b e
  ```

  Anything else there (a `fun`, a pair, a `let`, a `cast`, `absurd`, a case analysis, an
  induction) is the kernel error "unmarked proof". The exempt formers are
  `Term.neutralShaped` and `neutralShaped` in `Kernel.wiz` (which also lists `axiomC`); the
  check is `Ctx.requireMarker`. The body of a marked `fun` is exempt, because
  `Sort (imax a l)` is `0` exactly when `Sort l` is.
* **Inside a proof.** Two rules keep the checker from evaluating anything checked in proof
  mode. *The mode of a subterm is decided by its type* (`Ctx.modeAt`, `modeAt`): a
  subterm of a proof whose type is not a proposition, such as an index, is relevant again
  and its proofs need markers. *Bind by type* (`Ctx.evalAt`, `Ctx.instArgAt`, `evalAt`):
  where the checker needs a value to bind a variable or instantiate a type, a proof inside
  a proof is suspended. Without these, a Church tower of twos in `Prop` inside one marker
  took 65 536 β-steps at height 3 and did not finish at height 4.

**The invariant.** Call a value *proof-safe* if it is a neutral, `()`, or a glued constant
that unfolds to one. Every value the kernel's evaluator builds at a proposition is
proof-safe, so the kernel never performs a β, projection or ι step inside a proof. The
argument is by cases on the neutral-shaped forms: a variable of proposition type is only
bound to the value of a term checked in relevant mode, or by a kernel template that puts
proofs only into `cast`'s equation and `transp`; applying or projecting a proof-safe
value grows a spine. `refl`, `reflTy` and `transp` evaluate to stuck heads after
evaluating only their relevant parts (`transp`'s `p` and `e` are suspended). This is an
argument written in CoreSpec §8.6a and the code comments, not a mechanised proof.

**Level-generic terms (R1).** In `def k.{u} (A : Sort u) (a : A) : A := (fun x => x) a`,
`A` is not known to be a proposition when the body is checked, but at `u := 0` it is. The
level on the marker handles this: the inner `fun` is marked `prf.{imax u u}`, level
instantiation substitutes into the level, and at `u := 0` the term is a suspended proof.
While the declaration itself is checked, `u` is symbolic and the term is evaluated: that
is the generic computation, and a conversion that holds generically still holds at `0`.

**Conversion.** At a proposition, conversion answers before looking at either side
(CoreSpec §8.5). A proof can sit inside a neutral compared at a relevant type only under
`absurd`. There both kernels apply one rule: two neutrals whose prefixes up to the last
`absurd` are proofs of `False` (`Empty_0`) are equal when the motives and the eliminations
after it are (`falsePrefix` in `Wiz/Core/Conv.lean`; `falseNe` in `Kernel.wiz`). Two proof
heads with no `absurd`, followed only by applications, projections and `down`, are equal
in both kernels (`isProofHd`, `proofSpine` in `Kernel.wiz`).

## Who writes the marker

A typed pass inserts the markers just before the kernel: `Wiz/Elab/Mark.lean`
(`Decl.withMarks`, `Decl.withTopMarks`), and `markCheck`, `markInfer`, `markClosed` in
`Kernel.wiz`, below the line that says they are not part of the kernel, for the
self-hosted frontend. Marking while elaborating is not enough: metavariables hide types,
and many terms are built by hand (constructors, recursors, match compilation, tactics).

* **On demand.** The pass costs about as much as the kernel's check. `withMarksOnDemand`
  (`Wiz/Elab/Command.lean`) first sends the declaration with a marker on its body only,
  and runs the full pass only if the kernel answers "unmarked proof". What is stored and
  cached is the term the kernel accepted.
* **Untrusted.** A missing marker is "unmarked proof"; a wrong one is rejected by the Prf
  rule. The pass evaluates as it goes, so it must only be given elaborated terms; on an
  ill-typed term it may hit an evaluator panic instead of producing a kernel error.
* **Read-back.** Outside the kernel, `quote` writes every proof-headed neutral back
  marked. The kernel's own read-back (`quoteErasesProofs`; `quoteM .false` in
  `Kernel.wiz`) reads every proof head as `()` and never evaluates one, so kernel error
  messages do not run proofs.
* **Erasure.** A marker at level `0` is erased; at another level it is transparent. The
  compiler first drops markers that mark nothing at the instance it compiles
  (`Term.stripMarks`).

## The step budget outside the kernel

The elaborator, `#reduce` and hover read suspended proofs back into terms, and a proof
need not have a normal form. Each such read-back runs under a deterministic step budget
(`Budget` in `Term.lean`; `--proof-steps N`, default 1 000 000; `--trace-proof-steps`
prints what each read-back took). A step is one closure instantiation, counted, not timed.
When the budget runs out the proof reads back as a constant whose name is the message, and
the kernel rejects any term containing it. The kernel has no budget and refuses to run
with one set (`checkHeader`). The self-hosted toolchain has the same budget (`forceProof`,
`proofStub` in `Kernel.wiz`). On 2026-11-10 the largest read-back in `lib/`, `examples/`
and `selfhost/` took 9 170 steps (12 008 after the equality-of-descriptions change).

## Alternatives considered

* **Always marked** (every proof in a relevant position wrapped, variables too). Simpler to
  state, but every constructor's index proof `()` and every proof variable passed along
  would need a marker, and the check would run at every application. The neutral-shaped
  exemption loses nothing for the invariant. The strict form exists as
  `Globals.strictProofs` (off; no command-line flag).
* **For level-generic terms:** accept and document the gap; forbid instantiating such a
  parameter with `0` (Coq's restriction); re-check the instance in the kernel; or put the
  level on the marker. The level on the marker was chosen.
* **Relevance marks on binders** (each `app`, `let` and `lam` records whether it carries a
  proof). On strictly marked terms this is a bijection with the wrapper, but it changes
  `app` and `let` everywhere and still needs the wrapper (or more marks) for pair fields,
  `up`, `absurd` and bodies. Deferred.
* **A wall-clock deadline for read-back.** Rejected for a step count, so that a file that
  checks once always checks.

## Limits and what remains open

* **The elaborator's own evaluation.** A `let`-bound proof or an argument that the
  elaborator evaluates before the pass has run is not suspended, and is not under the
  budget. A proof without a normal form there makes elaboration loop. Nothing is accepted
  by a loop. This is the open part of P2 in Status.md.
* **Relevance marks on binders** and domain sorts on `λ` remain a later step.
  [Mandatory sorts](mandatory-sorts.md) (merged after this work) removed the other gap the
  marker relied on: the sort of a `Π`/`Σ` is now always written.
* `Globals.lazyProofs` can be turned off with `--eager-proofs`, which restores the old
  evaluator for experiments and turns the cache off.

## Tests

In group `selfhost` (`Tests/Groups/SelfHost.lean`), each on both kernels:

* "P2: the proof marker is required and verified, by both kernels (terms without the
  marking pass)": unmarked proofs rejected in each position, markers at the wrong level or
  on data rejected, the stuck proof formers accepted unmarked, and the `absurd` conversion
  rule.
* "P2 (I-1): a proof inside a marked proof is not evaluated: a tower of exponentials in
  Prop checks at once (both kernels)".
* "P2 (R1): a level-generic term is marked at its level, and is a suspended proof at the
  instance 0 (both kernels)".
* "P2: comparing types erases suspended proofs, but not what follows an absurd (both
  kernels)".
* "D1 (Abel–Coquand): both kernels check the let-encoded program, with regularity on too
  (P2: its let-bound proofs are marked, and never evaluated)".
* "every constructor of Term is covered by the traversals (S1: a missed one proved
  False)".
* "F7: reading a proof back stops at its step budget in the self-hosted kernel too (a
  tower under absurd, read back in a type)".
* The differential test "the Wiz kernel agrees with the Lean kernel (400 random terms)",
  where each side marks with its own pass, so the two passes are compared too.

In group `observational equality` (`Tests/Groups/Ott.lean`): "P2: proofs are never
evaluated, so Abel–Coquand checks even with full regularity (and nested)" and "P2: a cast
between propositions is stuck (a proof), not the equivalence applied".
