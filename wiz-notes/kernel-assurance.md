# The kernel assurance budget: spec, checked equivalence, proof-carrying export

Status: **design, 2026-11-23.** Agent `kernel-assurance`, branch `agent/kernel-assurance`
(worktree `/workspace/wt/kernel-assurance`, base `integration/train12` = `3fa0eec95`).
**No code written, no build run.** Every count below is from a read-only `grep`/`wc` in
this worktree or from the named document; the two are labelled. No claim here is a
measurement of behaviour.

Read for this note: `docs/Status.md` §7.0–7.2 and §8–9; `docs/bootstrap-chain.md`;
`docs/selfhost-compiler.md`; `docs/CoreSpec.md` §11, §13, §14, §15, §16; `WizMeta.lean`,
`WizMeta/Spec/Rule.lean`, `WizMeta/Checker.lean` (header and options), `WizMeta/Translate.lean`,
`Tests/Meta.lean`; `Wiz/Core/{Term,Level,Check}.lean` (the parts named below),
`Wiz/Cache.lean` (the `Sx` serialiser and `Effect`), `Wiz/Elab/Command.lean`
(`addDeclSorted`, `withMarksOnDemand`); `Wiz/Compiler/Bpf/Sexp.lean`; and the notes
`metatheory-plan.md`, `wiz-meta.md`, `audit-kernel.md`, `cache-trust-boundary.md`.

---

## 0. The one-page version

The kernel is the only component whose wrong answer a proof cannot outrun: a wrong
*accept* poisons every theorem downstream, a wrong *reject* only inconveniences a user.
That asymmetry fixes the target — **one-directional, accept-side soundness** — and it is
why the budget goes to the kernel and not to the elaborator.

Three artefacts, in the order they become true:

| # | artefact | what it is | what it buys |
|---|---|---|---|
| **A** | the spec | a declarative statement of the judgement the kernel is supposed to decide (WizMeta today) | a statement to be wrong *against* |
| **B** | the check | a relation between the spec and the algorithmic checker that is stronger than "two voters agreed" | the kernel's accepts are witnessed, not just tested |
| **C** | the export | a canonical serialisation of an elaborated declaration that a *different* implementation re-checks | the de Bruijn criterion applied to this toolchain's own output, and to the cache |

The single most important design decision in this note: **B and C are the same artefact
seen from two sides.** The export is the term; the certificate is the derivation; a
verifier is a total function from bytes to a judgement. That is why the budget is not
"verify the elaborator" and not "add more differential tests": it is *make every shipped
declaration carry a checkable derivation of its typing, in a written-down system, checked
by an implementation that is not the kernel*.

Today's position, stated without flattery:

* the spec is **partial** — 44 constructors against the kernel's 56, no quantities, no
  sizes, no `ν`, no `split`, no numerals, no marker rule, no `impl`/witness rule;
* the equivalence is **measured, not checked** — 24 cases in `=meta`, ~484 terms in the
  fragment, 0 disagreements on a corpus that cannot distinguish the switchable rule
  variants;
* the export **does not exist as a format**, but most of its substrate does:
  `Wiz/Cache.lean` already has a total S-expression printer and reader for `Term` and
  `Level`, exercised by the cache and by a 5-declaration round-trip test;
* the independent checker **does not exist**; the closest thing is WizMeta, which shares
  no code with `Wiz/Core` but was written from it and shares its design mistakes (F1, F2,
  K6).

The smallest first step (§6, S0) is one test file and no production code: **measure what
the third voter cannot see.** It is first because if the answer is "a lot", then "0
disagreements" is a weaker claim than §7.1 currently reads, and every later slice is
spending effort against a blind oracle.

---

## 1. What the kernel's judgement is

Precision here is load-bearing: a spec that states a different judgement than the kernel
decides is a spec of a different calculus, however many terms agree.

### 1.1 The entry points, as the code has them

`Wiz/Core/Check.lean`:

```
check   : Ctx R → Term R → VTy R → TCM (Usage R)      -- bidirectional, checking mode
infer   : Ctx R → Term R → TCM (VTy R × Usage R)      -- inference mode
checkType : Ctx R → Term R → TCM Level                -- a type is a term of some sort
```

`Ctx` is `{ globals, env, names, qtys, types, lvl, erased, proof, … }`: a context of
*values*, a de Bruijn level, and two modes that change the rules (`erased`, `proof`).
`Globals` is a name-indexed table plus `builtins`, `assumed`, and a score of flags that
change the judgement (`regularity`, `inertReg`, `lazyProofs`, `strictProofs`,
`predicativeProp`, `sortHolesOk`, `eager`, `quoteErasesProofs`, `quoteEqs`, `unboxStructs`,
`hidden`, `strictPrivacy`, …).

A declaration is judged by, in order (`addDecl`, `Check.lean:1760`):

1. `checkHeader g d` — the type is a type, the level params are well formed;
2. if `d.value = some v`: `check {globals := g} v (eval g [] d.type)` — the value checks
   at the type, in the empty local context, with usage = `0`;
3. `insert` into the table;
4. if `d.impl = some i`: `checkImpl g' d i` — the compiled implementation checks at the
   same type;
5. if `d.value` and `d.impl` are both present and `d.derivedEquations`: `checkImplAgrees`
   — *and* the compiled equations compute what the value computes (T1, partial
   correctness).

A partial definition (`addPartialDecl`) replaces 2 with: a **witness** `w` is checked at
the type in `erased` mode with usages unenforced; the value is absent; the body is
`impl`, checked by `addPartialImpl`.

The production path is `addDeclSorted` (`Elab/Command.lean:377`):

```
d.withSorts g                       -- untrusted, total, fills Π/Σ/ULift sort holes
→ withMarksOnDemand:                -- untrusted: try body-marker, then full Mark pass
    addDecl g (d.withTopMarks g)
      ↳ on unmarkedProof: addDecl g (d.withMarks g)
→ privacyCheck                      -- optional, off by default
```

So **what the kernel checks is not what the user wrote**: it is the sort-filled, marked
declaration. Anything the spec says about "the term" must say which of the three it means.

### 1.2 The judgement, written out

For a declaration `d` with `levelParams = [u…]` in a signature `Σ`:

```
Σ ⊢ d.type ∶ Sort l                      (l symbolic in u…)
Σ ⊢ d.value ⇐ d.type                     (if a value; else a witness in erased mode)
Σ ⊢ d.impl  ⇐ d.type                     (if an implementation)
Σ ⊢ d.impl ≡ d.value                     (if derived equations: checkImplAgrees)
∀ c ∈ d.type, d.value, d.witness: c ∈ Σ   (every constant resolves)
```

Stacked on top: `Σ` itself is well formed (each entry is judged in the prefix before it —
`addDecl` suffices, since it is called in order), and the *trust list* of `d`
(`Globals.axiomsOf`) is the set of entries that have no value and no witness, plus the
`assumed` registrations and native implementations the check and the compiled code reach.

### 1.3 The option vector is part of the judgement

`regularity := .full`, `predicativeProp := true` and `sortHolesOk := true` each change
which terms are accepted. A spec that does not name the vector is a spec of no particular
calculus. **Design decision (recommended): the export is defined only for the default
vector**, and the format carries one `options` atom that a verifier compares against the
defaults; any experimental mode produces no export and no assurance claim. This is already
the position §7.0's last row takes ("experiments: nothing on this page is claimed for
them"); making it a format-level refusal is cheaper than threading twelve flags through
the spec.

### 1.4 Scale, so the rest of the note is read at the right size

| | count | source |
|---|---|---|
| kernel files trusted by §7.0 | 11 | `Status.md` §7.0 |
| lines | **6 291** (`wc -l`); **5 003** non-blank, non-`--` | this worktree; `Status.md` records 6 286 / 4 998 at `d853fde79` |
| `partial def` in those 11 files | **123** (Eval 57, Check 36, Term 13, Conv 11, Level 4, Value 1, Templates 1) | `grep -c 'partial def'` |
| `panic!` in `Wiz/Core` | **21** (Eval 19, Check 1, Value 1) | `grep -c` |
| `Term` constructors | **56** | `Wiz/Core/Term.lean` |
| WizMeta | **6 837** lines, of which `Checker.lean` 1 065 | `wc -l` |
| spec `Tm` constructors | **44** | `WizMeta/Syntax.lean` |
| `=meta` cases / `=selfhost` third-voter case | 24 / 1 | `Tests/Meta.lean`, `Tests/Groups/SelfHost.lean:4113` |
| `lib/` | 107 `*.wiz`; ~10 000 declaration-like lines (crude grep, over-counts prose) | this worktree |

The 123 `partial` definitions are the reason a theorem about `Wiz/Core` is not a slice:
`partial` is opaque to Lean's logic, so `Sound(K)` for the real code is a rewrite into a
monad (or `partial_fixpoint`) of the code the perf lane is simultaneously optimising. That
is `metatheory-plan.md` §3.3's conclusion and nothing in the year since has changed it.

### 1.5 Why the budget is here and not on the elaborator

The ratio is the argument. `Wiz/Elab/` is **14 422 lines** in 16 files, and the parser and
syntax add 2 135 more, with metavariables, unification, implicit arguments, type classes,
macros, tactics and `deriving` on top. The kernel is **6 291** and its job is one
judgement.

An elaborator bug **cannot** make a theorem true: every declaration is re-checked from
scratch by `addDecl` (`CoreSpec` §16: "a bug in elaboration, `match` compilation or
recursion compilation can only make the kernel *reject* a declaration"). Verifying the
elaborator would protect the front end's convenience — better error messages, fewer
spurious rejections — and not the truth of anything. A kernel bug in the accept direction
is inherited by every proof downstream and cannot be caught by any of them.

So 6 291 inherited lines are worth more assurance effort than 14 422 preventable ones, and
the marginal value of a verified elaborator is close to zero *for soundness*. CompCert's
~100 kLoC of Coq and roughly six person-years (`Status.md` §7.2) bought semantic
preservation for C, a far simpler language than a quantitative type theory with
observational equality and extensible macros. That is the scale check for L2, and it is
also why L1 and the export — which do not need the elaborate proof — are the right first
purchase.

---

## 2. (a) The spec's shape

### 2.1 What exists

`WizMeta` is the right *architecture* and should be kept:

* **rules as data**: `structure Rule := (prems : List Jdg) (concl : Jdg)`;
* **one inductive**: `Derivable R j` = `j` is the conclusion of an `R`-rule whose premises
  are derivable;
* **fragments as unions of rule files**: T0, T1, `Tprog` (`Spec/Fragments.lean`);
* **seven judgements**: `wf`, `ty`, `eq`, `red`, `inert`, `inertD`, `peq`;
* **reduction as its own judgement**, so a rule a checker implements by contraction is
  told apart from one it uses only in conversion (η, irrelevance, InReg);
* **no proof reduction** is a property of the fragment (`WhRed`), matching P2;
* **a total reference checker** written from the rules: substitution-based, typed
  weak-head reduction, fuel, no environments, no quotation, no syntactic side conditions.

Two structural properties are worth more than they look: because the rules are data, a
*derivation* is a first-class object (§4.4), and because the checker is substitution-based,
it shares no algorithm with the kernel's NbE — the two agree for a reason, not by
construction.

### 2.2 The principle that exposes the six defects

> **The spec must not assume anything the elaborator would have got right.**

The kernel exists to distrust the elaborator. A spec that drops a check because "the
elaborator writes the sort", "the marking pass inserts the marker", or "`impl` is derived
from the checked value" is a spec of *the elaborator plus the kernel*, and its agreement
with the kernel is agreement about a smaller term than the kernel checks.

Measured against that principle, the current spec has six concrete defects. Each is a
place where "0 disagreements" is silent rather than reassuring.

| # | assumption the spec makes | where | what a wrong term could do | fix |
|---|---|---|---|---|
| **D1** | Π/Σ component sorts are consistent | `Translate.ofSorts` maps `BinderSorts ⟨dom,cod⟩` to the single `imax`/`max` it forms | the spec's image records one product sort, not the pair: `pi` at `⟨0,1⟩` and `⟨1,1⟩` both give a sort that is `1`, the kernel's `checkComponentSort` rejects the first, and the spec accepts both | carry both sorts in `Tm`; make each a **premise** of the pi/Σ rule |
| **D2** | every sort is written | `Opts.sortsOptional` (set by the harness's `kernelOpts`), the harness's `sortHolesOk` pre-check | a hole is a rejection in the kernel and an accepted `none` in the spec as the harness runs it | spec: a hole is not a type; harness: the pre-check is not the spec |
| **D3** | markers are present where needed | `ofTerm` refuses `prf` (no case), `Mark.infer` in `kernelInfer` | the kernel checks the **marked** term, the spec votes on the **unmarked** one; the bridge "marking preserves the judgement" is unproved and untested | a marker judgement, or an explicit bridge test (S1) |
| **D4** | quantities are labels | `Q` = `{0,1,ω}`, `ofQty` refuses a polynomial | 6 of the 484 corpus terms are rejected by the kernel for usage only; `QPoly` is not modelled at all | a usage judgement `Γ ⊢ t ∶ A ▷ U` (S2) |
| **D5** | `impl` agrees and witnesses inhabit | `ofDecl` refuses both | T1's `checkImplAgrees` and `addPartialDecl`'s witness rule have **no third voter** | declaration rules + the two checks (S2/S4) |
| **D6** | the open rule choices can be deferred | `EqTyCross`/`EqTyLevelled`, `PayloadKernel`/`Stuck`/`Uniform`, `kernelEqFormation`, qty-at-Prop-Π/Σ | §4.1 of `wiz-meta.md` says the corpus **does not distinguish** them; a switch that no term can flip is not a decision | one distinguishing term per switch, pinned (S1) |

D1 deserves its own sentence because it is the sharp one. `imax 0 1 = imax 1 1 = 1`, so
the translation is not injective on kernel terms, and the lost bit is exactly what the
meta-review's D2 added (PR #203: Π/Σ/ULift casts must not compute without checking that the
components are in one sort). The spec inherited the **elaborator's** view of annotations.
That is the one assumption this whole exercise exists to remove.

D6 is the second sharp one. `wiz-meta.md` §4.1: "The 537-term corpus does not distinguish
them." So the two `=meta` cases that run the corpus under both Π≡Π variants agree because
the corpus is blind, not because the rule is settled. **A switchable rule with no
distinguishing term is unfalsifiable**, and an unfalsifiable rule in a spec is worse than
no rule, because it reads as a decision.

### 2.3 The shape to aim at

1. **Own syntax, still separate from `Term`.** The separation is right (`Term` changes
   weekly; a proof must not). Keep it, but make `Tm` a *faithful image* of `Term` on the
   exported fragment: add `BinderSorts` to Π/Σ, `k` to `ulift`, `prf`, `mu.prop` and
   `ind.prop`, `size`/`szInf`/`szSuc`/`sizeLt`/`sfix`/`scase`, `nu`/`out`/`cocon`/
   `scofix`/`coit`, `split`, `letUnit`, `natLit`, `natOp`; and a `Decl'` with `impl` and
   `witness`. Metadata that the kernel *documents* as ignored (binder names, `BinderInfo`,
   enum labels, μ hints, `pp`) stays out — that is not an assumption, it is the kernel's
   contract, and `CoreSpec` §16 says so.
2. **The translation becomes faithful and testable in both directions.**
   `ofTerm : Term → Option Tm` stays (nothing outside the fragment gets a vote), but
   (a) `Tm` carries everything the kernel checks, so a term and its image have the same
   judgement up to the documented metadata; (b) an inverse `toTerm : Tm → Term` exists and
   `ofTerm (toTerm t) = some t` on the fragment; (c) a test asserts that the translation
   does not hide a distinction the kernel makes — for a pair the kernel distinguishes, the
   spec must not give their images the same verdict. Today there is no inverse and no such
   test, so D1 is invisible by construction.
3. **Every rule hypothesis is decidable or a premise.** Today `Rule`'s hypotheses are
   `Prop`s: some decidable (`s.equiv …`), some judgement-shaped ("`Γ ⊢ A inert`"), some
   presuppositions the rules *assume*. That mixture is why "the checker is right by
   construction and reading" is the only claim available. The discipline
   *hypothesis ∈ {decidable on data} ∪ {premises}* turns a derivation into something a
   small total function can validate (§4.4) and makes presuppositions explicit instead of
   assumed. A lint can enforce it syntactically once the rule files follow it.
4. **`set_option autoImplicit false` in every `WizMeta/Spec/*` file.** `wiz-meta.md` §2
   already records the failure mode: "a misspelt name in a rule is a fresh variable". A
   spec that can silently quantify over a name it never meant is not a statement.
5. **One answer per open question, recorded in one place.** Keep the variant files for
   experiments, but define `canonical : Opts` as *the* theory the equivalence is stated
   against, and have the differential report which variant each run used. The kernel's
   current answer is the only defensible choice for the *equivalence*; the *intended*
   answer is a separate decision (the four `wiz-meta.md` §7 decisions), and if they
   differ, that is a kernel bug to file, not a switch to leave on.
6. **A version, a commit, and a change policy.** `WizMeta` is a statement of intent at a
   commit. `metatheory-plan.md` N8 already proposes the rule: *a kernel PR that changes a
   rule changes the WizMeta rule in the same PR*. Without it the spec is documentation
   that happens to compile. The gate is cheap: a test that every `Term` constructor has a
   `Translate` case and every `Translate` case has a rule file mentioning it.

### 2.4 What the spec must not become

* **Not a second kernel.** Its value is being obviously right and slow. The reference
  checker is 1 065 lines against 6 291; if it grows closures or environments to keep up,
  it loses the property that makes it a voter.
* **Not a completeness oracle.** The kernel is allowed to reject more (usage, the μ guard,
  and the six documented excuses). The spec's job is the accept direction only.
* **Not a claim of consistency.** `Derivable` deriving no closed `False` is a *model*
  obligation (E1/T2 has none published; sizes have none at all — `metatheory-plan.md`
  §2.4). A spec that can derive `False` is still a correct spec of a wrong kernel; the
  export would certify the wrongness faithfully. Say this wherever the export is claimed.

---

## 3. (b) The check: what "equivalence" can mean

### 3.1 The ladder

| level | statement | how established | status today |
|---|---|---|---|
| **L0** | `∀ t ∈ C, verdict_K(t) = verdict_M(t)` | a differential run on corpus `C` | 24 `=meta` cases. Recorded 2026-11-11: 484 in fragment, 0 disagreements, qualified by 6 usage-only + 1 guard + 53 outside the fragment + ≤10 types not compared |
| **L1** | `∀ d ∈ E, K accepts d ⟹ ∃ a machine-checked derivation of j(d) in the spec` | the checker emits a derivation; a total `checkDeriv` validates it; `checkDeriv_sound` is proved once | **not attempted**; the rule data and `Derivable` exist |
| **L2** | `∀ t, K accepts t ⟹ Derivable (j t)` | a theorem about `Wiz/Core` | **out of scope**: 123 `partial` defs, a moving target; `metatheory-plan.md` §5.3 budgets M2 3–5 and M4 4–8 expert-months, and T2 normalisation (M7) 6–12 as research |
| **L3** | plus `Con(T)`: the spec derives no closed `False` | a model (papers for T0/T1; none for T2 sizes) | **research**, independent of L0–L2 |

The important move is **L1**: it is a *theorem* (about the spec and the certificate), and
it does not require touching `Wiz/Core` at all. L0 is what the docs currently mean by
"the third voter"; it cannot become a theorem by adding terms, only by becoming L1.

Note what L1 does **not** say: it says nothing about terms that were never exported, and
nothing about the kernel's *implementation* (the derivation was produced by the checker,
not by the kernel). The gap L1 leaves is exactly L2, and it should be named that way
rather than papered over.

### 3.2 What a vote is, and the three voters' actual independence

| voter | algorithm | written from | shares with `Wiz/Core` | fragment |
|---|---|---|---|---|
| Lean kernel | call-by-value NbE, closures, de Bruijn **levels**, glued unfolding | — | — | all 56 constructors |
| `Kernel.wiz` | NbE, mutual inductive values, de Bruijn **indices**, closed numerals | the Lean kernel | design (F1, F2, K6 were in both) | a fragment (`CoreSpec` §15) |
| WizMeta checker | **substitution**, typed whnf, fuel 3000 | the spec | design (`Translate` imports `Term`) | 44 constructors |

Three voters, two lineages. A bug in the *design* is invisible to all three; a bug in an
*implementation* is caught by any two. That is why the corpus must contain the attacks
that a shared design would pass: F1, F2 and O1 are in `MTm.samples` today; **the six
switchable-rule distinguishers are not** (D6).

### 3.3 The adjudication ledger

The differential's exception handling is currently a string test in `Tests/Meta.lean`
(`rejectionVerdict`: four substrings for usage, one for the μ guard). That is the right
*asymmetry* — a kernel-only rejection may be excused, a checker-only rejection never — but
the wrong *form*: a new kernel error message silently becomes a disagreement, and a new
excuse silently becomes a pass.

Design: an inductive `Excuse` in `WizMeta/Adjudication.lean`, each constructor carrying
`(kernel message pattern, reason, issue link, the rule the spec does not implement)`, with:

* `adjudicate : KernelVerdict → SpecVerdict → Outcome` total over `Excuse`;
* a test that **every `Excuse` is used by at least one corpus term** (so the list cannot
  grow vacuously);
* a test that an unexcused kernel-only rejection **fails** (today's `rejectionVerdict`
  already does this; keep it);
* one reviewed row per excuse, with the standing rule: *an excuse is a kernel defect until
  someone proves the rule the spec lacks is admissible*. `E5b` (`PayloadKernel` is not
  stable under substitution) is the cautionary case: the `=meta` group currently *pins*
  the kernel's inconsistency as a fact.

### 3.4 The three untested bridges

Each is a place where the term the spec votes on is not the term the kernel checked. Each
is a cheap test, and none exists today.

1. **Marking** (D3). `kernelInfer` marks, the reference checker sees the unmarked term.
   Test: for each corpus term, the verdict with `lazyProofs := false` (no marker required)
   equals the verdict with the default marking pipeline. Falsifier: a term where marking
   changes a verdict other than by supplying a required marker. (The old mode also
   *evaluates* proofs, so the test is about verdicts on the corpus, not a mode worth
   restoring.)
2. **Sorts** (D2). `withSorts` fills holes. Test: on the corpus, a declaration with a hole
   is rejected by both; a declaration whose sorts are written is unaffected by a second
   `withSorts`.
3. **Entry point.** The term-level differential uses `kernelInfer`, not `addDeclSorted`.
   The declaration-level differential (`leanDeclVerdict`) does use `addDecl` — good — but
   with `withMarks` rather than `withMarksOnDemand`, and without `privacyCheck`. Test: one
   sample declaration per case, run through `addDeclSorted` itself. Falsifier: a
   declaration that `addDecl` accepts and `addDeclSorted` rejects (that is a *harness*
   defect, not a kernel one, but it would make the differential's verdicts not the
   production verdicts).

### 3.5 Coverage as a gate, not a hope

`metatheory-plan.md` §5.1 records that the 400-term generator "did not reach every former
(it missed O1)" and proposes a coverage gate: every `Term`/`Val` constructor and every arm
of `vEq`/`vEqType`/`vCast` reached at least once, *counted*.

The gate belongs to the *check*, not to the generator: a differential whose corpus cannot
reach a rule is not evidence about that rule. `=meta` is already a CI case
(`.github/test-shards.json:178`), so the gate has somewhere to live. Two counters, both
cheap:

* constructor coverage: a set of `Term` tags over the corpus, asserted against the 56;
* rule coverage: every rule constructor of the fragment fires at least once (needs
  derivations; for L0, approximate by mutation — the stronger test below).

The mutation form is the one worth building: for each rule file, swapping the fragment for
one that omits it must change some verdict. That is a test that the corpus and the spec
are connected, and it needs no derivation machinery.

### 3.6 What the equivalence proves, and what it cannot

| proves | does not prove |
|---|---|
| **L0**: on corpus `C`, the three implementations agree (with a named exception list) | that `C` covers the rules (`§3.5`) |
| **L1**: for each exported `d`, a derivation of `j(d)` exists and passes `checkDeriv`, whose soundness is a theorem | that the kernel implements the spec (`L2`) |
| **L1**: the trust list of `d` is finite, named, and audited | that the spec is consistent (`L3`) |
| **L1**: the export is a faithful image (round-trip + digest) | that the spec is the *intended* theory (a human decision) |
| nothing about rejections | completeness: the kernel may reject derivable terms (6 usage-only + guard today) |
| nothing about erasure | the compiler, IR, RC, C/LLVM/Wasm backends, runtime, C compiler (`Status.md` §7.0) |
| nothing about `impl`/witness before their rules are in | T1's partial correctness as a *theorem* (it is a check, not a proof) |
| nothing about termination | `Term(K)`: fuel exhaustion is `unknown`, never `ok` |

The sentence to put in `docs/Status.md` §7.1 when L1 lands:

> Every declaration in `lib/` carries a machine-checked derivation in `WizMeta` of its
> typing judgement modulo the listed trust (one axiom, the `nat.*` registrations); the
> derivation checker is proved sound against the rule data. The kernel is **not** proved
> to implement the spec: a term outside `lib/` receives no such certificate, and the
> translation from `Term` to `Tm` is checked by round-trip, not by theorem.

---

## 4. (c) The export

### 4.1 Format: `wiz-core/1`

A versioned S-expression, refused **by name** if it is not exactly `wiz-core/1` (the
`bpf-core/1` precedent: `Wiz/Compiler/Bpf/Sexp.lean:444`, "this toolchain reads
`bpf-core/1`, not `{head}`").

```
(wiz-core/1
  (format 1)
  (options (regularity off) (inert-reg conv) (lazy-proofs true) (strict-proofs false)
           (predicative-prop false) (eager false) (rig "ZeroOneMany"))
  (module "List")
  (decl (name "List.append")
        (levels )
        (type  <term>)
        (value <term>|none)
        (inline false) (derived-equations false)
        (impl <term>|none)
        (witness <term>|none))
  …
  (trust (kernel (axioms ("castRefl"))
                 (builtins (("nat" "Nat") ("nat.succ" "Nat.succ") …))
                 (assumed ()))
         (runtime (natives (("Nat.add" "UInt64.add") …))
                  (builtins (("repr:…" "…") …))))
  (digest sha256-…))
```

Decisions, each with the reason:

* **One declaration per `decl` node, in dependency order.** `addDecl` is called in order,
  so an export replays the same prefix. A verifier that wants one declaration can check
  the prefix up to it; a verifier that wants the library checks all of it.
* **Self-contained in v1; Merkle references in v2.** v1 inlines the whole slice (the
  bootstrap-chain argument: a self-contained artifact is the one that verifies with
  nothing else). v2 adds `(uses <digest> <name>)` so a module need not inline `Prelude`.
  Inlining first is right because the *first* goal is a verifier that works on one file,
  and the size problem is second.
* **Canonical, and therefore hashable.** No binder names (write `_`; `Term`'s contract is
  that names are printing only), no `μ` hints, no enum labels, no source spans, no `pp`,
  no `Info`. Declarations sorted by dependency order with name as tie-break. Levels
  printed *as written*, not normalised: the kernel checks them as written, and
  normalisation is a decision procedure, not a simplification — a checker that normalises
  could accept a term the kernel rejects.
* **Names *are* kept** (`const`/`decl`/`builtin` names) — they are the identity of a
  declaration, and the export's whole point is that a name means one thing (Y4).
* **No `mvar`, no `hole`.** An export is a closed, elaborated declaration: a metavariable
  or an unfilled sort is a refusal by the writer, not a term a verifier has to interpret.
* **`options` is checked, not obeyed.** A verifier compares the atom against the default
  vector and rejects any other. Experimental modes therefore produce no claim.
* **The digest is over the canonical bytes of everything above it**, with the algorithm
  domain-separated (the cache already uses `Wiz/Smt/Sha256` with length framing; reuse the
  primitive, not the key scheme).

**A precedent already in the tree.** The self-hosted kernel stores every constant with its
value and type inline (`selfhost/Kernel.wiz:352`: `const (name) (params) (levels) (value ty)`),
which is why a `Kernel.wiz` term is checkable with no global table at all. The export is the
*typed* version of that idea, with the one difference that matters: the inline definitions
must be re-checked, not trusted to the frontend that built them (Y4 is exactly the case where
"one value per name" was an assumption).

### 4.2 What is *in* the export, and what must be *said about* it

Three kinds of thing, and conflating them is how assurance claims go wrong:

1. **What the kernel checked** — `type`, `value` (and `impl`/`witness` when present).
   These are the objects a derivation is about.
2. **What the check trusted** (`trust.kernel`) — axioms, `assumed` registrations, the
   library's `nat.*` registrations the checker must model natively (or as axioms), and the
   `builtin` keys that make numerals. This list is the *machine-readable* form of
   `Globals.axiomsOf` (`Check.lean:1841`), which today returns `List String` for
   `#print axioms`. **Refactor so both read one structured walk** — otherwise the export's
   list and `#print axioms` drift, and the drift is invisible.
3. **What the *program's behaviour* trusts** (`trust.runtime`) — `implemented_by`,
   `repr:`, native representations, partial bodies. The kernel never runs them and the
   typing derivation does not use them. Listing them is honesty, not checking: a reader
   must not think a `checked` export says the compiled code agrees with the definitions.

The `checked` verdict is always *modulo* (2). The report must print (2) next to it, the
way `#print axioms` does, and the format must refuse a `decl` whose constants are not
covered by a `trust` entry or a `decl` in the same file (an unresolved constant is a
format error, not a checker error).

### 4.3 Sizes and cost

* **Term nodes per declaration**: `Nat.rec` and the class recursors are the large ones
  (hundreds to low thousands of nodes); the median `lib/` declaration is small. A whole
  `lib/` export is plausibly tens to low hundreds of MB of text; gzip-friendly. *Not
  measured* — an S3 acceptance test should print the byte count.
* **Verification cost**: the reference checker is deliberately slow (substitution, fuel
  3000). Checking all of `lib/` may be minutes to hours; that is acceptable *once per
  change*, not per user run. CI shape: check the modules a PR touches; nightly, check all.
* **Cache shape**: the export is written at the same point as the cache entry
  (`Cache.Effect` already carries `decls` — each with `type`, `value`, `impl`, `witness`
  — plus `builtins` and `assumed`), so there is one serialiser and one place to drift. `--cache-verify` currently checks *bytes
  against manifest* (consistency, not typing — `cache-trust-boundary.md` §0); with exports
  it can additionally re-check *typing*, which is the only thing that would catch a buggy
  elaborator writing a self-consistent wrong entry.

### 4.4 The independent checker: what it is, and how it becomes a theorem

Four candidates, ranked by independence and by cost. The recommendation is **A then C**.

| | implementation | independent of `Wiz/Core`? | independent of the spec? | cost |
|---|---|---|---|---|
| **A** | WizMeta's checker, extended to the full syntax, made executable (`wizmeta-check`), reading `wiz-core/1` | **yes** (no shared code; different algorithm) | no (it *is* the spec's checker) | weeks (S2+S4) |
| **B** | `Kernel.wiz` over an export whose `const` carries `(value, ty)` inline | no (shared design, differential-tested) | yes | days-to-weeks (needs a `Tm` writer in Wiz) |
| **C** | a fresh implementation from the *format + CoreSpec* only, by a lane that has not read `Check.lean` | **yes**, maximally | yes | months for `lib/` |
| **D** | a second `Wiz/Core`-style kernel in Lean | no | yes | months, and it is not independent |

A is the right first checker because it already exists and covers most of the corpus, and
because its *disagreements* are the valuable output (WizMeta's review found D2). B is a
cheap fourth voter and a genuinely different *language*; it is worth having, but its shared
lineage means it cannot be the primary claim. C is what "independent re-checking" means at
full strength and should be started only after A has stabilised the format — otherwise the
format churns under it.

**The theorem that turns "checked" into a proof.** The rules are data, so build a
derivation datatype and a total validator:

```lean
inductive Deriv where
  | mk (r : Rule) (side : Bool) (kids : List Deriv)

def Deriv.concl : Deriv → Jdg
def checkDeriv (d : Deriv) : Bool                     -- total, structural
theorem checkDeriv_sound (h : checkDeriv d = true) : Derivable R d.concl
```

`checkDeriv_sound` is one induction, *provided* §2.3 item 3 holds: every hypothesis of a
rule is a decidable test on data or appears among its premises. That is the whole reason
to impose the discipline — without it, `checkDeriv` cannot decide `R r` and the theorem is
false as stated (there would be a `Prop` hypothesis nothing checks).

Then: an export is `checked` only when the checker returns a `Deriv`, and the report says
`checked (derivation …)`. The residual trust is (i) the rule data being the intended rules,
(ii) `checkDeriv`'s implementation of them, (iii) Lean's kernel accepting
`checkDeriv_sound`. (i) is the spec review; (ii) is ~200 lines and can be re-implemented
independently (candidate C); (iii) is the de Bruijn argument applied to the assurance
tooling itself — and it is a *much* smaller thing to trust than 6 291 lines of Wiz-specific
kernel.

**The tri-state, never binary:**

| verdict | meaning |
|---|---|
| `checked` | a derivation was produced and validated |
| `checked-modulo T` | as above, with the named trust list `T` (always printed) |
| `unchecked-part W` | the declaration used `W` (an `impl`, a witness, a `ν`, a size) that the checker does not implement; **not** a pass |
| `unknown R` | fuel exhausted, panic, or a format the checker refused; **not** a pass |
| `rejected M` | the checker says not derivable; on the shipped library this must be **0** and any occurrence is a kernel bug or a checker bug to adjudicate |

A `rejected` count above zero blocks the gate. An `unchecked-part` count is a *ratchet*:
a checked-in expected list, so a new unchecked construct fails CI until the rule is added
(“never weaken a gate to go green”).

### 4.5 Example report (shape, not a measurement)

```
wiz-core/1  digest sha256-<…>
  module lib/Prelude   options: default
  declared <n>   checked <n>   unchecked-part <u>   unknown <x>   rejected <r>
  kernel trust: 1 axiom (castRefl); <k> builtin nat.* registrations
  runtime trust: <i> implemented_by; <j> native representations  (not checked)
  derivations: <n> validated; rule coverage: <m>/<f> spec files fired
```

(`<…>` are placeholders; the only number in this block that is a documented fact is the
one axiom, `castRefl`. `Status.md` §7.1 lists the `nat.*` registrations.)

The `derivations` and `rule coverage` lines are what L1 buys; without them the report is
L0 with better manners.

---

## 5. Risks

Ordered by how quietly they fail.

1. **The spec is a moving target and rots.** A rule change in `Wiz/Core` that does not
   reach `WizMeta` makes the differential a comparison against an older theory; the tests
   still pass because the corpus is old. *Detector*: the `Translate`/rule-file coverage
   test (§2.3 item 6) and a `conformance` case that fails when a new `Term` constructor has
   no rule. *Mitigation*: N8's same-PR policy.
2. **Shared design mistakes.** All three voters can be wrong together (F1, F2, K6 were).
   *Detector*: distinguishing terms for every switchable rule (D6) and a mutation test
   (§3.5). *Mitigation*: candidate C, and adjudicating every excuse in the ledger.
3. **The corpus is mistaken for a theorem.** "0 disagreements" reads as soundness.
   *Detector*: a report format that always prints the denominator, the outside count, the
   uncompared count and the excuse count (§4.5 shape). *Mitigation*: the doc sentence in
   §3.6, and never writing "verified" before L1.
4. **The translation is lossy where it matters** (D1–D5). *Detector*: S0. *Mitigation*:
   the round-trip + injectivity tests, and a rule that the spec never drops a check because
   the elaborator would have done it.
5. **A checker that panics or loops is not a verdict.** `panic!` returns a default in
   `Wiz/Core` (21 sites), and fuel exhaustion in the reference checker is "neither".
   *Detector*: the tri-state, and a rule that no path returns `ok` on `unknown`.
   *Mitigation*: an export checker that is total by construction (fuel everywhere) and a
   test that a hit `panic!` in the kernel fails the run instead of defaulting.
6. **The export overclaims.** A `checked` line that hides an unchecked `impl` or a witness
   is worse than no export, because it looks like assurance. *Detector*: the tri-state and
   the `unchecked-part` ratchet. *Mitigation*: v1 certifies `type`/`value` only; the report
   says so in a fixed line.
7. **Format churn breaks the digest/cache story.** A format change invalidates every
   stored export and every digest recorded somewhere. *Detector*: the version atom plus a
   refusal-by-name. *Mitigation*: `wiz-core/2` is a new atom, never a reinterpretation of
   `1`; keep v1 readers in the tree for the retention window.
8. **Perf work changes the kernel under the proof.** The audit already lists thirteen
   perf findings in `Wiz/Core`; a `partial`→`Option` rewrite for provability would collide
   with them. *Mitigation*: do not rewrite `Wiz/Core` for proofs (L2 is out of scope);
   prove the *small* leaves (`Level.equiv`, `QPoly.le`, the size order) where the code is
   stable, and freeze a *copy* if a theorem about the whole is ever wanted.
9. **Sizes.** No model, known inconsistencies elsewhere, barely used. *Mitigation*: keep
   sized programs out of the export's `checked` class until T4 has a model (the
   `unchecked-part` mechanism exists precisely so this is sayable without blocking the
   rest).
10. **The export is treated as a build attestation.** `docs/bootstrap-chain.md`'s
    attestations bind *bytes to inputs*; the export binds *bytes to a judgement*. A signed
    export says "this declaration was checkable"; it does not say "the binary is
    reproducible" or "the C compiler is right". Keep the two documents' claim tables
    separate; `cache-trust-boundary.md` §1–5 is the signing half and this note is the
    typing half.

---

## 6. Slices, ordered, with acceptance tests

Effort is agent-time, low confidence, and excludes waiting on CI. A "day" is an agent-day
of editing and one test run; a "week" includes review.

### S0 — The fidelity probe (the smallest first step; 1–2 days, no production code)

**What.** One test file (a new case in `=meta`, or a `scripts/` check) that measures what
the spec cannot see:

* for every corpus term and every `lib/` declaration, `ofTerm` must return `none` only for
  a **named** reason (a `Lossy` variant, not a bare `none`), and the reason must be in a
  checked-in list;
* for a constructed pair per defect D1–D5, the test *demonstrates* the blindness: e.g.
  `pi` at `⟨0,1⟩` and `⟨1,1⟩` are both accepted by the spec (their `imax` is `1`) while
  the kernel rejects the first (`checkComponentSort`, `Check.lean:890`);
* the translation does not hide a distinction: for every pair of corpus terms that the
  kernel treats differently, the spec must not give their images the same verdict; and
  for every image the spec accepts, the kernel must accept the term it came from. In S0
  these are **reported, not asserted** — each reported pair is a named defect and becomes
  a work item; once fixed it is promoted to an assertion.

**Acceptance.** A printed table: N corpus terms, N with a named loss, the count per
defect, and the list of pairs where the spec's verdict differs from the kernel's on
translated terms. D1–D5 each has at least one witness (this *is* asserted: the
construction must succeed). The reported collapses are the S1/S2 backlog, not a test
failure. No kernel change; the one build (`lake build tests WizMeta`) goes through `heavy`
like every other build.

**Why first.** It is one test, it quantifies the value of every later slice, and it can
overturn the reading of "0 disagreements" in `Status.md` §7.1 — which is better learned
before S2 spends weeks extending a spec whose current votes are on a coarser term.

### S1 — Make the spec authoritative where it is permissive (3–5 days)

**What.** `autoImplicit false` in every `Spec/*` file; the hypothesis discipline (§2.3
item 3) applied file by file; one distinguishing term per switchable rule (D6); the three
untested bridges as tests (§3.4); the adjudication ledger (§3.3).

**Acceptance.** Flipping any `Opts` field changes at least one corpus verdict (a test that
iterates the fields); every `Excuse` is used by ≥1 term and every unexcused kernel-only
rejection fails; the marking/sorts/entry-point bridge tests pass on the corpus; `=meta`
grows from 24 to ~30 cases and stays green.

### S2 — Complete the spec to `Tprog` (3–6 weeks, the biggest single item)

**What.** `Tm` gains the constructors of §2.3 item 1; `Translate` gains its inverse and
the round-trip/injectivity tests; the rule files gain quantities (a usage judgement `▷ U`),
sizes/`ν`/`split`/`letUnit`/numerals/`prop`/`ulift.k`/`prf`; `Decl'` gains `impl` and
`witness` rules. *Quantities are the expensive part*: `QPoly` (polynomials, `≤`, join) is a
different decision procedure from the labels the spec has, and `QPoly.le` is one of the
three leaf procedures worth proving (S6).

**Acceptance.** The corpus's "outside the fragment" count is 0 for terms that use no
`ν`/size (the deliberately quarantined set stays named); `acceptUncompared` is 0 on the
corpus; the reference checker returns a verdict on every declaration of `lib/Prelude.wiz`
that the kernel accepts; the usage-only excuse disappears from the ledger (it is modelled,
not excused).

### S3 — The canonical export (1–2 weeks)

**What.** `Wiz/Export.lean`: `term`, `level`, `decl`, `options`, `trust` printers over
`Term`/`Level`/`Decl`, canonical (names erased, hints/labels dropped, dependency order);
`wiz export FILE -o FILE.wizcore`; a digest; a refusal-by-name for any schema but
`wiz-core/1`; the writer invoked at the `addDecl` boundary so the exported declaration is
the checked one.

**Acceptance.** (a) round-trip `parse ∘ print = id` on every `Term` in the corpus and in
`lib/Prelude.wiz`; (b) **determinism**: two processes with different `HOME`, `TMPDIR`,
locale and `SOURCE_DATE_EPOCH` produce byte-identical output (the `repro-fixpoint.sh`
shape, one file); (c) a declaration with an unresolved constant is a format error; (d) a
one-byte change to any term changes the digest.

### S4 — The independent checker, and the derivation theorem (2–4 weeks, then open-ended)

**What, in two halves that can run in parallel:**

* **S4a (the theorem, ~1 week).** `Deriv`, `checkDeriv`, `checkRule` per former file,
  `checkDeriv_sound`. No coverage needed: it is a theorem about whatever rules exist.
* **S4b (the checker).** WizMeta's checker extended to the full syntax, executable, reading
  `wiz-core/1` with a parser written from the format (not `Wiz/Cache.Sx`), returning the
  tri-state; then derivation emission (the hard half: the search must build the tree).

**Acceptance.** S4a: `checkDeriv_sound` compiles with no `sorry`; a mutated derivation is
rejected (negative test). S4b: `wiz verify lib/Prelude.wizcore` prints the §4.5 report with
`rejected 0, unknown 0`; a declaration that is ill-typed in a way the third voter cannot see
today (the D1 wrong component sort; `Type : Type`) is `rejected`; the `unchecked-part` list
is exactly the checked-in expected list.

### S5 — The library gate (1–2 weeks after S4)

**What.** CI checks the exports of the modules a PR touches; nightly checks `lib/`;
`--cache-verify=strict` optionally re-checks typing through the independent checker.

**Acceptance.** The report from §4.5 as a CI artifact with `rejected 0`; the
`unchecked-part` ratchet; a nightly run over all 107 files; a hand-forged cache entry that
is hash-consistent but ill-typed is caught by the strict mode (the `cache-trust-boundary`
attack, now *detected* rather than merely *possible*).

### S6 — Proved leaves (1–2 weeks each, independent of S2–S5)

**What.** `Level.lean`'s four `partial` functions made total; `equiv` proved sound (and
complete where it claims) against evaluation in ℕ; `QPoly.le` proved sound; the size order
proved sound. Each is a few hundred lines and does not depend on the export at all.

**Acceptance.** The theorems compile; the kernel uses the *same* functions (no second
implementation — a mismatch would be theatre); a `grep -c 'partial def'` on the proved
paths is 0; the proofs survive a kernel change (they are about leaf code that does not
move).

### S7 — Candidate C, the from-scratch checker (months; start only after S3 is stable)

**What.** An implementation from `wiz-core/1` + `docs/CoreSpec.md` only, written by a lane
that has not read `Wiz/Core/Check.lean`, in a different language (Wiz, Rust, or Python).
**Acceptance.** Agrees with A on the whole `lib/` export (no disagreement tolerated without
adjudication); its disagreements with A are triaged as A-bug / C-bug / spec-ambiguity, and
each resolution edits the format doc.

**Ordering rationale.** S0 can invalidate the premise of S2 (if the translation is lossy
in many places, S2's shape is wrong) and is one test. S1 makes every later vote mean
something. S2 buys *coverage*. S3 buys *a faithful artefact independent of the spec* —
which is why it can start before S2 finishes, and why the export is worth having even if
the spec stalls. S4a buys *kind* (a theorem) cheaply; S4b is the long pole. S5 makes it
used. S6 is orthogonal and should not wait. S7 is the only path to full independence and
must not start before the format settles.

---

## 7. Honesty ledger

| claim | status today | evidence / falsifier |
|---|---|---|
| the kernel is 6 291 lines / 5 003 non-comment, 123 `partial`, 21 `panic!` | **true at `3fa0eec95`** | `wc -l`, `grep -c`; `Status.md` records 6 286/4 998 at `d853fde79` |
| a declarative spec of the core rules exists | **true, partial** | `WizMeta`, 44 constructors vs 56; §2.2 D1–D6 |
| three implementations agree on the differential corpus | **measured (L0)** | recorded 2026-11-11: 484/537 in fragment, 0 disagreements; 6 usage-only, 1 guard, 53 outside, ≤10 uncompared. Not re-run for this note |
| the corpus distinguishes the switchable rules | **false** | `wiz-meta.md` §4.1; D6 |
| the third voter sees the component sorts the kernel checks | **false** | `Translate.ofSorts` collapses `⟨dom,cod⟩`; `Check.lean:890` checks each |
| the third voter sees the proof markers the kernel requires | **false** | `Translate.ofTerm` has no `prf` case; `kernelInfer` marks |
| the third voter sees `impl` agreement or witnesses | **false** | `Translate.ofDecl` refuses both |
| "checked equivalence" exists | **false**; L0 only | §3.1 |
| a derivation checker sound against the rule data exists | **not attempted**; the pieces exist | `Derivable`, `Rule` as data; §4.4 |
| an export format exists | **false**; most of the substrate does | `Cache.Sx`/`term`/`dterm` (exhaustive printer, total reader), `Effect.toSx`; no versioned envelope, no canonical form, no digest |
| an independent checker exists | **false** | WizMeta is an independent *implementation*, not an independent *checker*: it shares `Translate` with the kernel and its design with both kernels |
| the cache's replay is checkable | **false**; it is authenticated-or-not, not typed | `cache-trust-boundary.md` §0; `Effect.apply` inserts unchecked |
| a theorem about `Wiz/Core` exists | **false, and out of scope** | 123 `partial` defs; `metatheory-plan.md` §3.3 |
| the spec is consistent | **unknown** | T2 has no published model; sizes have none (E1, T4) |
| the export says anything about erasure/backends | **false** | `Status.md` §7.0's last rows |

The three sentences this note does **not** license anyone to write:

* "the kernel is verified" — it is not, and L1 would not make it so;
* "the spec is correct" — it is a careful statement; whether it is the intended theory is
  a human decision, and whether it is consistent is open;
* "the export proves the program" — it proves a typing judgement modulo a trust list; the
  compiled code, the C compiler and the runtime are outside it.

---

## 8. Decisions needed

1. **Accept the target as one-directional accept-side soundness**, with completeness
   explicitly out of scope (the kernel may reject more; the ledger names each excuse).
   *Recommend: yes.*
2. **Adopt L1 (derivation-checked) as the first "verified" milestone**, not L2, and write
   the doc sentence of §3.6 when it lands. *Recommend: yes; it is the only version that
   does not depend on rewriting `Wiz/Core`.*
3. **Fix the spec's permissiveness first (S0+S1)**, before extending its coverage (S2).
   *Recommend: yes — otherwise S2 extends a spec that cannot see the checks it is supposed
   to be a spec of.*
4. **The four open rule decisions** (`wiz-meta.md` §7): EqTy Cross/Levelled, payload
   Kernel/Stuck/Uniform, equations at every sort, quantities at Prop Π/Σ. The equivalence
   must name one. *Recommend: state the equivalence against the kernel's current answer,
   and file the intended answer as what the kernel should change to — not as a switch.*
5. **Export unit and retention**: per module, self-contained v1; digests in v2; exports
   written beside the cache. *Recommend: yes; the byte count is an S3 acceptance test.*
6. **Whether the independent checker is WizMeta (A) or a from-scratch lane (C) first.**
   *Recommend: A now, C after the format settles; B (`Kernel.wiz`) as a cheap fourth voter
   if someone wants a second language sooner.*
7. **A standing rule: a kernel rule change updates `WizMeta` and the export grammar in the
   same PR** (N8). Without it, S2's work has a half-life of weeks.
   *Recommend: yes; enforced by the conformance test, not by discipline.*
8. **Size policy for the claim**: `ν`/sizes are `unchecked-part` (certified as *outside*
   the claim, not silently passed) until T4 has a model. *Recommend: yes — this is exactly
   what the tri-state is for.*

---

## 9. What ran

Read-only only. No `lake build`, no `heavy`, no `wiz` invocation, no test run:

```
git worktree add … -b agent/kernel-assurance integration/train12
wc -l Wiz/Core/*.lean Wiz/Rig.lean Wiz/Rig/Instances.lean
grep -c 'partial def' / 'panic!' over the same files
grep -cE '^  \| ' for the Term / Tm constructor counts
grep -n / sed -n over the files and notes named in the header
```

No number in this note is a measurement of behaviour, a timing, or a test result. The
recorded differential counts (484/537, 230/248/6) are from `wiz-notes/wiz-meta.md`'s
2026-11-11 run and were not reproduced. The `lib/` declaration count is a crude grep and
over-counts; it is used only to size the export, not as evidence.

## 10. Adjacent work and non-duplication

* `wiz-notes/cache-trust-boundary.md` (2026-11-22) is the **signing** half of the cache
  question: who wrote the bytes. This note is the **typing** half: are the bytes
  well-typed. They compose; neither substitutes for the other. An export checked by §4.4
  and signed per that note is the first configuration in which a cache replay is both
  authenticated and typed.
* The in-flight lane `untrusted-elab-cache` is measuring the same cache boundary; its
  numbers should be cited in S5 when they exist, not here.
* `metatheory-plan.md` is the long-range plan (M2 = `Sound(xcheck, Tprog)`, M4–M9). This
  note does not replace it; it re-orders the *near* term around L1 and the export, and it
  argues that M2's infrastructure (`Deriv` + `checkDeriv_sound`) is worth building before
  the full checker.
* `wiz-notes/wiz-meta.md` is the record of the spec as built; §2.2's D1–D6 are the delta
  between that record and this design.
