# scry prover mode: design and first slice

Status: design + prototype (2026-11-19, branch `scry-prover`). Builds on
`scry-derivation.md` (S8 certificates), `scry-csharp.md`, and the rule-pack taint engine
(`lib/Scry/RuleTaint.wiz`, `Scry.Interproc`). The working copy of this note is
`scry/PROVER.md` in the repo.

## 0. The problem, in one sentence

A finding is a fact ("this path exists"); a prover must establish a *universal* claim
("no path exists", "every sink is behind a check"), and no finite derivation of a
Datalog fact proves a universal. Everything below follows from that difference.

The prototype's worked property is the brief's own example:

> no `System.Console.ReadLine` result reaches `System.Diagnostics.Process.Start`
> in `scry/corpus/csharp/taint/cwe78-process-safe.cs`.

The same claim on `cwe78-process-unsafe.cs` must *fail*, and a hand-written wrong proof
of it must be *rejected* by a checker that never runs the analysis.

## 1. The proposition language

A claim is about **one function's EDB**: the relations `Scry.RuleTaint` builds before the
fixpoint (`flow`, `src`, `sink`, `san`, `gen`, `param`, `retsrc`, `mstore`, `mload`, …).
The language is a finite, closed-world fragment of Datalog with negation, read as a path
property over `(point, register)` nodes:

```
atomic     R(t₁, …, tₙ)        R an EDB relation, tᵢ a logical variable or a U64
formula    φ ::= R(t⃗) | ¬R(t⃗) | φ ∧ φ | ∀x⃗. φ
claim      noFlow f I          I : set of (point, register) pairs
```

`noFlow f I` means:

1. **closure** — for every instance of every rule whose head is `tainted`, if the
   instance's `tainted` premises are in `I` and its other premises hold in the EDB
   (including the negated `san` premises), then its head is in `I`;
2. **no alert** — the `alert` rule has no instance with its `tainted` premise in `I`.

The pair `(f, I)` is the whole proposition. `I` is an *over-approximation of the
reachable taint*, not the fixpoint: any superset that is still sink-free works, and for
the safe C# twin a one-row `I` suffices.

### Why this fragment, and what it deliberately excludes

* It is the **tuple** fragment of the engine's taint rules. `evalAtoms` on the EDB with
  relation 4 replaced by `I` enumerates exactly the rule instances the closure obligation
  talks about, using the same matcher the engine uses. No new semantics is invented.
* **Memory is excluded.** `mstore`/`mload`/`mtainted` are a second mutual recursion; an
  invariant over `tainted` alone does not cover it. The checker *refuses* a function
  whose EDB contains a store or a load (`Scry.checkMemory`), with a reason. Refusing is
  the honest behaviour; silently ignoring the rules would be unsound.
* **`param`/`retsrc` are assumptions.** They are seeds that `Scry.Interproc` derives
  from callers/callees. The certificate is intraprocedural; the note says so, and
  `Scry.check` does not claim the seeds themselves. This is the same assumption
  `Scry.Certify` reports for findings.
* **Forbidden calls are a different property.** `badalert` (`gets`, `strcpy`, …) is not
  a flow property; a `noFlow` claim says nothing about it, and a program can have a
  proof and a forbidden-call finding at the same time. That is correct, not a gap in the
  proof, but a report must not read "checked" as "finding-free".
* **No arithmetic, no bounds, no guards-as-facts.** The engine has no EDB relation for
  "here a length was checked", so a `memcpy` length property is outside the current
  fact language (see §6).

## 2. The proof object

```wiz
structure Scry.Claim where
  func : String              -- a label; the EDB identifies the function
  invariant : List (Nat × Nat)
```

That is the certificate: **a finite set of `(point, register)` rows**. It is tiny
compared with the analysis trace (one row for the worked example), human-checkable by
reading the script, and it is not a re-encoding of the evaluator's provenance.

A proof of a finding stays a `Scry.Derivation` (`Scry.Cert`); the two certificate kinds
are duals:

| claim | certificate | checker |
|---|---|---|
| ∃ path (finding) | derivation tree, rule instance by rule instance | `Derivation.check` |
| ∄ path (no-flow) | invariant `I` | `Scry.check` |

## 3. What a tactic is here

A tactic **transforms a goal into subgoals over facts**, and the search is separate from
the check. The prototype's script language is deliberately small:

| tactic | goal transformation |
|---|---|
| `intro R` | finite `∀`-introduction: add every row of EDB relation `R` to `I` (the seed rows) |
| `apply ri` | apply rule `ri`'s tainted-head instances, adding their heads to `I` |
| `close` | derived tactic: `apply` every tainted-head rule to fixpoint (bounded by the EDB size) |
| `split` | split `noFlow f I` into the closure and no-alert obligations |

The default script is

```
intro 1; intro 6; intro 7; close; split
```

(`src`, `param`, `retsrc`; closure; check). `Scry.prove` runs it and returns the
resulting `Claim`; `Scry.proveWith` runs any script.

The script is **search**: it is recorded for reports, not replayed by the checker. A
user can skip it entirely and hand-write `I`; `Scry.check` accepts or rejects that. This
is the separation the whole design turns on: the prover may use the fixpoint, a
heuristic, or a human's insight; the checker is a total function of `(rules, EDB,
claim)`.

## 4. The checker, and why it is independent

`Scry.check p edb claim` has three obligations, in order:

1. **fragment** — refuse if the EDB has `mstore`/`mload` rows.
2. **closure** — for every rule with a `tainted` head (indices 0, 1, 2, 3, 7 of
   `ruleTaintProgram`), enumerate `Scry.evalAtoms` over the EDB with relation 4 replaced
   by `I`; every match's head `(point, register)` must be in `I`. The first miss is
   reported with the rule number and the fact.
3. **no alert** — enumerate the `alert` rule's body the same way; any match is a
   counterexample and is reported with the sink and argument.

It calls neither `Scry.analyze`/`Scry.eval` (the fixpoint) nor `Scry.prove` (the
search). The only shared component is the datalog *matcher* (`evalAtoms`), which is
part of the trusted semantics, not the search: it says which rule instances exist for a
given database, not which facts the analysis derived.

**Soundness argument (stated, not mechanised).** Let `T` be the least `tainted`
fixpoint. By induction on the height of a derivation: every `t ∈ T` is in `I` — the
base case is a rule whose `tainted` premises are empty, whose instance closure covers;
the step case applies closure to the instance built from the (smaller) premises, which
are in `I` by induction. Then the alert rule has no instance with premises in `T`,
because closure puts `T ⊆ I` and the no-alert obligation has no instance under `I`.
Therefore `alert` is empty: no path from a seed to a sink.

Two honest caveats:

* The argument assumes the EDB is the complete input (closed world) and that the rules
  are exactly `ruleTaintProgram`'s taint fragment. The checker checks the latter by
  refusing memory rows; the former is the engine's own assumption.
* The argument is a paper proof in this note. The prototype has **no** Wiz theorem
  `check ... = ok → alert empty`. Mechanising it needs the fixpoint's induction
  principle (a `Derivation`-height relation, as `Scry.Cert` has for the positive
  direction) and is the obvious next step, not a claim made here.

## 5. Worked example

The corpus is the C# taint pair; the analyser lowers it with `Scry.Cs.programOf`, then
`Scry.analyze` produces the per-function EDB. The worked example uses the `edb` of
`Fixtures.Runner.Main` (10 `flow` rows, 11 `gen` rows, no stores or loads, so the
fragment applies).

The proof script is the default one:

```
intro 1; intro 6; intro 7; close; split          # src, param, retsrc, closure, check
```

**Safe twin** (`cwe78-process-safe.cs`, `int.Parse(Console.ReadLine())` before the
`sink`). The prover produces

```
I = {(0,0)}                 # point 0, register 0: the Console.ReadLine result
check = ok
```

That is the whole certificate: one row, for a function with 10 flow edges and 11
definitions. The `int.Parse` call is a result sanitiser, so the transfer rule has no
instance at its point (`san` holds there), and closure adds nothing. A human can check
the claim by reading the code and the script; the analysis trace is not consulted.

The proof obligations the checker discharged:

1. **closure** (`Scry.checkRulesClosed`): rules 0, 1, 2, 3 and 7 have `tainted` heads.
   Rule 0's instance is `(0,0) ∈ I`; rules 1 and 2 have no `param`/`retsrc` rows; rule 7
   has no `mtainted` premise; rule 3 has no instance because `san` holds at the
   `int.Parse` point for the register it defines.
2. **no alert** (`Scry.checkAlertRules`): the alert rule has no instance whose
   `tainted` premise is in `I`; the sink's argument register is not `(0,0)`.
3. **fragment**: no `mstore`/`mload`/`mtainted` rows.

**Unsafe twin** (`cwe78-process-unsafe.cs`, the same script). The closure produces seven
rows, printed newest first:

```
I = {(10,10) (9,9) (7,7) (4,4) (3,3) (1,1) (0,0)}
check = rejected: the alert rule fires at sink 10 argument 1
```

`Scry.prove` returns `.none` at the `split` step: the script does not find a sink-free
invariant, and (correctly) the refusal is not a proof of the property either way. The
*checker* rejection is the refutation: with `I` covering the source, the alert rule has
an instance.

Wrong proofs, all rejected:

```
I = [(1,1)]                     on the safe C# EDB
  rejected: rule 0 derives tainted (0,0), which is not in the invariant
I = []                          (the safe invariant minus its seed)
  rejected: rule 0 derives tainted (0,0), which is not in the invariant
I = the unsafe 7-row invariant  checked against the safe program
  rejected: rule 3 derives tainted (2,2), which is not in the invariant
I = anything                    on a function with an mstore row
  rejected: the function stores (mstore); the memory rules are not covered by this checker
```

The third example is the point of the checker: the unsafe program's seven-row set is the
closure *there* (its `check` fails at the alert, not at closure); checked against the
safe program it is not even closed, because the two programs have different flow edges.
Nothing about the prover's state is trusted.

The tests also hand-write `I = [(0,0)]` for the tiny example and check it with no prover
involved (`ok`), then hand-write `I = [(1,1)]` (rejected). That is the "check without
search" path.

## 6. What is *not* proved

This section is the point of the exercise: a tactic system that can only re-derive what
the analysis already asserts is decoration, not verification.

1. **Nothing about arithmetic or memory safety.** "No unvalidated length reaches
   `memcpy`" is *not* proved here. It needs an EDB relation for length/guard facts and a
   bounds domain in the rule pack; the taint engine has neither. The C# twin's
   `int.Parse` is a *sanitiser* for taint, not a range check — the property proved is
   data flow, not length validity.
2. **No temporal/path logic.** "every write to `x` is preceded by a length check" is a
   dominator/cut property over the CFG. The design for it is: extract `guard(point, var)`
   and `use(point, var)` rows, prove that every source→use path crosses a guard with a
   cut certificate. That is a new proposition and a new checker; it is not in this slice.
3. **Not interprocedural.** `param`/`retsrc` are assumptions, not proved facts. The
   certificate says "given these seeds, no intraprocedural path"; the caller/callee
   argument is the summary walk's, as in `Scry.Certify`.
4. **Not the analysis's own soundness.** The parser, lowering, points-to, models and
   rule pack are trusted inputs. A wrong model makes a "proof" about the wrong program.
5. **The search is not verified, and `prove` returning `none` is not a proof.**
   `none` means "this script did not find a sink-free invariant", not "the property is
   false". Only `Scry.check`'s `ok` is an acceptance. (For the unsafe twin the checker
   *does* produce a counterexample — the alert obligation — which is a refutation of the
   claim, not a proof that every possible invariant fails.)
6. **No mechanised soundness.** See §4.

What makes the prototype more than decoration, concretely:

* the claim is universal over all sinks and all paths, not the existence of one path;
* the certificate for the safe twin is smaller than the fixpoint trace, and a human can
  read it;
* the checker is sensitive to the *program*, not the analysis's verdict: the unsafe twin
  is rejected with the same script shape;
* a hand-written `I` replaces the search entirely, and a wrong `I` is rejected — the
  tests do exactly that.

## 7. Prototype files and tests

| file | contents |
|---|---|
| `lib/Scry/Prover.wiz` | `Claim`, `Verdict`, `check`, the tactic datatype and `prove`/`proveWith` |
| `lib/Scry/ProverExamples.wiz` | two hand-built EDBs (safe/unsafe) with exact rows, for reading and for the tests |
| `Tests/Groups/ScryProver.lean` | group `scry-prover` (library shard): safe twin proves, unsafe twin refuted, wrong proofs rejected, memory refused |
| `scry/PROVER.md` | this note |

Test cases (all in the interpreter, reading the checked-in spills, so no tree-sitter and
no .NET):

| case | result |
|---|---|
| tiny examples: safe proves (`ok`, `I={(0,0)}`), unsafe refuted, empty and cross invariants rejected, `prove` on the unsafe EDB returns none | pass |
| the C# script: safe twin `ok` with a 1-row invariant; unsafe twin rejected at the alert; `prove` returns none | pass |
| wrong proof 1: the invariant minus its seed is rejected by rule 0 | pass |
| wrong proof 2: the unsafe invariant is rejected on the safe program (rule 3) | pass |
| fragment boundary: a store is refused, not accepted | pass |

`5 passed, 0 failed, 0 skipped` (`heavy --mem 5G`, `.lake/build/bin/tests --run
scry-prover 0..4`).

## 8. Alternatives considered

* **Refinement types over the value-flow summaries.** Exact and useful, but it needs a
  checker for the refinement logic and a semantics for the summaries; the EDB is already
  a finite first-order structure, and an invariant over it is the smallest honest step.
* **A Datalog query language with negation only.** Answers "is `alert` empty" by running
  the fixpoint; that is the analysis again, and it produces no artifact a second party
  can check. The invariant is the artifact.
* **A derivation for the negation (`\naf`).** Stratified negation gives a *model*, not a
  certificate; a proof of absence is coinductive. The invariant is the coinductive
  certificate for this finite monotone fragment.
* **Full temporal logic (LTL/CTL) over the CFG.** The right long-term language for
  "preceded by"; overkill for the first slice, and it needs guard facts before it can say
  anything the current EDB does not.

The shape is the one `code-analysis-design.md` §5.3 already prescribes for absence
certificates ("an invariant map `inv : Point → L` … a checker `Cert.check f inv` … a
post-fixpoint check, linear in the function's size"), specialised to the taint lattice
`L = 2^{point × var}` and with a tactic script on top. What §5.3 does not have, and this
note adds, is the *language* of claims and the separation of the script (search) from
the certificate (checking). The interval-domain instance, which is what a length/bounds
property needs, is the natural second user of the same checker shape.

## 9. Next slices

1. Mechanise the soundness theorem for `check` (derivation-height induction, reusing
   `Scry.Cert`'s flat-tree machinery).
2. Memory: extend `I` to `mtainted` (the invariant becomes a pair of sets) and check the
   two memory rules; then remove the refusal.
3. Interprocedural: make the `param`/`retsrc` seeds *subgoals* (a summary certificate per
   caller), so a corpus-wide claim is a tree of per-function invariants.
4. Guards/bounds: add `guard`/`use` EDB rows from `Scry.Bounds`, define the cut claim for
   "every write preceded by a check", and prove the `memcpy` length property on a C
   fixture.
5. A `scry prove FILE --claim …` driver: parse a small script, run it, print the
   invariant and the verdict, and exit non-zero on a rejected claim (with the offending
   fact).
