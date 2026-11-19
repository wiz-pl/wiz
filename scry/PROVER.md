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
claim      noFlow f I M S      I : tainted (point, register) rows
                               M : derived tainted locations
                               S : the source relations the claim quantifies over
```

`noFlow f I M S` means:

1. **closure of taint** — for every instance of every rule whose head is `tainted`
   (including the load rule), if the instance's `tainted`/`mtainted` premises are in
   `I`/`M` (or are EDB location seeds) and its other premises hold in the EDB (including
   the negated `san` premises), then its head is in `I`;
2. **closure of locations** — for every instance of the store rule, if its `tainted`
   premise is in `I` and its `flow`/`mstore` premises hold, then its location is in `M`;
3. **no alert** — the `alert` rule has no instance with its `tainted` premise in `I`.

The certificate `(f, I, M, S)` is the whole proposition. `I` and `M` are
*over-approximations of the reachable taint and tainted locations*, not the fixpoint: any
superset that is still sink-free works, and for the safe C# twin a one-row `I` suffices.
`S` selects the seeds: `{src}` is "no `Console.ReadLine` value reaches…", while
`{src, retsrc}` is the SQL property "every sink argument is a constant or a parameter
bind" (`param` flows are allowed by leaving `param` out).

### Why this fragment, and what it deliberately excludes

* It is the **tuple** fragment of the engine's taint rules. `evalAtoms` on the EDB with
  relation 4 replaced by `I` enumerates exactly the rule instances the closure obligation
  talks about, using the same matcher the engine uses. No new semantics is invented.
* **Memory is covered.** `mstore`/`mload`/`mtainted` form a second mutual recursion, so
  the invariant is a pair of sets: `I` over `(point, register)` and `M` over locations.
  The checker discharges the store and load rules as separate closure obligations. The
  EDB's `mtainted` rows are location seeds imported from other functions; they are part
  of the base, not of `M`.
* **A counterexample is a provenance path.** The alert obligation finds the first alert
  instance and walks the taint back to a seed through the same rule instances, rendering
  `src -> store -> load -> flow -> sink`. That walk is explanation, not proof; the
  checker's answer is still just the invariant's acceptance or the alert instance.
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
  invariant : List (Nat × Nat)   -- tainted rows
  locations : List Nat           -- derived tainted locations
  sources : List Nat             -- source relations quantified (`[]` = all)
  property : Scry.Property       -- noFlow | constantOrBound
```

That is the certificate: **a finite set of `(point, register)` rows and a finite set of
locations**. It is tiny compared with the analysis trace (one row for the worked
example), human-checkable by reading the script, and it is not a re-encoding of the
evaluator's provenance.

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

(`src`, `param`, `retsrc`; closure; check). `Scry.prove` runs it and returns a tagged
`Scry.Verdict` carrying the `Claim`; `Scry.proveWith` runs any script. A claim's
`sources` field selects the `intro` rows (and the checker drops the other seed
relations), so a claim about one property does not quantify over every seed.

The script is **search**: it is recorded for reports, not replayed by the checker. A
user can skip it entirely and hand-write `I`; `Scry.check` accepts or rejects that. This
is the separation the whole design turns on: the prover may use the fixpoint, a
heuristic, or a human's insight; the checker is a total function of `(rules, EDB,
claim)`.

## 4. The checker, and why it is independent

`Scry.check p edb claim` has four obligations, in order:

1. **vacuity** — the selected source relations must have at least one row, and the
   function must have at least one sink. Otherwise the verdict is `vacuous` with the
   reason ("the claim's source set is empty" / "the claim's sink set is empty"), never
   `proved`.
2. **taint closure** — for every rule with a `tainted` head (indices 0, 1, 2, 3, 7 of
   `ruleTaintProgram`), enumerate `Scry.evalAtoms` over the EDB with relation 4 replaced
   by `I` and relation 13 by the EDB seeds plus `M`; every match's head
   `(point, register)` must be in `I`. The first miss is `refused` with the rule number
   and the fact.
3. **location closure** — for the store rule (head `mtainted`), every instance whose
   `tainted` premise is in `I` must have its location in `M`.
4. **no alert** — enumerate the `alert` rule's body the same way; any match is a
   `refuted` claim with the provenance path and the sink/argument.

It calls neither `Scry.analyze`/`Scry.eval` (the fixpoint) nor `Scry.prove` (the
search). The only shared component is the datalog *matcher* (`evalAtoms`), which is
part of the trusted semantics, not the search: it says which rule instances exist for a
given database, not which facts the analysis derived.

**Soundness argument (stated, not mechanised).** Let `T` and `L` be the least `tainted`
and `mtainted` fixpoints. The two closure obligations are checked together by induction
on the height of a derivation: a seed is in `I` (checked by the seed-head rules), a
store step's location is in `M` because its tainted premise is in `I` (location
closure), and a load step's result is in `I` because its location is in `M` (taint
closure). Hence `T ⊆ I` and every *derived* location is in `M`; location seeds are
already in the EDB. Then the alert rule has no instance with premises in `T`, because
closure puts `T ⊆ I` and the no-alert obligation has no instance under `I`. Therefore
`alert` is empty: no path from a seed to a sink.

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
`Fixtures.Runner.Main`.

<!-- FACTBLOCK: filled from the prototype run -->

The proof obligations checked for the safe twin:

<!-- OBLIGATIONS: filled from the prototype run -->

The same script on the unsafe twin:

<!-- UNSAFE: filled from the prototype run -->

Wrong proofs, all rejected:

<!-- WRONG: filled from the prototype run -->

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
5. **The search is not verified.** `Scry.prove` returns a tagged verdict:
   `proved` (with the claim), `refuted` (with a witness), `refused` (the certificate is
   not closed), `script-failed` (an ill-formed script), or `vacuous`. Only `proved` is an
   acceptance. A refutation is an alert instance, not a proof that every possible
   invariant fails.
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
| `lib/Scry/ProverExamples.wiz` | tiny EDBs for the safe/unsafe pair, the memory pair, vacuity, source selection and `constantOrBound` |
| `Tests/Groups/ScryProver.lean` | group `scry-prover` (library shard): safe twin proves, unsafe twin refuted, memory covered, vacuity rejected, tagged verdicts, source selection |
| `scry/PROVER.md` | this note |

Test cases (all in the interpreter, reading the checked-in spills, so no tree-sitter and
no .NET):

<!-- TESTS: filled from the prototype run -->

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
2. Interprocedural: make the `param`/`retsrc` seeds *subgoals* (a summary certificate per
   caller), so a corpus-wide claim is a tree of per-function invariants.
3. Guards/bounds: add `guard`/`use` EDB rows from `Scry.Bounds`, define the cut claim for
   "every write preceded by a check", and prove the `memcpy` length property on a C
   fixture.
4. A `scry prove FILE --claim …` command: parse a small script, run it, print the
   invariant and the verdict, and exit non-zero on a rejected claim (with the offending
   fact). The dogfood driver `scry/tools/ProverMain.wiz` is the prototype.
5. Mechanise the memory closure induction alongside the taint one.
