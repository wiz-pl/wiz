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
           cut f G             G : the guard points the cut relies on
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
* **Guards/bounds are facts, not a dominant-check predicate.** `Scry.Bounds` now
  exports `guard (point, var, hi, target)` ("on the edge to `target`, `var <= hi`"),
  `use (point, var, loc, cap, kind, const)` (an index/length access into a buffer with
  `cap` cells) and `before (node, usePoint)` (dominance). A `cut` claim checks that every
  **write** use has a selected guard that dominates it and whose bound fits the
  buffer. `Scry.check` still trusts the EDB; the guard rows are the analysis's view of
  the branch, so a forged EDB is a forged proof, exactly as for `flow`/`src`.

## 2. The proof object

```wiz
structure Scry.Claim where
  func : String              -- a label; the EDB identifies the function
  invariant : List (Nat × Nat)   -- tainted rows
  locations : List Nat           -- derived tainted locations
  sources : List Nat             -- source relations quantified (`[]` = all)
  property : Scry.Property       -- noFlow | constantOrBound | cut
  guards : List Nat              -- the cut's guard points (a `cut` claim)
```

That is the certificate: **a finite set of `(point, register)` rows, a finite set of
locations, and for a cut, a finite set of guard points**. It is tiny compared with the
analysis trace (one row for the worked example), human-checkable by reading the script,
and it is not a re-encoding of the evaluator's provenance.

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

### The cut checker

`property .cut` is a *different* obligation, checked by `Scry.checkCut`:

1. **non-vacuity** — the EDB must have at least one **write** use (`kind` is
   `index-write` or `copy-write`), else `vacuous`;
2. **real cut points** — every point in `c.guards` must have at least one `guard` row,
   else `refused` (a certificate may not name a control point that proves nothing);
3. **coverage** — for every write use, either its length/index is a known constant that
   fits, or there is a guard row `(g, var, hi, target)` with `g ∈ c.guards`, `g`
   dominates the use (`before(g, use)`), the bound-carrying edge's target dominates the
   use (`before(target, use)`), and `hi` fits the buffer: an index needs `hi < cap`, a
   copy length needs `hi <= cap`. The first miss is `refuted` with the guard and the use
   named; an unknown capacity (`cap = 0`, the lowering's marker) is a refutation, never a
   silent pass.

The guard set is the certificate, not the search: `Scry.proveCut`/`--cut` use every
guard point in the EDB by default, and a hand-written subset is checked by the same
function. No taint obligation is involved; a cut says "every write is preceded by a
check", not "no attacker value reaches a sink". The two claims can be proved separately
and a report must not merge them.

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

1. **Arithmetic only through the analysis's constants.** The `memcpy` length property is
   now proved (§10), but the guard bound is a **constant** recovered by
   `Scry.boundsConstAt`; a symbolic `n <= m` or a bound from a function (`cap = min(x,y)`)
   is not a guard row. There is no interval/bounds domain in the rule pack, and the
   copy length's unit is the analysis's cell count, not a byte count for element types
   larger than one. The C# twin's `int.Parse` is a *sanitiser* for taint, not a range
   check.
2. **No temporal/path logic beyond dominance.** "every write to `x` is preceded by a
   length check" is checked as a **cut**: a selected guard point must dominate the write
   and its bound-carrying edge must reach it. That is a may-cut over the CFG, not LTL; it
   says nothing about a guard on *another* path, a loop invariant, or an interprocedural
   check. The `use` rows include loads (`index-read`, `copy-read`) but the `cut`
   obligation quantifies over **writes** only; a read property needs its own obligation.
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
| `lib/Scry/Prover.wiz` | `Claim`, `Verdict`, `check`, the cut checker, the tactic datatype and `prove`/`proveWith` |
| `lib/Scry/Bounds.wiz` | the out-of-bounds rules and `boundsFactsOfFunc`: `guard`/`use`/`before` rows derived from the same CFG, capacities and copy shapes |
| `lib/Scry/ProverExamples.wiz` | tiny EDBs for the safe/unsafe pair, the memory pair, vacuity, source selection, `constantOrBound` and the cut twins |
| `Tests/Groups/ScryProver.lean` | group `scry-prover` (library shard): safe twin proves, unsafe twin refuted, memory covered, vacuity rejected, tagged verdicts, source selection, the cut on tiny EDBs and guard extraction |
| `scry/PROVER.md` | this note |

Test cases (all in the interpreter, reading the checked-in spills, so no tree-sitter and
no .NET):

| case | expected |
|---|---|
| tiny safe/unsafe pair | `proved` / `refuted` with `src(0,0) -> flow(0,1,0) -> flow(1,2,1) -> sink(2,0,1)` |
| empty and cross invariants | `refused` (rule 0 / the extra taint admits an alert), never `proved` |
| memory pair | safe: `proved`, `I={(0,0)}`, `M={7}`; unsafe: `refuted` with `store(7,1,0) -> load(7,2,0)` |
| memory certificate gaps | no `M` is `refused` at rule 6 (`mtainted 7`); no load taint is `refused` at rule 7 (`tainted (2,0)`) |
| vacuity | a sink with no source is `vacuous` (source set empty); a source with no sink is `vacuous` (sink set empty) |
| source selection | the all-source claim is `refuted` by the parameter flow; the `src`-only claim is `proved` |
| `constantOrBound` | `proved` on the parameter-only flow, `refuted` when the untrusted source reaches the sink |
| tagged verdict | `apply 99` is `script-failed`, not `none` |
| the C# process pair | safe twin proved with a 1-row invariant; unsafe twin refuted at the alert |
| cut, tiny EDBs | the guarded copy is `proved`; an unordered guard is `refuted` naming `guard(0,3,32,1)` and `use(1,3,7,32,2,0)`; a weak bound, an unknown capacity, a phantom cut point and a constant overflow each have their own verdict |
| cut, C `memcpy` (corpus) | `memcpy-safe.c`: `proved` (1 guard row, 1 write use); `memcpy-weak.c`: `refuted` naming the guard, the use and the bound/capacity mismatch; `memcpy-unguarded.c`: `refuted` with no guard on the length register |

The `cut, tiny EDBs` and `guard extraction` rows run in the interpreter; the C rows run the
compiled driver through `scry/corpus/prover/check.sh` (the driver is the only usable entry
point for the frontend, as §9.5 says).

The dogfood corpus in `scry/corpus/prover/` is a separate, synthetic corpus:
`RecordSeeder`, `ReportProvider`, `EventEndpoint` and `PathHelper`, the modern C#
memory twin, and the C `memcpy-*` cut fixtures. `check.sh` asserts the tagged
verdicts, the memory path and the cut witnesses.

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
3. **Done (this slice): guards/bounds.** `guard`/`use`/`before` EDB rows from
   `Scry.Bounds`, the `cut` claim for "every write preceded by a check", and the
   `memcpy` length property on C fixtures (`scry/corpus/prover/c/`, §10).
4. A `scry prove FILE --claim …` command: parse a small script, run it, print the
   invariant and the verdict, and exit non-zero on a rejected claim (with the offending
   fact). The dogfood driver `scry/tools/ProverMain.wiz` is the prototype; it now has a
   `--cut` mode.
5. Mechanise the memory closure induction alongside the taint one.

## 10. Guards and bounds: the cut

Status: implemented on `prover-guards` (2026-11-19), based on `integration/train7`.

### Facts

`Scry.RuleTaint` fixes three prover-only relations (numbers 14–16; the taint rules never
read them):

```
guard (point, var, hi, target)   on the edge from point to target, var <= hi
use (point, var, loc, cap, kind, const)
                                 a memory access at point uses var as an index/length
                                 into location loc (cap cells); kind is index-write,
                                 index-read, copy-write or copy-read; const is 0 for
                                 "not a known constant", k+1 for the constant k
before (node, usePoint)          node dominates usePoint
```

`Scry.Bounds.boundsFactsOfFunc` derives them from the same inputs as the out-of-bounds
analysis: `boundsCondBounds` turns each branch edge into `var <= hi` (it mirrors
`boundsLtProves`; `and`-true and `or`-false distribute), `boundsIndexUsesAt` and
`boundsCopyUsesAt` read the reached `gepVar` sites and the pack's copy shapes, and
`boundsPtrCaps` supplies the capacity. `before` is the dominator set of each use point,
computed once when the production plan is flow-only. `Scry.addBoundsFacts` writes the
rows into the function's EDB.

### The claim

`Scry.Claim` gains `guards : List Nat`, and `Scry.Property` gains `cut`. Both the
property and the set are needed: the property selects the obligation, and the set is the
certificate a second party can read ("these are the checks the proof relies on"). An
empty `guards` is a legal but useless certificate; if there are writes it is refuted at
the first one. The default certificate is every guard point in the EDB
(`Scry.guardPoints`), and `Scry.proveFor` checks a cut claim directly — there is no
tactic search for a cut, because the set is the proof.

### The memcpy fixture

`scry/corpus/prover/c/memcpy-safe.c` is a 16/32-byte copy:

```c
char src[16];
char dst[32];
if (n > cap) return 1;      /* cap = 16, so n <= 16 */
memcpy(dst, src, n);
```

The derived EDB has one guard row `guard(g, n, 16, target)` and one write use
`use(copyPoint, n, dstLoc, 32, copy-write, 0)`. The cut over `{g}` is **proved**: the
guard dominates the copy, the edge target dominates it, and 16 ≤ 32.

`memcpy-weak.c` changes `cap` to 64 (same source length, so the checked-in spill still
matches). The guard is before the copy, but 64 > 32: **refuted**, with a witness of the
form

```
guard(g,n,64,target) allows register n up to 64 but the buffer holds 32 cells;
path guard(g,n,64,target) -> before(g,copyPoint) -> use(copyPoint,n,dstLoc,32,2,0)
```

`memcpy-unguarded.c` has no branch: **refuted** with `the write use(...) has no guard on
register n`. The tiny EDB `proverCutUnordered` covers the third shape, a guard that does
not dominate the copy (`does not dominate`).

### Verification status (this environment)

The implementation was written and inspected on `prover-guards`. The environment's
`wiz` and `scry-cst` executables hung at startup (`--version` included), and every
invocation was killed by its timeout. The `wiz check` probes, the `scry-prover` Lean
group and `check.sh` could therefore not be run here. The verdicts and witnesses above
are the implementation's expected output, not a measured run; the code, corpus and tests
are committed on `prover-guards` (`b26b982c`). This is the same class of environment
limit the dogfood recorded for the driver build.

### Limits (what the cut does not check)

* **The EDB is trusted.** `guard`/`use`/`before` are analysis output; a forged EDB forges
  a proof, exactly as a forged `flow`/`src` does. The checker does not recompute
  dominance from a `cfg` relation, and it does not re-run `Scry.Bounds`.
* **One function, one cut.** The proof is intraprocedural. A check in a caller, a
  validation helper, or a loop invariant does not produce a guard row for the callee.
* **Constants only.** The bound is a constant recovered by `boundsConstAt`; symbolic
  bounds, arithmetic (`n/2`), `min`/`max`, and the result of a function call are not
  guards. The capacity is the lowering's cell count, and copies are compared in the same
  units (a byte count into an `int` array is not scaled by the element size).
* **Writes, not reads.** The `cut` obligation filters `use` rows to index stores and copy
  destinations. Loads are in the EDB, but a read property (CWE-125 on a load) is not
  checked.
* **Unknown capacity is a refusal.** A `cap` of 0 (the lowering's unknown marker) makes
  the write refutable; the claim never silently passes an unanalysed extent.
* **No mechanised soundness.** The dominance/coverage argument is still a paper argument
  in this note; there is no Wiz theorem `checkCut ... = proved → every write guarded`.
