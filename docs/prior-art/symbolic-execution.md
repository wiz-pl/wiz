# Symbolic execution for Scry

This is a survey of symbolic execution written in November 2026 for Scry, Wiz's program-analysis tool. It covers
the classical definition, concolic and dynamic symbolic execution, path explosion, state merging, interpolation and
compositional summaries, the main engines (KLEE, angr, S2E, Manticore, Triton, SymCC, DART/CUTE/SAGE, Mayhem), C
memory models, how symbolic execution composes with taint, points-to, abstract interpretation, SMT solving and
e-graphs, and what a solver answer can and cannot justify. Its conclusion is a proposal: Scry should not build a
KLEE-style forking executor but a **concolic, trace-first witness slice** over Wil (record a concrete `Wil.run`,
extract its path condition, flip a bounded number of branch guards, validate every model by evaluating the path
condition and re-running Wil) that reports only "witness found" or "not found within budget", never absence.
Section 11 is that proposal; the rest is the survey it rests on.

**Confidence.** Citations are marked **H** (paper, DOI or publisher page checked), **M** (canonical reference or
vendor documentation, exact detail not re-checked) or **L** (plausible but unverified; a hypothesis, never a
citation). Claims about Scry's code name the file and definition; performance figures quoted from papers are the
papers' claims, not measurements made for this survey.

---

## 0. Reading guide

Four things get conflated; keep them apart: a **technique** (forward symbolic execution, concolic/DSE, abstract
interpretation, bounded model checking, CEGAR, fuzzing); an **engine** (KLEE, angr, S2E, Manticore, Triton, SymCC,
Mayhem), that is, a state representation, a scheduler and a memory model; a **solver interface** (SMT-LIB, model,
proof, unsat core, `unknown`); and a **product claim** ("found a witness", "proved infeasible", "no bug", "safe"),
each with a different quantifier and certificate. A feature can be new in Scry as an implementation while entirely
standard as an idea.

What Scry has today, and what each layer means for symbolic execution (SE):

| layer | what exists | consequence for SE |
|---|---|---|
| C front end | `cc -E` line markers (`scry/src/Scry/Preproc.wiz`), tree-sitter-c, a deliberate C subset lowered by `scry/src/Scry/Lower.wiz`; anything outside it becomes a havoc'd value plus a boundary warning (`Scry.havocAt`) | lowering is a trusted boundary; a Wil witness is not automatically a C witness |
| Wil IR | `lib/Scry/Wil.wiz`: three-address CFG, integer widths and signedness, CompCert-style block memory, `Wil.step`/`Wil.run` with fuel; loads, stores and frees fault on null, out-of-bounds, freed blocks and double free | a concrete trace is executable and checkable; no new semantics is needed for witnesses |
| Datalog | `lib/Scry/Datalog.wiz`: deep embedding, range restriction and stratification (`Program.check`); `lib/Scry/Cert.wiz`: flat derivation certificates checked by `Derivation.check`, with soundness theorems for fragments | findings already carry a checked derivation; SE should add evidence, not replace it |
| taint | `Scry.RuleTaint` (register-indexed Datalog), the rule pack `lib/Scry/rules/default.scry` (`command-injection`, `format-string`; forbidden calls `gets`, `strcpy`/`strcat`), model-derived length/size rules (`lib/Scry/Models.wiz`), interprocedural summaries (`Scry.Interproc`), Andersen-style points-to (`Scry.PointsTo`) | taint supplies candidates; SE validates a path |
| abstract interpretation | `lib/Scry/AiDomain.wiz` (intervals, constants, nullness, a reduced product), `lib/Scry/AiFixpoint.wiz` (widening worklist, `narrowOnce`, the post-fixpoint checker `check`) | over-approximate; SE is the dual, under-approximate tool |
| e-graph | `lib/Scry/Egraph.wiz`: union-find, congruence closure by rebuilding, saturation with fuel, extraction | a normaliser, not a reachability engine |
| solvers in Wiz | `smt`, `sat_decide`, `bv_decide`, `sat_decide_native` ([stage 28](../stages/28-solvers.md)) | the kernel already distinguishes a trusted answer from a checked one |
| evidence | `lib/Scry/Workflow.wiz`: an authority ladder `Scry.WfAuthority` (L0 to L5) and evidence kinds; `scry dynamic` sanitizer runs; a reserved concolic-witness slot | SE's product slots into an existing vocabulary |

Scry has no path-condition builder or solver integration of its own today. The `findings` workflow accepts an
externally produced model file (`--smt-model`, `Scry.wfSmtJson`) only when it is labelled `status: sat`,
`validated: true` and carries a model; it records the producer's label and does not re-evaluate the model.

Four design rules follow from the trust analysis in section 10 and are used throughout: the solver is untrusted, a
`sat` model is validated and a bare `unsat` is a hint, and no SMT answer enters the kernel; path feasibility and
counterexample validation come first, CEGAR and interpolation later; findings are checkable, and no soundness is
claimed for absence; and the composition is one-way (Datalog facts, then a path condition, then a validated model,
then filtered facts) until a feedback loop is measured.

---

## 1. Summary of findings

**F1. Symbolic execution is a semantics, not a solver.** An executor defines a state
`(point, symbolic store, path condition, path)` and a fork rule; speed, precision and soundness depend on the memory
model, scheduler and call handling, not on the solver brand [S1][S16][S17]. KLEE's experience is the canonical
statement: path enumeration and environment modelling dominate; the solver is a component [S9][S16].

**F2. Concolic execution is the right first shape for Scry.** DART, CUTE, SAGE and SymCC run one concrete path,
collect the guards, negate one guard and solve for a new input [S6][S7][S10][S23]. This is linear in trace length per
query, needs no state forking, and produces a concrete input that can be replayed. It is weaker than forking SE (it
only explores paths reachable from a seed) but it matches `Wil.run` and the product claim (witnesses, not absence).

**F3. Bounded SE is under-approximate; that is the point.** A path not explored is not a path that does not exist. A
bounded search that finds nothing says "no witness in this budget", never "safe" [S16][S17]. This is the solver
asymmetry: `sat` is existential and checkable; `unsat` is universal and needs a proof.

**F4. Path explosion has known mitigations, none free.** DFS, BFS, random, generational and directed search change
*which* paths are explored, not the exponential [S10][S16][S35]. State merging, summaries, interpolation and
abstraction trade formula size and precision for path count [S33][S22][S39]. A trace-first slice and budgets come
before a merging engine.

**F5. The memory model is the analysis.** KLEE's object model, S2E's full-system memory, Mayhem's index-based
symbolic memory and SymCC's shadow memory are different answers to "what is a pointer?" [S9][S19][S21][S23]. C
pointers, arrays, structs, unions, `malloc`/`free` and undefined behaviour decide whether a witness is a witness to
the intended program. Wil already has block memory and faults; a path-condition builder must say exactly what it
assumes.

**F6. The solver is the least trusted and usually the least expensive part.** A `sat` model is data; decoding it
wrongly defeats validation. `unsat` without a proof is an oracle. Model validation, path-condition construction and
the C-to-Wil lowering are the trusted components; each needs adversarial tests [S58][S59].

**F7. A boolean summary is not a compositional summary.** Scry's interprocedural `Scry.Summary` records tainted
parameter positions and a boolean `retTainted`; it loses "returns tainted only if parameter 1 is tainted". IFDS
summary edges are the relational object [S13][S14][S15]. For SE, a summary is a `(pre, post)` relation with an
under- or over-approximation label; an observed trace is a witness for one call, not a universal summary.

**F8. Taint, points-to, abstract interpretation and SE are complementary.** Taint and points-to are may analyses that
propose candidates and aliases; abstract interpretation over-approximates all paths; SE under-approximates some paths
and produces witnesses. The safe composition is one-way: facts, candidate, path, model, validated witness, report. A
feedback loop into the taint fixpoint has no termination or certificate story.

**F9. Wiz already has the trust vocabulary SE needs.** Reuse the derivation checker, the post-fixpoint checker and the
LRAT checker (`Derivation.check`, `lib/Scry/AiFixpoint.wiz`'s `check`, `Sat.lratCheck`), not a second notion of
"verified" [S60][S61][S62].

The full engine is a research programme. A trace, path-condition, flip and validate slice reuses what exists and adds
no theory; a forking, merging, interpolating, bit-vector, heap-shape engine is far larger, and its first measurable
win is not established.

---

## 2. What symbolic execution is

### 2.1 The classical definition

King's 1976 paper is canonical [S1]. A program runs with symbolic inputs; the state carries a **symbolic store**
`σ : Var ⇀ Expr`, a **path condition** `PC` over inputs, and a program point. At `x := e`, `σ[x] := e[σ]`. At
`if e`, the executor forks into `PC ∧ e` and `PC ∧ ¬e`, pruning a branch whose PC is unsatisfiable. A model of `PC`
at a sink is a test input. Clarke's 1976 system and the SELECT/DISSECT line are the same idea with different logics
and loop treatments [S2][S3][S4][S5].

Three assumptions are still the whole engineering problem: a decidable or semi-decidable theory for `PC`; a bounded
or invariant-annotated treatment of loops (the symbolic execution tree of an unbounded loop is infinite); and a
memory model for arrays and pointers, which early systems mostly lacked. Modern symbolic execution differs in memory
model, scheduler, solver interface and environment (libraries, syscalls, concurrency), not in the core rule.

### 2.2 State, path condition, feasibility

For a path `π = (b₁, …, bₙ)` with guards `gᵢ` (`eᵢ` or `¬eᵢ`), `PC(π) = ⋀ᵢ gᵢ(σᵢ)`, where `σᵢ` is the symbolic store
before `bᵢ`. A path is **feasible** iff `PC(π)` is satisfiable; a **model** `M ⊨ PC(π)` is an input, and running the
program on `M` should follow `π`. The gap between "the solver says sat" and "the program follows `π`" is where
path-condition-builder, memory-model and lowering bugs live.

| judgement | shape | check |
|---|---|---|
| `Feasible(π)` | existential over inputs | a model plus evaluation (and a run) |
| `Infeasible(π)` | universal over inputs | a checked proof, or a trusted decision procedure |
| `Reaches(π, sink)` | existential over a concrete run | a concrete trace, replayable |

`Feasible` is cheap and checkable; `Infeasible` is the hard direction; `Reaches` is the product a bug-finder
actually needs.

### 2.3 Forking and single-path execution

A **forking** executor keeps a worklist of states and clones at branches (KLEE, S2E, Manticore, angr). A
**concolic** executor keeps one concrete state, records the path's guards, asks the solver for an input that flips
one guard, and restarts on the new input (DART, CUTE, SAGE, SymCC, Mayhem's offline half) [S6][S7][S10][S23][S21].
"Dynamic symbolic execution" (DSE) is the general term; "concolic" is the concrete-plus-symbolic portmanteau.

| property | forking SE | concolic SE |
|---|---|---|
| paths explored | many, one process | one per concrete run |
| state explosion | exponential, in memory | linear in trace length per run |
| concrete replay | needs a model and harness | the run already happened |
| external calls | need models | execute concretely; only observed effects |
| precision | both sides without a seed | needs a seed reaching the branch |
| speed | interpreter overhead | native speed or instrumentation |
| product | path and model | concrete input, trace and flipped-guard model |
| failure mode | state explosion | no coverage without seeds; path divergence |

`Wil.run` is deterministic and fuel-bounded, so the concolic shape is natural: the concrete run already exists and is
checkable. A forking engine would need a Wil state scheduler, memory snapshots and a fair policy, none of which
exists.

### 2.4 What "path" means with calls

A whole-program path includes call and return edges. There are three treatments: **inline** the callee (exact for
that call, duplicates work, recursion diverges); **summarise** it as a relation between input and output states,
`may` (some executions) or `must` (all), with mixing handled by may-must analyses [S13][S12]; or **assume** an
uninterpreted summary, which is sound only as an assumption. Scry's interprocedural taint uses boolean summaries
(`Scry.Summary`), not relations. A first SE slice should inline direct calls and record an explicit assumption for
unresolved calls. (`Wil.run` itself faults on an indirect call today; `Scry.PointsTo` resolves indirect targets for
the taint layer only.)

---

## 3. Path exploration and path explosion

The symbolic execution tree has one node per state and one edge per fork. For `n` independent binary branches it has
`2ⁿ` leaves in the worst case; loops make it infinite; calls multiply it. Constraints prune it, but the tree is
still exponential on parsers, protocol handlers and data-dependent code. The **search strategy** decides which state
is selected next; it does not change the feasible path set, only order, memory and time to the first bug.

| strategy | next state | strengths | failure mode |
|---|---|---|---|
| **DFS** | deepest | deep bugs early; low memory | stuck in one subtree or loop; unfair |
| **BFS** | shallowest | broad shallow coverage; fair | frontier memory blows up |
| **random** | random ready state | diversifies; good empirical coverage | no guarantee; can starve |
| **generational** | negate one guard of a seed trace | simple; SAGE; good with seeds | limited to one generation's distance |
| **directed** | closest to a target | bug-driven; known sink | needs a distance heuristic; misses other bugs |
| **cost-guided** | cheapest query or most coverage | avoids solver blow-up | needs a cost model; starves expensive paths |

KLEE exposes several and adds coverage-age and query-cost heuristics; its random selection is deliberate, not an
accident [S9][S16]. SAGE's **generational search** runs a seed, negates each branch in the trace, solves, and uses the
new inputs as the next generation [S10][S35]: exactly the loop a Scry concolic slice can implement without a
scheduler.

**Path explosion.** Let `b` be the data-dependent branches on a path and `d` the depth; the naive tree is `O(2^b)`,
and loops add an unbounded factor. Mitigations: **bounds** (depth, instructions, wall time, solver queries, memory),
cheap but turning "no bug" into "no bug within the bound", so they must be reported; **pruning** (unsat PC,
subsumption, interpolants) [S33][S39][S45]; **merging** (fewer states, larger formulas) [S33][S22]; **summaries**
(reuse a callee relation) [S11][S12][S13]; **abstraction** (over-approximate; can lose the path) [S48][S49];
**concolic** execution (no fork) [S6][S23]. The engineering fact is that the solver is rarely the bottleneck; path
enumeration, memory modelling and formula size are [S9][S16].

**Fairness and reporting.** A newest-first search can starve an old branch; an oldest-first search can spend all its
time in a loop. A budgeted search must record which paths were never selected. A concolic loop is fair over the
finite guard set of a trace but not over the program: a branch no seed reaches is invisible. "10,000 paths" is not
evidence unless the paths are feasible, reach the sink and are checked. A report should look like:

```
seeds: 12; traces: 12; guards flipped: 31; feasible: 9; witnesses: 3;
pruned: 2 (checked contradiction); unknown: 17 (timeout/unsupported);
budget: exhausted (maxSolverCalls=64)
```

That is a coverage and cost statement, not a safety statement.

---

## 4. State merging

At a CFG join, states `(PC₁, σ₁)` and `(PC₂, σ₂)` can be merged into `PC = PC₁ ∨ PC₂` and
`σ(x) = ite(PC₁, σ₁(x), σ₂(x))`. This is exact for the two paths: every model follows one of them. It reduces state
count but grows terms; a chain of merges can produce a formula larger than the original paths. Kuznetsov et al. study
when and where merging pays, and the answer depends on the program and the query [S33]. Veritesting merges static
regions into predicated code and switches between static and dynamic execution, the same trade at a larger
granularity [S22].

| merge policy | path count | formula size | precision |
|---|---|---|---|
| no merge (fork) | high | small per state | exact per path |
| merge at every join | low | large | exact for merged paths (disjunction) |
| merge with abstraction | low | small | over-approximate; may add infeasible paths |
| subsumption (`PC₁ ⇒ PC₂` drops `PC₁`) | lower | unchanged | exact if the implication is valid |
| interpolation-based pruning | lower | unchanged | exact only if the interpolant is checked |

The dangerous direction is **dropping** a state: a wrong drop loses a real bug. Merging with a disjunction does not
drop models; abstraction and interpolation can. Trace partitioning keeps states separate by control-flow history and
joins only within a partition, recovering path sensitivity at the cost of more partitions [S56]; it is the
abstract-interpretation analogue of merging. A concolic slice does not merge. If a forking engine is ever built,
merging should be a measured option, not a default; the first question is whether merging reduces solver calls per
new branch on Scry's benchmark corpus.

---

## 5. Interpolation and compositional summaries

### 5.1 Craig interpolation

If `A ∧ B` is unsatisfiable, Craig's theorem gives `I` with `A ⇒ I`, `I ⇒ ¬B`, and `vars(I) ⊆ vars(A) ∩ vars(B)`
[S38]. In model checking, `A` is the prefix, `B` the suffix, and `I` an over-approximation of reachable states that
rules out the bad suffix; McMillan's interpolation-based model checking and lazy abstraction are the reference points
[S39][S40], and Henzinger et al. turn proofs into abstractions [S41]. For SE, an interpolant can summarise a function
or loop prefix, prune a suffix inconsistent with the prefix, or avoid predicate enumeration in CEGAR.

It is not a first step because: (1) it needs a proof-producing solver and solver-specific clause labelling; (2)
`A ⇒ I` and `I ⇒ ¬B` are validity questions, and checking them with the same trusted solver is circular, while
checking them in the kernel needs a decision procedure for `I`'s theory (Farkas certificates for linear integer
arithmetic, LRAT for bit-vectors, hard for arrays and strings); (3) interpolant quality is heuristic and a coarse one
can make CEGAR diverge; (4) the wins come from theory-specific code bases, not library calls. TRACER is the
software-model-checking precedent for interpolation-based path pruning [S45]; it is a target after a path-feasibility
baseline, not before.

### 5.2 Compositional summaries

A **summary** for `f` is a relation `S_f ⊆ State × State` (or `(pre, post)` over the interface), used at call sites
instead of inlining. It can be **may** (some executions; under-approximate; good for bug finding, because a witness in
the summary is a witness in the callee), **must** (all executions; over-approximate; good for absence, harder to
compute and check), or **may-must** (a pair used alternately) [S13]. Godefroid's compositional dynamic test
generation (SMART) computes and memoises summaries from dynamic runs [S11]; demand-driven compositional SE explores
only the callee paths relevant to a caller's query [S12]; under-constrained SE analyses a function with unconstrained
inputs and a model of the environment, the right shape for libraries and external models [S26].

A summary computed from one trace is **observed**: "this call had this effect", not "every call does". A summary used
for absence must be `must` and checked; one used for a witness can be `may`, but the witness must be replayed at the
call site or carry a derivation. Scry's boolean `Scry.Summary` is neither: it is a may-fact with no relation and no
path edges. IFDS summary edges are the next relational object [S13][S14][S15].

---

## 6. Under- and over-approximation, and what "sound" means

| analysis | quantifier over executions | a finding means | no finding means |
|---|---|---|---|
| concrete run | one | this input reaches the sink | nothing |
| bounded SE | some explored paths | this path is feasible and reaches the sink | no witness in the budget |
| merged SE (exact join) | some explored paths, joined | a merged path is feasible | no witness in the budget |
| SE with abstraction | over-approximation of explored paths | may be feasible; validate | nothing unless the abstraction is proved |
| taint (may) | all paths, may-flow | may flow | no flow, if sound |
| points-to (may) | all paths, may-alias | may alias | no alias, if sound |
| abstract interpretation (post-fixpoint) | all paths, over-approximate | may violate | no violation if the domain and transfer are sound |
| SMT `sat` | one model | feasible | not applicable |
| SMT `unsat`, unchecked | all models | infeasible if the solver is right | not applicable |
| SMT `unsat`, LRAT/Farkas checked | all models | infeasible | not applicable |
| summary (may / must) | some / all callee executions | a callee witness exists (may) | no behaviour outside the summary (must) |

"**Soundy**" is a fourth thing: sound for the modelled cases, incomplete and assumption-laden elsewhere. It is a useful
product label, not a mathematical claim. A checked post-fixpoint means "the result is checked as a post-fixpoint, but
the transfer functions are not proved sound"; Scry's abstract domains state their soundness obligations as `Prop`s
that the checker does not discharge (`lib/Scry/AiDomain.wiz`). A witness should mean "a concrete trace or model was
checked". An SE finding must never be labelled sound.

Bounded SE is under-approximate by construction: a bug found is real (given the semantics); a bug not found is not
absent. Turning it into an over-approximation needs a complete enumeration or a sound abstraction, a checked `unsat`
for every pruned path, a checked C-to-Wil lowering, and a checked environment model. Scry has none of these in full,
which is why section 11 recommends "witness, not absence". The engines sit on different sides:

```
under-approx  <-- concrete run <-- bounded SE <-- concolic SE
                       |                +--> merged SE (exact join)
over-approx   <-- taint/points-to <-- AI <-- predicate abstraction <-- CEGAR
```

The arrows are not a total order; they are different products. A finding from the top row is existential and
checkable; a "no finding" from the bottom row is universal only if the analysis is sound and complete enough. Only a
sound over-approximation (taint, points-to or abstract interpretation with proved transfer functions) can support a
no-finding claim; SE, concolic execution and sanitizers are bug-finders, not verifiers.

---

## 7. The tools

### 7.1 KLEE

KLEE is the reference open-source forking executor for C [S9]. It interprets LLVM bitcode with **memory objects**
(`MemoryObject` plus `ObjectState`, copy-on-write; pointers are symbolic expressions resolved against the object
table), a **constraint manager** (expression DAG, simplification, caching, constraint independence; STP originally,
Z3 and MetaSMT as options), a **POSIX/uclibc model** for files, `argv`, `env`, `stat`, `ioctl` and so on, and
**search and budgets** (DFS, BFS, random, coverage; `--max-memory`, `--max-instructions`, `--max-depth`,
`--max-time`; `.ktest` outputs). `klee_make_symbolic`, `klee_assume` and `klee_assert` are the user interface;
out-of-bounds accesses, use-after-free, division by zero and assertion failures are error states. Its lesson is not
"fork" but "the memory model and the environment model are the analysis"; its weaknesses are inline assembly,
`longjmp`, threads, C++ and complex libraries, and a "no bug" result is bounded by model and budget.

### 7.2 angr

angr is a binary analysis framework with symbolic execution as one service [S20]. It lifts machine code to VEX IR,
builds CFGs (`CFGFast`, `CFGEmulated`), represents state in `SimState` (registers, memory, files, constraints), uses
Claripy for expressions and solver access, and models library calls with `SimProcedure`. `explore(find, avoid)` is
the usual "find a path to this address" loop; Veritesting is an option; concretisation policies decide when a
symbolic address becomes a set of concrete addresses. It is excellent for reverse engineering, CTFs and automatic
exploit generation; it is not a sound verifier, and its state count on real binaries explodes [S20].

### 7.3 S2E

S2E is **selective symbolic execution** in a full-system VM [S19]: QEMU/KVM runs concretely by default and switches a
region to symbolic on demand; plugins observe and control the guest. "In-vivo" execution avoids re-implementing the
OS and devices, at the cost of a heavy VM and a coarse symbolic region. It is right for firmware, drivers and kernel
code, not for a CI library. Its lesson for Scry is "concrete until needed": a concrete trace plus selective flips is
cheaper than forking the whole program.

### 7.4 Manticore

Manticore is a Python-scriptable DSE framework for native binaries (x86, ARM) and the EVM, with a generic core engine,
a state life cycle (ready, busy, terminated), an event system and an SMT-LIB interface [S27]. It is archived but a
good design reference for a **scriptable** engine: state selection, concretisation policies and hooks are
first-class, and EVM support shows that SE is a semantics-agnostic state-space search.

### 7.5 Triton

Triton is a Pin-based dynamic binary analysis library: symbolic expressions for registers and memory, an AST, x86 and
x64 (now also ARM and RISC-V) semantics, taint analysis, snapshot and replay, and Z3/Bitwuzla interfaces [S28]. It is
a **library**, not a path explorer; the user writes the search. Its taint-plus-symbolic combination is the
"taint-guided SE" pattern: taint decides which bytes are input-dependent, and the symbolic engine tracks only those.
That is directly relevant to Scry, where taint proposes the path.

### 7.6 SymCC, SymQEMU, SymSan and hybrid fuzzing

SymCC compiles symbolic execution into the target with an LLVM pass [S23]. At each branch it calls a runtime that
builds expressions and asks the solver for a diverging input; the program runs at native speed and emits new test
cases. It is **concolic**: one path per run, orchestrated by a fuzzer. `symcc` and `sym++` are the C and C++
wrappers; `symcc_fuzzing_helper` coordinates with AFL; LibAFL exposes a `symcc_runtime` bridge [S29][S30]. The paper
reports up to three orders of magnitude over KLEE, an average of 12×, and two OpenJPEG CVEs [S23] (**M**, paper
claims).

SymQEMU applies the idea to binaries by instrumenting QEMU's TCG [S24]. SymSan builds concolic execution on LLVM's
DataFlowSanitizer, using DFSan labels as indices into an AST table; it reports a 62× speedup and a 6.5× memory
reduction over SymCC/SymQEMU and strong FuzzBench results [S25] (**M**, paper claims). The design point is that
**concolic execution is a dynamic data-flow analysis**: symbolic state is label propagation, and sanitizer
infrastructure already optimises shadow memory [S25].

No canonical publication for a system called "SymCC++" was found; `sym++` is SymCC's C++ driver, and the name is best
read as "SymCC with C++ support" (**L**). SymCC's fuzzing mode is: compile with SymCC, run under AFL or libFuzzer, and
exchange inputs through `symcc_fuzzing_helper` [S29][S30]. FuzzBench has `symcc_*` fuzzers; OSS-Fuzz can host such a
harness, but its default engines are libFuzzer, AFL++ and Centipede with sanitizers, not a first-class concolic
engine (**M**).

### 7.7 DART, CUTE and SAGE

DART starts with a random input, executes concretely, collects the path constraint, negates the last branch, solves
and repeats [S6]. CUTE extends this to C pointers and arrays (constraints on pointer dereferences and array indices,
inputs for data structures) and coined "concolic unit testing" [S7]. SAGE is the industrial whitebox fuzzer:
generational search over a trace's branch guards [S10][S35]. DART and CUTE are the closest designs to the proposed
Scry slice: no forking, one concrete run, a few flips, a concrete test case. The difference is that Scry's concrete
run is `Wil.run`, not a native process.

### 7.8 Mayhem and OSS-Fuzz

Mayhem is a binary-only hybrid executor: online (forking) and offline (concolic) execution, switching under resource
limits, with an **index-based memory model** for symbolic load and store addresses [S21]. It won the DARPA Cyber
Grand Challenge; every reported bug came with a working shell-spawning exploit, the strongest witness a bug-finder can
give [S21][S31]. Exploit generation is more than path feasibility; the lesson for Scry is "a finding should come with
a reproducible artefact", not "build an exploit generator".

OSS-Fuzz is continuous coverage-guided fuzzing with sanitizers at Google scale: a project supplies a libFuzzer or
AFL++ harness and a build script; ClusterFuzz runs it, deduplicates crashes and files bugs [S32]. It is not a symbolic
executor, but it is the best available **corpus and oracle**: a witness can be replayed in an OSS-Fuzz-style harness
with ASan and UBSan, and a FuzzBench-style comparison is the right way to evaluate a hybrid [S30][S32]. Sanitizers
are dynamic oracles: ASan detects heap, stack and global out-of-bounds accesses and use-after-free; UBSan detects
undefined behaviour; MSan detects uninitialised reads; TSan detects races [S68][S69][S70]. They have few false
positives for the errors they model, but they are incomplete and do not prove absence. A sanitizer report plus its
input is a witness; it is not a path condition and not a proof.

A useful contrast: KLEE, angr, S2E and Manticore fork over an IR or a VM; Triton is a library; SymCC and SymSan
compile concolic execution in and let a fuzzer orchestrate; Mayhem is a binary hybrid; OSS-Fuzz is a corpus and
sanitizer service. The memory model (objects, pages, index-based, shadow) is the main differentiator, not the solver.

---

## 8. C memory and pointer modelling

| model | used by | a pointer is | strength | weakness |
|---|---|---|---|---|
| **typed objects** | KLEE | object id plus offset | precise bounds, use-after-free, copy-on-write | object-table and aliasing cost; `malloc`-heavy code |
| **flat byte array or pages** | S2E, angr | address expression into pages | matches the machine; OS and syscalls | weak bounds and type information; symbolic addresses |
| **index-based** | Mayhem | base plus symbolic index, resolved on demand | avoids constraining the index | index approximation; bounds |
| **shadow memory** | SymCC, SymSan | concrete address plus shadow label | native speed; no object table | needs instrumentation; uninstrumented code loses labels |

Wil is closest to **typed blocks** (`Wil.MemBlock`, `Wil.memAlloc`): `alloc n` creates a heap block of `n` cells,
`slot n` a stack block, `gep` adds a cell offset, `load` and `store` check liveness and bounds, and `free` marks a
block dead. That is a good base for witnesses: `Wil.run` already faults on out-of-bounds access, null dereference,
use-after-free and double free (`Wil.memLoad`, `Wil.memStore`, `Wil.memFree`). A path-condition builder must decide
how a symbolic pointer or offset is represented; the simplest first answer is "concretise the address from the trace
and treat a different address as a new path", with an explicit assumption when the trace's address is not the only
possible one.

| construct | problem | what a model must say |
|---|---|---|
| pointer arithmetic | `p + i` with symbolic `i` | address expression; object bounds; one-past-the-end |
| arrays | symbolic index | bounds check before load and store; `ite` or array theory |
| structs and unions | layout, padding, bitfields, type punning | field offsets; effective type; union aliasing |
| `malloc`/`calloc`/`realloc`/`free` | symbolic size; aliasing; use-after-free | object identity; size; liveness; `realloc` may move |
| `alloca` | dynamic stack | frame lifetime; scope exit |
| strings | NUL termination; `strlen`/`strcmp`/`strcpy` | bounded byte array or string theory; libc models |
| integer promotion and conversion | widths, signedness, truncation | bit-vectors with C conversion rules |
| signed overflow | undefined behaviour | assume no overflow or model wrap-around; say which |
| shifts | `k ≥ width`, negative | undefined behaviour or Wil's word semantics; never silently SMT-LIB's |
| division and modulo | `x/0` | Wil follows `lib/Word.wiz` (`x/0 = 0`, `x%0 = x`); SMT-LIB leaves it underspecified |
| null, uninitialised, misaligned | undefined behaviour | assume definedness or treat as a UB sink |
| function pointers | indirect target | may-set from points-to; concretise or assume |
| varargs | `printf` formats | model per function; do not symbolically execute the ABI |
| `setjmp`/`longjmp`, signals, threads | non-local control | out of scope; do not claim |
| inline assembly | opaque | concretise or assume; warn |
| environment | argv, env, files, time, randomness | explicit model; the witness depends on it |

**Undefined behaviour is part of the path condition.** A C path condition is meaningful only under a semantics. If
the program has signed overflow, a bad shift, a null dereference, an uninitialised read or a data race, the "path"
may be a machine path, not a C path. An executor must either **assume definedness** (no overflow, in bounds,
initialised), making the witness a witness for the defined subset; **model undefined behaviour as a sink**, making it
a UB witness (a bug, but a different claim); or **refuse**, with a boundary warning. Scry's lowering already has a
havoc-plus-warning boundary, and `Wil.run` resolves a havoc'd value to the type's zero; an SE slice must carry those
warnings into its assumptions. A witness that crosses a havoc is not a witness for the C program.

**The memory model is where the cost is.** KLEE, S2E, Mayhem and SymCC all report that memory and pointer handling,
not solving, is the dominant engineering cost [S9][S19][S21][S23]. A first Scry slice should restrict memory
deliberately: scalars, direct calls, block memory with **concrete** addresses from the trace; symbolic **values**
(not addresses) in the path condition; `load` and `store` as an uninterpreted function or an `ite` over the trace's
block; and a symbolic address, a may-alias set, an unresolved call or a havoc as an assumption, not a silent model.
That is enough for direct taint-to-sink witnesses (CWE-78, CWE-134) and a concrete use-after-free witness (CWE-416),
without the heap-shape research programme.

---

## 9. Interactions with other analyses

### 9.1 Abstract interpretation

Abstract interpretation and SE are duals: abstract interpretation over-approximates all reachable states at each
point; SE computes a disjunction of feasible path conditions. Abstract interpretation can **guide** SE (intervals or
points-to prune a branch, simplify a PC, choose a concretisation, bound a loop counter), but a wrong result can prune
a real path. SE can **refine** abstract interpretation (a path condition validates an alarm; an infeasible path
prunes it; CEGAR refines the abstraction) [S42][S43][S44]. The `unsat` direction is the dangerous one: a wrong
`unsat` hides a state. State merging is a join; trace partitioning is the dual choice of partition [S56]. Scry's
abstract interpreter produces a post-fixpoint that `check` (`lib/Scry/AiFixpoint.wiz`) validates, while the
soundness of its transfer functions is stated but not proved; SE should consume its alarms as candidates, not as
proofs, with no feedback into the fixpoint until termination and cost are measured.

### 9.2 Taint and points-to

Taint is may-reachability: a source reaches a sink through def-use, memory and call edges. Points-to is may-alias: a
pointer may point to a set of locations. Both are over-approximations and both propose candidates.

* **Taint to SE.** A taint finding gives a source, a sink and a path; SE checks feasibility and produces an input.
  This is the natural Scry pipeline: rule pack, candidate, Wil path, path condition, model, `Wil.run`.
* **Points-to to SE.** Points-to resolves symbolic addresses, function pointers and aliases; a may-alias set forces a
  fork or an `ite`, a singleton avoids it; an unknown location (`Loc.unknown` in `Scry.PointsTo`) is an assumption,
  and the witness is conditional on it.
* **SE to taint.** A validated witness ranks a taint finding, but should not add a fact to the taint fixpoint in the
  same run; a separate refinement pass is a measured analysis, not a fixpoint rule.

Triton's "taint decides which bytes are symbolic, the symbolic engine tracks only those" is the efficiency pattern
[S28]. Scry's taint already knows which registers are attacker-controlled (`tainted (point, var)` in
`Scry.RuleTaint`), so a path-condition builder can restrict its symbolic variables and shrink the formula.

### 9.3 SMT solving

A path condition is a formula; the solver answers `sat`, `unsat` or `unknown`. The interaction points are: path
feasibility (a model, PC evaluation and `Wil.run`), branch contradiction (a local check, or an LRAT or Farkas proof),
loop-invariant inductiveness (post-fixpoint or implication), summary validity (`pre ⇒ post`), and interpolant
validity (`A ⇒ I`, `I ⇒ ¬B`). Wiz's solver tactics are a map of the trust options ([stage 28](../stages/28-solvers.md),
[S60][S61][S62]): `smt` asks Z3 and adds a trusted axiom per use, which an analysis claim should never rest on;
`sat_decide` asks a SAT solver for an LRAT certificate and checks it in the kernel, adding no trust; `bv_decide`
bit-blasts words and proves the encoding with per-operation lemmas, adding no axioms; `sat_decide_native` runs the
LRAT check compiled and adds an axiom per check behind `--trust-native`.

### 9.4 E-graphs

An e-graph is congruence closure: hash-consed e-nodes, union-find, rebuilding, extraction, e-class analyses and
explanations [S63][S64]. Egglog adds Datalog-style rules and lattice merges [S67]; relational e-matching shows that
e-matching is a join [S65]; proof-producing congruence closure shows how explanations become proofs [S66]. An e-graph
is excellent for **normalising** expressions before a rule match (`x+0`, `!!x`, pointer arithmetic), for equivalence
over a small theory, and for e-class analyses. It is **not** a reachability engine, not a scheduler, and not a proof
unless each rewrite is a proved lemma. Safe SE uses: simplify a PC before the solver if each rewrite is a proved
equivalence for the **machine** semantics (not mathematical integers); share common subterms (the DAG lesson of
`sat_decide`'s sharing); explain why two PCs are equivalent. The unsafe use is treating a C-level rewrite as valid
when it ignores overflow, aliasing or undefined behaviour. Scry's e-graph (`lib/Scry/Egraph.wiz`) has no proved link
to Wil's semantics, so it should stay off the taint, points-to and SE critical path until a rewrite set is proved and
a simplification win is measured.

### 9.5 Sanitizers and coverage

Sanitizers are dynamic bug oracles with a concrete input: ASan (heap, stack and global out-of-bounds, use-after-free,
double free) [S68], UBSan (signed overflow, bad shifts, null, misalignment) [S69], MSan (uninitialised reads) [S70],
TSan (races, which Wil does not model). A sanitizer report is a witness that something went wrong on that input; it
is not a path condition and not a proof. It is the best **ground truth** for an SE benchmark: if a Wil witness does
not reproduce under ASan or UBSan in the C program, either the lowering or the witness is wrong. Scry already runs
this oracle: `scry dynamic` compiles a file under ASan/UBSan, links sanitizer events to static findings at the same
line or function, and labels the result observed, never verified (`scry/src/Scry/Dynamic.wiz`).

Coverage-guided fuzzing is the complementary search: mutations find cheap paths; concolic execution solves the guards
mutations cannot. Hybrid fuzzing (AFL with QSYM, libFuzzer with SymCC, Driller) is the industrial pattern
[S23][S24][S25][S36]. A first slice can use a seed corpus and Wil branch coverage; fuzzer integration is a later
optimisation.

### 9.6 Composition

The rule is **one claim, one evidence kind, one checker, explicit assumptions.** A taint derivation does not imply a
path is feasible, and a model does not imply the C program is wrong. Taint carries a derivation, points-to an
assumption, abstract interpretation a checked post-fixpoint, SE a model and a trace, `unsat` an LRAT or Farkas proof,
an e-graph an extraction, and a sanitizer only an observation. Scry's `findings` workflow keeps these apart: static
analysis, certificates, SMT models, dynamic observations and concolic witnesses are separate evidence kinds
(`Scry.WfEvidenceKind`), never merged.

---

## 10. Trust: the solver is untrusted, the witness is checked

### 10.1 The asymmetry

A `sat` answer comes with a model: a finite valuation, checked by evaluation in time linear in the formula and the
model. An `unsat` answer comes with nothing checkable unless the solver emits a proof; checking is linear in the
proof with a large constant, and proof production is uneven across theories [S58][S59].

| answer | logical shape | what it can justify | validation |
|---|---|---|---|
| `sat` and a model | existential | a finding, a path, a test input | decode and evaluate (and run) |
| `unsat` and a proof | universal | a closed goal, a pruning step, absence *within the encoding* | check the proof |
| `unsat`, no proof | the solver's claim | a hint: drop a candidate, shrink a query | none |
| `unsat` core | a subset claim | diagnostics, minimisation | re-query with a proof |
| `unknown` or timeout | no answer | a boundary finding | none |

Promoting the third row to the second because "the solver is usually right" is exactly the mistake a certificate
prevents.

### 10.2 Model validation

A model is untrusted text until decoded and checked. A decoder must:

* parse `get-value`/`get-model` output for `Bool`, `Int`/`Nat`, `(_ BitVec w)`, arrays, uninterpreted functions and
  datatypes;
* reject a negative `Nat` (never clamp) and a bit-vector `≥ 2^w` (never truncate);
* read constructors by declared position, not by label;
* complete arrays with `as const`, and reject unused non-constant stores;
* evaluate an uninterpreted function only at the arguments the PC uses, and never trust a `define-fun` body;
* check that every free variable of the PC is assigned or explicitly unconstrained;
* evaluate the PC in Wiz (`PC.eval σ = true`) rather than asking the solver again;
* for a trace, run `Wil.run` and check the branch choices and the sink;
* keep the raw text and the decoded model for replay, and never print a model without its validation status.

A wrong decoder defeats validation: it is a trusted component and needs adversarial tests (a negative `Nat`, an
out-of-range bit-vector, an array default, an uninterpreted function, division by zero, an unknown call, undefined
behaviour, and a deliberately lying decoder that must be rejected).

### 10.3 Path feasibility

`Feasible(π)` is `sat` plus a validated model. `Infeasible(π)` is `unsat` plus a proof, or a local decision
procedure proved sound for the fragment (for example equalities, disequalities and bounds over the literals of one
path). A bare solver `unsat` is a **pruning hint**: using it to drop a candidate is a precision decision; using it to
claim absence is unsound. A result type for this should distinguish a validated model, a locally checked
contradiction, an untrusted solver `unsat`, a skipped query (no solver) and a boundary (timeout or unsupported
construct), and a prune should apply to the reported path only, never be read as a proof of absence.

### 10.4 Certificates and what can be checked

A certificate is a checkable object. For SE: a **concrete trace** (this input runs this path to the sink), checked by
`Wil.run`; a **PC evaluation** (this model satisfies this PC), checked by evaluation; a **Datalog derivation**,
checked by `Derivation.check`; an **abstract-interpretation post-fixpoint**, checked by `lib/Scry/AiFixpoint.wiz`'s
`check`; an **LRAT refutation**, checked by `Sat.lratCheck`; a **Farkas certificate**, checked by arithmetic. A
witness should carry **trace, PC, model and assumptions**, not just a model: the trace proves reachability, the PC
evaluation proves consistency, and the assumptions name what the model does not cover.

**Can be checked:** the model satisfies the PC; the trace reaches the sink; the branch decisions match; the Datalog
derivation; the post-fixpoint; an LRAT or Farkas proof; the SARIF schema and fingerprints. **Cannot be checked
today:** a bare `unsat`; the C-to-Wil lowering (trusted; differential tests only); the model of an external call or a
havoc (an assumption); the absence of another path; the completeness of the solver's model; an e-graph rewrite that
is not a proved Wil lemma; a sanitizer report as a proof.

### 10.5 The authority ladder

| level | evidence | who checks | supports |
|---|---|---|---|
| L0 | solver text (`sat`/`unsat`/`get-value`) | nobody | a UI hint |
| L1 | an answer, identity and query in a cache, or a recorded run | nobody (replay only) | a reproducible experiment |
| L2 | a `sat` model decoded and PC-evaluated, or a checked derivation | the kernel or evaluator | a path is feasible; a fact is entailed |
| L3 | a model plus a `Wil.run` trace reaching the sink | `Wil.run` | a finding with an execution witness |
| L4 | `unsat` plus an LRAT or Farkas proof checked in Wiz | the kernel | a closed goal or pruning step |
| L5 | L4 plus a checked encoding and lowering and an environment model | kernel and proof | absence for a bounded program |

This ladder is implemented as `Scry.WfAuthority` in `lib/Scry/Workflow.wiz`. Scry's `findings` workflow assigns L1
to static results and recorded dynamic runs, L2 to a checked derivation and to a model labelled validated, and accepts
a supplied concolic witness only at L2 or L3 (`Scry.wfPrepareWitness`); it never uses L4 or L5, since an absent
finding is not an absence certificate. The trusted `smt` tactic is L1 plus an axiom: its authority is the solver's
word, not L4.

### 10.6 Adversarial tests

Tests that matter try to make a trusted component lie: a decoder returning an out-of-range bit-vector or a negative
`Nat` (reject); a path-condition builder omitting a guard (`Wil.run` must disagree, and the test must fail); a trace
recorder recording the wrong branch (replay must disagree); a havoc treated as zero (the witness must carry a
lowering assumption); a wrong solver `unsat` (no prune unless a local check certifies it); a path that does not reach
the sink (an internal error, never a silently dropped finding); an e-graph rewrite invalid under machine arithmetic
(rejected); a sanitizer crash that does not reproduce (withdraw the C-level claim).

---

## 11. A concrete recommendation for Scry (proposal)

Everything in this section is a proposal unless it names existing code.

### 11.1 What exists today

| asset | state | use in the slice |
|---|---|---|
| `Wil` and `Wil.run` (`lib/Scry/Wil.wiz`) | deterministic, fuel-bounded; faults on use-after-free, out-of-bounds, null and double free; indirect calls fault; havoc is the type's zero | concrete trace and witness checker |
| Datalog, taint and certificates (`Scry.RuleTaint`, `Scry.Interproc`, `Scry.Certify`) | rule-pack taint with checked derivations, boolean interprocedural summaries, points-to | candidate source-to-sink paths |
| abstract interpretation (`lib/Scry/AiFixpoint.wiz`) | intervals, constants, nullness; post-fixpoint checker `check` | candidate alarms; not a path oracle |
| SARIF (`lib/Scry/Sarif.wiz`) | one writer; the path as `relatedLocations` | witness rendering |
| evidence workflow (`lib/Scry/Workflow.wiz`, `scry/src/Scry/WorkflowCmd.wiz`) | authority ladder, evidence kinds, CWE tiers (`Scry.wfCweTier`), a witness slot that accepts a `scry-workflow-witness/1` document at L2/L3 | where a witness is stored and reported |
| dynamic evidence (`scry/src/Scry/Dynamic.wiz`) | ASan/UBSan runs, a sanitizer corpus by CWE tier, a `--witness` data contract (`Scry.DynWitness`: input, validation label, path condition, model, assumptions, solver, budget) that is recorded, never applied | C-level replay of a witness |
| budgets (`scry/src/Scry/Budget.wiz`) | `--timeout`, `--max-nodes`, `--max-rounds`; a truncated run emits `scry/budget/*` notes | the reporting convention for SE budgets |

No path-condition builder, solver call or model decoder exists in Scry. The benchmark corpus
(`scry/bench/corpus/manifest.json`) records `cwe78/infeasible-safe.c` as a known false positive of the
path-insensitive taint analysis (mutually exclusive conditions); pruning it with a checked local contradiction is one
of the slice's first tests.

### 11.2 The slice: a concolic witness

**Goal.** For a taint candidate, produce a concrete input and a `Wil.run` trace that reaches the sink, or report
"not found within budget". No absence, no CEGAR, no state forking, no interpolation. Every reported finding has a
concrete trace; everything else is a statistic. Scry's sources call this slice S6a. The pipeline runs in one
direction:

```
seed corpus ──► Wil.run ──► trace (branches, values, memory, sink)
                               │
                               ▼
                         PathCond(trace)  (SSA over registers, guards, assume)
                               │
                     for each branch guard g (bounded)
                               ▼
                 solve(PC_prefix ∧ ¬g) ──► sat + model | unsat | unknown
                               │
                     decode + PC.eval + Wil.run
                               │
                     ┌─────────┴──────────┐
                     ▼                    ▼
              witness (trace+sink)   pruned/unknown (statistic)
                     │
                     ▼
              SARIF result: path + model + assumptions + budget
```

**Why concolic.** The concrete run already exists; the PC is extracted from it; the flip is one query; the new input
is replayed. `PC_prefix` is the guard prefix before the flipped branch; the suffix is replayed, not asserted. This is
the DART/CUTE/SymCC shape [S6][S7][S23], linear in trace length per query. It cannot find a path no seed reaches; that
is the honest limitation.

**Components.**

1. `Trace`: record a `Wil.run` (inputs, branch decisions, register values, memory operations, calls, sink, fuel),
   deterministically, with replay.
2. `PathCond`: a deep embedding with `eval`, `toSmt` and `vars`; SSA over registers; guards; `assume`; `load` as an
   uninterpreted function or `ite`; a list of assumptions.
3. `Flip`: enumerate guards, negate one, solve, decode, validate, re-run, cap.
4. `Witness`: input, trace, PC, model, assumptions, solver identity, validation status and budget, rendered as one
   SARIF result and as the `scry-workflow-witness/1` document the workflow already accepts.
5. Tests: `sat`, `unsat`, `unknown`, a negative `Nat`, an out-of-range bit-vector, a havoc, an unknown call,
   use-after-free, a lying decoder, a replay mismatch.
6. A pilot on the benchmark corpus plus about ten hand-built branch cases.

### 11.3 Data structures and contracts

Proposed shapes (not existing APIs):

```
structure Trace where
  inputs : List (Name × Val); branches : List (Point × Bool × Val)
  stmts  : List (Point × Kind); sink : Option Point; fuel : Nat

structure PathCond where
  vars : List (Name × Ty); guards : List Expr; assumes : List Expr
  assumps : List Assumption; eval : Assignment → Bool; toSmt : String

structure Witness where
  input : List (Name × Val); trace : Trace; pc : PathCond; model : Option Model
  solver : Option (name × version × queryHash)
  validation : none | pcChecked | traceChecked
  assumptions : List Assumption; budget : SeBudget
```

The validation labels `none`, `pcChecked` and `traceChecked` are already the ones `Scry.DynWitness` records.

Contracts that must be theorems, not comments: `Trace.ok_sound` (a replayed trace reaches its sink); `PC.eval_sound`
(an evaluated model satisfies the PC); `Model.decode_ok` (a decoded model satisfies the PC). `Trace.ok` replays branch
decisions and the sink; `PC.eval` is total on the fragment; `Model.decode` rejects out-of-range and partial models.
These are the analogues of `Derivation.check` and the post-fixpoint checker; they should be proved in Wiz, not
assumed.

### 11.4 Path budgets

Budgets are part of the result, not a hidden timeout. Proposed starting values, to be tuned by the pilot:

| budget | per trace | per finding | per run | on exhaustion |
|---|---|---|---|---|
| `maxSeeds` | | | 32 | `Boundary(seeds)` |
| `maxTraceSteps` | 4096 | | | `Boundary(trace)` |
| `maxFlips` | 8 | 16 | 256 | `Boundary(flips)` |
| `maxPaths` | | 64 | 512 | `Boundary(paths)` |
| `maxSolverCalls` | | 64 | 512 | `Boundary(solver-calls)` |
| `maxSolverMillis` | 2000 per query | 30 000 | 300 000 | `Boundary(solver-time)` |
| `maxModelBytes` | | 1 MiB | | `Boundary(model)` |
| `maxMemory` | | | 1 GiB | `Boundary(memory)` |

Rules: every loop returns a result with a status (complete, exhausted, failed) and its counts, never a bare value; an
exhausted run emits a `scry/budget/<reason>` note, following the existing `scry/budget/*` convention, and marks a
finding whose evidence crosses the truncation with a budget assumption; a cache key includes the budget and engine
version, and a cached full result is never served for a tighter budget; `maxSolverCalls` is the primary unit, wall
time a hard cap; the order is deterministic (seeds sorted, branches in trace order); `unknown` is not `unsat`, and a
timeout is a boundary, not a prune.

### 11.5 CWE targets

The first slice should target CWEs where a **concrete witness** is meaningful and the path condition is simple. The
tiers below are already encoded in `Scry.wfCweTier` and used by the dynamic corpus (`scry/bench/dynamic/`).

| CWE | example | current static evidence | what SE adds | prerequisites | tier |
|---|---|---|---|---|---|
| **CWE-78** command injection | `getenv` to `system` | `command-injection` taint derivation | concrete argv/env witness; branch flip to sink | direct call, scalar or string source | **T1** |
| **CWE-134** format string | `getenv` to `printf` format | `format-string` taint derivation | concrete format-argument witness | direct call | **T1** |
| **CWE-22** path traversal | `getenv` to `fopen` | no rule in the default pack | a witness that passes the check | string prefix/`strstr` model | T2 |
| **CWE-416** use-after-free | load after `free` | `use-after-free` memory rule (`lib/Scry/rules/uaf.scry`) | `Wil.run` fault witness | free, alloc, liveness; concrete address | T2 |
| **CWE-476** null dereference | `p->x` with `p` null | nullness alarm of the abstract interpreter | `Wil.run` fault witness | nullness, points-to | T2 |
| **CWE-190** integer overflow | tainted `malloc` size | model-derived `integer-overflow` (tainted size) | witness of an overflowing size | bit-vectors, widths | T3 |
| **CWE-787** out-of-bounds write | `memcpy` length | model-derived `buffer-overflow` (tainted length) | witness with an out-of-bounds index or length | lengths, arrays, bit-vectors | T3 |
| **CWE-121** stack out-of-bounds | `strcpy` into a stack array | `strcpy-overflow` forbidden-call rule | as CWE-787 | lengths, arrays, bit-vectors | T3 |
| **CWE-120, CWE-242** | `strcpy`, `gets` | forbidden-call rules | nothing (the call is the bug) | | **N/A** |
| **CWE-362** race | shared memory | none | not modelled | concurrency semantics | **N/A** |
| **CWE-79, CWE-89** | XSS, SQL injection | none (not C) | out of scope | | **N/A** |

**T1.** CWE-78 and CWE-134 come first: the sink is direct, the taint path is short, and a witness is a concrete env
or argv value. When a guard is `strcmp` or `strstr`, treat it as an uninterpreted predicate with a concrete witness,
or as a bounded byte array later. The finding says "this input reaches `system` with an attacker-controlled
argument", not "this is exploitable". **T2.** CWE-416 is attractive because `Wil.run` already faults on
use-after-free, but the points-to may-set means a witness using one alias is not a witness for all aliases; mark the
assumption. CWE-22 needs string reasoning; CWE-476 is easy if nullness is modelled. **T3.** CWE-190, CWE-787 and
CWE-121 need bit-vectors, widths and a sound length model; without them the witness may be for the wrong arithmetic.
**N/A.** CWE-120 and CWE-242 are forbidden-call rules (the call is the finding); CWE-362 needs concurrency, which Wil
lacks; CWE-79 and CWE-89 are not C.

### 11.6 Labels and reporting

An SE result is `witness` (a concrete input and trace reach the sink; the PC and model are checked), `pcWitness` (the
model satisfies the PC; no full trace), `pruned` (a checked contradiction or a sound `unsat` proof), `unknown`
(timeout, unsupported construct or havoc) or `noWitness` (no flip in the budget). `noWitness` is **not** "safe".
SARIF carries the source-to-sink path (SARIF's `codeFlows`, or the `relatedLocations` Scry's writer emits today) and a
properties object with the validation status, solver, assumptions, budget and analysis description. A pruned
candidate is a separate result or a counter, not a silent disappearance. A mode that claims soundness (which Scry
does not have) would forbid pruning on a bare `unsat`; a soundy mode allows it with a warning and a count.

### 11.7 Metrics and pilot

| metric | definition | target |
|---|---|---|
| witness rate and validity | `traceChecked` per finding; `Wil.run` reaches the sink per witness | report; validity **1.0** |
| new findings | SE-only against taint-only, per CWE | report |
| pruned and unknown | checked contradictions; timeouts and unsupported constructs | report; no false prunes |
| solver calls and decode failures | per run; rejected models | report; no decode failures |
| false "safe" | any "safe" claim | **0** (a gate) |
| regression | benchmark corpus | no new false positive; `infeasible-safe.c` pruned by a checked contradiction |

Pilot on the benchmark corpus plus about ten hand-built branch cases (two callers, a return-dependent branch,
recursion, an alias, a havoc, an unknown call, use-after-free, null, a string guard, a loop). Starting with Juliet or
SV-COMP is premature: the front end does not support enough C, and a low coverage number would be misread.

### 11.8 What not to build

* **A KLEE clone.** A forking Wil executor with snapshots, a scheduler, memory merging and a POSIX model is a
  multi-month project whose first measurable win is unproven.
* **Merging, interpolation or CEGAR** before a measured spurious-path rate and solver bill. Triggers: more than 30%
  of candidates pruned by checked contradictions, solver time dominating, or a real bug class missed by one-way
  filtering.
* **Absence.** It needs L5 (complete enumeration, a checked `unsat` per path, a checked lowering, a checked
  environment); Scry has none of these, so it should not claim absence.
* **A second SMT stack.** One path-condition, decoder and validator implementation should serve both pruning and
  witnesses; add bit-vectors and arrays only when a CWE needs them, and no solver-specific kernel features.
* **An e-graph on the PC critical path** without proved machine-semantics rewrites.
* **Concurrency, signals, `setjmp`/`longjmp`, inline assembly**: Wil does not model them.
* **A "safe" mode.** The product claim is "witness found" or "not found in budget".

### 11.9 Ordering

| step | work | depends on | gate |
|---|---|---|---|
| 1 | trace, path condition, flip, witness, tests and pilot (T1: CWE-78, CWE-134) | `Wil.run`, taint | witness validity 1.0; no new false positive; no absence claim |
| 2 | bit-vectors, arrays, lengths, memory in the PC (CWE-190, CWE-787, CWE-121) | step 1, a length domain, points-to | a checked out-of-bounds or overflow witness; no false "safe" |
| 3 | function summaries, under-constrained SE, IFDS path edges | step 1, relational summaries | return-dependent taint with a path-edge certificate |
| 4 | interpolation, CEGAR, merging | steps 1 to 3, a measured spurious rate | measured false-positive reduction; checked implications |
| 5 | absence for a bounded fragment | step 4, L5 | no false "safe"; refusal outside the fragment |

Step 1 comes before step 2 because a witness for a direct sink is worth more than a bit-vector engine with no path.
Step 3 comes before step 4 because summaries reduce paths while interpolation reduces formulas. Step 5 is not
recommended.

---

## 12. Uncertainty, falsifiers and open questions

| claim | confidence | falsifier |
|---|---|---|
| The classical, concolic and DSE taxonomy and the King, DART, CUTE, KLEE lineage | **H** | a standard text contradicting it; not expected |
| Bounded SE is under-approximate; a witness is existential | **H** | a bounded engine proving absence without complete enumeration |
| `sat` is checkable, a bare `unsat` is not | **H** | a cheap independent check for arbitrary `unsat` without a proof |
| The KLEE, S2E, Mayhem and SymCC memory-model characterisations | **M** | source or paper details differing |
| The SymCC and SymSan performance numbers | **M** (paper claims) | an independent benchmark |
| SymCC++ is a distinct published system | **L** | a paper or repository; currently no evidence |
| OSS-Fuzz's default engines exclude concolic execution | **M** | OSS-Fuzz documentation adding a concolic engine |
| The concolic slice reduces triage time and false positives | **L** | the step 1 pilot; that is its purpose |
| Bit-vectors and a length model are enough for CWE-787 and CWE-190 | **L** | the step 2 pilot; memory modelling may dominate |
| Absence is out of reach with current assets | **H** | a checked encoding, complete enumeration and an environment model |

Open questions:

1. **Trace or PC only.** A trace is stronger but may be expensive; measure its size and time.
2. **String guards.** A bounded byte array, a string theory, or an uninterpreted predicate with a concrete witness?
   Start with the last.
3. **Addresses.** Concrete addresses are simple but miss alias paths; a may-alias `ite` is precise but larger. Start
   concrete and mark the assumption.
4. **Seed source.** A hand corpus, a fuzzer corpus, or both? Start deterministic.
5. **Solver choice.** Z3 or cvc5: keep the query neutral, make the solver a flag, pin its identity.
6. **C reproduction.** Is a `Wil.run` witness enough, or must the C binary reproduce under ASan? For T1 a harness is
   cheap; for T3 it is essential. `scry dynamic` already provides the sanitizer side.
7. **Summary shape.** A boolean may-summary is a precision ceiling; relational IFDS summaries are next.
8. **E-graphs on PCs.** A measured simplification win would justify one; otherwise it is another trusted transformer.

---

## 13. Citations

Confidence: **H** = paper, DOI or publisher page checked; **M** = canonical reference or vendor documentation, exact
bibliographic detail not re-checked; **L** = plausible, not verified. DOIs are given where known; where a DOI was not
verified, the entry is **M** or **L** even if the work is well known. Keys are stable within this document; gaps in
the numbering are entries that were dropped.

### Classical symbolic execution

[S1] J. C. King, "Symbolic Execution and Program Testing", *CACM* 19(7):385–394, 1976. DOI 10.1145/360248.360252. **H** — path condition, symbolic state, test-data generation.
[S2] L. A. Clarke, "A System to Generate Test Data and Symbolically Execute Programs", *IEEE TSE* 2(3):215–222, 1976. DOI 10.1109/TSE.1976.233817. **M**.
[S3] R. S. Boyer, B. Elspas, K. N. Levitt, "SELECT — A Formal System for Testing and Debugging Programs by Symbolic Execution", *SIGPLAN Notices* 10(6):234–245, 1975. DOI 10.1145/390016.808445. **M**.
[S4] W. E. Howden, "Symbolic Testing and the DISSECT Symbolic Evaluation System", *IEEE TSE* 3(4):266–278, 1977. DOI 10.1109/TSE.1977.231142. **M**.
[S5] C. V. Ramamoorthy, S.-B. F. Ho, W. T. Chen, "On the Automated Generation of Program Test Data", *IEEE TSE* 2(4):290–294, 1976. DOI 10.1109/TSE.1976.233835. **M**.

### Concolic and dynamic symbolic execution

[S6] P. Godefroid, N. Klarlund, K. Sen, "DART: Directed Automated Random Testing", *PLDI 2005*, 213–223. DOI 10.1145/1065010.1065036. **H** — concrete plus symbolic, negate the last branch, random seeds.
[S7] K. Sen, D. Marinov, G. Agha, "CUTE: A Concolic Unit Testing Engine for C", *ESEC/FSE 2005*, 263–272. DOI 10.1145/1081706.1081750. **H** — pointer and array constraints, concolic unit testing.
[S9] C. Cadar, D. Dunbar, D. Engler, "KLEE: Unassisted and Automatic Generation of High-Coverage Tests for Complex Systems Programs", *OSDI 2008*. URL https://llvm.org/pubs/2008-12-OSDI-KLEE.pdf. **H** — object memory, copy-on-write, constraint independence, POSIX model, search and budgets.
[S10] P. Godefroid, M. Y. Levin, D. A. Molnar, "Automated Whitebox Fuzz Testing", *NDSS 2008*. URL https://www.ndss-symposium.org/ndss2008/. **M** — SAGE and generational search; the URL is the proceedings index.
[S11] P. Godefroid, "Compositional Dynamic Test Generation", *POPL 2007*, 47–54. DOI 10.1145/1190216.1190220. **H** — function summaries and memoisation (SMART).
[S12] S. Anand, P. Godefroid, N. Tillmann, "Demand-Driven Compositional Symbolic Execution", *TACAS 2008*, LNCS 4963, 367–381. DOI 10.1007/978-3-540-78800-3_27. **H** — demand-driven summaries.
[S13] P. Godefroid, A. V. Nori, S. K. Rajamani, S. D. Tetali, "Compositional May-Must Program Analysis: Unleashing the Power of Alternation", *POPL 2010*, 43–56. DOI 10.1145/1707801.1706307. **M** — may/must summaries; DOI from Crossref, page range not re-checked.
[S14] T. Reps, S. Horwitz, M. Sagiv, "Precise Interprocedural Dataflow Analysis via Graph Reachability", *POPL 1995*, 49–61. DOI 10.1145/199448.199462. **H** — IFDS, exploded supergraph, meet over all valid paths.
[S15] M. Sharir, A. Pnueli, "Two Approaches to Interprocedural Data Flow Analysis", in *Program Flow Analysis: Theory and Applications*, Prentice-Hall, 1981, 189–233. **M** — functional and call-string approaches.
[S16] C. Cadar, K. Sen, "Symbolic Execution for Software Testing: Three Decades Later", *CACM* 56(2):82–90, 2013. DOI 10.1145/2408776.2408795. **H** — path explosion, memory and environment as the limits.
[S17] R. Baldoni, E. Coppa, D. C. D'Elia, C. Demetrescu, I. Finocchi, "A Survey of Symbolic Execution Techniques", *ACM Computing Surveys* 51(3):50, 2018. DOI 10.1145/3182657. **H** — taxonomy, search strategies, applications.

### Tools

[S19] V. Chipounov, V. Kuznetsov, G. Candea, "S2E: A Platform for In-Vivo Multi-Path Analysis of Software Systems", *ASPLOS 2011*, 265–278. DOI 10.1145/1950365.1950396. **H** — selective symbolic execution in a full-system VM.
[S20] Y. Shoshitaishvili, R. Wang, C. Salls, N. Stephens, M. Polino, A. Dutcher, J. Grosen, S. Feng, C. Hauser, C. Kruegel, G. Vigna, "SOK: (State of) The Art of War: Offensive Techniques in Binary Analysis", *IEEE S&P 2016*, 138–157. DOI 10.1109/SP.2016.17. **H** — angr, VEX, SimProcedure, explore.
[S21] S. K. Cha, T. Avgerinos, A. Rebert, D. Brumley, "Unleashing Mayhem on Binary Code", *IEEE S&P 2012*, 380–394. DOI 10.1109/SP.2012.31. **H** — hybrid online/offline execution, index-based memory, exploit generation.
[S22] T. Avgerinos, A. Rebert, S. K. Cha, D. Brumley, "Enhancing Symbolic Execution with Veritesting", *ICSE 2014*, 1083–1094. DOI 10.1145/2568225.2568293. **M** — static/dynamic merging; DOI not re-checked.
[S23] S. Poeplau, A. Francillon, "Symbolic Execution with SymCC: Don't Interpret, Compile!", *USENIX Security 2020*, 181–198. URL https://www.usenix.org/conference/usenixsecurity20/presentation/poeplau. **H** — LLVM pass, runtime, concolic execution, fuzzer integration; performance claims are the paper's.
[S24] S. Poeplau, A. Francillon, "SymQEMU: Compilation-Based Symbolic Execution for Binaries", *NDSS 2021*. DOI 10.14722/ndss.2021.24118. **H** — TCG instrumentation; binary-only.
[S25] J. Chen, W. Han, M. Yin, H. Zeng, C. Song, B. Lee, H. Yin, I. Shin, "SymSan: Time and Space Efficient Concolic Execution via Dynamic Data-Flow Analysis", *USENIX Security 2022*, 2531–2548. URL https://www.usenix.org/conference/usenixsecurity22/presentation/chen-ju. **H** — DFSan labels as AST indices; the 62× and 6.5× figures are the paper's claims.
[S26] D. A. Ramos, D. R. Engler, "Under-Constrained Symbolic Execution: Correctness Checking for Real Code", *USENIX Security 2015*, 49–64. URL https://www.usenix.org/conference/usenixsecurity15/technical-sessions/presentation/ramos. **H** — function-level SE with unconstrained inputs and an environment model.
[S27] M. Mossberg, F. Manzano, E. Hennenfent, A. Groce, G. Grieco, J. Feist, T. Brunson, A. Dinaburg, "Manticore: A User-Friendly Symbolic Execution Framework for Binaries and Smart Contracts", *ASE 2019*, 1186–1189. DOI 10.1109/ASE.2019.00133. **H** — state life cycle, event system, EVM and native targets.
[S28] F. Saudel, J. Salwan, "Triton: A Concolic Execution Framework", *SSTIC 2015*. URL https://www.sstic.org/2015/presentation/triton_dynamic_symbolic_execution_and_runtime_analysis/. **M** — Pin-based library, taint plus symbolic execution plus snapshots; the paper is in French.
[S29] SymCC documentation, "Combining SymCC with a fuzzer". URL https://github.com/eurecom-s3/symcc/blob/master/docs/Fuzzing.txt. **H** — `symcc_fuzzing_helper`, AFL, input exchange.
[S30] LibAFL Book, "Concolic Tracing & Hybrid Fuzzing". URL https://aflplus.plus/libafl-book/advanced_features/concolic/concolic.html. **H** — `symcc_runtime`, SymCC/SymQEMU integration.
[S31] "The Mayhem Cyber Reasoning System", *IEEE Security & Privacy* 16(2):52–60, 2018. DOI 10.1109/MSP.2018.1870873. **H** — Cyber Grand Challenge, exploit generation, product context.
[S32] Google OSS-Fuzz documentation. URL https://google.github.io/oss-fuzz/. **M** — continuous fuzzing, sanitizers, libFuzzer/AFL++/Centipede; check the current documentation for engine names.

### Path explosion, merging, interpolation, summaries

[S33] V. Kuznetsov, J. Kinder, S. Bucur, G. Candea, "Efficient State Merging in Symbolic Execution", *PLDI 2012*, 193–204. DOI 10.1145/2345156.2254088. **H** — merging at joins; the formula-size trade-off.
[S35] E. Bounimova, P. Godefroid, D. Molnar, "Billions and Billions of Constraints: Whitebox Fuzz Testing in Production", *ICSE 2013*, 122–131. DOI 10.1109/ICSE.2013.6606618. **H** — SAGE at scale; generational search.
[S36] N. Stephens, J. Grosen, C. Salls, A. Dutcher, R. Wang, J. Corbetta, Y. Shoshitaishvili, C. Kruegel, G. Vigna, "Driller: Augmenting Fuzzing Through Selective Symbolic Execution", *NDSS 2016*. URL https://www.ndss-symposium.org/ndss2016/. **M** — hybrid fuzzing; the URL is the proceedings index.
[S38] W. Craig, "Three Uses of the Herbrand–Gentzen Theorem in Relating Model Theory and Proof Theory", *Journal of Symbolic Logic* 22(3):269–285, 1957. DOI 10.2307/2269665. **M** — interpolation.
[S39] K. L. McMillan, "Interpolation and SAT-Based Model Checking", *CAV 2003*, LNCS 2725, 1–13. DOI 10.1007/978-3-540-45069-6_1. **H**.
[S40] K. L. McMillan, "Lazy Abstraction with Interpolants", *CAV 2006*, LNCS 4144, 123–136. DOI 10.1007/11817963_14. **H** — interpolant summaries.
[S41] T. A. Henzinger, R. Jhala, R. Majumdar, K. L. McMillan, "Abstractions from Proofs", *POPL 2004*, 232–244. DOI 10.1145/964001.964029. **M** — proofs to abstractions.
[S42] E. Clarke, O. Grumberg, S. Jha, Y. Lu, H. Veith, "Counterexample-Guided Abstraction Refinement", *CAV 2000*, LNCS 1855, 154–169. DOI 10.1007/10722167_15. **H** — CEGAR.
[S43] T. Ball, S. K. Rajamani, "The SLAM Project: Debugging System Software via Static Analysis", *POPL 2002*, 1–3. DOI 10.1145/503272.503274. **H** — predicate abstraction and refinement.
[S44] T. A. Henzinger, R. Jhala, R. Majumdar, G. Sutre, "Lazy Abstraction", *POPL 2002*, 58–70. DOI 10.1145/503272.503279. **H** — lazy predicate abstraction.
[S45] J. Jaffar, J. Murali, J. A. Navas, A. E. Santosa, "TRACER: A Symbolic Execution Tool for Verification", *ICSE 2012*, 1381–1384. DOI 10.1109/ICSE.2012.6227133. **M** — interpolation-based path pruning.

### Abstract interpretation and dataflow

[S48] P. Cousot, R. Cousot, "Abstract Interpretation: A Unified Lattice Model for Static Analysis of Programs by Construction or Approximation of Fixpoints", *POPL 1977*, 238–252. DOI 10.1145/512950.512973. **H** — Galois connections, widening.
[S49] G. A. Kildall, "A Unified Approach to Global Program Optimization", *POPL 1973*, 194–206. DOI 10.1145/512927.512945. **H** — monotone frameworks, MOP/MFP.
[S56] X. Rival, L. Mauborgne, "The Trace Partitioning Abstract Domain", *ACM TOPLAS* 29(5):26, 2007. DOI 10.1145/1275497.1275501. **H**.

### Trust, proofs, solvers

[S58] L. Cruz-Filipe, M. J. H. Heule, W. A. Hunt, M. Kaufmann, P. Schneider-Kamp, "Efficient Certified RAT Verification", *CADE-26*, LNCS 10395, 2017. DOI 10.1007/978-3-319-63046-5_14. **H** — LRAT/RAT checking.
[S59] H. Lammich, "Efficient Verified (UN)SAT Certificate Checking", *JAR* 64:513–532, 2019. DOI 10.1007/s10817-019-09525-z. **H** — verified (UN)SAT checking.
[S60] [Stage 28: solvers](../stages/28-solvers.md) (this repository), sections 28a to 28e. **H** — Wiz's `smt`, `sat_decide`, `bv_decide` and `sat_decide_native`.
[S61] L. de Moura, N. Bjørner, "Z3: An Efficient SMT Solver", *TACAS 2008*, LNCS 4963, 337–340. DOI 10.1007/978-3-540-78800-3_24. **H**.
[S62] C. Barrett, P. Fontaine, C. Tinelli, "The SMT-LIB Standard: Version 2.6", 2017; version 2.7 announced 2026. URL https://smt-lib.org/. **H** — commands, `get-model`/`get-value`, `unknown`.

### E-graphs, sanitizers

[S63] C. G. Nelson, "Techniques for Program Verification", PhD thesis, Stanford, 1980. **M** — congruence closure; the original e-graph.
[S64] M. Willsey, C. Nandi, Y. R. Wang, O. Flatt, Z. Tatlock, P. Panchekha, "egg: Fast and Extensible Equality Saturation", *PACMPL* 5(POPL):23, 2021. DOI 10.1145/3434304. **M** — e-graphs, extraction, e-class analyses.
[S65] Y. Zhang, Y. R. Wang, M. Willsey, Z. Tatlock, "Relational E-Matching", *POPL 2022*. DOI 10.1145/3498693. **M** — e-matching as a join.
[S66] R. Nieuwenhuis, A. Oliveras, "Proof-Producing Congruence Closure", *RTA 2005*, LNCS 3467, 453–468. DOI 10.1007/978-3-540-32033-3_33. **M** — explanations to proofs.
[S67] Y. Zhang et al., "Better Together: Unifying Datalog and Equality Saturation", *PLDI 2023*. DOI 10.1145/3591239. **H** — egglog; lattice merges.
[S68] K. Serebryany, D. Bruening, A. Potapenko, D. Vyukov, "AddressSanitizer: A Fast Address Sanity Checker", *USENIX ATC 2012*. URL https://www.usenix.org/conference/atc12/technical-sessions/presentation/serebryany. **H** — ASan.
[S69] LLVM, "UndefinedBehaviorSanitizer". URL https://clang.llvm.org/docs/UndefinedBehaviorSanitizer.html. **M** — UBSan.
[S70] LLVM, "MemorySanitizer". URL https://clang.llvm.org/docs/MemorySanitizer.html. **M** — MSan.
