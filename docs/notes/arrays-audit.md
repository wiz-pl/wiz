# The Arrays audit: `List` indexed in a loop

`List.getD`, `List.setAt` and `List.nth` walk the list to the index, so a loop that
indexes a `List` N times costs Θ(N²) cons cells, while `Array`/`Bytes`/`U32Array` index
in O(1). This note records the audit of `lib/` and `scry/` (2026-11-19), the one place
the change was contained, and the places it was not, with their cost.

The costs are operation counts, not wall times: a list read at index `i` walks `i` cons
cells (and a `List.setAt` at `i` allocates a new prefix of length `i`). Wall times belong
to `bench/stdlib-bench.py` under a measurement window. Two modes were added to that
harness, `list-index` and `egraph`; see `bench/README.md`.

## Occurrences

`grep -rn 'List\.getD\|List\.setAt\|List\.nth' lib scry/src --include='*.wiz'` finds
178 occurrences on 175 lines:

| module | occurrences | what |
| --- | ---: | --- |
| `lib/Scry/Cert.wiz` | 106 | the proof checker: rule/node/done tables, in code and in lemma statements |
| `lib/WordArray.wiz` | 24 | the `U8Array`/`U32Array`/`U64Array` *models* (`getD` is defined as `List.getD`) |
| `scry/src/Scry/Project.wiz` | 14 | the whole-program record: `funcTu`, `units`, `funcs`, `paths`, `maps` |
| `scry/src/Scry/Preproc.wiz` | 12 | `Pre` line/file tables: `lineFile`, `lineOrig`, `lineStart`, `texts`, `fileLines` |
| `lib/Scry/Datalog.wiz` | 7 | `Program` schema tables: `arities`, `funcs`, `strata` |
| `scry/src/Scry/Lower.wiz` | 5 | `blocks`, `b.stmts`, `pre.texts`/`paths` |
| `scry/src/Scry/ProjectTaint.wiz` | 3 | `u.tu.paths`/`files`, `p.funcTu` |
| `scry/src/Scry/CstStore.wiz` | 3 | `rowAt` and the two reads of a tuple row |
| `lib/Scry/Eval.wiz` | 2 | the lattice function table and the stratum table |
| `scry/src/Scry/ProjectIO.wiz` | 1 | `paths f`, the same field as `Project` |
| `scry/src/Scry/CstOptics.wiz` | 1 | a tuple column read |

Beyond `WordArray.wiz` there are none outside `lib/Scry/` and `scry/src/`, and its 24
occurrences are the interpreter's deliberately list-backed model (compiled code calls
the native `wiz_warray_*` functions instead), so they are not a hot path.

## Changed: `lib/Scry/Egraph.wiz`

The e-graph's union-find stored `parent : List Nat` and `rank : List Nat`, and extraction
stored the costs as `List Nat`. They are now `U64Array` (`lib/WordArray.wiz`, already
imported). The table is private to the module, so the change is contained.

| site | before | after |
| --- | --- | --- |
| `Scry.EGraph.findGo` (line 181) | a hop at id `x` scanned `x` cons cells | `U64Array.getD`: O(1) compiled |
| `Scry.EGraph.union` (lines 239–252) | two rank reads and a link copied Θ(N) | two `getD`, three `set`: O(1) compiled |
| `Scry.EGraph.add` (lines 222–223) | each new id appended to both lists: Θ(N), so building N ids Θ(N²) | two `push`: O(1), Θ(N) total |
| `Scry.EGraph.compressFrom` (line 259) | one `setAt` per id: Θ(N²) | one `set` per id: Θ(N) compiled |
| `Scry.EGraph.costPass` (lines 381–385) | one relaxation pass Θ(N²) | `getD`/`set`: Θ(N) compiled |
| `Scry.EGraph.costs` (line 395) | `egRep` built a `List Nat` | `egU64Rep` builds a `U64Array`, O(N) |

So `find` on a path of length k went from Θ(k·N) to Θ(k); a union from Θ(N) to O(1);
`compress` from Θ(N²) to Θ(N); extraction (`N + 1` relaxation passes) from Θ(N³) to
Θ(N²). The checksums are unchanged (`tests --run scry-egraph` and the
`examples/scry-egraph-*.wiz` digests are the gate).

`U64Array`, not `Array`: `Array` (`lib/Std.wiz`) is an axiom whose operations are
`extern`, so `#eval` of the e-graph would panic ("foreign functions only run in compiled
code"), and the `scry-egraph` cases run most graphs under the interpreter. `U64Array` is
a sealed `List U64` *model* with `implemented_by` natives: the interpreter and the
kernel see the model (the same list as before, so the examples' `#eval` still works),
compiled code (C, LLVM) uses the runtime's `uint64_t` array. The natives are registered
once in `lib/WordArray.wiz` and already have ledger rows, so using the type here adds no
trust row.

## Changed: `scry/src/Scry/CstStore.wiz`

The store's relation tuples were already a `U32Array` (`relTuples`), but both readers
converted the whole column to a list and then sliced it once per row:

```wiz no-check
let flat := List.map UIntN.toNat (U32Array.toList s.relTuples);   -- O(tuples)
List.take arity (List.drop (lo + j * arity) flat)                  -- O(tuples) per row
```

so `relationsOf` and the relation half of `render` were O(tuples²) (and `render` calls
`relRows` per relation). `Scry.CstStore.tupleRow` reads `relTuples` by index instead:
one row is O(arity), and all rows are O(tuples). This is internal to two functions; no
record, fixture or output text changes. The gate is `scry/tests/relations.wiz` (the
arity-2/arity-3/empty relation round trip through `relationsOf`, `render` and `ofText`,
with its `.expected` golden) and the `=scry-c2wil` spill fixtures.

## Left, with the cost

| site (lines) | indexed value | cost | why left |
| --- | --- | --- | --- |
| `lib/Scry/Cert.wiz` (131, 250–251, 266, 376–390, 428–436, 513, 542, …; 106 sites) | `done pid`, `p.rules ri`, `d.nodes d.root` in the checker and in the *statements* of its lemmas | one step Θ(N) for N nodes/rules; a certificate of S steps Θ(S·N) | the lists are part of the theorem statements (the specification), so an `Array` field changes every statement and proof; the model stays list-backed and a native index would be a refinement |
| `lib/Scry/Datalog.wiz` (138, 155, 209–211, 222–223) | `p.arities rel`, `p.funcs i`, `strat rel`; per atom/rule | Θ(R) (relations) / Θ(F) (functions) per lookup | `Program`/`Rule` are the public record built by the tests and the front ends; a change touches every fixture. R and F are the schema size (typically ≤ 50) |
| `lib/Scry/Eval.wiz` (246, 460) | `List.getD funcs i` per lattice `map`; `List.getD strat rel` per stratum filter | Θ(F), Θ(R) per evaluation | same records as above; F is the transfer-function table |
| `lib/Scry/Egraph.wiz` `etableFindL` (196–198; called at 217, 267, 307, 322) | the hash-cons table (`List (ENode × Nat)`) scanned per `add`/`rebuildNodes` | Θ(E) per lookup, Θ(N·E) for N adds | a hash-consed equality table, not a numeric index: the right structure is `U64Map`/a native table; `Array` would not help |
| `lib/Scry/Egraph.wiz` `rebuildNodes` (270–271) | `List.append` on `nodes`/`etable` per node | Θ(N²) per rebuild pass | append-heavy rather than index-heavy; `Array.push` fixes it, but `nodesOfGo`/`canonical`/`costPass` then fold over an `Array`, which is a larger change to the rebuild |
| `scry/src/Scry/Preproc.wiz` (144–145, 296–305, 315–331) | `lineFile i`, `lineOrig i`, `lineStart i` (one per line), `texts file`, `fileLines file` | a lookup Θ(L) for L lines; a pass over T tokens Θ(T·L) | `Pre` is threaded through `Preproc`, `Project`, `ProjectTaint`, `ProjectIO` and built in fixtures |
| `scry/src/Scry/Project.wiz` (360, 517–519, 609, 634, 663, 739, 792–794, 827–887) | `funcTu i`, `units`, `funcs`, `paths`, `maps` by function/file id | Θ(F) per lookup, Θ(F²) for a pass over all functions | `Project` is the whole-program record, shared with `ProjectIO`/`ProjectTaint` |
| `scry/src/Scry/ProjectIO.wiz` (131) | `paths f` | Θ(F) per file path read | the same `Project` field as above |
| `scry/src/Scry/ProjectTaint.wiz` (56–57, 76) | `u.tu.paths`/`files`, `p.funcTu` | Θ(F) per slice location/function | the same `Project` field as above |
| `scry/src/Scry/CstStore.wiz` (222, two reads; 558) | `rowAt row i` / `List.getD row (i + 1)` on a *tuple* row passed in as a list | Θ(arity) per column read; rows are per token | the columns already are `U32Array`; the list is the per-token row handed to the optic, and making rows arrays is a cross-package change (`CstOptics`, the taint passes) |
| `scry/src/Scry/CstOptics.wiz` (70) | a tuple column (`t.tuples`, by index) | Θ(#tuples) per column | the tuple table is a list in the CST store's public record |
| `scry/src/Scry/Lower.wiz` (106–107, 125, 1636, 2477) | `blocks i`, `b.stmts p`, `pre.texts f` | Θ(#blocks) per terminator; Θ(#stmts) per position | the lowering pass holds the block/statement tables |
| `lib/Scry/Analysis.wiz` `Scry.nthD` (91–94; used at `RuleTaint.wiz:746`, `Taint.wiz:255`) | row columns in taint transfer | Θ(arity) per column | a U64 row's arity is small and fixed by the relation |
| `lib/Hdl/Display.wiz` `Display.romGo` | `List.take`/`List.drop` at each binary-search level | Θ(N) per level, Θ(N log N) | small circuit tables, and the result is a proof-carrying ROM |
| `lib/Plot.wiz` `Plot.thin` | `List.drop` per sampled point | Θ(N) per point, Θ(N²) for the pass | plotting only; the input is a sampled list |

## The benchmark modes

`list-index` (default N = 4000) builds `[0, N)` and does 10 passes of N reads at a
pseudo-random index; on a list that is ≈ 5·N² cons cells (≈ 8·10⁷ at 4000), while the
same reads on an `Array` (`array-index`, which also writes) are 20·N array operations.
`egraph` (default N = 3000) builds N e-nodes, unions N pseudo-random pairs and does 10·N
`find`s over the same code the change touched; its checksum is identical before and
after the change. Run them with the existing harness:

```sh
scripts/stdlib-bench.py --size list-index=4000 --size array-index=4000
scripts/stdlib-bench.py --baseline-bin OLD-BENCH-EXE --reps 15
```
