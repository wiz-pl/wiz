# The Arrays audit: `List` indexed in a loop

`List.getD`, `List.setAt` and `List.nth` walk the list to the index, so a loop that
indexes a `List` N times costs Θ(N²) cons cells, while `Array`/`Bytes`/`U32Array`
index in O(1). This note records the audit of `lib/` and `scry/` (2026-11-19), the one
place the change was contained, and the places it was not, with their cost.

The numbers here are operation counts (a list read at index i walks i cells), not wall
times: wall times belong to `bench/stdlib-bench.py` under a measurement window. Two
modes were added to that harness, `list-index` and `egraph`; see `bench/README.md`.

## Changed: `lib/Scry/Egraph.wiz`

The e-graph's union-find stored `parent : List Nat` and `rank : List Nat`, and
extraction stored the costs as `List Nat`. They are now `U64Array` (`lib/WordArray.wiz`,
already imported):

| site | before | after |
| --- | --- | --- |
| `Scry.EGraph.findGo` (`U64Array.getD`) | a hop at id `x` scanned `x` cons cells | O(1) compiled |
| `Scry.EGraph.union` (two `U64Array.getD`, three `U64Array.set`) | a link copied Θ(N) | O(1) compiled |
| `Scry.EGraph.add` (two `U64Array.push`) | each new id appended to both lists: Θ(N), so building N ids Θ(N²) | O(1), Θ(N) total |
| `Scry.EGraph.compressFrom` (`U64Array.set`, once per id) | one pass Θ(N²) | Θ(N) compiled |
| `Scry.EGraph.costPass` (`U64Array.getD`, `U64Array.set`) | one relaxation pass Θ(N²) | Θ(N) compiled |
| `Scry.EGraph.costs` (`egU64Rep`) | `egRep` built a `List Nat` | an `U64Array`, O(N) |

So `find` on a path of length k went from Θ(k·N) to Θ(k); a union from Θ(N) to O(1);
`compress` from Θ(N²) to Θ(N); extraction (`N + 1` relaxation passes) from Θ(N³) to
Θ(N²). The checksums are unchanged (`tests --run scry-egraph` and the
`examples/scry-egraph-*.wiz` digests are the gate). `parent`, `rank` and `costs` are
private to the module — no other module or example reads the fields — which is what
made the change contained.

`U64Array`, not `Array`: `Array` (`lib/Std.wiz`) is an axiom whose operations are
`extern`, so `#eval` of the e-graph would panic ("foreign functions only run in
compiled code"), and the `scry-egraph` cases run most graphs under the interpreter.
`U64Array` is a sealed `List U64` *model* with `implemented_by` natives: the interpreter
and the kernel see the model (the same list as before, so the examples' `#eval` still
works), compiled code (C, LLVM) uses the runtime's `uint64_t` array. The natives are
registered once in `lib/WordArray.wiz` and already have ledger rows, so using the type
here adds no trust row.

## Left, with the cost

| site | indexed value | cost | why left |
| --- | --- | --- | --- |
| `lib/Scry/Cert.wiz` (106 `List.getD`) | `done pid`, `p.rules ri`, `d.nodes d.root` in the checker and in the *statements* of its lemmas | one step Θ(N) for N nodes/rules; a certificate of S steps Θ(S·N) | the lists are part of the theorem statements (the specification), so an `Array` field changes every statement and proof; the model stays list-backed and a native index would be a refinement |
| `lib/Scry/Datalog.wiz` (6) | `p.arities rel`, `p.funcs i`, `strat rel`; per atom/rule | Θ(R) (relations) / Θ(F) (functions) per lookup | `Program`/`Rule` are the public record built by the tests and the front ends; a change touches every fixture. R and F are the schema size (typically ≤ 50) |
| `lib/Scry/Eval.wiz` (2) | `List.getD funcs i` per lattice `map`; `List.getD strat rel` per stratum filter | Θ(F), Θ(R) per evaluation | same records as above; F is the transfer-function table |
| `lib/Scry/Egraph.wiz` `etableFindL` | the hash-cons table (`List (ENode × Nat)`) scanned per `add`/`rebuildNodes` | Θ(E) per lookup, Θ(N·E) for N adds | a hash-consed equality table, not a numeric index: the right structure is `U64Map`/a native table; `Array` would not help |
| `lib/Scry/Egraph.wiz` `rebuildNodes` | `List.append` on `nodes`/`etable` per node | Θ(N²) per rebuild pass | append-heavy rather than index-heavy; `Array.push` fixes it, but `nodesOfGo`/`canonical`/`costPass` then fold over an `Array`, which is a larger change to the rebuild |
| `scry/src/Scry/Preproc.wiz` (12) | `lineFile i`, `lineOrig i`, `lineStart i` (one per line), `texts file`, `fileLines file` | a lookup Θ(L) for L lines; a pass over T tokens Θ(T·L) | `Pre` is threaded through `Preproc`, `Project`, `ProjectTaint`, `ProjectIO` and built in fixtures |
| `scry/src/Scry/Project.wiz` (13) | `funcTu i`, `units`, `funcs`, `paths`, `maps` by function/file id | Θ(F) per lookup, Θ(F²) for a pass over all functions | `Project` is the whole-program record, shared with `ProjectIO`/`ProjectTaint` |
| `scry/src/Scry/CstStore.wiz` (2) | `rowAt row i` / `List.getD row (i + 1)` | Θ(arity) per column read; rows are per token | the CST store is scry's central index; rows would become `U32Array`, a cross-package change |
| `scry/src/Scry/Lower.wiz` (5) | `blocks i`, `b.stmts p`, `pre.texts f` | Θ(#blocks) per terminator; Θ(#stmts) per position | the lowering pass holds the block/statement tables |
| `lib/Scry/Analysis.wiz` `Scry.nthD` (used at `RuleTaint.wiz`, `Taint.wiz`) | row columns in taint transfer | Θ(arity) per column | a U64 row's arity is small and fixed by the relation |
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
