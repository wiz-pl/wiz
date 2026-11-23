# scry: the large-file path (2026-11-15)

Status: profile and fix, no analysis change. Branch `agent/scry-scale`, based on
`agent/scry-points-to` `bb1a6294`. Numbers are wall time on this 32-core Linux machine,
with the branch's own `grail`/`scry`; they are **informational**, not a `perf-run`
measurement (the machine is shared). "warm" means the source and binary were already in
the page cache; "cold" is the first run after a build.

Two passes are recorded here. The first (`f9294ec4`) removed the linear/quadratic work
in the CST store, the text slicing and the origin map, and added the limits contract.
This pass removes the remaining **per-function** quadratic work: point lookups, the
reaching-definitions fixpoint, the points-to state and the repeated plan/summary work.

**Restack (2026-11-16, `agent/scry-linearise`).** `eeb1b172` never landed; it is merged
here onto master after #376. Two things differ from the numbers below. The lowering keeps
master's `Scry.recoverTop` (it unwraps `ERROR` nodes, which is what recovers the
`old-wizard.c`/`droste.c` units) and **not** this pass's `topNodes`, which also descended
`preproc_ifdef`/`linkage_specification` and would change lowering outputs; item 9 below is
therefore superseded by `recoverTop`, and the generated grammar keeps 2 functions / 12
boundary warnings. Plans are prepared with the exported-entry sources #376 added
(`Scry.prepareAllWithEntries`). The re-measured numbers are in "Restack measurements" at
the end.

## The pathological input

`native/tree-sitter-c/src/parser.c` is the generated tree-sitter-c grammar: 3 872 012
bytes, 1 110 871 CST nodes, 1 110 870 edges, 2 functions, 12 lowering-boundary warnings,
2 memory warnings, 0 findings, 31 `ERROR`/`MISSING` nodes. It now finishes complete under
one second of analysis after parsing.

`old-wizard.c` (475 KB, 107 938 CST nodes) is a Futhark-generated C unit with 1 115
functions and one 87 KB function (`futrts_pixel_8826`). **Before this pass the raw file
lowered 0 functions**: its definitions sit under `ERROR`/`preproc_ifdef` nodes
(`#ifdef __cplusplus … extern "C" {`), and the lowering walked only the translation
unit's direct children. That silent empty result is fixed by the preprocessor/error
descent below. It now analyses 1 115 functions, 3 936 boundary warnings, 372 memory
warnings and 2 checked findings.

Reproduce and bound it:

```sh
cd scry
grail build
./.grail/bin/scry taint native/tree-sitter-c/src/parser.c --json --allow-errors --progress
./.grail/bin/scry taint ../old-wizard.c --json --allow-errors --progress
./.grail/bin/scry taint big.c --json --allow-errors --max-rounds 1   # marked partial
grail test scale
```

## Stage profile (3.9 MB generated parser.c, warm)

| stage | before (first pass) | after | detail |
|---|---:|---:|---|
| `read` | 0.42 s | 0.34 s | 3 872 012 bytes, 118 873 lines |
| `parse` | 1.23 s | 0.77 s | tree-sitter → shim columns, 1 110 871 nodes |
| `store` | 0.07 s | 0.05 s | copy columns into `Scry.CstStore` |
| `lower` | 0.51 s | 0.18 s | 3 functions, 13 boundary warnings |
| `points-to` | < 0.01 s | < 0.01 s | 5 vars, 2 locations, 3 rounds |
| `plans` | — | < 0.01 s | 3 prepared plans (new stage line) |
| `summaries` | < 0.01 s | < 0.01 s | 1 round, converged; includes the final results |
| `origins` | < 0.01 s | < 0.01 s | 10 entries |

Warm wall time **1.3–2.2 s**; peak RSS **535 MiB** (the node columns dominate). The
first (cold) run is ≈ 6–7 s. Before the first pass it timed out at 300 s.

## Function-heavy files

| input | nodes | functions | before | after (warm) | peak RSS |
|---|---:|---:|---:|---:|---:|
| `tree-sitter/lib/src/parser.c` | 17 163 | 51 | 117.7 s (note) / 25.2 s (measured) | **0.12–0.23 s** | 49 MiB |
| `tree-sitter/lib/src/query.c` | 34 450 | 114 | 180.7 s (note) / 7.0 s (measured) | **0.19–0.45 s** | 56 MiB |
| generated tree-sitter-c `parser.c` | 1 110 871 | 3 | timeout (300 s) | **1.3–2.2 s** | 535 MiB |
| `old-wizard.c` | 107 938 | 1 115 | 0 functions (silent) | **13.5–19 s** | 154 MiB |
| `wizard-test/build/v_x3/w.c` | 535 497 | 1 281 | 0 functions (silent) | lower 4.6 s; points-to ≈ 250 s | 1.2 GiB |

`old-wizard.c` stage profile after the fixes (one 13.5 s run):

| stage | cumulative | delta |
|---|---:|---:|
| `read` | 0.06 s | 0.06 s |
| `parse` | 0.15 s | 0.09 s |
| `store` | 0.16 s | 0.01 s |
| `lower` | 0.57 s | 0.41 s |
| `points-to` | 12.81 s | 12.24 s, 11 rounds, 4 065 vars, 595 locations |
| `plans` | 12.92 s | 0.11 s, 1 115 plans |
| `summaries` | 13.27 s | 0.35 s, 1 round (the final results are reused) |
| `origins` | 13.52 s | 0.25 s, 11 357 entries |

The runtime parser's old 25 s was one huge function on every pass: null checks, stores,
loads and calls spent their time in `locate`/`stmtAt` and in list-based reaching
definitions, and the final results re-evaluated every function after convergence. It is
now flat.

## The larger generated unit

`wizard-test/build/v_x3/w.c` (6.6 MB, 535 497 nodes, 1 281 functions) is the same kind
of Futhark output at a larger scale. Its lowering is 4.6 s and its **points-to is the
remaining hot spot**: 10 rounds, 24 s each, 12 751 vars and 2 687 locations. A full run
is over 300 s on this machine, so the honest result is the bounded one:

```
scry taint v_x3/w.c --max-rounds 1 --json --allow-errors
# truncated: true, budget.pointsToRounds = 1, scry/budget/points-to-incomplete
# 27 s wall, every reported finding is still a real derivation
```

## What was wrong (this pass)

1. **Every point lookup walked the block list.** `Scry.Fn` derived the statement and
   terminator at a point from `locate` (O(blocks)) and `List.nth` into the block's
   statements (O(pc)); `predsOf` scanned every point and every successor. For a
   straight-line function of n statements that is O(n²) per query, and the analyses
   query every point many times. `Scry.flatten` now builds point → statement/terminator,
   point → succ/pred and block → block/succ/pred tables once (`U64Map`: sorted-list
   model in kernel/interpreter, native hash table when compiled). `nodeStmt`, `nodeTerm`,
   `succs` and `predsOf` are constant-time.
2. **Reaching definitions was one CFG edge per global round.** `rdIn` recomputed every
   point from the previous `ins`, with O(points) lookup per point, so a straight-line
   body needed O(points) rounds of O(points²) work. `Scry.dataDepsFlow` is a block-level
   worklist: a block's statement chain is traversed once, its exit map stored, and only
   successor blocks are reprocessed when the map moves. A straight-line function is one
   block and one pass. The production engine (`fnInfoFlowWithG`) needs only def-use
   edges, so it does not compute the point-level `rd` table or the dominator sets (both
   remain in `fnInfo` for the analysis tests).
3. **Points-to state was an association list.** `ptGet`/`memGet` scanned the whole map,
   `ptPut`/`memAdd` rebuilt it, and `stateEq` re-scanned it per key. `pt` and `mem` are
   now `U64Map`s keyed by a 64-bit hash of the register/location (collisions merge keys,
   which over-approximates a may-analysis rather than losing a fact). `mem` keeps the
   location beside its set so the table and equality checks can read it back.
4. **Flattening happened per round and per call.** `ptStep`/`fnStep` called
   `Scry.flatten` for every function every round; `fnRetVars` flattened the callee for
   every call site. The fixpoint flattens the program once (`ptSolveGB`), `fnStepG` takes
   the flattened `Scry.Fn`, and `fnRetVars` reads the blocks directly.
5. **The fixpoint was Jacobi inside functions and backwards across them.** `fnStep`
   evaluated every statement against the function's input state, and `ptStep` folded
   from the last function to the first, so a call chain propagated one callee per round.
   Statements now read the accumulated state in source order and functions are visited
   source order (`List.foldl`): the same least fixpoint, fewer rounds (old-wizard 29 →
   11, generated grammar 2–3, runtime parser 7 → 5).
6. **Every summary round rebuilt every plan and then re-ran the final pass.**
   `prepareFunc` (def-use graph + memory scan) depends only on `(function, pack,
   points-to)`, so `prepareAll` builds each plan once; the converged summary round's
   results are reused as the final results (the old code threw them away and evaluated
   every function again). The round's deduplicated memory seeds are computed once.
7. **Per-argument taint and def-use queries scanned every row.** `flowHasVar` scanned
   all data edges and `argTainted` scanned all taint rows for every call argument, and
   `growSummaries` re-scanned every result for every callee. `FnInfo.depIdx` indexes
   `(use, var) → def points`, `taintIdxOf` indexes `var → tainted points`, and
   `paramContribFrom` builds one entry per result and makes one pass over the call sites.
   `dedupSeeds` is a hash set instead of a `List.any` + append-to-end loop.
8. **Use-after-free scanned every free for every access.** `freedHit` walked the whole
   free list and ran an O(n²) BFS for each candidate. `freeByLocOf` indexes location →
   free points, the BFS carries a visited set and prepends only the fresh successors,
   and an access only tests frees on its own locations.
9. **Lowering skipped preprocessor/`ERROR` wrappers.** `lowerTU` used the translation
   unit's direct children; generated Futhark C puts its functions under
   `preproc_ifdef`/`linkage_specification` (and tree-sitter's recovery puts the whole
   `extern "C"` block under `ERROR`). `topNodes` descended those nodes, so `--allow-errors`
   recovered the real 1 115-function unit instead of returning “0 functions”. (Superseded
   in the restack by master's `Scry.recoverTop`, see the top.)

## What remains

* **Points-to is still a global round loop.** It is not quadratic in file size, but each
  round visits every function, and a memory-heavy unit needs one round per cross-function
  store → load layer (11 rounds on `old-wizard.c`, 10 on `w.c`). A per-function dirty
  worklist was implemented and measured: because almost every function has a load/store,
  any memory change dirties nearly all of them, and the signature checks made the run
  *slower* (13.5 s → 20 s). The next step is a location-indexed memory reader/writer
  worklist (dirty only the functions that read a changed location), not a coarser
  function-level one.
* **Lowering's `assemble`** still finds each sealed block with `List.find` over the
  done list (O(blocks²) per function); `externalOf` calls `funcIndex` (O(functions)) per
  external callee. Both are small at these sizes but are the next lowering polynomials.
* **`locSort`** is an insertion sort; keys (`locShow`) are now built once, but the sort
  is still O(L²) comparisons (L = 595 on old-wizard, 2 687 on w.c).
* **`w.c` full run** is over 300 s. Use `--max-rounds` (sound, marked) or raise
  `--timeout`; the default 300 s still refuses with exit 124 rather than hanging.

## Limits (the contract)

| option | default | behaviour |
|---|---|---|
| `--timeout SECS` | 300 s | cooperative checks between stages/rounds/functions; `SIGALRM` guard for a single uncheckpointable stage. Exit **124** with a message, no silent hang; `0` disables |
| `--max-nodes N` | 2 000 000 | refuse before lowering with the count and the flag; `0` disables |
| `--max-rounds N` | historical bound | cap points-to **and** summaries; the result is a sound lower bound and is marked `truncated` |
| `--progress` | off | `scry: [stage] …` on stderr, per stage and per ten functions |

The JSON has `"truncated"` and a `"budget"` object (`nodes`, `pointsToRounds`,
`pointsToComplete`, `summaryRounds`, `summaryComplete`, `notes`); a capped run also adds
`scry/budget/points-to-incomplete` / `scry/budget/summaries-incomplete` to the boundary
list and SARIF. Findings that are reported are still real derivations — only recall is
reduced.

## Verification

`grail test` (9 tests) passes, including `tests/scale.wiz`: the node count, the complete
default run, the `--max-nodes` refusal, the marked `--max-rounds 1` result, and a
`--timeout 1` run of the 3.9 MB grammar exiting 124 with the timeout message and no
stdout. `tests/taint.wiz` covers the JSON/SARIF shape and every fixture count/path.
The Lean `scry-taint` cases for reaching definitions, dominators, points-to kinds, the
interprocedural memory summary, certificates, SARIF and the C-lowering pipeline pass
individually; the full Lean suite is left to CI.

(Original pass.) Counts changed only where `topNodes` recovered more of an
error-recovered tree; the restack keeps master's `recoverTop`, so the generated grammar
stays at 2 functions / 12 boundary warnings.
`grail test` (9 tests) passes, including the new `tests/scale.wiz`: on a checkout with
the vendored grammar it checks the node count (1 110 871), that the default run is
complete, that `--max-nodes 1000` refuses cleanly, that `--max-rounds 1` marks a partial
result, and that the CLI's `--timeout 1` exits 124 with the timeout message and no
stdout. When `native/tree-sitter-c/src/parser.c` is absent the test prints
`scale: skip (… absent)` and passes; the timeout sub-check is skipped when
`.grail/bin/scry` has not been built. `tests/taint.wiz` covers the JSON/SARIF fields.

## The lowering regression after the preprocessor path (2026-11-16)

Branch `agent/scry-scale-lower`. After `scry-integrate` (#376), `Scry.Cst.ofStore` goes
through `Scry.Preprocessed.plain` and `Scry.Cst.ofPreprocessed`, so **every** node origin
(`originOf`, i.e. every `emitAt`/`warnAt`) ran `Scry.mapSpan`. That function is O(file)
per span: `posOf` scans the line-start list linearly and takes `String.length` of the
whole original text (twice per span), and `mapSpan` takes `String.drop start` of both the
preprocessed and the original text (a `String` is a `List Char`). Lowering cost was
therefore *(spans lowered) × (file size)*.

Size ladder, cut from the real generated `parser.c` at case and table-entry boundaries
(`ts_lex` with its first *k* `case`s, then a prefix of `ts_small_parse_table` after it).
Time is the `lower` stage alone (`--progress`), peak is `VmHWM` at the end of lowering;
light-slot wall clock, **informational**. Reproduce with
`python3 scripts/lower-ladder.py native/tree-sitter-c/src/parser.c OUT` and
`scripts/lower-probe.sh .grail/bin/scry OUT/<input>.c`:

| input | bytes | before | after | peak (before / after) |
|---|---:|---:|---:|---:|
| `ts_lex` 40 cases | 164 795 | 4.35 s | 0.05 s | 57 / 57 MiB |
| `ts_lex` 80 cases | 178 953 | 12.5 s | | 61 MiB |
| `ts_lex` 160 cases | 195 592 | 23.5 s | | 67 MiB |
| `ts_lex` 324 cases | 229 525 | 46.1 s | 0.17 s | 80 / 77 MiB |
| + 6 000 table lines | 374 580 | 65.3 s | 0.23 s | 121 / 121 MiB |
| + 12 000 table lines | 520 000 | 86.4 s | 0.25 s | 164 / 164 MiB |
| + 25 000 table lines | 839 093 | | 0.41 s | 260 MiB |
| + 52 000 table lines | 1 473 629 | | 0.67 s | 453 MiB |
| full `parser.c` | 3 872 012 | ≈ 9–10 min (extrapolated: +0.137 s/KB) | 1.56 s | 1.19 GiB |

The fix builds `Scry.SpanIndex` once per unit (`Scry.spanIndexOf`: the line tables as
`U64Array`s, the preprocessed and original texts as word arrays, each file's length), and
`Scry.Cst.ofPreprocessed` maps with `Scry.mapSpanAt`: a binary search for the line and a
slice comparison, O(log lines + span). `Scry.mapSpan` stays as the reference definition;
`tests/preproc.wiz` checks that the two agree on every node of the `cc -E` fixture
(including line-fallback origins). The remaining growth with file size at a fixed function
is linear (building the index and the store). `scry taint --json/--sarif/--origin-map`
output is byte-identical on all 105 C fixtures, and `scry project` (with and without
`--taint`, facts included) on the five project corpora.

Note: after lowering, the summary stage of `ts_lex` still takes minutes on master; that
is the per-function analysis that `agent/scry-scale` `eeb1b172` linearised and that had
not landed.

## Restack measurements (2026-11-16, `agent/scry-linearise`)

`eeb1b172` restacked onto master (after #376) and stacked on the span-index fix above.
Light-slot wall clock, `scry taint FILE --json --allow-errors`, whole pipeline;
**informational**, not a `perf-run` measurement. "master" is `d23473da`.

| input | master | linearise only | linearise + span index | peak (stacked) |
|---|---:|---:|---:|---:|
| `tree-sitter/lib/src/parser.c` (17 163 nodes) | 69.4 s | 2.47 s | 0.27 s | 73 MiB |
| `tree-sitter/lib/src/query.c` (34 450 nodes) | 19.2 s | 7.31 s | 0.34 s | 88 MiB |
| ladder `ts_lex` 40 cases | > 180 s (killed in summaries) | | 0.18 s | 58 MiB |
| ladder `ts_lex` 324 cases | | | 2.95 s | 614 MiB |
| generated `tree-sitter-c/src/parser.c` | not measurable under light | | 6.70 s | 1.16 GiB |

The original claim (runtime `parser.c` 25.2 s → 0.12–0.23 s) holds in shape: 69.4 s →
0.27 s on today's master, which has grown more per-node work since. Without the span
index the restacked analysis alone gets the runtime `parser.c` to 2.5 s; the rest was
lowering. Stage profile of the generated grammar (stacked): parse 0.9 s, lower 1.6 s,
points-to 0.5 s, **plans 2.9 s** (the next hot spot: preparing `ts_lex`'s plan), summaries
and origins < 0.1 s.

Restacked onto `ba1834a7`, #438's bounds rules read `rd`/`dom` from the plan's
`Scry.FnInfo`, which the linearised engine builds flow-only (both empty), so they found
nothing (`tests/oob.wiz` failed). `Scry.boundsReaching` now answers reaching definitions
from the def-use index (every query is at a use), and `Scry.boundsOfUnitWith` computes a
function's dominators only when it has a candidate finding (guards only remove findings).

Output changes against the base (`agent/scry-scale-lower` `ba1834a7`: master `5522efd4`
with #438 and the span index; 114 C fixtures under each of the default, `oob` and `uaf`
rule packs, JSON/SARIF/origin map/stderr): origin maps and stderr are identical
everywhere; findings, boundary and memory lists are identical everywhere except one
witness: under the `uaf` pack, `tests/fixtures/uaf-loop.c`'s single use-after-free
(same rule, point, location, free and sink) names the loop-entry `malloc` (point 0) as its
`alloc` node instead of the in-loop one (point 10). Both allocations reach the free; the
witness is the first location of `p`'s points-to set, whose order follows the order the
solver discovers locations in (source order now). That is also the only SARIF change. The JSON differs only in `budget`: `pointsToRounds` drops on 71
files (3 → 2 on 31, 4 → 2 on 29, 4 → 3 on 7, 5 → 2 on 2, 6 → 3, 7 → 4: the source-order
Gauss–Seidel solver needs fewer rounds) and rises on none, and `summaryRounds` rises on
two project files (`math.c`, `taint/io.c`: 2 → 3). (The first restack also raised
`pointsToRounds` 1 → 2 on pointer-free units: the hash-map state compared key counts, so
the empty entries the first round inserts counted as a change. `Scry.locMapEq` and
`Scry.memMapEq` now read a missing key as the empty set, as master's list state did.)
For `math.c` and `io.c` the extra summary round is real: both have a `static helper`
(`return x + 1`) called from an exported function with its tainted parameter; the
restacked analysis records that `helper` then returns a tainted value (round 2 adds it,
round 3 confirms), which the base's summaries never record. No finding depends on it in
the corpus.

Generated grammar on the stack (light probe, informational): 6.1 s, 1.19 GiB peak
(points-to 0.5 s, plans 2.7 s, summaries < 0.1 s); `agent/scry-scale-lower` alone spends
24.5 s in points-to and is still in `ts_lex`'s summaries after 270 s, so the scale test
belongs on this branch. `tests/scale.expected` was stale on master since #376 (it still
said 12 boundary and 2 memory warnings, 2 points-to rounds); the CLI on this branch reports
8 063, 36 and 3 (the lowering's 8 062 boundary warnings already appear on
`agent/scry-scale-lower` and on `a0938b97`), and the expected line says so; the pending
heavy `grail test scale` run confirms it.

## 2026-11-19: the span index re-measured on the train

PR #463 was freshened onto `integration/train7`. Its analysis fix had already landed from
`agent/scry-scale` (`eeb1b172`), so this isolates the span index on the current tree: the
same binary built with `Cst.ofPreprocessed` calling `Scry.mapSpan` ("before") and with the
committed `Scry.mapSpanAt` ("after"). One `heavy` job on one node,
`scripts/perf-scale.sh -n 1 --timeout 300`; **informational**, not a `perf-run` window.

| input | nodes | functions | lower before | lower after | total before | total after | peak |
|---|---:|---:|---:|---:|---:|---:|---:|
| `native/tree-sitter-c/src/parser.c` | 1 110 871 | 2 | 60.68 s | 1.94 s | 66.72 s | 7.99 s | 1.08 GiB |
| `native/tree-sitter/lib/src/parser.c` | 17 163 | 51 | 1.65 s | 0.08 s | 1.95 s | 0.39 s | 64 MiB |
| `native/tree-sitter/lib/src/query.c` | 34 450 | 113 | 4.05 s | 0.14 s | 4.36 s | 0.46 s | 75 MiB |

The lowering half is 31x / 20x / 29x. The original >300 s / 142.6 s figures were the span
mapping *and* the per-point analysis together; the analysis half is `eeb1b172`, already in
the train, so the table above is the span index's own contribution.
