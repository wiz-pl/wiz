# scry: the large-file path (2026-11-15)

Status: profile and fix, no analysis change. Branch `agent/scry-scale`, based on
`agent/scry-points-to` `bb1a6294`. Numbers are wall time on this 32-core Linux machine,
with the branch's own `grail`/`scry`; they are **informational**, not a `perf-run`
measurement (the machine is shared). "warm" means the source and binary were already in
the page cache; "cold" is the first run after a build.

## The pathological input

`native/tree-sitter-c/src/parser.c` is the generated tree-sitter-c grammar: 3 872 012
bytes, 1 110 871 CST nodes, 1 110 870 edges, 2 functions, 12 lowering-boundary warnings,
2 memory warnings, 0 findings, 31 `ERROR`/`MISSING` nodes. On the base commit it did not
finish under `timeout 300 scry taint … --json --allow-errors` (exit 124, no JSON).

Reproduce and bound it:

```sh
cd scry
grail build
./.grail/bin/scry taint native/tree-sitter-c/src/parser.c --json --allow-errors --progress
./.grail/bin/scry taint native/tree-sitter-c/src/parser.c --json --allow-errors \
    --max-nodes 200000 --timeout 60 --max-rounds 8
grail test scale        # skips when the vendored grammar is absent
```

## Stage profile (3.9 MB parser.c, warm)

| stage | cumulative | delta | detail |
|---|---:|---:|---|
| `read` | 0.42 s | 0.42 s | 3 872 012 bytes, 118 873 lines |
| `parse` | 1.65 s | 1.23 s | tree-sitter → shim columns, 1 110 871 nodes |
| `store` | 1.72 s | 0.07 s | copy columns into `Scry.CstStore` |
| `lower` | 2.23 s | 0.51 s | 2 functions, 12 boundary warnings |
| `points-to` | 2.23 s | < 0.01 s | 4 vars, 1 location, 2 rounds |
| `summaries` | 2.23 s | < 0.01 s | 1 round, converged |
| `origins` | 2.23 s | < 0.01 s | 8 entries |

Warm wall time **≈ 1.2–2.2 s** (page-cache and machine load dependent; the table is a
2.2 s run); the first (cold) run was **≈ 6–7.5 s**. Peak RSS **654 MiB**
(`/proc/<pid>/status` `VmHWM`), dominated by the 1.1 M-node columns (shim + copied Wiz
arrays) and the source text; the 17 k- and 34 k-node files below peak at 34 MiB and
71 MiB.

Before: `timeout 60` gave exit 124 with no JSON; the real-corpus report records exit 124
at 300 s.

## Function-heavy files

The generated grammar is mostly tables. The tree-sitter runtime files are the opposite:
many functions with large bodies. On the base commit:

| input | nodes | before | after (warm / cold) | peak RSS |
|---|---:|---:|---:|---:|
| `tree-sitter/lib/src/parser.c` | 17 163 | 117.7 s | 50.3 s / 56.4 s | 34 MiB |
| `tree-sitter/lib/src/query.c` | 34 450 | 180.7 s | 15.6 s / 35–38 s | 71 MiB |
| generated tree-sitter-c `parser.c` | 1 110 871 | timeout (300 s) | 1.2–2.2 s / 6–7.5 s | 654 MiB |

`--progress` on the runtime `parser.c` localises the remaining cost: lowering is ~0.1 s
(warm), points-to 1.9 s, and the summary fixpoint 29.5 s + the final evaluation 20.7 s.
One generated function, `ts_parser__advance`, accounts for ~21 s **per pass** (two passes
exist: summary and final results). `query.c` converges in one summary round; its points-to
takes 2.4 s over 113 functions. A single very large function's rule evaluation is the
remaining hot spot; it is not quadratic in file size but it is not cheap, and that is why
`--timeout` (or a smaller `--max-nodes`) is the escape hatch.

Exact counts for the runtime files are unchanged from the real-corpus report:
`query.c` 14 parse errors, 1 473 boundary, 9 memory; `parser.c` 1 parse error, 1 271
boundary, 8 memory; 0 findings in both.

## What was wrong

1. **CST child lookup copied the whole column.** `Scry.CstStore.childArcs` did
   `U32Array.toList s.children` + `List.drop lo` + `List.take k` for **every** node.
   On 1.1 M nodes that is O(nodes) per child arc, i.e. O(nodes²) for the lowering walk.
   It now reads `children`/`childField` by index (`arcsFrom`, O(children)).
2. **Token text was sliced with `String.drop`.** `String` is a `List Char` in this
   runtime, so `Scry.Cst.textOf` walked from byte 0 for every identifier. `Cst` now
   keeps one materialised `U32Array` of the source and `textOf` slices that
   (`U32Array.slice` + `toList`), O(span). `U32Array` rather than `Bytes` is deliberate:
   it has a pure list model, so interpreted lowering (the Lean test groups) keeps
   working, while compiled code uses the native array. The source `String` is still
   retained for `Scry.spanText`/the lowering tests (the CLI held it anyway).
3. **The origin map rescanned the file per point.** `lineColAt` ran over the source for
   every program point and every boundary warning. `Scry.lineStartsOf` now builds the
   line-start table once and `lineColFrom` binary-searches it (O(points + lines)).
4. **The edge-label relabel materialised a full column as a list**
   (`Native.toCstStore`): now `U32Array.foldl` + `push`.
5. **The fixpoints had no usable bound.** Points-to and the summary loop used
   `2 × program points + 8` rounds, which is finite but astronomically large, and there
   was no way to stop or report an incomplete answer. Both now take `--max-rounds`,
   return `rounds`/`complete`, and a capped run is explicitly `truncated`.

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

Observed contract paths:

```
$ scry taint big.c --max-nodes 1000
scry: big.c: 1110871 CST nodes exceeds --max-nodes 1000; refusing to lower (raise --max-nodes explicitly)
# exit 1, no JSON

$ scry taint big.c --timeout 2
scry: [stage] store elapsed=27ms 17163 nodes, 17162 edges
scry: timeout after 2 s (--timeout); no analysis result was produced
scry: raise --timeout, or bound the work with --max-nodes/--max-rounds
# exit 124

$ scry taint big.c --max-rounds 1 --json
… "truncated":true, "budget":{"pointsToRounds":1,"pointsToComplete":false,
  "notes":[{"rule":"scry/budget/points-to-incomplete", …}]} …
```

## Verification

`grail test` (9 tests) passes, including the new `tests/scale.wiz`: on a checkout with
the vendored grammar it checks the node count (1 110 871), that the default run is
complete, that `--max-nodes 1000` refuses cleanly, that `--max-rounds 1` marks a partial
result, and that the CLI's `--timeout 1` exits 124 with the timeout message and no
stdout. When `native/tree-sitter-c/src/parser.c` is absent the test prints
`scale: skip (… absent)` and passes; the timeout sub-check is skipped when
`.grail/bin/scry` has not been built. `tests/taint.wiz` covers the JSON/SARIF fields.

## The 2026-11-17 scale profile

On the base commit the generated tree-sitter-c grammar did **not** finish under the
runner's 300 s cap. `--progress` reached `store` (1 110 871 nodes, ~1.5 s) and then spent
the rest of the run in `lower`; the 17 k-node runtime `parser.c` took 142.6 s and the
34 k-node `query.c` 49.9 s. Two independent **superlinear** passes were responsible.
Both are fixed on this branch.

### What was wrong

1. **Every node origin was mapped in O(file).** Since `Cst.ofStore` goes through
   `Cst.ofPreprocessed`, each `originOf`/`emitAt`/`warnAt` called `Scry.mapSpan`, which
   `String.drop`s from the start of the preprocessed and original texts (a `String` is a
   `List Char` here) and scans the line-start list. Lowering cost was
   *(spans lowered) × (file size)*. `Scry.spanIndexOf` now builds the line tables and the
   word arrays once, and `Scry.mapSpanAt` binary-searches the line and compares slices
   (O(log lines + span)). `Scry.mapSpan` stays as the reference definition;
   `tests/preproc.wiz` checks the two agree on every node of the `cc -E` fixture,
   including the line-fallback branch.
2. **Per-function analysis was point-at-a-time.** `Scry.fnInfoWith` materialised
   reaching-definition and dominator sets with one round per point; `predsOf` scanned
   every point and `lookupSet` scanned an association list, so a large `ts_lex` cost
   O(points³). The production taint path now uses `Scry.fnInfoFlowWith`: a block-level
   reaching-definitions worklist over `Scry.Fn`'s `U64Map` point/block indexes, with the
   same def-use edges and no point-level `rd`/`dom` table. `Scry.fnInfo` keeps the
   point-level tables for the analysis tests and the old `Scry.Taint` prototype, and
   `Bounds` builds them per function only when the opt-in out-of-bounds rules are in the
   pack, so the default pack and this corpus never pay for them.

### Phase table (warm, informational)

`scry taint FILE --json --allow-errors --progress`; wall and `ru_maxrss` come from
`wait4`, stage deltas from `--progress`, and peak RSS is `VmHWM` sampled when the stage
line arrived. A stage absent from a run is `–`. The `before` rows are the pre-fix binary
on this checkout; the base generated-grammar run was bounded at 240 s, timed out in
`lower` (exit 124), and would not have finished at 300 s either.

| input | run | read | parse | store | rules | lower | points-to | summaries | results/analyse | origins | wall | peak |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| generated grammar (1.1 M) | before | 0.49 | 0.96 | 0.06 | – | >239* | – | – | – | – | 240.7 | 988 MiB |
| generated grammar (1.1 M) | after | 0.29 | 0.69 | 0.05 | 0.09 | 1.97 | 20.51 | 3.82 | 3.07 | 0.03 | 31.7 | 1 058 MiB |
| runtime `parser.c` (17 k) | before | 0.01 | 0.02 | 0.00 | – | 4.59 | 1.22 | 94.91 | 41.68 | 0.01 | 142.6 | 60 MiB |
| runtime `parser.c` (17 k) | after | 0.01 | 0.01 | 0.00 | 0.00 | 0.07 | 1.03 | 0.32 | 0.08 | 0.00 | 1.6 | 60 MiB |
| runtime `query.c` (34 k) | before | 0.03 | 0.03 | 0.00 | – | 15.50 | 2.11 | 16.39 | 7.43 | 0.79 | 49.9 | 68 MiB |
| runtime `query.c` (34 k) | after | 0.02 | 0.03 | 0.00 | 0.00 | 0.14 | 1.56 | 0.41 | 0.05 | 0.00 | 2.3 | 72 MiB |

`wall` includes JSON rendering, which is not a stage: ~1 s for the grammar and ~8 s for
the pre-fix `query.c` run (1 702 boundary warnings). `summaries` on this branch also
contains the per-function plan construction; the reference engine that reports a separate
`plans` stage measured 5.6 s for the grammar and 0.02 s for `query.c`. The numbers are
informational and move with machine load: a later run of the same grammar binary during
the machine's heavy baseline load measured 84.4 s (points-to 46.9 s, summaries 11.4 s,
analyse 9.9 s, peak 845 MiB). The safe-corpus counts are unaffected.

### Hot spots

| # | hot spot | evidence | class | fixed |
|---|---|---|---|---|
| 1 | origin mapping (`mapSpan` per emitted node) | `lower` 15.50 s on `query.c`, >239 s (timeout) on the grammar; 0.14 s / 1.97 s after | algorithmic, O(spans × file) | yes |
| 2 | per-function reaching definitions + dominators | `summaries`+`analyse` 136.6 s on runtime `parser.c`, 23.8 s on `query.c`; 0.40 s / 0.46 s after | algorithmic, O(points³) | yes |
| 3 | points-to closure | 20.51 s on the grammar, 1.56 s on `query.c`, 1.03 s on runtime `parser.c`; `PtState` `pt`/`mem` are association lists and `fnStep` re-flattens each function per round | algorithmic + list constant factor | no |
| 4 | CST store and view | `store` is only 0.05–0.06 s, but the 1.1 M columns and the two `SpanIndex` word arrays peak at ~1.0 GiB; `CstStore.arcsFrom` is O(children), so no whole-column traversal remains | linear time, constant-factor memory | no |
| 5 | Datalog joins and delta loop | after the fixes `summaries` is 3.8 s on the grammar (mostly plan construction) and 0.3–0.4 s on the runtime files; `TupleRel.candidates` picks the shortest bound column, but an unbound first atom (`flow` in `rtRuleProp`) scans the relation and `deltaRows` filters the delta linearly | algorithmic in theory, not hit by this corpus | no |

`Scry.Egraph` is imported only by `examples/scry-egraph-*.wiz` and the `scry-egraph`
tests; no lowering, points-to or taint pass calls it. Its `rebuild` is O(nodes) after a
batch of unions, but it is not on the scale path, so it is not a hot spot here. The
`Lower` passes themselves (`scanTypes`, `scanSyms`, `lowerFuncs`) are linear in the
top-level/function nodes they visit; the superlinear cost was the origin mapping, not the
pass structure.

### Reproducing the table

`scripts/perf-scale.sh` runs the three vendored inputs through `scry taint --progress`
and prints one TSV row per stage (delta, `VmHWM`) plus a `TOTAL` row. It needs bash,
python3 (only for `fork`/`wait4`; no `time` or `ps`), a built `.grail/bin/scry`, and the
vendored tree-sitter sources. `-n N` reports the median of N runs, `--timeout` keeps a
capped run as `exit 124`, and `--bench` also runs the safe corpus:

```sh
cd scry
scripts/perf-scale.sh
scripts/perf-scale.sh -n 3 --bench
```

The safe corpus stays at TP 32 / FP 1 / TN 17 / FN 0 (`scry bench --no-timing
--fail-on-regression`). The remaining cost is points-to; the fix is to replace the
`PtState` association lists with `U64Map`s and flatten/plan each function once, not a
rule change, so it is left out of this measurement-only change.
