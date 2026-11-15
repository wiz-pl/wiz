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
