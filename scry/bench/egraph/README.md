# E-graph engine benchmark

This is the committed source of the e-graph speed claim in `CHANGELOG.md` and
`wiz-notes/audit-scry.md` finding 3. It pins the two revisions, the harness, the
derived counts and the measured JSON/TSV. There are no numbers in the documentation
without a matching artifact here.

## What is compared

Both binaries are built from `examples/scry-egraph-bench.wiz` by the same `wiz`
compiler; only the `Scry.Egraph` source differs:

| | revision | `Scry.Egraph` |
|---|---|---|
| old | `9de503419^` | the reference engine: the hash cons is a flat association list (`etableFindL`), and `rebuildNodes` appends one node at a time |
| new | `HEAD` | the one engine: `etable` is a `U64Map` from an e-node hash to a bucket, and `rebuildNodes` conses onto a fresh list |

`9de503419` is the collapse commit; `scry/src/Scry/Egraph.wiz` on `HEAD` is
byte-identical to that commit's `lib/Scry/Egraph.wiz`, so the "new" column describes
the current engine. `add` and `rebuild` are the two operations audit finding 3 names.

## Inputs and cases

The harness takes a size `N` and builds a deterministic graph; it reports counts and
its own `Clock.monotonic` milliseconds. The driver checks the counts before timing:

| mode | graph | derived counts |
|---|---|---|
| `add N` | N distinct leaf e-nodes in an empty graph | `nodes = N`, `classes = N` |
| `rebuild N` | N leaves and N unary `f(leaf)` nodes, every leaf unioned with leaf 0, then one `rebuild` | `nodes = 2`, `classes = 1` |
| `merge N` | the same graph, then one `mergeFacts` over the N−1 equality rows | `nodes = 2`, `classes = 1` |

`add` isolates the hash cons. `rebuild` isolates congruence closure and the node-table
rewrite: the first pass still visits all 2N nodes, and the old engine appended each one
to the table. `merge` is the Datalog stratum's operation (`Plan.mergeTuples`):
`mergeRows` unions every row and then one rebuild closes the graph.

## Reproduce

```sh
# a compile, so this goes through heavy (AGENTS.md)
heavy --sshfs -- python3 scry/bench/egraph/run.py --wiz .lake/build/bin/wiz
python3 scry/bench/egraph/run.py --check    # build + verify the derived counts only
```

The driver creates throwaway `git worktree`s at the two revisions under `/tmp`, copies
the harness, builds both, warms each (engine, case) once, then measures `--rounds`
(3 by default) interleaved rounds. It never modifies the checkout. Requirements: the
tree's own `wiz` (`--wiz`), `git`, and a `wiz build` that can link C.

The harness prints `add_ms` / `rebuild_ms` / `merge_ms`; the driver reports the median
of the runs and the wall time. **The times are informational** — measured on a shared
machine, not a `perf-run` window — and the *scaling* (the ratio between sizes) is the
claim, not any absolute millisecond.

## Files

* `results.json` — pinned revisions, host, per-round records and medians.
* `results.tsv` — the median table in text form.
* `../../examples/scry-egraph-bench.wiz` — the harness (a `-- test: skip` example).
