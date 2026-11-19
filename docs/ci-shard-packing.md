# Cap-aware shard packing (measured 2026-11-19)

CI's test matrix is one job per shard entry (`.github/test-shards.json`), and the
organization's Actions plan allows **20 concurrent jobs** in all. With the current
expansion that is 32 test jobs, so on paper 12 jobs start in a second wave. This note
asks whether repacking the cases into **at most 20 jobs** shortens the wall clock in one
wave, and answers: **not by 5 minutes**, so nothing was changed.

## How the numbers were made

* Case table: three completed `test-timings` artifacts of the same 29-shard shape
  (runs 44347818324, 44347829914, 44355377993 — the last at `4ad29792`, the master
  merge that `ci-critical-path` is based on). A case's own time is its median over the
  runs, with the builds it did subtracted, as `scripts/ci.py baseline` does. The
  `selfhost-libdiff` cases are the four 552 s sweep parts and three checks of
  `.github/test-timings.json` at `ci-critical-path` (that branch has not had a CI run of
  its own; the 552 s is its estimate, not a measurement).
* Costs: `scripts/ci.py`'s own `estimate`, `part_cost` and `partition`. `part_cost` is a
  part's case seconds plus every shared program it builds (`checker` 340 s, `compiler`
  362 s, `parser` 17 s, `tower-wiz` 35 s here).
* Wave: all shards released when `build` ends, longest first (the order
  `scripts/ci.py matrix` emits), a fixed 20 slots, so the makespan is the last
  completion. Add the `build` job separately: its median is 17 min (3.6 min on a Cachix
  hit, 49.6 min cold in run 44355377993).
* Current expansion at `ci-critical-path` (`0ded4e45`): **32 jobs**, longest first.

## Current expected makespan

The 8 `library` parts are the longest at **28.63 min** each, so with 20 slots the test
makespan is **28.63 min**, and **45.6 min** with the median build. The second wave does
not extend it: the 12 late jobs are the short tail (six `selfhost` parts at ~9 min, then
`core` 7.9, `hdl-*` 3–4, `prop` 1.7, `parse-diff` 1.6, `audit` 1.2), and the last of them
starts at about 17 min and finishes at about 18, before the library parts do.

That number is the model, not this commit's run. With each run's own case times in turn,
the same expansion gives 26.60, 28.44 and 33.46 min; the three differ by cache state and
machine load. Treat it as 28.6 ± 4 min.

## The three packings

| packing | jobs | longest job | test makespan | win |
|---|---:|---:|---:|---:|
| current | 32 | 28.63 | 28.63 | — |
| filter-preserving | 20 or 21 | 28.10 | 28.10 | 0.5 min |
| aggressive merges | 20 | 25.26 | 25.26 | 3.4 min |
| unconstrained floor | 20 | 22.34 | 22.34 | 6.3 min |

**Filter-preserving** means each bin stays inside one shard's path-filter/runner class:
`library` absorbs `backends` (both `"jobs": 4`, no `inputs`), `scaling` absorbs `prop`
and `audit` (no `inputs`, no `jobs`), and the two `hdl-*` shards merge. Split counts:
`selfhost` 3, `library` 9, `scaling` 2, `selfhost-libdiff` 2. The longest bin is a
`selfhost` part at 28.10 min; nine `library` parts sit at 27.19. That is 21 jobs, and
the one that waits (`selfhost-parse-diff`, 1.6 min) runs at 7.4–9.0 min, before the
library parts finish, so the makespan is still 28.10. Merging `grail-selfhost` into
`semantics` (its inputs are a subset) makes it exactly 20 jobs with the same makespan;
that merge broadens `grail-selfhost` to any `lib/*` change, so it buys a job, not time.
The 0.5 min is inside the model's uncertainty.

**Aggressive merges** also puts `core` into the `library` family and makes one bin of
`hdl-verified` + `hdl-uart-temporal` + `selfhost-parse-diff`, and one of
`grail-selfhost` + `semantics`. Split counts: `library` 10, `selfhost` 4, `scaling` 2,
`selfhost-libdiff` 2. This is the best a shard file can do while every job still runs
one shard's kind of work:

| job | cases | minutes |
|---|---:|---:|
| library-1 … library-10 | 175–187 each | 25.26 each |
| selfhost-libdiff-1, -2 | 3, 4 | 24.44 each |
| grail-selfhost + semantics | 8 | 21.53 |
| selfhost-1 … selfhost-4 | 7–136 | 21.03–21.09 |
| scaling-1, scaling-2 | 36, 42 | 20.90 each |
| hdl-verified + hdl-uart-temporal + selfhost-parse-diff | 4 | 9.01 |

Every case is in exactly one job (2151 cases in all). The longest job is 1.02x the
median, so it also satisfies the 1.5x balance rule. But it broadens three filters:
`core` now runs on any code change (it had `inputs`), `grail-selfhost` now runs on
any `lib/*` change (it had four lib files), and `selfhost-parse-diff` now runs on any
code change (it sits in the `hdl` bin, which has no `inputs`). That is a throughput cost
on pull requests that the makespan number does not count.

**Unconstrained floor**: a case-level LPT/local-search packing that may mix anything
reaches 22.34 min in 20 bins. It is not deployable: `library` has no `inputs`, so any
bin containing a library case must also have no `inputs` (otherwise that case would stop
running on unrelated changes), and such a bin runs on every code change. A packed bin
that mixes library cases with `selfhost` cases therefore makes the whole selfhost shard
— 84 min of work — run on every pull request, including one that touches only `scry/`.
That is a large increase in PR work to save 6 min on a full run.

## What the runs actually show

The 20-slot pool is shared with the other workflows (`golden diff`, `scry goldens`,
`release`, …), and the measured runs never came close to using 20 slots on their own:
run 44347829914 peaked at **17** of this run's jobs at once, run 44355377993 at **14**.
The delays are other workflows' jobs, not this matrix's 29 entries. In the second run,
jobs started when only 3–8 of this run's own jobs were running. A 20-entry shard file
does not shorten that queue; it only stops this run from adding to it.

So the model's 0.5–3.4 min is the part packing controls, and the measured data gives no
reason to expect more. The note `ci-runner-plans-2026-11-18.md` reaches the same
conclusion from the other side: the 16.5 min median slack is cap contention, and the
fix is a higher cap (free via Support, or Team at 60), not fewer jobs.

## Decision

No `--max-parallel` mode and no new shard file: the deployable win is 0.5 min, and even
the most aggressive merge is 3.4 min, under the 5-minute bar. The unconstrained 6.3 min
requires every PR to run the full suite.

If this is revisited, the pieces to change are: `expanded` must de-duplicate the cases
of a merged shard before partitioning (the current `library` select list already picks
eight cases twice; merging two shards makes `partition` put some of them in different
parts), and a merged shard needs explicit `inputs` equal to the union of its members'
(no member may rely on "no `inputs`", or the bin runs everywhere).

## Applied (2026-11-19, `integration/train6`)

The **filter-preserving** packing is now in `.github/test-shards.json`, with the three
merges that cost no extra pull-request work because the receiving shard already runs on
every change (`library` is the default shard; `hdl` and `semantics` have no `inputs`):

| change | before | after |
|---|---:|---:|
| `selfhost` parts | 8 | 3 |
| `selfhost-libdiff` parts | 4 | 2 |
| `library` parts | 8 | 10 |
| `scaling` parts | 3 | 2 |
| `backends` | its own shard | into `library` (same `jobs`) |
| `prop`, `audit` | own shards | into `scaling` |
| `hdl-verified` + `hdl-uart-temporal` | 2 | one `hdl` |
| `core`, `examples` | own shards | into `library` (it is `default: true`) |
| `grail-selfhost` | own shard | into `semantics` (its `inputs` are a subset) |
| `selfhost-parse-diff` | own shard | into `hdl` |

Result: **19 test jobs** (from 35), one wave under the 20-job cap, generated by
`scripts/ci.py matrix` and still longest-first. The cost is one filter: `hdl` now has no
`inputs`, so it runs on any change, as `library` already did. That is deliberate here —
CI runs on `integration/*` only, so a broader filter costs no pull-request throughput,
and the single wave is what makes a 19-job train feasible at the cap.

`scripts/ci.py check` verifies the selectors and that every case is covered; run it with
the built `tests` binary when this file changes.
