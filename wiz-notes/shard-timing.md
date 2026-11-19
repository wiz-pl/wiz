# CI shard timing — `integration/train6` (PR #538)

Run: [44583848685](https://github.com/wiz-pl/wiz/actions/runs/44583848685) (CI #1444, attempt 1),
head `1b8e5d11`, event `pull_request`, created 2026-11-19 18:04:09Z, completed
20:16:54Z, conclusion **failure**. This is the latest completed matrix on #538. The
five earlier train6 runs (1439–1443) never reached the test matrix: their `build` job
failed or was cancelled. They are not matrix measurements.

Numbers are from the jobs API (`startedAt`/`completedAt`), the job logs, and the
`test-log-*` artifacts (per-case JSONL). Group times are the test driver's own
`(group: X s; cases Y s)` lines. `scripts/ci.py plan` in the build log supplied the
estimates the packing was made from. The run is red (32 failed cases over the 19
shards; `wasm modules` and `trust ledger` also failed), so these are the wall times
of a red run.

The API has no queue timestamp, no runner size and no scheduling reason. "Wait" below
is `startedAt - run created_at`; "after build" is `startedAt - build completedAt`.
Everything else is measured.

## Per-job wall time

All times UTC, from the run's jobs API.

| job | result | start | end | wall min | wait from run start min | wait after build min |
|---|---|---:|---:|---:|---:|---:|
| changes | success | 18:04:15 | 18:04:22 | 0.1 | 0.1 | — |
| docs style | success | 18:04:13 | 18:04:24 | 0.2 | 0.1 | — |
| name collisions (reachable) | success | 18:04:13 | 18:04:27 | 0.2 | 0.1 | — |
| prelude drift | success | 18:04:26 | 18:04:40 | 0.2 | 0.3 | — |
| docs examples | skipped | — | — | — | — | — |
| bootstrap fixpoint | skipped | — | — | — | — | — |
| **build** | **success** | **18:04:25** | **18:52:19** | **47.9** | **0.3** | — |
| test (selfhost-1) | success | 18:52:22 | 20:16:43 | **84.3** | 48.2 | 0.1 |
| test (selfhost-2) | failure | 18:52:22 | 19:50:50 | 58.5 | 48.2 | 0.1 |
| test (selfhost-3) | success | 18:52:22 | 19:15:20 | 23.0 | 48.2 | 0.1 |
| test (selfhost-libdiff-1) | success | 18:52:22 | 19:15:13 | 22.9 | 48.2 | 0.1 |
| test (selfhost-libdiff-2) | success | 18:52:22 | 19:29:27 | 37.1 | 48.2 | 0.1 |
| test (library-1) | failure | 18:52:22 | 19:30:07 | 37.8 | 48.2 | 0.1 |
| test (library-2) | failure | 18:52:22 | 19:36:28 | 44.1 | 48.2 | 0.1 |
| test (library-3) | failure | 19:04:40 | 19:26:47 | 22.1 | **60.5** | **12.3** |
| test (library-4) | failure | 18:52:22 | 19:20:05 | 27.7 | 48.2 | 0.1 |
| test (library-5) | failure | 18:52:22 | 19:17:29 | 25.1 | 48.2 | 0.1 |
| test (library-6) | failure | 19:02:13 | 19:33:52 | 31.6 | **58.1** | **9.9** |
| test (library-7) | failure | 18:52:22 | 19:11:25 | 19.1 | 48.2 | 0.1 |
| test (library-8) | failure | 18:52:22 | 19:21:37 | 29.2 | 48.2 | 0.1 |
| test (library-9) | failure | 18:52:22 | 19:11:01 | 18.6 | 48.2 | 0.1 |
| test (library-10) | failure | 18:52:23 | 19:21:26 | 29.1 | 48.2 | 0.1 |
| test (scaling-1) | failure | 18:52:23 | 19:11:57 | 19.6 | 48.2 | 0.1 |
| test (scaling-2) | failure | 18:52:22 | 19:05:15 | 12.9 | 48.2 | 0.1 |
| test (hdl) | success | 18:52:23 | 19:02:11 | 9.8 | 48.2 | 0.1 |
| test (semantics) | success | 18:52:22 | 19:16:22 | 24.0 | 48.2 | 0.1 |
| wasm modules | failure | 18:52:22 | 19:27:59 | 35.6 | 48.2 | 0.1 |
| trust ledger | failure | 18:52:22 | 19:33:03 | 40.7 | 48.2 | 0.1 |
| docs (wiz doc --lib + site) | skipped | — | — | — | — | — |
| web | skipped | — | — | — | — | — |
| deploy docs to Pages | skipped | — | — | — | — | — |
| CI result | failure | 20:16:46 | 20:16:53 | 0.1 | 132.6 | 84.5 |

Build breakdown (from the build log, not the API):

| build phase | wall min |
|---|---:|
| checkout + setup + Cachix config | 0.5 |
| `nix build .#wiz .#tests` | 42.6 |
| — `wiz-unwrapped` (558 Lean jobs) | 29.8 |
| — `wiz` wrapper | 12.7 |
| PR-cache push check | 0.1 |
| check-shards + matrix plan | 0.6 |
| runtime / index / package / reproducibility / docs-examples checks | 4.1 |

## Makespan

| span | minutes |
|---|---:|
| first test start (18:52:22) → last test end (20:16:43, selfhost-1) | **84.3** |
| build (18:04:25 → 18:52:19) | 47.9 |
| build start → last test end | **132.3** |
| run created → CI result end | 132.7 |

The critical path is `build` (47.9) + `selfhost-1` (84.3). The next longest
build-dependent jobs are `selfhost-2` 58.5, `library-2` 44.1 and `trust ledger` 40.7;
none is within 40 minutes of `selfhost-1`.

Ancestor comparison (not like-for-like: different commit, green vs red): master run
1437 at `18160a94` ran the pre-packing 32-job matrix, its `build` substituted from
`badlydrawnwizards` in **6.3 min**, its test makespan was **50.1 min** (first test
09:36:38 → last 10:26:42) and the run took 70.9 min. The 19-job train6 matrix has a
test makespan 34.2 min longer; `selfhost-1` alone accounts for that difference.

## Queueing and waves

- The run has 32 jobs: 19 test shards, `build`, 2 non-test post-build jobs
  (`wasm modules`, `trust ledger`), 4 pre-build checks, 2 skipped pre-build jobs,
  3 skipped docs jobs and `CI result`. The post-build fanout is therefore **21 jobs**,
  not 19.
- A 20-job cap cannot start 21. **One job must queue even with no other workflow
  running.** Measured, **two** test jobs queued because `scry goldens (grail test)`
  (run 44583848857, 18:04:30 → 19:04:38, cancelled) held the 20th slot:
  - 18:52:22–23: 17 test jobs + `wasm modules` + `trust ledger` + `scry goldens`
    = **20 running** (max org concurrency, 18:52:23).
  - 19:02:11 `hdl` ends → 19:02:13 `library-6` starts (+9.9 min).
  - 19:04:38 `scry goldens` ends → 19:04:40 `library-3` starts (+12.3 min).
  - Max of this run's own jobs: **19** (19:04:40–19:05:15).
- Wait from run start is 48.2 min for every build-dependent job: that is the build,
  not the scheduler. The two real scheduler waits are `library-6` (+9.9 after build)
  and `library-3` (+12.3 after build).
- The two waits do not gate: `library-6` ends 19:33:52 and `library-3` 19:26:47,
  while `selfhost-1` ends 20:16:43. Removing both waits changes the makespan by
  **0 minutes**.
- The "19 test jobs, one wave" prediction is **not** the shape that ran: wave 0 is
  17 test jobs + 2 non-test jobs (19 of the run's jobs), then two second-wave test
  jobs at +10 and +12 min. Against a 20-job cap the run is one job over before any
  other workflow is counted.

## Cache

Two caches are configured: trusted `badlydrawnwizards`, PR `wiz-pl`.

- **All 19 shards are hits.** Every test log has
  `copying path '/nix/store/…-wiz-0.1.0' from 'https://wiz-pl.cachix.org'` and the
  same for `…-wiz-tests-0.1.0`; no test log has a `building '/nix/store/…-wiz-…drv'`
  line. Setup + substitution to the first test line is 35–40 s.
- **The `build` job is the miss.** Its setup configures only `badlydrawnwizards`
  (no `cachix-pr-name`), so it rebuilt `wiz-unwrapped` (558 jobs, 29.8 min) and
  `wiz` (12.7 min): 42.6 min of `nix build` inside a 47.9-min job.
- The explicit PR-cache push step at 18:47:40 printed
  **`Nothing to push - all store paths are already on Cachix.`** The exact
  `wiz`/`tests` paths were already in `wiz-pl`; the build job simply cannot read
  that cache.
- `Pushing is disabled` / `skipPush is enabled` is the Cachix action's post-step for
  the read-only trusted cache (and, in the shards, for both caches). It is **not** a
  failed PR push. The PR push step ran and found the paths present.
- For comparison, master run 1437 (pre-packing, head `18160a94`) substituted its
  build from `badlydrawnwizards` and spent **6.3 min** in `build`.

**Verdict:** the matrix did **not** rebuild paths it should have substituted; the
shards are 19/19 cache hits. The `build` job rebuilt paths that were already in the
PR cache because it never adds the PR cache as a substituter. That is a workflow
cache-read defect worth ~42.6 min, separate from the shard file.

## Where the time went

Aggregated group elapsed over all 19 test jobs, from the logs. "Elapsed" is the
group's wall time in each job summed over jobs; it is not a serial-time model, but it
shows which groups carry the work.

| group | elapsed min | jobs |
|---|---:|---:|
| selfhost | 109.0 | 2 |
| selfhost-libdiff | 58.4 | 2 |
| scry-csharp | 42.7 | 10 |
| scry-taint | 32.8 | 10 |
| scaling | 28.7 | 2 |
| selfhost-host | 27.9 | 2 |
| scry-prover | 15.1 | 8 |
| examples | 14.9 | 3 |
| grail-selfhost | 12.5 | 1 |
| native | 10.9 | 9 |
| semantics | 10.6 | 1 |
| audit-kernels | 10.5 | 2 |

Inside the critical jobs:

| job | wall min | groups (min) |
|---|---:|---|
| selfhost-1 | 84.3 | selfhost 74.8, selfhost-cli-diff 8.1, selfhost-cli 0.6, selfhost-macro 0.1 |
| selfhost-2 | 58.5 | selfhost 34.2, selfhost-host 15.9, audit-kernels 7.3, selfhost-macro 0.4 |
| selfhost-3 | 23.0 | selfhost-host 12.0, prop-kernels 5.1, audit-kernels 3.2, false-fuzz 2.1 |
| library-2 | 44.1 | examples 11.0, scry-taint 5.5, scry-csharp 5.2, scry-prover 2.2 |

`selfhost-1` is 83.7 min of test run plus 0.6 min of setup; 74.8 of those minutes are
the `selfhost` group alone. No other single group in any job exceeds 11 min.

## Did the rebalanced packing hit its predicted shape?

- **Job count: yes.** `scripts/ci.py check-shards` in the build log: 136 groups,
  2360 cases, each in exactly one of **19 shards**.
- **Single wave: no.** 17 test jobs start at t0, 2 at +9.9/+12.3 min; and the run
  has 21 post-build jobs, so one would queue even without the foreign
  `scry goldens` job.
- **Balance: no.** Test-job wall times have median 25.1 min and maximum 84.3 min
  (`selfhost-1`) = **3.36×**, above the 1.5× rule. The plan's longest estimate was
  `selfhost-1` at 3267 s (54.5 min); it measured 5023 s (83.7 min).

Plan estimate (build log) vs measured wall:

| shard | plan estimate min | measured min |
|---|---:|---|
| selfhost-1 | 54.5 | 83.7 |
| selfhost-2 | 10.6 | 57.9 |
| selfhost-3 | 10.6 | 22.4 |
| selfhost-libdiff-1 | 42.7 | 22.9 |
| selfhost-libdiff-2 | 42.7 | 37.1 |
| library-1…10 | 24.5 each | 18.6–44.1 |
| scaling-1, -2 | 12.5 each | 19.6, 12.9 |

**Cause.** `partition` keeps every case that uses the same shared program in one
unit, so the `selfhost` cases that use the compiler are one indivisible cluster. By
this run's measured case times that cluster is **90.1 min** including one compiler
build (the actual `selfhost-1` is 84.3). Simulating the same cluster-preserving
partition with `split` 2–5 leaves the longest part at 90.1 min every time; only
`split-cases: true` (each case its own unit) distributes the compiler cases, at the
cost of one compiler build per part.

The build log warned that **64 selfhost cases are not in
`.github/test-timings.json`** and were estimated at their group's median. The
baseline's compiler cluster is 48.6 min against 90.1 min measured (1.85× low), which
is why the plan said 54.5 min for the part that took 84.3.

## Recommendation

**Re-split `selfhost`: add `"split-cases": true` (keep `split: 3`) and refresh
`.github/test-timings.json` from this run's `test-log-*` JSONL.**

With this run's measured case and build times, three `split-cases` parts project to a
**52.9-min longest part** on the shard's selected cases, instead of 84.3 min; the
jobs' `selfhost-cli*` cases (8.7 min of work in total across the three jobs) are
picked up by `resolved()` and are not in that projection, so treat 53 min as a floor.
The job count stays 19 — no new cap pressure. (`split: 4` with `split-cases` projects
41.8 min on the same selected set, but takes the post-build fanout to 22 jobs and adds
queueing; this is not needed to remove the 84-min outlier.)

Not the cap: the only waits are 9.9 and 12.3 min and both finish 43–50 min before
`selfhost-1`; starting them earlier changes the makespan by zero. Not the cache push:
the shards substituted and the PR push found nothing to push; the `build` job's
missing PR-cache read is a separate ~42.6-min workflow defect, worth its own change.
