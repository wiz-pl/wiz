# Stage 33: a Wiz-native test runner

Today five runners share the work of testing Wiz: the Lean `tests` driver, `grail test`,
and the Python scripts `ci.py`, `flaky.py` and `golden-diff.py`. They select tests
differently, time out differently and write different timings, and none of them knows
how much memory a test needs. Stage 33 builds one runner, `wiz-test`, in Wiz. This
stage is its **pure core** (`lib/TestRun/*.wiz`). Process supervision, the `Scope`
worker pool and the adapters for the Lean suite and grail's goldens come later and
drive this core (the plan's lanes TR2 and TR3).

The core is pure for two reasons. `#eval` runs all of it, so the tests need no
processes, no clock and no machine. And the scheduler's invariant is a theorem about
the same definitions that run.

Tests: group `testrun` (`Tests/Groups/TestRun.lean`). Each case is a Wiz program whose
`#eval`s print a transcript.

## 33a: ids and selection (`lib/TestRun/Id.wiz`)

**Stable ids.** A Lean-suite case's id is `group/slug`. The slug is the case name in
lower case, with every run of other characters replaced by a single `-`, cut to 64
characters. Repeats within a group become `slug-2`, `slug-3`, and so on. A golden test's
id is `pkg:path`. The index stays available as an alias (`=G#3`). Timings and the
quarantine are keyed by id, so renaming a case changes one line of the baseline instead
of silently dropping the case from it.

**Selectors.** These include the Lean driver's forms, plus new ones:

| selector | selects |
|---|---|
| `=G` | group `G` |
| `=G#3,7` | cases 3 and 7 of `G` |
| `G` | groups whose name starts with `G` |
| `=G/slug` | one case, by id |
| `tests/rv/**` | golden files, by path glob (a plain path is one file) |
| `~text` | cases whose name contains `text` |
| `+tag`, `-tag` | cases with / without a tag |
| `!SEL` | cases `SEL` does not select |
| `@shard:NAME[/k]` | a CI shard, or part `k` of a split one |
| `@failed`, `@changed` | the last run's failures; cases whose cache key changed |

A selection is the union of its **includes**, or every case when there are none. Each
**filter** (`+tag`, `-tag`, `!SEL`) then narrows it. Three things are errors (exit 2 in
the runner): an unknown flag (`--x`), a malformed selector, and an include that
selects nothing. `@failed` and `@changed` may select nothing.

**Globs.** `*` matches any run of characters except `/`, and `?` matches one such
character. `**` matches anything, and `**/` matches any number of whole directories,
including none (`tests/**/*.wiz` matches `tests/a.wiz`). The matcher runs a
nondeterministic automaton over the path, so its time is linear in the path's length,
whatever the pattern.

## 33b: the plan (`lib/TestRun/Plan.wiz`)

**Limits.** A case has a time limit and a memory reservation, resolved field by field:

1. what the case **declares**: a golden header's `timeout`/`mem`, or a group's entry in
   `.github/test-shards.json`;
2. what was **learned** from the baseline: `max(256, p95(peak) × 5/4 + 64)` MiB and
   `max(60 s, 4 × p95(time))`;
3. the **class default**: `check` 300 s / 1 GiB, `run` 300 s / 1.5 GiB, a Lean case
   600 s / 1 GiB, a fixture 1800 s / 5 GiB.

A limit's `source` is the source of its memory reservation. Only a learned reservation
earns the retry-alone of 33d. When the baseline needs more memory than a case declares,
`Limits.drift` warns, and the declaration still wins. `Limits.scale` implements
`--timeout-scale` (in thousandths).

**Order and packing.** Fixtures (shared builds) start first, then cases longest first
(LPT); ties keep selection order, because the merge sort is stable. `Plan.pack k` splits
a shard into `k` parts. Cases that share a fixture form one unit, so a fixture is built
once per shard until fixtures are cached by key. Units go into parts longest first,
each into the least loaded part.

## 33c: memory admission (`lib/TestRun/Budget.wiz`)

A `Pool` has a budget (MiB), the current reservations, the number of running cases, and
`jobs`. A case reserving `r` is admitted in one of two ways:

* **it fits**: fewer than `jobs` cases run and `reserved + r ≤ budget`, and it holds `r`;
* **alone**: nothing runs. A case larger than the whole budget then holds all of it, so
  nothing else starts beside it.

Otherwise it waits. Proved, with no axioms:

* `Budget.admit_le : Pool.admit s r = some g → g.pool.reserved ≤ g.pool.budget`: after
  any admission, the reservations are within the budget;
* `Budget.release_le`: releasing keeps that;
* `Budget.release_take`: releasing a fitted case gives back exactly its reservation;
* `Budget.admit_fits_held` and `Budget.admit_busy`: what `fits` and a busy pool decide.

`OkPool` packages a pool with the proof of its invariant. `OkPool.admit` and
`OkPool.release` are the only ways to change one, and the scheduler holds an `OkPool`.
So the invariant holds **in every state the scheduler can reach**
(`Sched.reserved_le`), by construction and not by a separate induction over runs.

## 33d: the scheduler (`lib/TestRun/Sched.wiz`)

The scheduler is a state machine that a driver feeds:

```
Sched.feed : S → Nat → Event → S × List Cmd     -- at time t (ms), this happened
Sched.wake : S → Option Nat                     -- call back with tick by then
```

The events are `started`, `exited` (exit code, OOM flag, peak, skip reason, notes,
output), `tick`, `pressure ok` and `interrupt`. The commands are `run` (slot, attempt,
limits), `kill` (slot, signal), `print` and `record`.

* **Admission** follows `heavy`'s rules. Cases start in plan order while the pool
  admits them. When the head of the queue does not fit, at most `maxBypass` later
  cases that do fit may pass it; after that the runner drains until the head fits. A
  closed pressure gate (PSI, MemAvailable) starts nothing.
* **Time limits.** At the deadline the scheduler sends `kill 15`, then `kill 9` once the
  grace period has passed. The exit is recorded as `timeout`. Every driver enforces the
  deadline of its own child, so no task is cancelled from outside.
* **Memory.** If an OOM-killed case's reservation was *learned*, the case is retried
  once, alone, with the whole budget, and its record notes the drift (a cold-cache peak
  like golem_intc's). A declared reservation is not retried.
* **Retries.** A failure or timeout is retried up to `retries` times. A pass on a retry
  is `flaky`, never `pass`.
* **Interrupt.** The scheduler sends `kill 15` to every running case, then `kill 9`
  after the grace period, and starts nothing more. The summary counts the cases it
  never started.

`Sched.runScript` feeds a script of timed events. `Sched.simulate` runs a whole plan on
a virtual clock against simulated processes, given each attempt's duration and result.
At every step its transcript shows what is reserved and what is running. The `testrun`
tests are such transcripts: memory packing and bypass, the bypass limit, a case run
alone, the pressure gate, timeout escalation, a learned OOM retried alone, flaky passes
and an interrupt.

## 33e: records and the baseline (`lib/TestRun/Report.wiz`)

Log lines follow the Lean driver: `✓` passed, `✗` failed (with its output indented
below), `⊘` skipped (with the reason), each with the time in seconds. Timeouts,
over-budget cases, flaky passes and interrupts say so on the line below.

A timings record is one JSON line per attempt. It is a **superset** of the Lean
driver's `--timings` line (`shard`, `group`, `index`, `case`, `seconds`, `ok`, `notes`),
so `ci.py summary`, `balance` and `check-skips` read it unchanged. It adds `id`,
`status` (`pass|fail|skip|timeout|oom|cached|interrupted|flaky`), `attempt`,
`peak_mib`, `limit` (`timeout`, `mem_mib`, `source`), `enforce` and `queued_s`.

`Report.learn` builds the baseline from such lines: for each id, the p95 (nearest rank)
of the time and of the peak over passing runs. It also reads the Lean driver's records,
keying each one as `group/slug(case)`, so today's timings seed it.

## 33f: expected-output tests (`lib/TestRun/Golden.wiz`)

These are grail's semantics, in pure Wiz. A file's first line is its header:
`-- test: check`, `-- test: run` or `-- test: skip REASON`, and a file without one is a
`check` test. `check` and `run` take options as words, in any order: `timeout SECS`,
`build-timeout SECS`, `mem SIZE` (`512M`, `5G`), `tags a,b`, and `args …` (the rest of
the line). The word form extends the per-test `timeout SECS` proposed for `grail test`.

* A missing `F.expected` fails, and the message names `--update`.
* A difference reports the first differing line in grail's words (`line N:` /
  `expected:` / `actual:`). A failure without a header gets grail's note on why it was
  taken for `check`.
* `--update` never writes the output of a failed build or a timeout
  (`Golden.mayUpdate`).
* Normalisation is explicit. A package lists its replacements (`$PKG`, `$STORE`), and
  nothing else is replaced.
