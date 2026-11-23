# F54 — scry analysis liveness (points-to key collision)

Status: fixed on `agent/f54-fuzz-liveness`, based on local `integration/train12`
`f489cc876`. The scry package was **not** rebuilt here (the build queue is reserved for
train11); the validation command is at the end.

## Symptom

The incremental-cache differential fuzzer (`scripts/incremental-fuzz.py`, seed
20261125, program 2) produced a 4-file project (95 lines) on which an
`--allow-errors` analysis stopped making progress: 15 MB RSS, no child process, the
main thread sleeping on a futex while one worker ran at ~100% CPU for more than two
minutes. The campaign was classified `slow-input`. The preserved inputs were not
minimised. Reproduced here with the pre-fix binary:

```sh
scry project . --taint --allow-errors --json --rules …   # >15 s, killed
```

`scry project` without `--taint` finished in 0.06 s, and each file's `scry taint`
finished in milliseconds, so the hang is in the whole-program analysis after lowering.

The same behaviour reduces to **one file**: three functions, each declaring
`(int x, int y, char *p)`, with unit1 containing `char0++` and `p[0] = x[NULL]`, unit2
containing `v3` and a loop, and unit3 carrying a chain of `if` statements to raise the
round fuel. This is the checked-in regression fixture (below).

## Root cause

`Scry.vkKey` (`scry/src/Scry/PointsTo.wiz`) keyed the points-to register map by

```
(h XOR var) * 1099511628211 + 1442695040888963407,   h = FNV-1a(function name)
```

XOR is linear in the low bits. The FNV hashes of the sequential names `unit1`/`unit2`/
`unit3` differ by exactly one in the low bit, so

```
(unit1, 1) and (unit2, 0)   -> the same U64
(unit1, 0) and (unit2, 1)   -> the same U64
(unit1, v) and (unit2, v-1) -> the same U64
```

The same happens for `sink1`/`sink2`/`sink3`. The map is only 64-bit keyed, so the
collision **merges two abstract registers**. The design calls a merge sound (both maps
are may-analyses), and it is, but it is not *liveness-preserving*: with `p` at
parameter index 2 in all three functions, the merged register becomes both the base
and the destination of a `gepVar`/`gep`. Each fixpoint round then adds one more
`anyOff`/`field` level to the location set:

```
{x, anyOff x, anyOff (anyOff x), …}
```

The location domain is therefore **not finite**. The only guard was the round fuel
`8 + 2 * total points`, which is linear in program size and permits hundreds of rounds
for a small recovered unit. Union, equality and `locHash`/`locEq` recurse on the
location depth, so the per-round cost grows with the round number. Measured with the
pre-fix binary on the same file using `--max-rounds`:

| rounds | points-to time | locations |
|---:|---:|---:|
| 32 | 20 ms | 31 |
| 64 | 226 ms | 63 |
| 128 | 6.9 s | 127 |
| 256 | >20 s | 255+ |

That is a practically non-terminating fixpoint, not a blocked thread: the worker is
busy and the main thread simply waits for it.

`Scry.Eval.findStepA` was inspected during this work. It is **not** an infinite loop:
the `| steps, .succ k` pattern is the decrement, so the scan from `Array.size` down to
0 terminates. Its comment now says so; there is no code change there.

## Fix

1. **Strong register key.** `Scry.mix64` now combines with a multiplicative step
   (`h * FNV-prime + x`) followed by the MurmurHash3 finalizer (`mixFinal64`), instead
   of XOR plus a weak linear mix. The systematic `(unit1, v)`/`(unit2, v-1)` collision
   is gone. A 64-bit collision is still possible, but it is now a 2^-64 event rather
   than a property of adjacent names.

2. **Finite location lattice (the termination invariant).**
   - `Scry.locDepth` counts `field`/`anyOff` nesting (a base location is 0).
   - `Scry.maxLocDepth = 8` is the bound.
   - `Scry.addOffBounded` is `addOff` with the depth bound; a field beyond the bound
     widens to `Loc.unknown`.
   - `Scry.anyOffBounded` is idempotent: `anyOff (anyOff b) = anyOff b`; a base at the
     bound widens to `unknown`. (`anyOff unknown` keeps its old value: one wildcard of
     the unknown location is already finite.)
   - `Scry.rhsLocs` and the two `Lifetime` transfer functions use the bounded
     constructors. With `unknown` as the top, every widening is a sound may-location:
     it can add targets, never remove a real one.

   The location domain is now finite (finite bases × finite constants × depth ≤ 8), so
   the round loop terminates by the existing `stateEq` check even if a genuine
   recursive pointer or a future key collision creates a self-feeding `gep`.

3. **Diagnostic when the bound is hit.**
   - `Scry.PtResult.depthCapped : Bool` is true when a location at
     `maxLocDepth` exists, so a deeper field/wildcard is widened to `unknown`.
   - `Scry.pointsToWarningsAt` emits a `scry/memory/location-depth` memory warning at
     the first function's entry (point 0), so the project report can show the message
     under a real source file; the cap and the recall caveat are in the detail. It is
     appended to `ProgramResult.warnings` by both analysis entry points, so it appears
     in `scry taint`'s warnings and in `scry project --taint`'s `memory` array/SARIF.
   - `Scry.pointsToBudgetNotes` adds `scry/budget/points-to-depth`, and `scry taint`
     sets `truncated: true` when the cap was reached. A capped run is never silent.

## Regression

- `scry/tests/fixtures/fuzz-regression/fuzz-regression-hang-analysis-location-depth.c`
  — 52 lines, the three-function collision above (30 `if` statements in unit3 to set
  the fuel). Pre-fix it exits 124
  (`--timeout 2`) or is killed after the external budget; the location count grows one
  per round.
- A row in `scry/tests/fixtures/fuzz-regression/manifest.json`:
  `category: "hang"`, `mode: "taint"`, `timeout_s: 3.0`,
  `signature: "hang:analysis-location-depth"`. The normal replay
  (`grail build fuzz-regressions`) is the must-terminate case; after the fix the
  fixture is `clean` and the replay reports it as `fixed`.
- `scry/tests/taint.wiz` now also runs the fixture and checks that
  `points-to` completes and the location table stays under 1000 entries. Four pure
  checks pin the invariant without the fixture: the old collision pair
  `(unit1,1)`/`(unit2,0)` must have different keys, `anyOffBounded` is idempotent,
  20 `addOffBounded` steps stop at `maxLocDepth`, and the result is `unknown`. The
  expected lines are in `scry/tests/taint.expected`.

No fuzz campaign was run for this fix (the queue is reserved). The fixture is replayed
by the normal regression target, not by a fresh fuzz loop.

## Remaining risk

- **Hash collisions** are still possible (2^-64). A collision merges two registers;
  the location-depth bound now makes that terminating, but precision is lost silently.
  The old comment promised a merge was harmless; that promise is now true for
  liveness, not for precision.
- **Depth cap precision.** A real pointer chain deeper than 8 is widened to `unknown`.
  The diagnostic says so. A reported finding is still a real derivation, but a precise
  alias through the widened chain can be lost, so recall on such chains is reduced.
  The cap matches the layout bound already used for recursive records
  (`Scry.cellsOfGo` cuts off at 8).
- **Round fuel.** The fix makes the state finite; it does not change the historical
  `8 + 2 * total points` round bound. A huge program can still exhaust that bound and
  is reported as `scry/budget/points-to-incomplete`; `--max-rounds` remains the user
  control.
- The `Lifetime` transfer has the same bounded constructors, but the memory analysis
  was not re-timed; the fixture's hang is in points-to and the stack showed
  `ptLoopGB`.
- Not run: `grail build scry`, `grail test tests/taint.wiz`, and
  `grail build fuzz-regressions`; see the command below.

## Validate

```sh
cd scry
grail build scry
grail test tests/taint.wiz
grail build fuzz-regressions
# direct check of the fixture (must finish well inside 2 s, no truncation):
./.grail/bin/scry taint \
  tests/fixtures/fuzz-regression/fuzz-regression-hang-analysis-location-depth.c \
  --allow-errors --json --timeout 2
```

The direct check should exit 0 with `"pointsToComplete": true`; a pre-fix binary exits
124 with `scry: timeout after 2 s`.
