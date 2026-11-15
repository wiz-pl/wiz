# The C runtime's libFuzzer harnesses

`scripts/test-fuzz.sh` compiles `runtime/fuzz/runtime.c` (the runtime as one
translation unit with `-DWIZ_API=`, the LLVM backend's ABI) and one harness with
Clang's libFuzzer, AddressSanitizer and UndefinedBehaviorSanitizer. It runs from
a generated seed corpus and keeps the runtime ABI unchanged: the harness includes
`wiz_rt.h` and calls only exported entry points.

## Harnesses

| target | what it drives |
| --- | --- |
| `values` | constructors and fields (`field_at`, `proj`, `set`, `reset`/`reuse`, `drop_moved`), owned/shared references, closures and partial application, memoised suspensions, constants |
| `data` | `Str`, `Bytes`, `Array`, `StrMap`, `U8/U32/U64Array`, `WordMap` and Wiz `String`s; slices, past-the-end indices, copy-on-write from a shared value; a model checks map size and membership |
| `words` | Nats (small scalars, GMP, shifts), `UIntN`/`IntN` at widths 0..128, arithmetic and comparisons, shifts, division by zero and signed division by -1, `UInt64`/`Float64` raw words |
| `finalizers` | foreign objects with a finalizer in constructors, arrays, maps, an MVar and a lazy cell; sharing through `wiz_retain`/`wiz_release`; the finalizer must run exactly once per object |

The input is a small bytecode. A harness reads operations from it and supplies
the runtime with owned arguments, valid field indices and acyclic values, the
same way generated code does. Every root is dropped before the input returns, and
`wiz_live_objects()` is compared with its value at entry: a leaked object aborts
the input, so one iteration does not rely on LeakSanitizer's process-exit check.

## Seeds

`scripts/gen-fuzz-seeds.py` writes the seed corpus:

* the existing programs in `runtime/corpus/` (`values.c`, `numbers.c`,
  `text.c`, `threads.c`) as raw seed bytes, so fuzzing starts from the cases the
  sanitizer corpus already covers;
* one short structured seed per operation, so no opcode is missing at the start.

`scripts/test-fuzz.sh` copies the seeds into a temporary corpus before running;
libFuzzer's new units never dirty the worktree. A failing input is deduplicated by
SHA-256 and a `crash-*` unit is minimised with `-minimize_crash=1`. On failure the
script keeps its temporary directory (seeds, logs, deduplicated and minimised
units) and prints its path.

## Commands and exit status

```sh
scripts/test-fuzz.sh                       # 5000 inputs per harness (the smoke run)
scripts/test-fuzz.sh --max-total-time 60   # one minute per harness
scripts/test-fuzz.sh --target data --runs 20000
scripts/test-fuzz.sh --list                # targets and seed programs
```

The script reads `WIZ_CFLAGS`, `WIZ_LDFLAGS` and `WIZ_LIBS` like
`scripts/test-sanitizers.sh`; run it under `nix develop`. Exit status is 0 for a
pass, 1 for a failing harness, 2 for a usage error, and 3 when Clang/libFuzzer or
a working sanitizer is absent (a `skip:` line, which CI reports as a warning).

## Limits

* Generated code also uses the inline form (`-DWIZ_API=static`); it is covered by
  `scripts/test-sanitizers.sh`, not by these harnesses.
* Threads, channels, `Sys` (environment, files, processes) and the 32-bit value
  representation are out of scope. The finalizer harness does not spawn threads.
* Shift amounts, exponents, input strings and the size of a value in the number
  pools are bounded so one input cannot cause an unbounded GMP allocation. Those
  are harness limits, not runtime contracts.
* The harnesses do not prove memory safety and are not an open-ended fuzz
  campaign: CI runs a bounded smoke corpus (`--runs 20000` per target).
