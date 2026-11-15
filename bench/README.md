# Standard-library benchmarks

`stdlib-bench.wiz` measures the standard library's hot data structures; `../scripts/stdlib-bench.py`
drives it, takes repeated samples and writes JSON.  Both are deterministic: a mode does the
same work at the same size on every machine, and prints a checksum of that work (so a
compiler or runtime change cannot delete it as dead code).

```sh
wiz build bench/stdlib-bench.wiz -o bench/.build/stdlib-bench
scripts/stdlib-bench.py --reps 7 --json /tmp/stdlib.json
```

The script builds the program itself (using `.lake/build/bin/wiz` when it exists) and
runs each mode in its own process.  Samples are wall-clock nanoseconds measured with
`time.perf_counter_ns`; the JSON records every sample, the median, variance, standard
deviation and coefficient of variation (`cv`).  Use `--size MODE=N` for an experiment.

## Modes and sizes

| mode | N | work |
|---|---:|---|
| `strmap-insert` | 200000 | build N `Str` keys, insert them all |
| `strmap-find` | 200000 | build the map, 8 passes of N pseudo-random hits |
| `strmap-miss` | 200000 | build the map, 8 passes of N misses (keys prebuilt) |
| `strmap-iterate` | 200000 | visit every entry by its key, 4 passes |
| `array-push` | 2000000 | push N numbers |
| `array-index` | 500000 | build, then 10 passes of N reads and writes |
| `array-map` | 1000000 | build, then map every element into a new array |
| `array-fold` | 1000000 | build, then fold every element |
| `bytes-append` | 2000000 | append a 16-byte chunk N times |
| `bytes-slice` | 2000000 | slice 64 bytes out of an 8 KiB buffer N times |
| `bytes-compare` | 2000000 | compare two equal 4 KiB buffers N times |
| `text-split` | 40000 | split an N-chunk string on `,`, 8 passes |
| `text-replace` | 40000 | replace every `,` with `Z`, 8 passes |
| `text-trim` | 40000 | trim an N-chunk string padded with spaces, 8 passes |
| `text-eq` | 40000 | compare two equal N-chunk strings, 200 times |
| `text-suffix` | 40000 | `endsWith`, `stripSuffix` and `dropEnd`, 3 passes |
| `sort` | 100000 | insert N keys into `U64Map`, read them back sorted 8 times |
| `hash` | 300000 | `NatList.hash` of an 8-number list, 300000 times (a different seed each time) |

## Comparing two builds

Two runs of the same build differ by several percent when other work shares the machine.
For a change, build the old and new executables and interleave them:

```sh
scripts/stdlib-bench.py --baseline-bin /tmp/old-bench --reps 15
```

This alternates one run of each per sample, changing which build goes first, and
reports the median of the per-pair ratios (with the min and max and every ratio), which
cancels machine drift.  `--baseline FILE` instead compares the medians with an earlier
JSON; `--fail-regression PCT` turns a slowdown into exit status 1, and
`--allow-checksum MODE` permits a deliberate checksum change (a new hash function, say).
`--bin FILE` runs an existing executable without rebuilding it (the usual way to keep
the A side of a comparison).

`stdlib-baseline.json` is a recorded reference run and `stdlib-bench.json` the run after
the changes, with both the samples and the interleaved `ab` ratios.  Absolute times move
with machine load; use `--baseline-bin`, not two separate runs, to decide whether a
change is a regression.  Regenerate the reference after a deliberate change and keep the
old file.

## Memory

`../scripts/mem-bench.py` measures peak RSS (not time) of a fixed corpus: cold checks of
`lib/`, the largest example, a `wiz build`, and the self-hosted checker. It records
`mem-baseline.json`, gates a run at +25 % relative and at a per-invocation hard cap, and
has a `--self-test` for the thresholds. See docs/building.md, "Memory budget".
