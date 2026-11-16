# Fuzzing scry's C front end

This directory adds **dynamic evidence** to scry's static findings. It is a bounded
coverage-guided bug search, not a verifier: a run that finds nothing does not show that
the parser, the shim or the analysis is free of crashes, memory errors or undefined
behaviour.

## What is fuzzed

The target is the vendored C front end:

```
fuzz/ts_shim_fuzz.c          libFuzzer target; includes native/ts_shim.c
native/tree-sitter/…         the pinned tree-sitter 0.27.2 runtime
native/tree-sitter-c/…       the pinned tree-sitter-c 0.24.2 grammar
```

libFuzzer calls `scry_parse("c", bytes, len)` and checks the struct-of-arrays contract
the Wiz side reads: preorder ids, one root, parent/first-child/next-sibling links, the
child CSR, the edge arrays, in-range kind/field ids, spans inside the input, and the
`ERROR`/`MISSING` flag count. A violation aborts with

```
SCRY-FUZZ INVARIANT: <what> (node=N, input_offset=BYTE)
```

which is a minimisable artifact just like an ASan/UBSan report.

The Wiz/Lean analysis pipeline above the shim is **not** fuzzed by this target. The
dynamic report is about the C parser boundary; the static `scry bench` report is about
the taint rules. They are placed beside each other in one report, not merged into one
metric.

## Build and run

The driver finds `clang` on `PATH`, from `SCRY_FUZZ_CC`, or in `/nix/store`
(`*clang-wrapper-*/bin/clang`) and checks that its resource directory ships
`libclang_rt.fuzzer`. If no such clang exists, the run is a clean skip (exit 0) with the
reason in the report.

```sh
cd scry
# static half (34 cases on this branch)
./.grail/bin/scry bench --no-timing --json build/bench.json --markdown build/bench.md

# bounded smoke: build, seed from the bench/tests corpus, fuzz, minimise, dedup,
# map artifacts, sweep the static corpus once, write build/fuzz/dynamic.{json,md}
python3 fuzz/run.py --build --runs 5000 --time 15 --seed 20261115 \
  --static build/bench.json --out build/fuzz
```

The reproducible command is printed in `dynamic.json` under `command`; the same
`--seed`, `--runs`, `--time` and `--max-len` reproduce the bound. `--runs` is an
execution bound and `--time` a wall-clock bound; whichever is reached first stops
libFuzzer. Use `--clean` to start from the checked-in seeds again (the run directory is
under `scry/build/`, which is git-ignored).

Exit status: 0 for a clean run or a skip, 1 when a dynamic finding is reported (and for
an internal libFuzzer failure), 2 for a malformed invocation or a failed build.

## Seeds

`run.py` seeds from `bench/corpus/**/*.c`, `tests/fixtures/**/*.c`, `corpus/**/*.c` and
`fixtures/*.c`, plus the resolved files of the static report's cases. Files are deduped
by SHA-256 and copied into `build/fuzz/corpus/`. The fuzz target does not read the
manifest; the static report supplies the corpus-case cross-references.

## Minimise and dedup

For each artifact, the driver replays it once, then runs libFuzzer's
`-minimize_crash=1` (bounded by `--minimize-runs`) into `build/fuzz/minimized/`.
The signature is textual and deterministic:

* ASan: `asan:<error-kind>` + the first three stack frames;
* UBSan: `ubsan:<message>` + the first three frames;
* invariant: `invariant:<what>` + frames;
* `timeout`, `oom`, `leak` when no stack site exists.

Addresses, thread ids and long numbers are normalised away, so the same fault at the
same source site groups even when the heap address changes. Dedup keeps the smallest
artifact per signature (then the lexicographically smallest SHA-256). This is
best-effort: two different bugs with the same top three frames can collapse, and a
stack trace is not a proof of the root cause.

## Mapping an artifact to scry source spans

`scry fuzz-span FILE [--offset N] [--json]` reads the file, runs the same shim, and
reports the input's CST summary using the span shape of static findings:

```json
{
  "format": "scry-fuzz-input", "version": 1, "kind": "dynamic",
  "path": "…", "bytes": 34, "nodes": 14, "edges": 13, "roots": 1, "errors": 2,
  "root": { "node": 0, "kind": "translation_unit", "status": "root",
            "start": 0, "stop": 34, "line": 1, "column": 1, … },
  "error_spans": [ { "node": 5, "kind": "ERROR", "status": "ERROR",
                     "start": 11, "stop": 16, "line": 1, "column": 12, … } ],
  "crash_offset": 15,
  "crash_span": { "node": 8, "kind": "identifier", "status": "node",
                  "start": 15, "stop": 16, … }
}
```

`--offset` is the byte offset from an invariant line (`input_offset=N`); the result is
the smallest CST node containing it, with ties going to the later/deeper node. For a
native ASan/UBSan crash there is usually no input offset, so `crash_span` is `null`;
the corresponding **native** frames are in `dynamic.json` under `frames`, and the input
side is represented by the root and `ERROR`/`MISSING` spans. That is the honest split:
a stack frame points at the shim/tree-sitter C source, while the input span points at
the fuzzed C source.

`fuzz-span` reads with `FS.readFile`, which stops at NUL and decodes UTF-8. The driver
therefore only maps an artifact that is ASCII with no NUL; for anything else the
`scry` field is

```json
{"status": "skipped", "reason": "artifact contains NUL; …"}
```

The fuzzer itself still explores arbitrary bytes. Byte and character columns agree for
the ASCII C the front end targets; a non-ASCII source would need a byte-column mapper.

## The dynamic evidence report

`dynamic.json` is an evidence document with two halves:

```json
{
  "format": "scry-dynamic-evidence", "version": 1, "kind": "dynamic",
  "status": "clean | findings | skipped | error",
  "tool": {"engine": "libFuzzer", "sanitizers": ["address", "undefined"], …},
  "command": "…", "bounds": {"runs": …, "seconds": …, "max_len": …},
  "corpus": {"seeds": 57, …},
  "static": {
    "present": true, "path": "scry/build/bench.json",
    "summary": {"cases": 34, "findings": 22, "overall": {…}},
    "corpus_sweep": {"cases": 34, "clean": 34, "crash": 0, "skipped": 0},
    "cases": [{"id": "cwe78/…", "outcome": "tp", "findings": 1,
               "dynamic": "clean"}, …]
  },
  "dynamic": {
    "counts": {"artifacts": 0, "unique": 0, "dropped": 0},
    "stats": {"runs": …, "coverage": …, "features": …},
    "findings": [ { "id": "dyn-001", "kind": "dynamic", "signature": …,
                    "summary": …, "frames": […], "scry": {…}, "reproduce": … } ]
  },
  "limits": "…",
  "note": "A bounded run that finds no crash is not evidence of safety. See limits."
}
```

`static.corpus_sweep` runs each static case once through the same harness and sanitizers.
A `clean` case means those bytes did not crash in one execution under ASan/UBSan; it does
not change the static TP/FP/TN/FN judgement and it is not a verdict on the analysis.
`dynamic.md` is a human-readable rendering of the same document.

## Results from this branch

* The first harness run found a **744-byte leak on every successful parse**: the shim
  pre-allocates an error store at entry and the success path returned without freeing it.
  LSan reported it on an empty input; `native/ts_shim.c` now frees it on success. That is
  a concrete dynamic finding, fixed here, not a claim that the rest is clean.
* Bounded smoke (`--runs 5000 --time 15 --seed 20261115`, clang 21.1.8,
  `-fsanitize=fuzzer,address,undefined`): 57 unique seeds, 5000 executions, 1625
  coverage edges, 4066 features, **0 artifacts**, and a 34/34 clean one-execution sweep
  of the static corpus. The counts are in `build/fuzz/dynamic.json` and repeated in
  `wiz-notes/scry-fuzz.md`. **This is a bounded observation, not a safety result.**

## Limits

* Bounded and machine-local. libFuzzer's coverage, the compiler version, the vendored
  parser and the seed corpus determine what ran; a later run can find something.
* The target is the C shim and tree-sitter-c only. The lowering, points-to, Datalog,
  taint and SARIF layers are not libFuzzer targets; a Wiz-side crash would need a separate
  replay harness.
* ASan/UBSan catch memory and UB classes they instrument; they do not prove functional
  correctness, and a cleanup/leak report is not necessarily a bug in the analysis.
* Minimisation is libFuzzer's, on the same target and a bounded run; the minimised input
  may no longer resemble valid C.
* Dedup is textual stack-signature based; different root causes can share a signature.
* Span mapping is ASCII-only and byte/character exact only under that restriction.
* The static half is 34 cases on this branch (`agent/scry-bench` at the merge point); the
  expanded rule-pack baseline lives on `agent/scry-rules`, so these counts are not the
  headline bench numbers from `wiz-notes/scry-bench.md`.
