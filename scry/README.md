# scry

The code-analysis platform's grail package. The design is
`wiz-notes/code-analysis-design.md` §4/§6; the package layout, schema and the S1
checklist are in `wiz-notes/scry-package.md`.

S1 now parses C with a **vendored tree-sitter** (`native/README.md`: tree-sitter
v0.27.2 and tree-sitter-c v0.24.2, both MIT). One C shim, `native/ts_shim.c`, parses a
file, walks the tree with a `TSTreeCursor` and bulk-loads the CST into struct-of-arrays
columns; no `TSNode` crosses the FFI. `src/Scry/Native.wiz` exposes the columns as
`U32Array`/`U64Array` and builds the `Scry.CstStore` model. The JSON fact store and the
`scry-cst 1` spill format remain for the synthetic corpus and for differential tests.

```sh
cd scry
cp ../grail.local.wiz .         # this machine's toolchain (not committed)
grail build                     # check src/gen, build .grail/bin/scry, run the commands
grail test                      # schema, cst, native shim, codegen, CLI, parse --stats, taint
grail build schema              # regenerate gen/C/Schema.wiz from node-types.json
grail build schema-check        # fail if the checked-in schema is stale
grail run scry -- parse --stats fixtures/hello.c
grail run scry -- parse --stats fixtures/broken.c
grail run scry -- facts fixtures/demo.facts.json
grail run scry -- query fixtures/demo.facts.json --kind call_expression
grail run scry -- explain fixtures/demo.facts.json 4
```

Commands: `facts`, `query --kind|--edge|--rel`, `explain`, `parse --stats` (a C source,
a `scry-cst` spill, or a JSON store), `cst` (JSON store → spill), `taint` (C →
Wil → taint → findings/SARIF), and `bench` (run the checked-in taint corpus and compare
findings with its manifest). `parse --stats` prints counts only; the perf agent owns
throughput numbers.

## `scry taint`: C → Wil → taint → findings/SARIF

`scry taint` is the S2 + S4 pipeline end to end:

```sh
grail run scry -- taint corpus/c2wil/taint-unsafe.c
grail run scry -- taint FILE.c --rules ../lib/Scry/rules/default.scry --sarif out.sarif
grail run scry -- taint FILE.c --json --allow-errors
grail run scry -- taint FILE.c --fail-on-finding
```

The stages are: parse with the vendored tree-sitter shim (S1) and build the
`Scry.CstStore`; lower the translation unit with `Scry.Lower` (S2), whose `Wil.Stmt`/
`Wil.Term` carry a `Wil.Span` (file, byte range, CST node); run the rule-pack engine
(`Scry.RuleTaint`) and the direct-call summaries/path stitching (`Scry.Interproc`) with
the default pack `lib/Scry/rules/default.scry` (or `--rules FILE`); certify each alert's
derivation with `Scry.Certify`; print findings with their source spans; and, with
`--sarif OUT`, write SARIF 2.1.0 (`Scry.Sarif`). `--origin-map` prints the
`(function, program point) -> span` table used for the locations.

Each finding names its **derivation status**: `checked` when its Datalog certificate
verifies against the function's EDB, `unchecked` otherwise. `--fail-on-finding` exits 1
when a finding or a lowering-boundary warning is present, so the command can gate CI.

**Boundary warnings are not false negatives.** The lowering is deliberately a subset:
a struct field, array/subscript, cast, `?:`, `sizeof`, string literal, global, switch,
`goto`, or an unsupported declaration becomes `havoc` **and** a warning naming what was
not modelled. `scry taint` prints those warnings as `lowering-boundary` findings and puts
them in SARIF; they are `unchecked` (there is no derivation, and the value is unknown).

The remaining gap is **points-to and memory**. Taint tracks registers through the
def-use layer, but `store`/`load`, aggregate fields, arrays and heap objects are not
modelled precisely, so a flow that goes through memory can be missed; the lowering's
havoc warning is the visible boundary. Indirect calls are kept unknown (the call graph
records them), and per-warning source spans are not yet attached (a boundary warning
points at the function definition). A parser error is refused by default;
`--allow-errors` analyses the recovered tree and reports the `ERROR`/`MISSING` count.

`tests/native.wiz` checks the shim on `fixtures/hello.c`: 55 nodes, 54 edges, the root
span `[0,95)`, parent/child/next-sibling links, and that `fixtures/broken.c` is refused
by `parseChecked` (tree-sitter's recovery tree has 2 `ERROR`/`MISSING` nodes).

## `scry bench`: the taint corpus and metrics

`scry bench` runs the same pipeline as `scry taint` over `bench/corpus/manifest.json`,
compares the findings with the manifest's expectations, and writes stable JSON and
Markdown. The checked-in corpus is **S0/S2**: the existing `tests/fixtures/taint-*.c`
goldens plus hand-authored safe/unsafe pairs for CWE-78 (command injection), CWE-134
(format string), CWE-242 (`gets`) and CWE-120/121 (`strcpy`/`strcat`). S1/S3/S4 are
optional external corpora (`--extra DIR`); no third-party corpus is checked in.

```sh
grail run scry -- bench                         # build/bench.json + build/bench.md
grail run scry -- bench --no-timing --json -    # deterministic report on stdout
grail run scry -- bench --extra /path/to/subset # an external manifest
grail run scry -- bench --fail-on-regression    # exit 1 if the baseline changed
grail run scry -- bench --update-baseline bench/baseline.json
```

Reported per CWE and overall: TP/FN/TN/FP case counts, TPR, FPR, Youden's J, precision,
F1, macro averages, path validity (the path ends at the reported sink; a taint path also
starts at a source), certificate (`checked`) coverage, boundary warnings, and runtime.
The ratios are computed in integer basis points, so the checked-in baseline is stable.

Metrics are per **case**, not per alert. An `unsafe` case is TP only when every expected
finding is matched with valid evidence and no extra finding appears; a `safe` case with a
finding is FP; a `safe` case with a *blocking* lowering boundary is `unknown`, not TN. A
missing corpus/manifest is a clean skip (exit 0), and a missing individual case file is
`skipped`. Runtime is wall clock from `Clock.monotonic` and is marked informational: it
is not a `perf-run` measurement, and the perf agent owns real numbers.

`tests/bench.wiz` checks the metric formulas, the boundary/path/outcome rules, the
missing-corpus skip, and that the corpus still matches `bench/baseline.json`. The corpus
policy and the external-manifest hook are in `bench/corpus/README.md`.

Limits: the shim is sequential (one parser, one tree, one file) and tree-sitter-c is the
only grammar. Threads, a native store shared across files, and tree-sitter queries are
the remaining S1 work.
