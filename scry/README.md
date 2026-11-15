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

S2's C→Wil lowering is `src/Scry/Lower.wiz` (see `wiz-notes/scry-c2wil.md`), and
`src/Scry/Preproc.wiz` is its preprocessing entry point: `Scry.preprocess` parses
`cc -E` line markers, blanks them (so tree-sitter never sees a directive and every
offset is unchanged), and maps each node's preprocessed span back to the original
file/line/column in `Wil.Span`. `scry-cst -E [-D…] [-I…] FILE` runs `cc -E` and spills
the blanked text, which is how `corpus/c2wil/preproc/main.i.cst` was generated.

```sh
cd scry
cp ../grail.local.wiz .         # this machine's toolchain (not committed)
grail build                     # check src/gen, build .grail/bin/scry, run the commands
grail test                      # schema, cst, native shim, preproc, codegen, CLI, parse --stats, taint, project
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
Wil → taint → findings/SARIF), `bench` (run the checked-in taint corpus and compare
findings with its manifest), and `project` (a `compile_commands.json` multi-file C
project: cross-TU call graph, project EDB, per-file findings/SARIF and a TU cache).
`parse --stats` prints counts only; the perf agent owns throughput numbers.

## `scry taint`: C → Wil → taint → findings/SARIF

`scry taint` is the S2 + S4 pipeline end to end:

```sh
grail run scry -- taint tests/fixtures/taint-unsafe.c
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

## Points-to and memory

`Scry.PointsTo` is a **flow-insensitive, field-sensitive** Andersen-style points-to
analysis over the lowered Wil; the taint rules consume it, so a `store` propagates taint
into the locations it may alias and a later `load` receives it.

The location lattice is a set of

| location | meaning |
|---|---|
| `Loc.stack f p` | a stack slot: an address-taken scalar, or a struct/array local |
| `Loc.glob n` | a module-level global |
| `Loc.heap f p` | a heap object (`malloc`/`calloc`) |
| `Loc.fn n` | a function address (function pointers) |
| `Loc.field b k` | cell `k` of `b` (a field, an array element, pointer arithmetic) |
| `Loc.anyOff b` | *some* cell of `b` (a variable index) |
| `Loc.unknown` | memory the analysis could not bound (one merged location) |

Offset 0 is the identity, so `*p` and `p[0]` are the same cell; `anyOff b` overlaps `b`
and every `field b k`, which is the array policy ("smash first, refine later"). The
solution is a set of monotone inclusions (`x = y`, `x = p + k`, `x = *p`, `*p = y`,
`free(p)`, parameter and return flow across resolved calls), a fixed point over the whole
program: context-insensitive, field-sensitive, and cheap enough for the corpus.

**No alias and unknown are different.** An empty location set means the pointer is null or
a constant: it aliases nothing, so there is no flow and no warning. A set containing
`Loc.unknown` means the analysis failed to bound the target (a havoc'd pointer, a
function parameter with no caller, an unmodelled external's pointer result): the taint
still propagates (a may analysis) **and** an `unknown-memory` warning is reported at the
store/load. `free` is tracked too: a store/load of a freed location is a
`use-after-free` warning (the finding is still reported). An indirect call is resolved
through the function-pointer location set; when no target is known it is an
`unknown-indirect` warning and nothing is propagated.

Supported in memory: struct/union fields by constant offset, array elements by constant
index, a variable index (widened to the base object), `&x`/`*p`/`**pp`, pointer arithmetic
by a constant or a variable index, `malloc`/`calloc`/`free`, globals, function pointers
(assigned, copied, passed as an argument, stored in memory), pointer returns
(`p = f()`), aliased parameters, and the `strcpy`-family copy model. Not modelled:
`realloc`, external calls' memory effects outside that table, heap shape (a linked list
through two allocation sites is two sets, not a shape), context sensitivity, and
offsets past one `anyOff` level.

Fixtures and their expected results are in `tests/fixtures/mem-*.c` and asserted by
`tests/taint.wiz`: same-slot store/load (1 finding, path through `store`/`load`),
different slot (0), struct fields and a global field (2, and the sibling field 0), array
elements (1, sibling elements/arrays 0), a variable index (`a[i]` keeps the array, so 1
finding and no false positive on `b[i]`), heap (1), pointer-to-pointer (1), aliased
parameters (1 across two calls), `free` then use (1 finding + `use-after-free`), known
indirect target (1), unknown indirect target (0 findings + `unknown-indirect`),
returned pointer (1), `strcpy` into one array (1, the other array 0), and an unmodelled
external's pointer (1 finding + two `unknown-memory` warnings).

**Boundary warnings now carry spans.** `Scry.Warning` has a `Wil.Span`, so a
`lowering-boundary` result points at the construct (a cast, `sizeof`, a skipped `goto`, …)
instead of the function definition. SARIF rule ids are namespaced (`scry/c/<rule>`,
`scry/lowering/boundary`, `scry/memory/<kind>`) and the run declares
`columnKind: utf16CodeUnits` (the C slice is ASCII, where a byte column is a UTF-16
column; a non-ASCII source would need an explicit conversion).

A parser error is refused by default; `--allow-errors` analyses the recovered tree and
reports the `ERROR`/`MISSING` count.

`tests/native.wiz` checks the shim on `fixtures/hello.c`: 55 nodes, 54 edges, the root
span `[0,95)`, parent/child/next-sibling links, and that `fixtures/broken.c` is refused
by `parseChecked` (tree-sitter's recovery tree has 2 `ERROR`/`MISSING` nodes).

## `scry project`: multi-file C projects

`scry project DIR` builds a project from `DIR/compile_commands.json` (or `--compdb
FILE`), or from every `*.c` under `DIR` when no database exists. Each translation unit is
preprocessed with **its own** `-I`/`-D`/`-U`/`-include` flags, parsed, line-mapped and
lowered; the units are then merged:

* the project file table dedupes a shared header by path and keeps each unit's line map;
* `static` functions are qualified `static:<tu>:<name>`, so two units' helpers never
  collide; a call inside a TU resolves to that TU's helper;
* a non-`static` symbol resolves to the first definition in project order; a second
  definition is reported in `duplicates`, not silently merged, and is not analysed;
* a call with no definition anywhere is `unresolved` and its callee is `0` in the EDB.

```sh
grail run scry -- project corpus/project
grail run scry -- project corpus/project --facts -          # project EDB
grail run scry -- project query corpus/project --rel symbols
grail run scry -- project query corpus/project --rel callgraph
grail run scry -- project corpus/project/taint --taint --json
grail run scry -- project corpus/project/taint --taint --sarif out.sarif
grail run scry -- project corpus/project/taint --taint --json --cache --cache-stats
```

`--taint` runs the same points-to → summaries → rule pack → certificates pipeline over
the whole project (the functions are one Wil program, so a finding can cross a TU
boundary). The JSON has project counts, a `files` array with each file's findings,
boundary warnings and memory warnings, the unresolved/duplicate call lists, and the cache
stats. Human output groups the same counts by file.

SARIF is the multi-file writer: `runs[0].artifacts` lists the real project files with
URIs relative to the project root and `uriBaseId: "%SRCROOT%"`; every result's
`artifactLocation` carries the matching `index`, so a result in a header points at the
header. The single-file `scry taint` SARIF writer is unchanged.

`--cache[=DIR]` (default `.scry-project-cache`) caches each TU's `scry-cst 1` store. The
key covers the source path/text and flags; the entry is validated against a digest of the
**actual preprocessed text**, so a changed header or macro is a miss, not a stale hit.
`--cache-stats` adds hit/miss/write/corrupt counts and implies `--cache`.
`--fail-on-finding` returns exit 1 when a finding or boundary warning is reported.
`--skip-broken` records a TU whose `cc -E`/parse fails in the `skipped` list and analyses
the rest, which is how a real repository with optional platform headers stays usable;
without it the first broken TU is a hard error.

System-header bodies (`/usr/…`, `/nix/store/…`, the toolchain includes) are blanked after
`cc -E` by default: the line map and offsets stay valid, but the analyser sees the
project's code rather than glibc inline bodies. `--keep-system-headers` analyses them at
full fidelity (much slower on real code). Calls into those headers remain direct calls;
unresolved externals carry the usual warning.

The deliberate limits are stated in `src/Scry/Project.wiz`: no link-time alias analysis,
no global initialisers, no interprocedural memory beyond the existing points-to model, and
function pointers resolve only through the points-to analysis.

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

## Real C corpus

`scripts/real-corpus.sh` runs `scry taint --json --allow-errors --sarif` over the C
sources that are already on this machine (the Wiz C runtime/sockets/serial/infoview/
self-hosted runtime, the `wiz-rv/sw` bare-metal programs, the vendored tree-sitter
library, and two generated project files when present) and writes a per-file JSON,
SARIF, runtime and warning summary. It skips missing external files, so it also runs on
a bare checkout.

```sh
scry/scripts/real-corpus.sh                  # build/real-corpus/summary.{json,md}
SCRY_LIMIT=300 SCRY_STRESS=1 scry/scripts/real-corpus.sh  # include the 3.8 MB parser
```

The checked-in result and the precision/false-positive follow-up list are in
`bench/real-corpus.md` (raw machine record: `bench/real-corpus.json`). There are only
two findings in 24 files and both are manually judged false positives; the report lists
the parse-recovery, exec-sink, bounds, points-to-argument and warning-noise gaps.

`scripts/project-corpus.sh` is the multi-file counterpart: it generates a
`compile_commands.json` for the synthetic `corpus/project/taint` project and each real
group, runs `scry project --taint` with the cache, and writes
`build/project-corpus/summary.{json,md}`. The synthetic ground truth is
`bench/project-corpus.truth.json`; the checked-in result is
`bench/project-corpus.{json,md}`. The real groups have no independent labels, so their
findings are a manual spot-check, not a precision/recall claim.

Limits: the shim is sequential (one parser, one tree, one file) and tree-sitter-c is the
only grammar. Threads, a native store shared across files, and tree-sitter queries are
the remaining S1 work.
