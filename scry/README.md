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

The C# frontend's first slice (design: `CSHARP.md`) parses with
tree-sitter-c-sharp (fetched by Nix; `native/README.md`) through the same shim (`scry-cst FILE.cs` spills it);
`src/Scry/CsCst.wiz` views the store as a `Scry.Cst` and `src/Scry/CsLower.wiz` lowers
methods to Wil (receiver as argument 0, `using`-resolved BCL names). Its fixtures, their
spills and the rule pack are in `corpus/csharp/`; the tests are the `scry-csharp` group
(`tests =scry-csharp`).

```sh
cd scry
cp ../grail.local.wiz .         # this machine's toolchain (not committed)
grail build                     # check src/gen, build .grail/bin/scry, run the commands
grail test                      # schema, cst, native shim, preproc, codegen, CLI, parse --stats,
                                # taint, report, project, dynamic, fuzz spans, scale
grail build schema              # regenerate gen/C/Schema.wiz from node-types.json
grail build schema-check        # fail if the checked-in schema is stale
grail run scry -- parse --stats fixtures/hello.c
grail run scry -- parse --stats fixtures/broken.c
grail run scry -- facts fixtures/demo.facts.json
grail run scry -- query fixtures/demo.facts.json --kind call_expression
grail run scry -- explain fixtures/demo.facts.json 4
grail run scry -- fuzz-span fixtures/broken.c --json
grail run scry -- egraph fixtures/egraph-const.c
grail run scry -- egraph fixtures/egraph-const.c --rewrite
```

Commands: `facts`, `query --kind|--edge|--edge-src|--rel`, `explain`, `parse --stats` (a C source,
a `scry-cst` spill, or a JSON store), `cst` (JSON store → spill), `taint` (C →
Wil → taint → findings/SARIF), `dynamic` (compile/run under ASAN/UBSAN/coverage and
correlate with the static findings), `bench` (run the checked-in taint corpus and compare
findings with its manifest), `project` (a `compile_commands.json` multi-file C project:
cross-TU call graph, project EDB, per-file findings/SARIF and a TU cache), `report`
(one self-contained HTML page of the taint evidence), `fuzz-span` (map a fuzz artifact
to CST spans for the dynamic-evidence report), `repl` (the Wiz REPL with `Scry.Repl`
preloaded) and `egraph FILE.c [--fuel N] [--rewrite]` (C -> Wil ->
e-classes, then a deterministic fold/identity saturation report). The `egraph` report is
read-only: it does not change the CST, the Wil program or any Datalog fact. `--rewrite`
additionally runs `lib/Scry/EgraphExtract.wiz`, which extracts the saturated classes back
into a **checked** `Wil.Program` (straight-line functions, single-definition registers, no
registers outside the original right-hand side, strictly cheaper terms) and prints the
transformation report. That program is an optional input to a later analysis;
`lib/Scry/EgraphTaint.wiz` is the differential used by the tests, and Datalog stays
authoritative. `parse --stats` prints counts only; the perf agent owns throughput numbers.

## Optics and accessors

`lib/Scry/Optics.wiz` and `src/Scry/CstOptics.wiz` add a read-only `Getter`/`Fold`/
`Lens`/`Traversal` layer over the existing Wil, analysis, CST and fact types. It is
additive and non-mutating: no pass or existing query is migrated, and no second
representation is introduced. The CST/facts half is direct traversal (`Fold`), not a
lens per node; only Wil values have pure local rewrites (origins, data-dependence
variables). See `OPTICS.md` for the API, laws, what is deliberately an ordinary function,
and the limits. The new `query --edge-src L` command is the one additive CLI query:

```sh
grail run scry -- query fixtures/demo.facts.json --edge-src function
```

## `scry repl`: the Wiz REPL with `Scry.Repl` preloaded

`scry repl` is not a second shell. It is the ordinary **`wiz repl`** with `Scry.Repl`
imported as a prelude, so `:type`, `:load`, errors and EOF behave exactly as in the Wiz
REPL, and the Scry surface is ordinary Wiz definitions you can `#check`, compose and
wrap:

```sh
cd scry
scry repl                       # = wiz repl --prelude Scry.Repl -I src -I ../lib
scry repl tests/fixtures/taint-unsafe.c   # load the file before the first prompt
scry repl --script SESSION.wiz            # one command per line, for tests/CI
```

The module is `scry/src/Scry/Repl.wiz`, imported as `Scry.Repl`. Its state is a small
cache under `.scry-repl/` (`state.json`, the cached CST columns `uN.cst`, `findings.json`,
`taint.json`, `config.json`). `load` parses a C file with tree-sitter **once** and writes
the columns; `facts`, `queryKind`/`queryEdge`/`queryRel`/`queryEdgeSrc`, `functions`,
`calls` and `callers` read those columns and never re-parse the C. `taint` lowers the
cached columns once and records the findings; `taintPaths`, `findings`, `show`, `triage`
and `repro` read that record. A second `load` replaces the session (the previous unit is
forgotten); `loadDir` loads every `.c` under a directory and the accessors concatenate
their results.

Because the REPL is ordinary Wiz, effects run with `:run` (the Wiz REPL's compiled
runner), and the values are ordinary `List`/`Option` results:

```
wiz> #check Scry.Repl.load
Scry.Repl.load : String → IO Unit
wiz> def u := Scry.Repl.load "tests/fixtures/taint-unsafe.c"
wiz> :run u
loaded tests/fixtures/taint-unsafe.c (1 unit; use facts/query/functions)
wiz> def fns := Scry.Repl.functions
wiz> :run fns
functions: 1
  main
wiz> def cs := Scry.Repl.calls "system"
wiz> :run cs
calls system: 1
  main:6:3  system(cmd)
wiz> def t := Scry.Repl.taint
wiz> :run t
...
wiz> def ps := Scry.Repl.taintPaths
wiz> :run ps
...
wiz> def fs := Scry.Repl.findings
wiz> :run fs
f_0123456789abcdef  new  command-injection  system  tests/fixtures/taint-unsafe.c
wiz> def tr := Scry.Repl.triage "f_0123456789abcdef" "confirmed"
wiz> :run tr
f_0123456789abcdef: new -> confirmed
```

`facts` returns `List Scry.Stats`, `functions` `List String`, `calls` `List
Scry.Repl.CallSite`, `taintPaths` `List Scry.Repl.Finding`, `findings` `List String` and
`taint` the finding count, so a session can `List.filter`/`map`/`foldl` them, or define a
new helper. `jsonOn`/`jsonOff` switch the printed form to one JSON object per call (the
same schema names as `scry taint`/`scry findings`). `diff "BASE"` keeps the findings whose
sink line is in `git diff -U0 BASE`; `repro ID` runs a recorded finding under the
workflow reproducer.

Errors are printed and the session continues: a missing file, a parse error, a bad rule
pack or an unknown Wiz name does not end the REPL. `loadDir`/`--project` load several
units, but a query and the taint record are still per active unit; cross-file points-to
and a single project-wide store are the remaining work.

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

**Command sinks and exported entries.** The command-injection rule covers `system`,
`popen`, `execl`, `execlp`, `execv`, `execvp`, `execve`, `posix_spawn` and
`posix_spawnp`. `sink execl args` checks every argument, so the real
`execl("/bin/sh", "sh", "-c", cmd, NULL)` pattern reports the tainted word at argument
3; the non-variadic calls name their path/argv positions. A function with external
linkage, no caller in the translation unit, and no address taken (`p = f`, a `qsort`
callback) is an **exported C-ABI entry**: its parameters are sources, because an
external/Wiz caller supplies them. `main`, `static` functions, internally called
functions and callbacks keep the ordinary parameter summary, so the policy does not
turn every helper into a source. `tests/fixtures/taint-entry-*.c` and the
`tests/fixtures/taint-exec-*.c` pair are the positive/negative controls.

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
(`p = f()`), aliased parameters, and the `strcpy`-family copy model. `malloc`/`calloc`/
`realloc`/`free` are read from the external model table (`Scry.Models`), so `realloc` is
an allocation effect rather than havoc. Not modelled: `realloc`'s may-free of the old
object, external calls' memory effects outside the model table, heap shape (a linked list
through two allocation sites is two sets), context sensitivity, and offsets past one
`anyOff` level.

## External function models

`Scry.Models` is one table of libc/syscall effects: `source` (a written buffer or
`getenv`'s result), `sink` (a command/format/length/size argument), `sanitise` (a policy
sanitiser's result or in-place clean), `copy`/`copyArgs` (`strcpy`, `sprintf`'s formatted
destination), `alloc`/`free` (`malloc`/`calloc`/`realloc`/`free`) and the explicit
`unknown` fallback. A policy sanitiser is only applied when the pack names it
(`RulePack.trustsSanitiser`), so a pack that omits `sanitize` keeps the no-sanitiser
behaviour. The rule pack's own lines are applied first; model facts are a
deduplicated fallback, so `system` is not reported twice. A model sink makes the
`exec*` family's **variadic argv** a command sink (argument 3 of
`execl("/bin/sh", "sh", "-c", cmd)`, not only the path), `sprintf`'s format argument a
format-string sink, and `sprintf`'s formatted arguments a copy into the destination.

An external call with a pointer result or argument and no model is an explicit
`unmodelled-external` warning at the call point; its pointer result stays `Loc.unknown`,
so a store/load through it still propagates and warns `unknown-memory`. Read-only calls
(`strlen`, `strcmp`, …) have an empty effect list — modelled as pure, not unknown.

Fixtures and their expected results are in `tests/fixtures/mem-*.c` and asserted by
`tests/taint.wiz`: same-slot store/load (1 finding, path through `store`/`load`),
different slot (0), struct fields and a global field (2, and the sibling field 0), array
elements (1, sibling elements/arrays 0), a variable index (`a[i]` keeps the array, so 1
finding and no false positive on `b[i]`), heap (1), pointer-to-pointer (1), aliased
parameters (1 across two calls), `free` then use (1 finding + `use-after-free`), known
indirect target (1), unknown indirect target (0 findings + `unknown-indirect`),
returned pointer (1), `strcpy` into one array (1, the other array 0), and an unmodelled
external's pointer (1 finding + two `unknown-memory` warnings and one `unmodelled-external`).

**Boundary warnings now carry spans.** `Scry.Warning` has a `Wil.Span`, so a
`lowering-boundary` result points at the construct (a cast, `sizeof`, a skipped `goto`, …)
instead of the function definition. SARIF rule ids are namespaced (`scry/c/<rule>`,
`scry/lowering/boundary`, `scry/lowering/parse-recovery`, `scry/memory/<kind>`) and the
run declares
`columnKind: utf16CodeUnits` (the C slice is ASCII, where a byte column is a UTF-16
column; a non-ASCII source would need an explicit conversion).

A parser error is refused by default; `--allow-errors` analyses the recovered tree,
reports the `ERROR`/`MISSING` count, and adds a `scry/lowering/parse-recovery` warning.
Tree-sitter can wrap every declaration after a syntax error in one top-level `ERROR`
(the generated `old-wizard.c`/`droste.c` shape); the lowering unwraps those nodes and
keeps the partial functions and facts, then says how many functions it recovered. If
none can be recovered the warning says `unit not analysed` instead of returning a
silent empty result.

## Large files: limits, progress and partial results

The C → Wil → points-to → taint pipeline used to scale worse than linearly: the CST child
lookup copied the whole child column per node, token text was sliced with
`String.drop` (a `List Char`, so O(file) per identifier), and the origin map scanned the
source from byte 0 for every program point. The vendored tree-sitter-c grammar
(`native/tree-sitter-c/src/parser.c`, 3.9 MB, 1.1 M nodes) therefore never finished under
a 300 s limit. The lookup, slice and line-table paths are now O(children), O(span) and
O(points + lines); the fixpoint machinery is bounded and reports what it did.

```sh
grail run scry -- taint FILE.c --progress
grail run scry -- taint FILE.c --progress --timeout 60 --max-nodes 200000 --max-rounds 8
```

| option | default | contract |
|---|---|---|
| `--timeout SECS` | 300 | hard wall-clock limit; `0` disables. On expiry the run stops with a message and exit **124**, never a silent hang |
| `--max-nodes N` | 2 000 000 | refuse a CST larger than `N` *before* lowering, naming the count and the flag; `0` disables |
| `--max-rounds N` | historical bound | cap the points-to **and** summary fixpoints; a capped run is a sound lower bound and is marked `truncated` |
| `--progress` | off | one `scry: [stage] name elapsed=…` line per stage (and per ten functions in the summary fixpoint) on **stderr**; stdout stays the JSON/lines |

`--json` carries the contract in a `budget` object (`nodes`, `truncated`,
`pointsToRounds`, `pointsToComplete`, `summaryRounds`, `summaryComplete`, `notes`) next
to the findings. A capped fixpoint adds a `scry/budget/points-to-incomplete` or
`scry/budget/summaries-incomplete` diagnostic to the boundary list and SARIF, so a caller
cannot mistake a truncated run for a complete one. Every reported finding is still a
real derivation; only recall can be reduced.

Measured on this machine (`grail` build, cold-ish cache; wall time, informational;
the table is `scry/bench/scale.md`, "Function-heavy files", on the base commit):

| input | nodes | before | after (warm / cold) | peak RSS |
|---|---:|---:|---:|---:|
| `tree-sitter-c/src/parser.c` (3.9 MB, generated tables) | 1 110 871 | **timeout at 300 s** | **≈ 1.2–2.2 s warm, 6–7.5 s cold** | 654 MiB |
| `tree-sitter/lib/src/parser.c` (17 k nodes, one huge function) | 17 163 | 117.7 s | 50.3 s / 56.4 s | 34 MiB |
| `tree-sitter/lib/src/query.c` (34 k nodes, 113 functions) | 34 450 | 180.7 s | 15.6 s / 35–38 s | 71 MiB |

Parsing and building the store account for ≈ 1.7 s of the 3.9 MB case; the rest is the
lowering walk. One generated grammar function dominates the two tree-sitter runtime
files: rule evaluation of a single very large function is the remaining hot spot, and
`--timeout` (or a smaller `--max-nodes`) is the escape hatch.

`tests/scale.wiz` is the regression test: on a checkout with the vendored grammar it
asserts the node count, that the run is complete under the default limit, that
`--max-nodes` refuses cleanly, that `--max-rounds 1` returns a marked partial result, and
that the CLI's `--timeout 1` exits 124 with the timeout message and no stdout. When
`native/tree-sitter-c/src/parser.c` is absent it prints `scale: skip (… absent)` and
passes, so a bare tree stays green.

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
Markdown. The checked-in corpus is **S0/S2** (52 cases in
`scry/bench/corpus/manifest.json`): the existing
`tests/fixtures/taint-*.c` goldens plus hand-authored safe/unsafe pairs for CWE-78
(command injection), CWE-134 (format string), CWE-242 (`gets`) and CWE-120/121
(`strcpy`/`strcat`), and the external-model cases. S1/S3/S4 are optional external
corpora (`--extra DIR`); no third-party corpus is checked in.

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
The checked-in baseline (`scry/bench/baseline.json`, produced by
`grail run scry -- bench --update-baseline bench/baseline.json`) has **52 cases**:
TP/FN 32/0, TN/FP 17/1, unknown 2, TPR 100.00%, FPR 5.56%, precision 96.97%, 44/44
valid paths and checked certificates, and 62 boundary warnings (4 blocking, 3 cases).

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

## Diff-aware review (`--diff`, `--changed-lines`)

PR review needs the findings on the changed lines, not the backlog. `scry taint` can
filter against a unified diff:

```sh
scry taint FILE.c --diff origin/main                 # git diff -U0 origin/main -- FILE.c
scry taint FILE.c --diff HEAD --diff-context 2       # two unchanged lines either side
scry taint FILE.c --changed-lines saved.patch        # a saved unified diff (from a file)
scry taint FILE.c --diff all                         # no filter (the full report)
```

A finding is shown when its **sink line** is on a changed line, or when a step of its
source -> sink path is (a changed source/flow line keeps the finding visible). Everything
else is suppressed **with a count**: the summary says how many findings and warnings were
suppressed on unchanged lines. The default (no flag) is the full report, byte for byte;
`--diff all` is the same but says so. `--fail-on-finding` gates on what the diff shows,
so a pre-existing finding does not fail a PR; a finding with no origin ("unlocated") is
shown and still fails, because the filter cannot prove it is unchanged.

The mode is line-based and deliberately honest about what it cannot know:

* a file with no diff entry is treated as unchanged (all its findings are suppressed with
  a count, and the summary says the match failed; check the path spelling);
* a rename is a rename only when the patch says so (`rename from`/`to`, or `git diff -M`,
  which `--diff` passes); a pure rename has no changed lines;
* a binary diff has no line mapping, so its findings are shown with a note;
* an insertion that merely shifts a sink down one line does not mark the sink line as
  changed (git reports the inserted line); a deleted-and-re-added sink does;
* a path is a path of program points. A step in another function or hunk counts as a
  changed step, but the filter does not prove the path is still *reachable*: it is a
  review filter, not a new analysis. Losing a step (for example a source call removed)
  suppresses the finding, not silently: the suppressed count grows.

`--json` adds a `diff` object (mode, `filtered`, `file`, `matchedPath`, `matched`,
hunks, `addedLines`, `changedRanges`, and `shown`/`suppressed`/`unlocated` counts for
findings, boundary warnings and memory warnings); each shown finding/warning gets a `diff` verdict (`inChangedHunk`, `shown`,
`matchedBy` sink/path, and the line). SARIF stays **complete** in diff mode: suppressed
results are kept with `baselineState: "unchanged"` when the diff proves the line is
unchanged, in-diff ones are `"new"`, and no state is claimed when the diff cannot decide
(a binary file, no matching entry, a deleted file), so an upload diff never marks an
untouched finding as fixed. Every result carries
`partialFingerprints: {"scry/v1": "f_<16 hex>"}` (or `b_…` for a boundary warning), a
line-independent id built from the rule, normalized path, sink function/callee/argument
and path shape; moving a finding keeps the id, renaming the sink or changing the path
shape creates a new one. Two identical sinks in one function with the same path shape can
still collide (the id is a handle, not a proof of uniqueness).

## `scry report`: one self-contained HTML page

SARIF and JSON are for machines; a corpus review needs a page. `scry report` runs the
same pipeline as `scry taint` and writes one HTML file with an inlined stylesheet, no
JavaScript and no remote resource:

```sh
scry report FILE.c --out report.html
scry report DIR --out report.html --allow-errors
scry report FILE.c --diff origin/main --out review.html
scry report DIR --changed-lines saved.patch --out review.html
```

The page has a summary table (files, findings, checked/unchecked, boundary and memory
warnings, shown/suppressed), a sorted finding table, and one section per file. Each
finding shows its rule, severity, CWE, the coarse chain (`source → flow → sink`, or
`alloc → free → sink` for a use-after-free), its evidence (`static (L1)` plus
`certificate (L2, checked)` or `(L0, unchecked)`), the source excerpt with the sink line
highlighted and every path step numbered, and the diff verdict when filtering is on.
A directory is a corpus of **independent translation units**, not a project; use
`scry project DIR --taint` for a cross-TU call graph.

**Escaping is the whole game.** The C source is escaped exactly once (`&`, `<`, `>`, `"`,
`'`) into a text cell; there is no `innerHTML` and no script. A file containing
`<script>alert(1)</script>` renders that text. `tests/report.wiz` uses a fixture with
exactly that string, an ampersand and quotes, and asserts the raw tag is absent while
`&lt;script&gt;` is present. The page also has no external URL, so it cannot phone home.

**Deterministic output.** There is no timestamp, host name or elapsed time in the page.
Files and findings are sorted, and every finding anchor is its semantic workflow id
(`f_<16 hex>`, rule + normalized path + sink + path shape), never a line number, so two
runs over the same input are byte-identical and a line move keeps the link. A genuine
id collision (two identical sinks with the same path shape) gets a `-2`, `-3` anchor
suffix; the displayed id stays the semantic id.

`--diff BASE` is evaluated **per file**, so a directory page shows each file's own
suppressed count. The wording and counts come from `Scry.TaintCmd`'s diff helpers, not a
second filter. Suppressed findings and warnings stay on the page in a native `<details>`
block; a filter is not a deletion.

What the page does **not** claim: it is a rendering of one run's evidence, not a proof.
A clean file is not a proof of absence, a boundary warning is a documented gap rather
than a pass, and the page does not include dynamic evidence, SMT models or concolic
witnesses (those live in a `scry findings` bundle). It is static evidence only, and it
needs no JavaScript to read — so there is no client-side filtering, sorting or
collapsing beyond the browser's native `<details>`.

`tests/report.wiz` pins the tainted/safe/XSS fixtures, the sink and step spans, the
suppressed-count line, finding-id anchors and two-run byte identity. The reusable
renderer is `lib/Scry/Report.wiz`; the IO half is `scry/src/Scry/ReportCmd.wiz`.

## `scry dynamic`: observed execution evidence

`scry dynamic FILE.c` compiles and runs the file under AddressSanitizer /
UndefinedBehaviorSanitizer, parses crash/UB/leak events, resolves their first frame to a
Scry source span, and links each event to the static findings/memory warnings at the
same line (else the same function). With `llvm-profdata`/`llvm-cov` it also reports line
coverage and whether each static site's line executed.

```sh
grail run scry -- dynamic tests/fixtures/mem-free.c
grail run scry -- dynamic FILE.c --json --sarif out.sarif
grail run scry -- dynamic FILE.c --no-coverage --timeout 5
grail run scry -- dynamic FILE.c --witness witness.json   # S6a data contract
grail run scry -- bench --dynamic                         # the dynamic corpus
```

Dynamic evidence is **separate** from a static finding (`properties.kind = dynamic`,
`claim = none`) and is *observed*, not verified: a validated event needs a recognised
sanitizer signature and a frame in the analysed file; a clean run is not a proof of
absence. No compiler/sanitizer is a clean skip. The corpus (`bench/dynamic/`) covers the
prior-art tiers T1 CWE-78/134, T2 CWE-416/476, T3 CWE-190/787/121 and a leak; CWE-120/
242/362 are out of scope for a witness. `--witness` records the future S6a concolic
witness (path condition, model, assumptions, budget) without solving or promoting it;
`wiz-notes/scry-dynamic.md` has the design and the counts.

## Fuzzing the C front end (dynamic evidence)

`fuzz/` runs a bounded libFuzzer campaign over the vendored C shim and tree-sitter,
with `-fsanitize=fuzzer,address,undefined`. The target checks the struct-of-arrays
contract (preorder ids, parent/CSR/edge agreement, in-range ids, spans inside the input,
`ERROR`/`MISSING` flags); a violation, ASan report or UBSan report is minimised and
deduplicated by stack signature. `scry fuzz-span FILE [--offset N] [--json]` maps an
artifact to the same `start`/`stop` span shape the static findings use, including the
smallest CST node containing an invariant's `input_offset`.

```sh
cd scry
./.grail/bin/scry bench --no-timing --json build/bench.json
python3 fuzz/run.py --build --runs 5000 --time 15 --seed 20261115 \
  --static build/bench.json --out build/fuzz
```

The driver seeds from `bench/corpus/**/*.c` plus the taint fixtures, sweeps the static
corpus once under the same sanitizers, and writes `build/fuzz/dynamic.json` and
`dynamic.md` with a `dynamic` evidence section beside the static `scry bench` cases. A
missing clang/libFuzzer is a clean skip (exit 0). Finding no crash in a bounded run is
**not** evidence of safety; the target covers the C parser boundary, not the Wiz
lowering/taint pipeline. `fuzz/README.md` has the schema, the exact bounds and the
limits.

`tests/fuzz.wiz` checks the span mapper and the JSON shape on `fixtures/broken.c`. The
first harness run found and this branch fixes a 744-byte leak on every successful parse
in `native/ts_shim.c`; that is a dynamic finding, not a clean bill of health.

Limits: the shim is sequential (one parser, one tree, one file) and tree-sitter-c is the
only grammar. Threads, a native store shared across files, and tree-sitter queries are
the remaining S1 work.

## Real CVE corpus (opt-in)

`bench/cases/cve-*/` holds twelve reduced reproducers of historical CVEs (CWE-78/134/22/
416/476/190/787/125), each with its upstream vulnerable revision, licence and expected
result in `case.json`. `scripts/cve-bench.sh` compiles each one with a plain C compiler,
runs `scry taint` per case with `--timeout`/`--max-nodes`, and records wall time, peak
RSS, expected/matched findings and extras. It is **opt-in only**: it is not part of
`scry bench`, `grail test`, the fast gate or CI, and one case takes about a minute.

```sh
cd scry
scripts/cve-bench.sh                       # build/cve/summary.{json,md}
scripts/cve-bench.sh --case cve-2020-1752  # one case
```

**No third-party code is checked in.** Each case directory holds our `harness.c` (the
reduction) and `upstream.json`, which pins every source (tags resolved to commits, a
SHA-256 per file) and the line ranges of the few spans that are verbatim upstream code;
`scripts/cve-fetch.py assemble` fetches them into a content-addressed cache and writes
the compilable `case.c` files under `build/cve-src/`. The bench drivers run it first.
Of the 38 case files (v1 and v2), 8 contain upstream spans (214 lines in all); the other
30 are rewritten reductions and fetch nothing.

The checked-in table, the honest precision/recall (0/6 in-scope CVEs detected today),
the per-case miss reasons and the top analysis gaps are in `bench/cve.md`. Treat the
synthetic `scry bench` rates as a regression corpus, not as real-world recall.

## `scry findings`: exploration → triage → repro → verify

`scry findings` is the workflow/evidence layer over the existing analysis. `scan` calls
`Scry.analyzeFile` (**the same pipeline as `scry taint`**, not a second analysis) and
writes a local JSON store plus one artifact directory per finding:

```sh
grail run scry -- findings scan FILE.c --db scry-workflow/findings.json \
  --artifacts scry-workflow
grail run scry -- findings list --state confirmed
grail run scry -- findings show f_0123456789abcdef
grail run scry -- findings triage f_0123456789abcdef --state confirmed --reason 'ASAN repro'
grail run scry -- findings repro f_0123456789abcdef --sanitize both
grail run scry -- findings verify f_0123456789abcdef
```

The **semantic id** is `f_<16 hex>` over the rule id, normalized path, sink function,
sink callee + argument and the coarse path shape. Line/column, program points,
timestamps and rule-array indices are excluded, so a line move keeps the id; a renamed
sink or a changed path shape is a new id. A separate `lineHash` is the
GitHub-compatible primary-line identity. The **triage machine** is
`new -> triaged -> confirmed -> fixed`, with `false-positive` and reopen edges; an
illegal edge is an error. `fixed` is a triage decision, never an automatic result of
`verify`.

`repro` selects or generates a deterministic harness/input, builds with
`-fsanitize=address,undefined` when the compiler accepts it (and records a fallback to an
uninstrumented build when it does not), runs under `timeout`, and stores the exact
commands, exit status, stdout/stderr and the first sanitizer lines as `dynamic.json`.
`verify` re-runs the same analysis and the stored repro and reports the verdict
`not-reported-and-repro-clean` (or `...no-dynamic`), `still-reported`,
`not-reported-but-repro-crashed`, or `inconclusive`: **"not reported by this run" is
never "absent from the program"**. The static certificate and the dynamic trace are
separate evidence items; see `wiz-notes/scry-workflow.md`.

A concolic-witness slot is reserved for the future S6a slice
(`wiz-notes/prior-art/symbolic-execution.md` §11): `repro --witness FILE` accepts a
`scry-workflow-witness/1` document only when its `authority` is L2/L3 and it is
`validated`, uses its `input` as the deterministic input, and records its path condition
and model. The prototype does **not** run symbolic execution.
