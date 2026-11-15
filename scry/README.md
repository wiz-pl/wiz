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
(`p = f()`), aliased parameters, and the `strcpy`-family copy model. `malloc`/`calloc`/
`realloc`/`free` are read from the external model table (`Scry.Models`), so `realloc` is
an allocation effect rather than havoc. Not modelled: `realloc`'s may-free of the old
object, external calls' memory effects outside the model table, heap shape (a linked list
through two allocation sites is two sets), context sensitivity, and offsets past one
`anyOff` level.

## Null dereference (S5 alarm, opt-in)

`Scry.Nullness` wires the S5 abstract-interpretation alarm (`Scry.AiFixpoint`'s
`Alarm.nullDeref`) to Wil and therefore to `scry taint`. It builds the `ACfg` of each
function, runs the same worklist/fixpoint engine, and reports a
`scry/memory/null-dereference` warning at a load or store through a pointer that may be
null:

* a failed allocation (`malloc`/`calloc`/`realloc`), a `fopen`/`getenv` result, or any
  other call result that is dereferenced without a check;
* a pointer set to `NULL` and used without a guard;
* a pointer that is **not** an access through a parameter: a parameter is assumed to be a
  valid object at entry. That is the documented false-negative boundary; nullness does not
  flow into a callee.

The check-kills-null rule is the branch condition: `if (p)`, `if (p != NULL)` and
`if (!p)` refine nullness on each edge, so an early return removes the null value from the
path that reaches the dereference. A constant-false branch is pruned before alarms are
read (the fixed CVE-2017-7659 control: the helper always returns `APR_ENOMEM`, so
`if (status == APR_SUCCESS) { req->method; }` is unreachable).

**Decision: opt-in.** `scry taint --null-deref` runs it (`Scry.analyzeWithNull` in the
library); the default `scry taint` does not. Unchecked allocations are common in real C,
so the pass adds a warning on every `p = malloc(...); p->x`; keeping it off preserves the
default pack's pinned results and lets a user choose the diagnostic. The CVE-476
measurement below runs with the flag. Functions longer than `Scry.maxNullPoints` (300
program points) are skipped: the list-based worklist is a prototype and the pass must not
turn a one-minute CVE analysis into a ten-minute one.

## Path traversal (opt-in pack)

`lib/Scry/rules/path-traversal.scry` is the default pack **plus** a `path-traversal`
rule: taint from `getenv`/`read`/`recv`/`fgets`/`getline`/`fread` or C's `argv` reaches
`open`, `openat`, `creat`, `fopen`, `freopen`, `stat`/`lstat`, `unlink`, `remove`,
`rename`, `chdir`, `opendir`, `access`, `mkdir` or `rmdir`. Run it with
`--rules ../lib/Scry/rules/path-traversal.scry`.

`source argv result` is a pack directive, not a call pattern: it seeds the second
parameter of `main` as a source. It is in this pack only, so the default pack's results do
not change.

`realpath` is a model (`Scry.Models`): it sanitises its **result** and the destination it
writes (argument 1), never its input. `realpath(user, buf); open(buf)` is clean;
`realpath(user, buf); open(user)` is still reported; `p = realpath(user, 0); open(p)` is
clean.

**Decision: opt-in.** A path API is not a bug by itself, and the rule needs a source
policy (`argv`) that would change the default pack's behaviour. The default pack keeps
its four rules and its pinned counts; the path pack is a deliberate `--rules` choice.
`tests/fixtures/path-*.c` and `tests/taint.wiz` cover the vulnerable/`realpath` pairs,
including the "sanitiser result used, input still used" control.

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
`scry/lowering/boundary`, `scry/memory/<kind>`) and the run declares
`columnKind: utf16CodeUnits` (the C slice is ASCII, where a byte column is a UTF-16
column; a non-ASCII source would need an explicit conversion).

A parser error is refused by default; `--allow-errors` analyses the recovered tree and
reports the `ERROR`/`MISSING` count.

`tests/native.wiz` checks the shim on `fixtures/hello.c`: 55 nodes, 54 edges, the root
span `[0,95)`, parent/child/next-sibling links, and that `fixtures/broken.c` is refused
by `parseChecked` (tree-sitter's recovery tree has 2 `ERROR`/`MISSING` nodes).

## `scry bench`: the taint corpus and metrics

`scry bench` runs the same pipeline as `scry taint` over `bench/corpus/manifest.json`,
compares the findings with the manifest's expectations, and writes stable JSON and
Markdown. The checked-in corpus is **S0/S2** (48 cases on this branch): the existing
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
The checked-in baseline on this branch is **48 cases**: TP/FN 30/0, TN/FP 15/1,
unknown 2, TPR 100.00%, FPR 6.25%, precision 96.77%, 35/35 valid paths and checked
certificates, and 45 boundary warnings (4 blocking, 3 cases).

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
