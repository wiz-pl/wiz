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
a `scry-cst` spill, or a JSON store), `cst` (JSON store → spill), and `taint` (C →
Wil → taint → findings/SARIF). `parse --stats` prints counts only; the perf agent owns
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

Limits: the shim is sequential (one parser, one tree, one file) and tree-sitter-c is the
only grammar. Threads, a native store shared across files, and tree-sitter queries are
the remaining S1 work.
