# Prover corpus: no-flow proofs

Proofs about program shapes the prover's author did not write, run with the
`Scry.Prover` branch (`scry-prover`) plus the C# frontend. The report is
`wiz-notes/scry-prover-dogfood.md`.

The driver prints a **tagged verdict**: `proved`, `refuted` (with a provenance path),
`refused` (the certificate is not closed), `script-failed`, or `vacuous` (the claim's
selected source set or sink set is empty). A memory finding names its `store` and `load`
edges; a vacuous claim is never reported as proved.

| proof | code | claim | result |
|---|---|---|---|
| `p1-process-safe.sh` | `scry/corpus/csharp/taint/cwe78-process-safe.cs` (`Fixtures.Runner.Main`) | no `Console.ReadLine` value reaches `Process.Start` | `proved`, invariant 1 row |
| `p1b-field-service.sh` | `synthetic/RecordSeeder.cs` (`Fixtures.Hosting.RecordSeeder.RunAsync`) | the same claim over a method that reads a field and calls a service | **vacuous**: the memory coverage is exercised, but the unit has no `Console.ReadLine` and no `Process.Start` (`SRC=0`, `SINK=0`) |
| `p1c-vacuous.sh` | same file, `…EnsureAsync` | the same claim on the memory-free method | **vacuous** (`SRC=0`, `SINK=0`); the old rubber stamp is gone |
| `p2-sqlcommand.sh` | `synthetic/ReportProvider.cs` (`Fixtures.Data.ReportProvider.FetchAsync`) | every `SqlCommand` argument is a constant or a parameter bind (no caller value in the text) | `proved` with `--classify`; the field-load memory is covered, and no untrusted source reaches the command text |
| `p3-header-processor.sh` | `synthetic/EventEndpoint.cs` (`Fixtures.Requests.EventEndpoint.HandleAsync`) | an unvalidated request header does not reach the event processor | `proved` |
| `p3b-logpath.sh` | `synthetic/PathHelper.cs` (`Fixtures.Files.PathHelper.Resolve`) | no request-supplied name reaches a filesystem handle | **vacuous**: the lowered unit has no sink (`SINK=0`); this used to be a memory refused |
| `p6-modern-store.sh` | `cwe78-modern-unsafe.cs` (`Fixtures.Modern.CommandEndpoints.Run`) | the P1 claim on the modern C# twin | **refuted** through `store(2,23,25) -> load(2,31,35) -> flow(31,32,35) -> sink(32,1,35)`; the analysis found it and the prover can now witness it |
| `p4-process-unsafe.sh` | `cwe78-process-unsafe.cs` | the P1 claim on the unsafe twin | **refuted**, `src(9,9) -> flow(9,10,9) -> … -> sink(10,1,9)` |
| `p5-helper-safe.sh` | `helper/Files.cs` (`SafeWrite`) | no header value reaches the file write | `proved`, invariant 3 rows |
| `p5b-helper-unsafe.sh` | `helper/Files.cs` (`UnsafeWrite`) | the same claim on the unsafe twin | **refuted**, `src(6,7) -> flow(6,8,7) -> … -> sink(8,0,7)` |
| `p7-memcpy-safe.sh` | `c/memcpy-safe.c` (`main`) | every write is preceded by a check (the `memcpy` length `n` is guarded by `n <= 16` and the destination is 32 cells) | `proved (every write is preceded by a check)`; 1 guard row, 1 write use |
| `p8-memcpy-weak.sh` | `c/memcpy-weak.c` | the same cut, but the guard allows 64 into a 32-cell destination | **refuted**; the witness names `guard(...)`, the copy `use(...)` and the bound/capacity mismatch |
| `p9-memcpy-unguarded.sh` | `c/memcpy-unguarded.c` | the same cut with no check | **refuted**; the witness names the use and says there is no guard on the length register |
| `p10-prove-cli.sh` | the CLI itself (`scry-prove`) | the safe/unsafe C# pair, a hand-written certificate, a wrong one, a bad script, a vacuous method and a bad claim | exercises every exit status (`0` proved, `1` refuted/refused/script-failed, `2` usage, `3` vacuous) and the `--json` object |

The `synthetic/` fixtures are written for this corpus. They keep the shape each proof
exercises and are pure ASCII; no private source is checked in. `p2` runs with
`--classify`, which selects the `constantOrBound` property: no flow from the untrusted
sources (`src`, `retsrc`), while `param` flows are allowed. That is the logical form of
"every argument is a constant or a parameter bind": an argument reached by no untrusted
source is derived only from constants and parameters. The claim is about the safety
consequence, not the syntactic shape of the string.

The `c/` fixtures are the guards/bounds slice: the driver lowers them with the C
frontend, analyses `main`, adds the `guard`/`use`/`before` rows derived from
`Scry.Bounds`, and checks a `cut` claim. `p7` is the safe copy; `p8` weakens the guard
bound (64 into 32 cells, with the same source length so a spill generated for one
matches the other); `p9` removes the guard. The C spills are checked in when available;
`check.sh` regenerates a missing one with `scry-cst` (`SCRY_CST=/path/to/scry-cst`).
The proofs need neither tree-sitter nor .NET once the spills are present.

`--cut` uses every guard point in the EDB as the certificate; `--guards 2,3` selects a
subset, and the checker refuses a point with no guard row. A `cut` verdict is separate
from a no-flow verdict: "every write is preceded by a check" says nothing about which
values reach a sink.

## Build and run

The driver reads a `.cs`/`.c` file and its checked-in `.cst` spill, so the proofs need
neither tree-sitter nor .NET at run time:

```sh
scry/corpus/prover/build.sh          # builds scry/build/prover and scry/build/scry-prove
scry/corpus/prover/check.sh          # runs every proof and asserts the verdicts
```

`WIZ=/path/to/wiz` selects the compiler. `WIZ_BUNDLED=1` is for a packaged wiz wrapper
that already supplies its own `--cc`/`--cflags`/`--ldflags`: the script then does not
override them with `grail.local.wiz`'s paths.

`scry/build/scry-prove` is the `scry prove` command without the native parser, so the
corpus runs in a worktree that has no `native/` tree-sitter sources. The full CLI has the
same command as `scry prove`:

```sh
scry prove scry/corpus/csharp/taint/cwe78-process-safe.cs \
  --claim "noFlow Fixtures.Runner.Main" --pack scry/corpus/csharp/csharp.scry
# 0 proved; --json prints the invariant and the verdict; a rejection exits 1 or 3.
```

`SCRY_PROVE=/path/to/scry-prove` overrides the CLI binary for `p10`.

Regenerate a spill with the native `scry-cst` tool:

```sh
scry-cst FILE.cs > FILE.cst
```

`PROVER=/path/to/prover` overrides the driver; `SCRY_PROVE=/path/to/scry-prove`
overrides the CLI used by `p10`.

### Known drift (2026-11-20)

On `integration/train8` the untouched dogfood driver disagrees with two checked-in
expectations; this is analysis/lowering drift since the corpus was recorded, not the
`scry prove` slice (`lib/Scry/Prover.wiz` is append-only on that branch):

* `p2-sqlcommand` is **refuted** at `sink(15,0,...)` through `src(0,1)` (the
  `requestedDates` projection); the recorded result was `proved`. Either the lowering
  now lets the projected element reach the interpolated text, or the fixture needs a
  shape that does not rely on an unused lambda parameter.
* `p6-modern-store` is refuted with the same `store -> load -> sink` shape, but the
  lowering's point ids are `store(3,25,25) -> load(3,33,35) -> sink(34,1,35)` rather
  than the recorded `(2,23,25)/(2,31,35)/(32,1,35)`.

`p7`–`p9` need the C spills, which `scry-cst` (and therefore `native/`) produces; a
worktree without `native/` stops at `ensure_spill` with exit 2. `p10` runs before that
point and needs only the checked-in C# spills.

## Provenance and caveats

* The `synthetic/` fixtures are hand-written for the corpus: a record seeder, a
  report provider, an event endpoint and a path helper. The `.cst` files are their
  `scry-cst` spills. The C# fixtures under `scry/corpus/csharp/` are the shared frontend
  corpus.
* The SQL pack declares the usual untrusted sources (`Console.ReadLine`, environment,
  request headers/query) and the `SqlCommand` sinks. The synthetic provider builds its
  command text from constant fragments and `@date{i}` parameter names, so no untrusted
  value reaches the text.
* The path pack declares the effect of a real validation as a sanitiser
  (`Path.GetFullPath`). The EDB has no guard facts, so the certificate is only as strong
  as that assumption; the note ranks this as the second language gap.
* Memory is covered, but the certificate is still intraprocedural: `param`, `retsrc` and
  the `mtainted` location seeds are assumptions about callers/callees, as in
  `Scry.Certify`. A memory seed's producer is another function's store; the proof does
  not certify that store.
