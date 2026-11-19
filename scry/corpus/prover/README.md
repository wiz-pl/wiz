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

The `synthetic/` fixtures are written for this corpus. They keep the shape each proof
exercises and are pure ASCII; no private source is checked in. `p2` runs with
`--classify`, which selects the `constantOrBound` property: no flow from the untrusted
sources (`src`, `retsrc`), while `param` flows are allowed. That is the logical form of
"every argument is a constant or a parameter bind": an argument reached by no untrusted
source is derived only from constants and parameters. The claim is about the safety
consequence, not the syntactic shape of the string.

## Build and run

The driver reads a `.cs` and its checked-in `.cst` spill, so the proofs need neither
tree-sitter nor .NET at run time:

```sh
scry/corpus/prover/build.sh          # builds scry/build/prover (needs the Wiz toolchain)
scry/corpus/prover/check.sh          # runs every proof and asserts the verdicts
```

`WIZ=/path/to/wiz` selects the compiler. `WIZ_BUNDLED=1` is for a packaged wiz wrapper
that already supplies its own `--cc`/`--cflags`/`--ldflags`: the script then does not
override them with `grail.local.wiz`'s paths.

Regenerate a spill with the native `scry-cst` tool:

```sh
scry-cst FILE.cs > FILE.cst
```

`PROVER=/path/to/prover` overrides the binary.

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
