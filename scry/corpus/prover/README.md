# Dogfood corpus: no-flow proofs

Proofs about code the prover's author did not write, run with the `Scry.Prover`
branch (`scry-prover`) plus the real-code C# frontend (`agent/cs-real`, merged into
this branch because the prover branch predates the file-scoped-namespace fix). The
report is `wiz-notes/scry-prover-dogfood.md`.

| proof | code | claim | result |
|---|---|---|---|
| `p1-process-safe.sh` | `scry/corpus/csharp/taint/cwe78-process-safe.cs` (`Fixtures.Runner.Main`) | no `Console.ReadLine` value reaches `Process.Start` | `ok`, invariant 1 row |
| `p1b-crux-api.sh` | `real/BootstrapPartnerCredentialSeeder.cs` (`Crux.Api.Hosting…RunAsync`) | the same claim over a real Crux.Api namespace | **refused**: `mload` (8 loads); no `Console.ReadLine`/`Process.Start` in the unit either |
| `p1c-crux-api-vacuous.sh` | same file, `…EnsureAsync` | the same claim on a memory-free method | `ok`, but **vacuous**: `I = {}`, `SRC=0`, `SINK=0` |
| `p2-sqlcommand.sh` | `real/SqlReportProvider.cs` (`ReportService.Provider…FetchRrnsAsync`) | no caller-supplied value reaches a `SqlCommand`'s text | **refused**: `mload` (2 loads at the `SqlCommand` point) |
| `p3-header-processor.sh` | `real/CommunicationsWebhookEndpoints.cs` (`Crux.Api.Endpoints…SendGridMarketingWebhook`) | an unvalidated header value does not reach the webhook processor | `ok`, invariant 10 rows |
| `p3b-logpath.sh` | `real/LogFileReader.cs` (`Crux.Dashboard.Api…Resolve`) | no request-supplied name reaches a filesystem handle | **refused**: `mtainted` (a tainted location seed) |
| `p6-modern-store.sh` | `cwe78-modern-unsafe.cs` (`Crux.Api.Endpoints…ReportEndpoints.Run`) | the P1 claim on the modern C# twin | **refused**: `mstore`, although the analysis finds it (`FINDINGS=1`) |
| `p4-process-unsafe.sh` | `cwe78-process-unsafe.cs` | the P1 claim on the unsafe twin | **rejected**, `tainted(9,9) -> flow(9,10,9) -> sink(10,1,9)` |
| `p5-helper-safe.sh` | `helper/Files.cs` (`SafeWrite`) | no header value reaches the file write | `ok`, invariant 3 rows |
| `p5b-helper-unsafe.sh` | `helper/Files.cs` (`UnsafeWrite`) | the same claim on the unsafe twin | **rejected**, `tainted(6,7) -> flow(6,8,7) -> sink(8,0,7)` |

The two refusals are results, not crashes: the checker refuses a function whose EDB has
memory rows instead of accepting a claim it cannot justify. The note ranks that refusal
as the top friction.

## Build and run

The driver reads a `.cs` and its checked-in `.cst` spill, so the proofs need neither
tree-sitter nor .NET at run time:

```sh
scry/corpus/prover/build.sh          # builds scry/build/prover (needs the Wiz toolchain)
scry/corpus/prover/check.sh          # runs every proof and asserts the verdicts
```

Regenerate a spill with the native `scry-cst` tool (`scry/README.md`):

```sh
scry-cst FILE.cs > FILE.cst
```

`PROVER=/path/to/prover` overrides the binary.

## Provenance and caveats

* `real/` files are copied verbatim from the Nexus and ReportService checkouts, with two
  **text-only** normalisations forced by the frontend's byte/char span bug:
  `SqlReportProvider.cs` had its UTF-8 BOM stripped, and
  `CommunicationsWebhookEndpoints.cs` had its em dashes replaced by `-` (in strings and
  comments). `BootstrapPartnerCredentialSeeder.cs` and `LogFileReader.cs` are pure ASCII
  and unmodified. Without the normalisation the lowerer produces names such as
  `portService.Provider;\n.lReportProvider :…` and `ocessor.P.ocessAsync(e(`, and the
  analysis is about a different program.
* The SQL and log-path packs declare the *effect* of a real validation as a sanitiser
  (`Path.GetFullPath` for the log path). The EDB has no guard facts, so the certificate
  is only as strong as that assumption; the note ranks this as the second language gap.
* `p2` would prove the safety consequence of "every `SqlCommand` argument is a constant
  or a parameter bind" — no caller value reaches the text — not the positive statement.
  The proposition language cannot say "is a constant or a bind"; and the method is
  refused before the claim is even checked.
