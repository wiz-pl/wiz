# Joern gap fixtures (2026-11-19)

Corpus cases ported from Joern's `csharpsrc2cpg` tests. `lower/toplevel.cs` now
lowers (the gap is closed); `lower/lambda.cs` remains a characterization test for a
known scry gap. The lambda case is **not** a claim of support: the golden records what
scry does today, then the case reports itself skipped with the gap as the reason. If
the gap is fixed the golden changes, the case fails, and the golden and
`.github/skip-allowlist.json` entry must be updated together.

Full comparison: `wiz-notes/scry-vs-joern-2026-11-19.md` (Joern commit
`4cd5cb11b0ed125a8db9867c5f2f46449a6fb79c`).

## `lower/toplevel.cs` (Joern `TopLevelStatementTests.scala:9`)

Top-level statements become a synthetic `toplevel_Program.<Main>$` method with a
`string[] args` parameter (Joern's `<file>_Program.<Main>$` naming). The file's
declarations keep their own scope: `ReportScope` is still `ReportScope`, not a member
of the synthetic class. A top-level local function becomes a nested static function,
`toplevel_Program.<Main>$.<Name>`, and may be called before its declaration. A
`Process.Start` at top level is now a call in that method, so the CWE-78 analysis can
report it.

## `lower/lambda.cs` (Joern `LambdaTests.scala:11`)

A lambda is an opaque `fnptr $lambda:<n>` and its body is not lowered. `Select(x => x *
x)` keeps only the `Select` call; `cmd => Process.Start(...)` keeps no `Process.Start`
call at all, so the CWE-78 analysis has no finding for it. The golden `lambda.wil` has
the two lowered functions and the four warnings.

## Regenerating

```sh
cd scry
.grail/bin/scry-cst corpus/csharp/lower/toplevel.cs       > corpus/csharp/lower/toplevel.cst
.grail/bin/scry-cst corpus/csharp/lower/toplevel-async.cs > corpus/csharp/lower/toplevel-async.cst
.grail/bin/scry-cst corpus/csharp/lower/toplevel-class.cs > corpus/csharp/lower/toplevel-class.cst
.grail/bin/scry-cst corpus/csharp/lower/lambda.cs         > corpus/csharp/lower/lambda.cst
```

Goldens are written by `SCRY_CS_WRITE=1 tests =scry-csharp`, which writes the files and
fails, so a new golden is reviewed in the diff (the same rule as every other C# golden).
