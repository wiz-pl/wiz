# Joern gap fixtures (2026-11-19)

Two corpus cases ported from Joern's `csharpsrc2cpg` tests, recorded as
characterization tests for known scry gaps. They are **not** claims of support: the
golden records what scry does today, then the case reports itself skipped with the gap
as the reason. If the gap is fixed the golden changes, the case fails, and the golden
and `.github/skip-allowlist.json` entry must be updated together.

Full comparison: `wiz-notes/scry-vs-joern-2026-11-19.md` (Joern commit
`4cd5cb11b0ed125a8db9867c5f2f46449a6fb79c`).

## `lower/toplevel.cs` (Joern `TopLevelStatementTests.scala:9`)

Top-level statements have no synthetic `<Main>$` in scry. The file lowers to **0
functions and 0 warnings**; a `Process.Start` at top level is invisible. The golden
`toplevel.wil` is empty on purpose.

## `lower/lambda.cs` (Joern `LambdaTests.scala:11`)

A lambda is an opaque `fnptr $lambda:<n>` and its body is not lowered. `Select(x => x *
x)` keeps only the `Select` call; `cmd => Process.Start(...)` keeps no `Process.Start`
call at all, so the CWE-78 analysis has no finding for it. The golden `lambda.wil` has
the two lowered functions and the four warnings.

## Regenerating

```sh
cd scry
.grail/bin/scry-cst corpus/csharp/lower/toplevel.cs > corpus/csharp/lower/toplevel.cst
.grail/bin/scry-cst corpus/csharp/lower/lambda.cs   > corpus/csharp/lower/lambda.cst
```

Goldens are written by `SCRY_CS_WRITE=1 tests =scry-csharp`, which writes the files and
fails, so a new golden is reviewed in the diff (the same rule as every other C# golden).
