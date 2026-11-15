import Tests.FuzzDiff

/-!
# The deterministic differential fuzzer's test group

The **fast PR subset** of `Tests/FuzzDiff.lean`: a fixed seed (`fastSeed`), four generated
kernel terms judged by both kernels, and four generated programs run by Lean→C and the IR
interpreter.  Wiz→C is excluded here (it builds the self-hosted compiler, about six
minutes); `scripts/fuzz-diff.sh --nightly` and `.github/workflows/fuzz-diff.yml` run the
full campaign, with Wiz→C and shrinking.

`Tests/FuzzDiff/corpus.tsv` pins the cases; a corpus row that no longer replays fails the
third case (a generator change must be deliberate).
-/

namespace Tests.FuzzDiff

def group : Group where
  name := "fuzz-diff"
  exercise := "deterministic differential fuzzing of the kernels and compilers"
  shard := "fuzz-diff"
  cases := [
    { name := "the Lean kernel and Kernel.wiz agree on generated terms (fast seed)",
      run := fun _ => fastTermCase },
    { name := "Lean→C and the IR interpreter agree on generated programs (fast seed)",
      run := fun _ => fastProgramCase },
    { name := "the checked-in corpus replays", run := fun _ => replayCorpusCase },
    { name := "the shrinker reduces a failing choice sequence", run := fun _ => shrinkSelfTest }
  ]

builtin_initialize registerGroup group

end Tests.FuzzDiff
