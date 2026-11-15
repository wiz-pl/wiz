# `fuzz-diff`: deterministic differential fuzzing

`Tests/FuzzDiff.lean` generates terms and programs from a **seed** and a **choice
sequence**, then compares the pipelines that must agree:

| question | reference | tested against |
|---|---|---|
| is a closed term accepted, and what is its normal form? | the Lean kernel | `selfhost/Kernel.wiz` (`Kernel.wiz`, in `Tests.FalseFuzz`) |
| what does a program print? | Lean frontend + C backend | the self-hosted compiler + C backend (`selfhost/*.wiz`) |
| what does a program print? | Lean frontend + C backend | the Lean frontend's IR interpreter (`#run`) |

A skip is not a pass. With no C toolchain (or no Boehm GC for the self-hosted backend)
the affected pipeline is reported as skipped and the run does not pretend otherwise.

## Running it

```sh
lake build wiz tests

# the fast PR subset (fixed seed, no self-hosted compiler): about two minutes
lake test -- '=fuzz-diff'

# one campaign; the seed and counts are printed and replayable
.lake/build/bin/tests --fuzz-diff --seed 20261115 --terms 8 --programs 16

# a full one, with Wiz→C and shrinking
.lake/build/bin/tests --fuzz-diff --seed 20261115 --terms 16 --programs 32 --shrink

# one case again
.lake/build/bin/tests --fuzz-diff --replay term 20261115 3 1,2,0,...
.lake/build/bin/tests --fuzz-diff --replay program 20261115 5 2,1,0,...
```

`--no-wiz` omits the self-hosted compiler, which is useful for a quick run. `WIZ_FUZZ_COMPILER=/path/to/compiler` uses an already built self-hosted compiler;
otherwise it is built once from `selfhost/*.wiz` and cached under `/tmp` by the **source
hash**, so editing the harness does not rebuild it.

`scripts/fuzz-diff.sh --nightly` picks today's date as the seed (printed, so a failure
is replayable), runs the full campaign and writes a report. The scheduled workflow
`.github/workflows/fuzz-diff.yml` runs that. `scripts/fuzz-diff.sh --fast` is the same
subset as the test group.

## The fast fragment

The fast subset compares term **verdicts**; the normal forms are compared in the full
campaign (`--nf`, on by default except under `--fast`), because a normal form can be much
more work than a check and a verdict difference is already actionable.

The term side deliberately stays in a fragment where the kernels are expected to agree:
closed types over `Unit`, `Enum`, `Empty`, `Nat`, `Nat × Nat`, `Nat → Nat` and `Nat = Nat`,
without sizes, `ν`, casts, descriptions, proof markers or linear/erased binders. Those
constructs have pinned differences (`Tests/FalseFuzz`, `Tests/Prop`); a run that reaches
them would be a re-test of that list, not a new signal. A generated term outside the
fragment is regenerated.

The program side covers `Nat`, `Bool`, `List Nat`, `Option Nat`, `Nat × Bool` and a
recursive `Tree`. Every generated program is accepted by the Lean
frontend first; a rejected one is a **generator** finding, not a compiler difference.

## Shrinking and the corpus

A finding is shrunk by delta-debugging its choice sequence: drop runs of choices, zero
them, halve them, and keep the smallest sequence that still fails (kernel candidates are
batched into one `Kernel.wiz` program). The replay command printed with every finding is
the shrunken sequence.

Every generated case is written to `.lake/fuzz-diff/corpus-cache.tsv` (unless
`--no-cache`), keyed by `kind seed index`, and `Tests/FuzzDiff/corpus.tsv` is the
checked-in corpus used by the fast subset. Regenerate it deliberately with
`tests --fuzz-diff --fast --update-corpus` and review the diff: choice sequences are
generator output, so a change there is a change of the generated cases.

## Last full run

Seed `20261116`: 8 generated terms (16 kernel judgments), 24 programs (24 Lean→C, 24
Wiz→C, 21 IR; the pair focus is compiler-only), **0 findings, 0 skipped**.
Seed `7`: 16 terms (32 kernel judgments), **0 findings**.  The fast seed `20261115` runs
4 terms (verdicts) and 4 programs; the checked-in `corpus.tsv` is its replay set.

## False differences

* Program output is compared exactly (after trimming the interpreter's final newline).
* Diagnostics are not compared across frontends: a rejected generated program names the
  frontend and the message, but not a per-pipeline pinned wording.
* Generated programs are well typed by construction; the generator's only type-directed
  device is the small `PTy` language in `Tests/FuzzDiff.lean`. An ill-typed generated
  program is a harness bug and is reported as such.
* `Nat` arithmetic follows the Prelude's definitions in both frontends. Division and
  modulus are always given a `Nat.succ` denominator, so a division by zero is not a
  difference either implementation happens to define differently.
