# Differential pipelines (COMP-02)

The corpus and harness live in [`Tests/Differential.lean`](../Differential.lean); the CI
group is [`Tests/Groups/Differential.lean`](../Groups/Differential.lean).  This directory
holds the golden baseline (`baseline.tsv`) and this note.

```sh
lake build wiz tests
scripts/differential.sh                      # compare with the baseline
scripts/differential.sh --report /tmp/diff.md
scripts/differential.sh --case arith-big --pipeline wiz-c-rc
scripts/differential.sh --update             # rewrite baseline.tsv (review the diff!)
```

`lake test -- '=differential'` runs the same corpus as one test case per (program,
pipeline), so CI reports every pass and skip separately.

## Pipelines

| name | what runs |
|---|---|
| `lean-c` | Lean frontend → erasure → IR → C (`Build.build`, `llvm := false`), run with the C runtime and GMP |
| `lean-llvm` | the same, through `llc` and LLVM IR |
| `wiz-c-gc` | `selfhost/*.wiz` compiler → C → `selfhost/rt.c` with Boehm GC |
| `wiz-c-rc` | the same compiler with `--rc` (Perceus reference counting, leak check at exit) |
| `ir-interp` | the Lean frontend's `#run`, i.e. `IRRun`'s reference-counted interpreter on a checked heap |

A pipeline is started only if its tool is available.  No `llc`, no `--gc-cflags`, no
`gmp.h`, or no C compiler gives **skip** with a reason (a skipped case is not a pass).
A corpus case can also name a pipeline it cannot exercise (for example the IR interpreter
does not run an IO `main`, and the self-hosted frontend has no type classes yet); that is
an explicit skip with a written reason, not a silent pass.

## Corpus

Fifteen small programs:

* arithmetic: factorial, large `Nat` values, division, powers and bit operators;
* data: lists, inductive trees, arrays, `StrMap`, strings;
* IO: multiple `IO.println` lines, plus `Process.exit`;
* classes: dictionary dispatch in the Lean pipelines and the interpreter;
* FFI: `extern "strlen"` with a C header;
* errors: type mismatch, unknown identifier, linearity/quantity error;
* compile-only: a structure and a string program, comparing normalized generated code.

Run cases define `out : Nat` and print it, so the interpreter's `#run out` and the compiled
programs produce the same decimal text.  A rejected case must report an error in every
pipeline that has a frontend; the exact message is pinned per pipeline.

## Baseline and report

`baseline.tsv` is tab-separated, with a comment header:

```
case<TAB>pipeline<TAB>verdict<TAB>exit<TAB>observed<TAB>note
```

* `verdict` is `pass`, `skip` or `diff`; `exit` is the program's exit code (0 when not
  run);
* `observed` is exact stdout for a run, the normalized diagnostic text for a reject, and
  a 64-bit hash of the normalized generated code for a compile-only case;
* `note` is the skip reason or a failure explanation.

`scripts/differential.sh` prints a Markdown report: a matrix of cases × pipelines, then
the skips and diffs with their notes.  `--report FILE` writes it to a file.

`--update` rewrites the baseline from the current machine.  Do it deliberately, on a
machine with the full toolchain, and read the diff: a changed hash, message or stdout is
the signal the harness exists to produce.

## False-difference filters (explicit and small)

* stdout and exit codes are exact.  Trailing whitespace in diagnostics is stripped;
  positions are not included in the Lean messages (the harness records `Message.text`,
  not `Message.render`, so the same message does not move when a line is added above).
* self-hosted diagnostics are the `error…` lines on stderr, with the case's temporary
  directory replaced by `<tmp>`; whitespace is trimmed.
* Lean generated C is cut at `/* ---- generated ---- */` so the runtime and foreign glue
  (which are not code-generator output) do not enter the hash.  Full-line comments, blank
  lines and trailing whitespace are dropped; nothing inside a line is rewritten, so string
  literals remain significant.
* LLVM generated code drops full-line `;` comments, blank lines and trailing whitespace.
* There is no cross-pipeline equality check for diagnostics: the Lean and self-hosted
  frontends word errors differently.  Each pipeline's exact message is pinned in the
  baseline, and every reject case must at least contain its `expectedDiag` fragment.
