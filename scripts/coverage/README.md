# Coverage scripts (research)

Two read-only measurement tools. Neither is wired into CI: the first needs a clang/LLVM
toolchain and produces generated-C coverage, the second is a static lexical map. The
findings, numbers and raw reports are in `/workspace/wiz-notes/test-coverage.md` (not in
this checkout).

## `wiz-c-coverage.sh` — one Wiz program, generated-C coverage

```sh
# clang must match llvm-cov's major version; `wiz build` needs GMP's headers and library
WIZ_COV_CLANG=/nix/store/.../bin/clang \
WIZ_COV_LLVM_COV=/nix/store/.../bin/llvm-cov \
WIZ_COV_PROFDATA=/nix/store/.../bin/llvm-profdata \
WIZ_COV_CFLAGS=-I/nix/store/...-gmp.../include \
WIZ_COV_LDFLAGS=-L/nix/store/...-gmp.../lib \
  scripts/coverage/wiz-c-coverage.sh examples/array.wiz /tmp/array-coverage
```

`wiz build -o OUT` writes the generated C to `OUT.c` (`Wiz/Compiler/Build.lean:155`), so
the script builds with `-fprofile-instr-generate -fcoverage-mapping`, runs the program,
merges the profile and writes `report.txt`, `functions.txt`, `show.txt`, `export.json`,
`summary.txt` and `commands.txt` under the output directory. `wiz-c-coverage.py` is the
analyzer it calls.

The C backend emits no `#line` directives, so the output is generated-C coverage. The
summary separates the runtime (pasted at the top of every `main.c`) from the generated
declarations (after `/* ---- foreign functions ---- */`) and lists the generated
functions that executed, with their demangled Wiz names.

## `test-lib-map.py` — static test-to-library reach

```sh
scripts/coverage/test-lib-map.py                 # human table
scripts/coverage/test-lib-map.py --markdown      # two Markdown tables + summary
scripts/coverage/test-lib-map.py --json          # machine-readable
scripts/coverage/test-lib-map.py --root DIR      # another checkout
```

It walks `lib/**/*.wiz` for declarations, the import graph over `lib`, `hdl/src`,
`scry/src`, `selfhost` and `drafts/feral/lib`, and the corpus (`Tests/**`,
`examples/**`, `hdl/examples/**`, `drafts/feral/**`). `direct` is an `import M` line;
`closure` is transitive reachability; `lex` is a qualified-name token hit (an upper
bound: comments count); `any` is the weaker last-component hit; `group files` counts
`Tests/Groups/*.lean` files that import the module or contain one of its qualified
declaration names. It is a static map, not an execution profile.
