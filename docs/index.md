# Wiz documentation

The standard library's API documentation is published from `master` at
<https://wiz-pl.github.io/wiz/docs/> (one page per module, with interactive signatures;
the [API index](https://wiz-pl.github.io/wiz/docs/api.html) lists every module and
declaration, and search covers names, doc comments and signatures; docs/building.md,
"Documentation site"). The site's root is a landing page
(<https://wiz-pl.github.io/wiz/>) and <https://wiz-pl.github.io/wiz/playground/> is a
static playground that runs the self-hosted checker in the browser;
<https://wiz-pl.github.io/wiz/bench/> is the benchmark page, generated from the JSON
checked into the repository. This file indexes the repository's documentation; the
published `/docs/` is generated from `lib/` by `wiz doc --lib`.

* [install.md](install.md): installing Wiz with tower or Nix, editor setup, a first
  grail package, troubleshooting
* [tour.md](tour.md): a tour of the language for people who know a little functional
  programming; [`notebooks/tour.ipynb`](notebooks/tour.ipynb)
  ([exported page](notebooks/tour.html)) is the same tour as a runnable notebook
* [stability.md](stability.md): what a release promises (0.1.z)
* [release.md](release.md): making a release (checklist, tagging, smoke test)
* [CHANGELOG.md](../CHANGELOG.md)
* [building.md](building.md)
* [tools/wiz-mcp/README.md](../tools/wiz-mcp/README.md): a stdlib-only MCP server that
  gives an MCP client (OpenCode, Claude Code, Zed) type checking, formatting, building,
  and the language server's diagnostics, hover and tactic state
* [bench/README.md](../bench/README.md): the standard-library benchmark harness, its
  modes and how to compare two builds; the published page is generated from the JSON
  the harness writes (web/build-bench.py)
* [ci-runner.md](ci-runner.md): a self-hosted runner for the heavy CI shards
* [exercises.md](exercises.md): generating the exercise tree from this one
* [hardware.md](hardware.md): hardware in Wiz, from a circuit to a proved temporal property
* [CoreSpec.md](CoreSpec.md)
* [Status.md](Status.md)
* [dsls.md](dsls.md): the embedded languages (DSLs) in Wiz, and the conventions they follow
* [error-codes.md](error-codes.md): the error codes and their quick fixes
* [playground-lsp.md](playground-lsp.md): the playground's goals panel and the language-server contract a self-hosted `wiz lsp` must implement
* [tools/jupyter.md](tools/jupyter.md): the opt-in Jupyter kernels for Wiz (`wiz repl` or a `wiz check` batch fallback), the `%%scry` taint cell magic, and the deterministic notebook exporter (`wiz-nb export`)
* [resources.md](resources.md): resources in Wiz: quantities, regions, optics, Feral and separation logic, with one running example
* [ROADMAP.md](../ROADMAP.md)

## The stages

The implementation is built in stages; each stage's doc describes what it added, its
files, and its exercises. Section numbers (`4c`, `22e` …) are stable, and other docs and
comments refer to them: section `NNx` is in `stages/NN-*.md`. The stages are grouped by
topic below, so the numbers are not in order.

**New sections are files of their own**: a new section of stage NN goes in
`stages/NN-topic/<slug>.md` (the directory next to the stage's file; `# <title>` heading,
no letter), and other docs refer to it by that path. Two branches adding sections then
touch different files, and no section letter needs claiming. The lettered sections in
the stage files stay as they are. A new stage is still a new `stages/NN-topic.md` and a
line below.

### The kernel and the elaborator (in Lean)

* [Stage 1: the core kernel](stages/01-kernel.md)
* [Stage 2: the extensible parser](stages/02-parser.md)
* [Stage 3: the elaborator](stages/03-elaborator.md)
* [Stage 4: data](stages/04-data.md)

### Running programs

* [Stage 5: erasure and the interpreter](stages/05-erasure.md)
* [Stage 6: macros](stages/06-macros.md)
* [Stage 7: type classes](stages/07-type-classes.md)
* [Stage 8: the backend](stages/08-backend.md)
* [Stage 9: the C FFI](stages/09-ffi.md)
* [Stage 10: effects](stages/10-effects.md)
* [Stage 25: concurrency](stages/25-concurrency.md)
* [Stage 32: concurrency as a model](stages/32-conc-model.md): the `Conc` effect, a pure scheduler, a model checker
* [Stage 27: trusted evaluation (`native_refl`)](stages/27-trusted-evaluation.md)
* [The trust ledger](trust-ledger.md): the reviewed trusted base of `lib/`, its gate and expiry policy
* [Stage 28: solvers (`smt`, `sat_decide`, `sat_decide_native`, `bv_decide`)](stages/28-solvers.md)

### Self-hosting

* [Stage 12: towards self-hosting](stages/12-towards-selfhosting.md)
* [Stage 13: the language, for programs this size](stages/13-language.md)
* [Stage 14: the kernel in Wiz](stages/14-selfhost-kernel.md)
* [Stage 15: performance for self-hosting](stages/15-performance.md)
* [Stage 16: data in the self-hosted frontend](stages/16-selfhost-data.md)
* [Stage 17: elaboration in the self-hosted frontend](stages/17-selfhost-elaboration.md)
* [Stage 18: more data in the self-hosted frontend](stages/18-selfhost-more-data.md)
* [Stage 19: the frontend checks the self-hosted sources](stages/19-selfhost-checks-sources.md)
* [Stage 20: the frontend checks itself, and gets faster](stages/20-selfhost-checks-itself.md)
* [Stage 21: bootstrap](stages/21-bootstrap.md)
* [Stage 30: type classes in the self-hosted toolchain](stages/30-selfhost-typeclasses.md)

### Tooling

* [Stage 11: tooling](stages/11-tooling.md)
* [Stage 23: grail, a build tool](stages/23-grail.md)
* [Stage 26: tower, a toolchain manager](stages/26-tower.md)

### Numbers and libraries

* [Stage 22: numbers for hardware and systems code](stages/22-numbers.md)
* [The value-level semantics matrix](semantics-matrix.md): every numeric and textual
  boundary, with the value the spec asks for and which backends were compared
* [Stage 29: native data structures](stages/29-natives.md): word arrays, word maps, interned strings
* [Libraries](libraries.md)
* [Reference manual](https://wiz-pl.github.io/wiz/docs/reference.html): every
  standard-library declaration with its full signature, doc comment and class instances,
  and the notation table (generated, not committed: `nix build .#reference`)

### Verification

* [Stage 24: separation logic](stages/24-separation-logic.md)
* [Stage 35: deadlock freedom for a synchronous model](stages/35-deadlock.md): progress and acyclicity for a finite model, not the IO API
