# scripts/

One-line index of every script and data file here: what it does and who calls it. Each
script carries its own header with the full input/output contract (`usage`, environment
variables and exit status); this page is only for finding the right one. Paths are
relative to the repository root.

Conventions: a script is **standalone** (no shared shell or Python library is sourced
from here, so a single script still works when copied or fetched by itself); the
interpreter is named in the shebang; `sh` scripts avoid bash-isms and are run by `sh`
where a checkout may not preserve the executable bit. A script that needs a build says
so in its header and skips cleanly when the build is absent.

Git hooks: the repository also ships a checkout-wide hook directory, `.githooks/`
(`pre-commit` refreshes `.github/repo-subsets.json`; `pre-push` warns when a registered
light check has no clean record for the commit being pushed, and never blocks). Enable
it once per clone with `git config core.hooksPath .githooks`; CI does not depend on it
(the `docs_style` job runs the same checks), and no hook fails a commit or a push.
`scripts/install-hooks.sh` is the older, per-clone alternative that copies `.git/hooks/*`
(it does not install the ledger warning); do not enable both.

## Gates and CI glue

| script | does | called from |
|---|---|---|
| `pre-commit.sh` | runs the cheap CI gates locally: `--fast` (docs style, changed-file format, ledger fixtures, skip lint, YAML) or `--full` (adds the trust ledger, the reproducibility corpus, the formatter group); exit 3 means no tool could run | `install-hooks.sh`, `.pre-commit-hooks.yaml` |
| `install-hooks.sh` | installs `.git/hooks/pre-commit` (fast tier on staged files) and `pre-push` (full tier); a foreign hook is kept unless `--force` is given | by hand; `pre-commit.sh --self-test` exercises it |
| `test-embed.sh` | checks that Lake re-embeds `runtime/rt_*.inc` after an edit (a temporary copy of the checkout) | local dev shell only (`docs/building.md`); needs an incremental Lake build, so CI does not run it |
| `check-docs-style.py` | fails on authoring artefacts in user-facing docs: `/workspace` paths, agent roles, status checkmarks, "the user's decision" | `ci.yml` (`docs_style`), `pre-commit.sh --fast` |
| `check-companion-lists.py` | early `docs_style` gate for generated companion lists: `.github/libdiff-corpus.txt`, `legacy-names.tsv` + `Wiz/LegacyNames.lean`'s digest, stale/expired `.github/name-collisions-baseline.json` entries, and the `.github/repo-subsets.json` hashes; prints one `companion drift:` line naming both sides | `ci.yml` (`docs_style`), `--self-test` |
| `repo-subsets.py` | the one table of build subsets (`lean`, `runtime`, `wizlib`, `packages`, `tests`, `docs`) and their content hashes over `git ls-files`; `--write` updates `.github/repo-subsets.json`, `--check` is the gate, `--print NAME` is for shell use, `--self-test` proves locality; `.githooks/pre-commit` runs it | `check-companion-lists.py`, `.githooks/pre-commit`, `scripts/lake-cache.sh key` |
| `lake-cache.sh` | the Lake seed's trust plumbing: `key` (trusted and untrusted Actions keys from `flake.lock`, `lean-toolchain`, the architecture and the `lean`/`runtime` subset hashes), `empty` (the `empty-lake` store path the producer starts from), `save` (a `withLakeCache` `lake` output), `choose` (the restored seed, else `empty-lake`), and `build` of flake.nix's `withLakeCache` | `ci.yml` (`lake_seed` on a push to master; `build` and `web_modules` on a pull request) |
| `check-release-consistency.py` | the release packet (candidate, counts, artifacts, checklist) and the machinery the docs name: versions, channels, `scripts/...` commands and release artifacts must still be produced by the tree | `ci.yml` (`docs_style`); `--for-tag` at the tagging PR |
| `check-wizc-release.sh` | the chain release gate (R1/R2): runs the packed `wizc` on a fixture with a known stdout, requires a one-byte variant to disagree, and checks `wizc-seed.json` (self.wiz, seed.c, Tables.wiz, rt.c); `--self-test-behaviour`/`--self-test-pin`, `--write-pin` | `bootstrap-chain.yml` (`release` job); `=selfhost-trust` |
| `gen-libdiff-baseline.py` | rewrites `Tests/libdiff-baseline.tsv` from the checked-in libdiff classification and corpus; `--check` fails when it is stale | by hand when the classification or the corpus changes; `=selfhost-libdiff` reads the baseline |
| `check-docs-examples.py` | runs every fenced `wiz` block through `wiz check`/`wiz run`, compares expected output, and resolves relative doc links | `ci.yml` (`docs_examples`), `--self-test` |
| `check-names.py` | checks every declaration's current name against `legacy-names.tsv`: normal reports, `--quiet` is the CI gate, `--strict-names` fails on every name outside its module prefix; a stale row is an error, a malformed row exit 2 | `ci.yml` (`docs_style`, added by the namespace train) |
| `check-repro.sh` | builds `Tests/ReproPaths` under two absolute paths with different environment and byte-compares the artifacts; `--compiler` also builds the compiler twice | `ci.yml`, `pre-commit.sh --full` |
| `check-stc.sh` | the STC metatheory gate: builds `STC` and `STC.Prototype.Totality`, requires an `.olean` for every `STC/**.lean`, rejects `sorry`/`admit`/`axiom`; `self-check` runs the two deliberate breaks (each must fail) | `ci.yml` (`stc`) |
| `ci.py` | helpers for `ci.yml`: `matrix`, `plan`, `changes`, `check-shards`, `balance`, `summary`, `baseline`, `check-skips` | `.github/workflows/ci.yml`, `pre-commit.sh --fast` (skip lint) |
| `check-shards.py` | the shard plan's totality gate: every group in a shard or in `.github/test-shard-exclusions.json` (reason and owner), no stale exclusion, and every skip-allowlist entry matches a case; `--self-test`, `--groups FILE` (a captured `tests --list`), `--json` | `.github/workflows/ci.yml` through `ci.py check-shards`; by hand for a review |
| `host-unsafe-ledger.py` | checks `.github/host-unsafe.tsv` against the `unsafe`/`extern`/`implemented_by` uses in host Lean; `--print` writes rows | `ci.yml`, `pre-commit.sh --fast`, `Tests/host-unsafe-ledger/run.sh` |
| `trust-ledger.sh` | runs the test driver's `--trust-ledger` gate over `lib/` (check, print, update); needs `lake build wiz tests` | `ci.yml`, `pre-commit.sh --full`; the gate itself is in `Tests/Native.lean` |
| `trust-ledger-merge_test.sh` | tests the ledger merge driver, including a real `git merge` through `.gitattributes` | `ci.yml` |
| `trust-ffi-audit.sh` | lists every `extern` in `lib/` with its ledger rows and, with `--check`, compiles the ledger's C prototypes | docs only (`docs/trust-ledger.md`) |
| `flaky-ci.sh` | CI glue for `flaky.py`: classify a failed shard, decide the verdict, expire quarantines, `self-test` | docs only; the `ci.yml` half of its commit is not on master yet |
| `golden-diff.py` | re-runs only the failing golden cases in a temporary copy and emits a Markdown diff | `.github/workflows/golden-diff.yml` |
| `grail-index-check.sh` | finds a `grail` binary and runs `grail index check` on a static index | `ci.yml`, `examples/fate-index/README.md` |
| `test-runtime.sh` | compiles `runtime/wiz_rt.h` plus `runtime/rt_*.inc` in both ABI modes (`WIZ_API=` and `WIZ_API=static`) | `ci.yml` |
| `test-perf-dashboard.sh` | end-to-end check of `perf-dashboard.py` on `fixtures/perf/` (no network, no toolchain) | docs only (`docs/stages/15-performance.md`) |
| `flaky.py` | reruns failing test cases, classifies them, and maintains the expiring quarantine | `flaky-ci.sh`, by hand |
| `checks-ledger.py` | records the light checks that ran on each commit in the gitignored, untrusted `.checks/` ledger (`run`, `status`, `warn`, `--self-test`); keyed by commit + name, so an amend invalidates | `.githooks/pre-push`; by hand |

## Local check ledger (advisory, not a gate)

`checks-ledger.py` is the local half of the light checks: `run NAME` records the
commit, timestamp, command, exit status and whether the worktree was clean in
`.checks/records.jsonl`; `status` shows, for `HEAD`, which registered checks have
a clean record; `warn` is what `.githooks/pre-push` calls. Records are keyed by
**commit + check name**, so an amend or rebase (a new SHA) makes them stale and
the hook asks for a fresh run.

Registered today: `docs-style`, `companion-lists`, `repo-subsets`,
`legacy-names-digest` and `repo-subsets-write`. The `CHECKS` table at the top of
the script is the one list, one line per check. `dirty` is the worktree at the
start of the run; the record also keeps `dirty_after`, so an update script that
writes a file shows as a clean start followed by a change (commit or discard its
output). `--self-test` builds a throwaway repository and proves the behaviours
(no record warns, a clean run stops the warning, a dirty run does not count, a
new SHA warns again).

`.checks/` is gitignored and **untrusted by design**: any process can write it,
nothing signs it, and CI does not read it. Treat the warning as a fast-fail
reminder, never as a security or merge gate.

## Trust ledger

| script | does | called from |
|---|---|---|
| `setup-trust-merge.sh` | installs, shows or unsets the local `merge.trust-ledger.driver` git config | `docs/trust-ledger.md`, `trust-ledger-merge_test.sh` |
| `trust-ledger-merge.sh` | the `%O %A %B` git merge driver: three-way merge of ledger rows by `module<TAB>declaration<TAB>item` | git, via `.gitattributes` once setup has run |

## Release

| script | does | called from |
|---|---|---|
| `release-tarball.sh` | makes the reproducible `wiz-ARCH-linux.tar.gz` (binaries, stdlib, editors, bundled C toolchain, licences) and its `.sha256` | `release.yml`, `Tests/Tower.lean` |
| `bundle-cc.sh` | assembles `share/wiz/cc/` (clang, lld, compiler-rt, glibc 2.27 sysroot, static GMP and GC, CaDiCaL) from `bundle-cc.sources` | `release.yml` |
| `release-snapshots.sh` | publishes/prunes `snapshot-<sha>` releases and moves `nightly` once CI passed | `release.yml`, `nightly.yml` |
| `test-release-snapshots.sh` | tests `release-snapshots.sh` against a fake `gh` and a local bare repository; publishes nothing | `release.yml` |
| `test-release-install.sh` | installs a tarball as a simulated tag with `tower-init.sh` and smoke-tests the toolchain, bundled compiler and a grail package | `release.yml` |
| `tower-init.sh` | the `curl`-to-`sh` installer: tower plus a default toolchain (nightly or a tag) | docs (`docs/install.md`); users |
| `build-tower-wiz.sh` | builds `tower/` with a grail into `BINDIR/tower`, no Lean at build time | `release.yml`, `flake.nix` |
| `mkexercises.py` | generates the exercise tree from the solution tree's marker blocks (solution-only files are dropped) | `release.yml` (tags only), docs |
| `grail-archive.sh` | the deterministic registry archive: `git archive` plus `gzip -n`, printing the SHA-256 the index records | docs (`docs/stages/23-grail/index-repository.md`, `examples/fate-index/README.md`); by hand |

## Benchmarks and performance

| script | does | called from |
|---|---|---|
| `stdlib-bench.py` | measures `bench/stdlib-bench.wiz`, with JSON output and paired `--baseline-bin` A/B | `bench.yml`, `web/build-bench.py` |
| `bench-threshold.py` | gates a stdlib A/B JSON on the median paired ratio (default 10%) | `bench.yml` |
| `mem-bench.py` | measures peak RSS of a fixed corpus and checks it against `bench/mem-baseline.json` | `bench.yml` |
| `perf-dashboard.py` | turns `perf-history.tsv` and CI timings into one self-contained HTML page | `test-perf-dashboard.sh`, by hand |
| `branch-rot.py` | classifies local (and `--remote`) branches as redundant, in-flight, attic or needs-PR; opt-in deletion | docs only (`docs/building.md`, monthly hygiene) |
| `stack-status.py` | prints and refreshes the merge-stack ledger kept outside the repository | docs only (`docs/building.md`) |

## Bootstrap and generators

| script | does | called from |
|---|---|---|
| `fixpoint.sh` | the three-stage bootstrap fixpoint: stage N's C must equal stage 1's; records time and peak RSS | `ci.yml`, `fixpoint.yml` |
| `GenSelfhost.lean` | writes the fixpoint inputs (`compiler.wiz`, `self.wiz`) into `$OUT` | `fixpoint.sh`, `bench/selfhost-build.sh` |
| `GenSelfhostTables.lean` | the `genSelfhostTables` Lake target: regenerates `selfhost/Tables.wiz` from the grammar | `lakefile.lean` |
| `gen-semantics-matrix.py` | regenerates `docs/semantics-matrix.md` and `Tests/Semantics/cells.tsv` from the stage rules | by hand (`docs/semantics-matrix.md`) |
| `gen-legacy-names.py` | regenerates `legacy-names.tsv` (module, name, reason class, file, line) from the seven library/tool roots (`lib`, `scry/src`, `scry/gen`, `hdl/src`, `tower`, `web`, `selfhost`); `--check`, `--print-digest`, `--update-digest` | by hand (namespace compatibility baseline) |

## Wasm experiments

| script | does | called from |
|---|---|---|
| `wasm-peak.mjs` | runs a Wasm module under Node and prints its result, peak linear memory and `wiz_main` time as JSON | docs (`docs/stages/08-backend/wasm.md`) |
| `wasm-workload.wiz` | the fixed allocation workload those measurements use | docs; its compiled module is what `wasm-peak.mjs` measures |

## Data files (not scripts)

| file | is |
|---|---|
| `bundle-cc.sources` | the external inputs of `bundle-cc.sh`: `FILE SHA256 URL…`, mirrors in order |
| `fixtures/perf/history.tsv` | a small perf-history log for `test-perf-dashboard.sh` |
| `fixtures/perf/ci-2026-11-12.jsonl`, `ci-2026-11-13-2ebcfd13.jsonl` | two CI `test-timings.jsonl` runs (a trend and a failing case) for the same test |
| `release-licenses/` | the third-party licence texts `release-tarball.sh` copies into the tarball, and its `NOTICE` |
