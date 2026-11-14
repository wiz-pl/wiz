# Building, testing and CI

## Building and testing

```sh
lake build          # the library and the `wiz` executable
lake test           # all exercise tests; every case runs in its own process
lake test -- conv   # only the groups whose name starts with "conv"
lake test -- =c     # only the group named exactly "c"
lake test -- '=selfhost#0,3'          # only cases 0 and 3 of the group "selfhost"
lake test -- --list                   # the group names
lake test -- --list-cases =selfhost   # the selected cases: GROUP<tab>INDEX<tab>NAME
lake test -- --timings t.jsonl rig    # also append each case's time to t.jsonl
.lake/build/bin/tests --run selfhost 3  # one case (also selfhost#3): exit 0 passed, 1 failed, 3 skipped
```

Every case prints its wall time (`✓ name (12.345 s)`), and every group its total.
`--timings FILE` (with `--shard NAME` as a label) appends one line of JSON per case:
`shard`, `group`, `index`, `case`, `seconds`, `ok`, and `notes`, which say which shared
programs the case used and built (`Tests.note`: `uses checker`, `built checker 331.2`;
the self-hosted checker and compiler are built by the first case that needs them and
kept under `/tmp`).

An unimplemented exercise shows up as `✗ ... not implemented yet (hit a sorry)`. A case
that cannot run here (no C toolchain, no `nix`, …) calls `Tests.skip REASON` and shows up
as `⊘ name` with `skipped (REASON)`; the total counts it apart (`…, 2 skipped`), and it is
not a pass. A selector that picks no group, a case index the group lacks, and an unknown
flag are errors (exit code 2), not an empty run.

`tests --run GROUP INDEX` runs one case as `lake test -- '=GROUP#INDEX'` does: in a child
process, with the toolchain of `grail.local.wiz` (toolchain flags after it override it),
printing the case's name and result, a failure's output, and a last line
`GROUP #INDEX: passed|FAILED|SKIPPED`. Build the driver first (`lake build wiz tests`):
plain `lake build` does not, and a stale driver runs whichever case had that index.

**The trust ledger.** `scripts/trust-ledger.sh` walks every declaration of `lib/` (and
`examples/hdl-verified.wiz`, which must stay axiom-free), runs `#print axioms`, and
compares the trusted base it finds with the checked-in `.github/trust-baseline.tsv`: a
new `axiom`, `sorry`, `native_refl` or SMT axiom, `implemented_by`/`repr:`
implementation, `builtin` registration or `partial` definition fails until the baseline
is updated after review. The `native` group runs the `lib/` part in CI, the
`hdl-verified` group the example's; `scripts/trust-ledger.sh --update` regenerates the
baseline (build the driver first). `--print` shows the recorded sources; the baseline's
header explains the format.

### Running cases in parallel (`--jobs`)

`lake test -- --jobs N` (default 1) runs the cases of a group that opted in N at a time, in
a bounded pool of child processes; a group that did not opt in still runs one case at a
time, and groups themselves run one after another. Output and `--timings` lines stay in
the group's case order (each case's output is buffered until the cases before it are
printed), so a parallel log is a sequential log but for the times; a case's `seconds` is
its own process's time, not the time it waited in the pool; the totals and the exit code
are the same as a sequential run, and a failing case does not stop the others. An
exception kills the cases still running, and the cases stay in the driver's process
group, so Ctrl-C reaches them as it did sequentially.

The opt-in is `parallel := true` on a `Group` (`Tests/Harness.lean`). Enable it only for a
group whose cases share no mutable state: every case's files must be its own (its own temp
directory, or a fixed path that no other case touches), and a group has no build
directory in the work tree, no port, no environment variable of the driver and no cached
program another case builds; no case
may assert on wall time or on the machine's load (a `scaling`-style bound). A case that
needs a shared program the first case builds (the self-hosted checker, the Wiz `tower` in
`.lake/build/tower-wiz`) is not parallel-safe: N processes would build it N times.
`--jobs-all` also parallelizes the
groups that did not opt in, for auditing one group's isolation — not for CI. On a 4-core
runner `--jobs 4` is the useful setting; more jobs only add memory pressure (a case that
compiles C can peak at a few hundred MB).

**Embedded files.** Lake does not track files a module reads with `include_str`, so each
embedded file gets a library of its own whose `needs` names the file as an
`input_file` (`lakefile.lean`): Lake mixes the file's content hash into that library's
module traces, so editing the file rebuilds the embedding module and its importers, and
the artifact cache never serves a stale one. The only one today is the C runtime,
`runtime/wiz_rt.h` plus `runtime/rt_{core,num,words,data,sys,con}.inc`, embedded by
`runtime/WizRuntime.lean` (library `WizRuntime`, imported by `Wiz/Compiler/C.lean`); the
parts are concatenated in the order of the old single file, so generated C is unchanged.
A new `include_str` goes in such a library too, not in `Wiz` (a `needs` on `Wiz` would
rebuild all of it); `scripts/test-embed.sh` checks the setup (CI runs it in the build
job), and `scripts/test-runtime.sh` compiles the runtime alone with `cc -fsyntax-only
-Wall -Wextra`, with `WIZ_API=` and `WIZ_API=static` (the header's prototypes are checked
against the parts).

## Test layout

Adding a test group touches no shared file:

* **A new group is a new module** `Tests/Groups/<Name>.lean` that ends with
  `builtin_initialize registerGroup myGroup` (`Tests/Harness.lean`). Lake generates
  `Tests/Groups.lean` (an import of every file in `Tests/Groups/`; not committed, see the
  `testGroups` target in `lakefile.lean`) and `Tests/Main.lean` imports it, so the group
  is in the suite as soon as its file exists. Copy a small one (e.g.
  `Tests/Groups/Struct.lean`) to start. Set `shard := "backends"` in the group to run it
  in a shard other than the default (`library`), or add a selector to
  `.github/test-shards.json`.
* **New cases of an existing group** go in its module: the group `elab: structural
  types` is `structGroup` in `Tests/Groups/Struct.lean` (`grep -l 'name := "…"'
  Tests/Groups/*.lean` finds a group by name). A helper only one group uses lives in
  that group's module; `Tests/Elab.lean` holds the helpers several groups use (`ok`,
  `fails`, the library loaders, the self-hosted programs, …).
* The older modules (`Tests/Grail.lean`, `Tests/Lint.lean`, …) still list their groups
  (`groups` at their end, concatenated by `Tests/Main.lean`); a new group goes in
  `Tests/Groups/` all the same.
* `scripts/migrate-tests.py` made this layout from the old single `Tests/Elab.lean`,
  deterministically; a branch that still edits the old file replays its changes with it
  (AGENTS.md, "Test layout").

## What `wiz build` links

`wiz build` turns a program into C (or LLVM IR) and hands it to a C compiler with the
runtime (`runtime/wiz_rt.h` and `runtime/rt_*.inc`), which needs GMP; programs from the
self-hosted compiler also need the Boehm GC. The release toolchains (what tower installs) bring all of that in
`share/wiz/cc` (docs/stages/26-tower.md, 26f): clang, a glibc 2.27 sysroot, and GMP and the
GC as static libraries (the bundled clang needs glibc 2.30 or later; programs it builds
need glibc 2.27 or later and nothing else), and CaDiCaL, the SAT solver of `sat_decide`
(docs/stages/28-solvers.md, 28b), which writes LRAT proofs (the Lean toolchain's copy, MIT
licence, in `share/wiz/cc/LICENSES/lean4-LICENSES` with Lean's third-party licences; z3 is
not bundled). A checkout uses `cc` and the system's GMP unless you pass
`--cc`/`--cflags`/`--ldflags` (the Nix dev shell writes them to `grail.local.wiz`).

**Licences of what is linked into your programs.** The Wiz Runtime Library Exception
(COPYING.RUNTIME) lets you distribute programs compiled by Wiz under any terms, but it
covers only Wiz's own runtime. Other libraries keep their licences:

* **GMP** is under the LGPL-3.0-or-later (or GPL-2.0-or-later). The release toolchain
  links it **statically**, as Lean does for Lean programs. If you give someone a binary
  built that way under terms that are not the (L)GPL, the LGPL asks you to: say that the
  program uses GMP and include the GNU LGPL and GPL texts (they are in
  `share/wiz/cc/LICENSES/`); offer GMP's source (or say where to get it); and let the
  recipient relink your program with a modified GMP, which for a static binary means also
  providing your program's object files (or its source). If your program's source is
  public anyway, you have done the last part already. Using programs yourself, or in a
  company without giving them to others, creates no obligations.
* With **dynamic** GMP only the notice and the source offer remain, because the user can
  replace `libgmp.so`. To build that way, use the system's compiler and GMP:
  `--cc gcc` (with `libgmp-dev` installed; tower: `tower set cc gcc`).
* The **Boehm GC** (self-hosted runtime) has an MIT-style licence: keep its notice
  (`share/wiz/cc/LICENSES/bdwgc-README.QUICK`).
* glibc is linked dynamically, as with any C program. The compiler-rt builtins clang
  links in (Apache-2.0 with LLVM exception) need no notice.

A release toolchain's `share/wiz/NOTICE` says the same, and also lists the third-party
code linked into `wiz`, `grail` and `tower` themselves; the licence texts are in
`share/wiz/LICENSES/` and `share/wiz/cc/LICENSES/`.

## Continuous integration

`nix develop` gives the toolchain the tests need besides Lean (see `flake.nix`): GMP and
LLVM's `llc` for the C and LLVM backends, Boehm GC for the self-hosted backend, a C
compiler, and elan, which installs the Lean in `lean-toolchain`. Entered at the
repository root, it writes this machine's paths to the uncommitted `grail.local.wiz`,
which grail and the test driver read (`Tests/Main.lean`; flags to `lake test -- …` win);
`wiz` takes flags. Nothing reads environment variables.

GitHub Actions (`.github/workflows/ci.yml`) runs on pushes and pull requests to
`master`. Every job runs in that dev shell (with the Cachix cache, when
one is configured); the elan toolchain and `.lake` (including Lake's artifact cache) are
cached between runs.

* **The test suite** runs in parallel shards, one job per entry of `.github/test-shards.json` (each entry
  is a list of `lake test` selectors). A group that no shard's selectors pick runs in
  the shard its `Group.shard` names, else in the shard marked `"default": true`
  (`library`), so **a new group needs no edit there**; the build job checks that every
  case is in exactly one shard (`scripts/ci.py check-shards`, after splitting). See
  "Test layout" below for where a new group goes. Each shard's job summary has a table of every case's time
  (three decimals), group subtotals and the shard's total; the `CI result` job sums the
  shards up (a table of shard totals and the grand total, and the 15 slowest cases) and
  uploads every case's time as the `test-timings` artifact.
* **Documentation style** (the `docs_style` job): `scripts/check-docs-style.py` fails on
  absolute paths from an agent's scratch tree, internal `agent/...` branch names and AI
  worker roles, U+2705 status checkmarks, and decision/step phrases attributed to
  "the user" in `README.md`, `ROADMAP.md`, `CHANGELOG.md` and `docs/**/*.md`. It runs the
  script's fixtures (`--self-test`) and then the check, on every push and pull request
  (including docs-only ones), and `CI result` requires it. No code block is exempt; a
  reviewed exception goes in the script's `ALLOW` list with a reason.
* **Trust ledger** (the `trust-ledger` job): `scripts/trust-ledger.sh --check` runs the
  `--trust-ledger` mode of the test driver (`Tests/Native.lean`) over `lib/` and the
  axiom-free examples, and compares the sources of trust it finds with
  `.github/trust-baseline.tsv`: a new `axiom`, `sorry`, `native_refl` or SMT axiom,
  `implemented_by`/`repr:` implementation, `builtin` registration or `partial`
  definition fails until it is reviewed and the baseline regenerated with
  `scripts/trust-ledger.sh --update`. The `native` and `hdl-verified` groups check the
  same ledger in the shards; this job runs the whole of it without a shard's path
  filter to skip it, and `CI result` requires it when code changed.
* **Split shards.** A shard with `"split": N` runs as N jobs `NAME-1` … `NAME-N`, each a
  list of `=GROUP#I,J,…` selectors. `scripts/ci.py` balances the parts with the case
  times in `.github/test-timings.json`: the cases that use the same shared program (the
  self-hosted checker or compiler, which the first case that needs it builds) stay in
  one part, so each program is built once, and the other cases fill the parts up. A new
  case counts as its group's median, with the programs most of its group uses. The
  baseline holds only the split shards' cases, one per line (`selfhost`, `library` and
  `scaling`; the last is a sweep over `lib/` and `examples/`, split 2 with its long case
  in one part).
  `scripts/ci.py plan` shows the parts and their
  estimates. The heavy groups have dedicated shards of their own (`hdl-verified`,
  `prop`, `audit`), so adding a slow case there does not unbalance `core`.
  To refresh the baseline from a CI run:
  `gh run download RUN -n test-timings && scripts/ci.py baseline timings.jsonl > .github/test-timings.json`.
* **`"jobs"`.** A shard may say `"jobs": N` to give `lake test` `--jobs N` (above): its
  opted-in groups run N cases at a time. Only set it on a shard whose groups were
  verified (and opted in) to be safe in parallel; `core`, `library` and `backends` use
  4 on the 4-core hosted runner. A shard of one long case (`grail-selfhost`,
  `hdl-verified`) and the shards that build a shared program (`selfhost`) keep 1. A
  case's `seconds` stays its own process's time, so shard balance is unaffected.
* **Shard balance.** CI's wall time is its longest job, so the invariant is that **no
  test shard's test time is over 1.5× the median shard's**. Every split shard's cases
  have an entry in `.github/test-timings.json`, and no shared program is built by two
  parts of one split shard. It is tracked in two places:
  * `scripts/ci.py check-shards` (the build job) warns when a split shard has cases
    that are not in the baseline.
  * `scripts/ci.py balance` (the `CI result` job) checks the run's measured case times.
    It adds a "Shard balance" table to the run summary and a warning annotation for each
    violation.

  Both only warn, on pull requests and on master. A new case has no time until a CI run
  has measured it, and runner times vary, so a failure here would block merges that are
  correct.

  On a master push whose tests all passed and whose balance drifted, the `CI result`
  job uploads the regenerated baseline as the `test-timings-baseline` artifact. It also
  prints the command that applies it, in the warning and in the summary:
  `gh run download RUN -R wiz-pl/wiz -n test-timings-baseline -D .github`.
  Commit the result in a small PR. CI does not open that PR itself. A PR opened with the
  workflow's token runs no CI (GitHub does not trigger workflows from it), so it could
  not merge on green, and the workflow would also need write permissions.

  If a shard stays over the limit after the refresh, raise its `"split"` or make it a
  split shard. `scripts/ci.py plan` shows the predicted parts. One case longer than the
  limit cannot be split: `grail-selfhost` is one case of several minutes, and
  `scaling`'s sweep over `lib/` and `examples/` is one case of about 14 min (the
  `scaling` shard's other part holds its 26 shorter cases).
* **The exercise tree** is checked only for a release tag: the `exercise tree` job of
  `release.yml` generates it with `scripts/mkexercises.py` into a temporary directory
  and builds it (`lake build wiz grail tests`), and the tarball job (which publishes)
  waits for it. Pull requests and master pushes don't build it. It does not run the
  exercise tree's tests (almost all of them fail by design). See
  [exercises.md](exercises.md).
* **The bootstrap fixpoint** (`scripts/fixpoint.sh`: the stage-1 C of the toolchain
  equals its stage-2 C) runs weekly on `master`, or from "Run workflow" with
  `fixpoint` ticked. It takes a long time; run it locally with `nix develop -c
  scripts/fixpoint.sh`.
* **The Nix package** (the `nix package` job): `nix build .#wiz` builds `wiz` and
  `grail` with Lake and nixpkgs' Lean (the flake checks that it is the version in
  `lean-toolchain`), and wraps them with the toolchain as flags (`--cc`, `--cflags`,
  `--ldflags`, `--llc`, `--gc-cflags`, `--gc-ldflags`; flags you pass come later and
  win) and, for `wiz`, the packaged standard library as a module root after `./lib`. CI
  pushes it to the public Cachix cache `badlydrawnwizards` on pushes and on pull
  requests from this repository (which have the token). The tests still use Lake, whose
  artifact cache rebuilds only what changed. `packages.tests` is the test driver
  (`nix run .#tests -- --list`), from the same build, so building `wiz` builds it too.
* **The packaged read-only elaboration cache.** The `wiz` package prewarms the
  elaboration cache during its build and installs it at `$out/share/wiz/cache`: the
  `.wizc` effects and the `.wizm` seen markers, with no `bin/` memo and `a-w`
  permissions. Both wrappers (`wiz` and `grail`) add
  `--cache-ro $out/share/wiz/cache` after their toolchain flags, so a packaged run
  replays the standard library instead of elaborating it; a user's `--cache` (the
  default `~/.cache/wiz`) is still written, so the store cache is only ever read.
  There are two sets of entries in that one directory, because `wiz` and `grail` are
  different executables and the cache mixes the running binary's hash into every key
  (`Cache.binaryId`; an entry written by one is never read by the other):
  * **wiz**: every module of `lib/` (all 61 `.wiz` files today, in sorted order: one
    `wiz check` of a one-line `import M` for each module `M`), about 4,200 entries and
    50 MB. Checking a module's own file would key its commands by the main text, which
    an importer never looks up, so the warm run imports it instead.
  * **grail**: a minimal package in `$TMPDIR` whose `grail.wiz` imports `Grail` and
    whose check target imports `Std` (about 440 entries, 3.3 MB, about 3 s). grail
    elaborates in-process, so even a `grail build` of a one-target package would
    elaborate its build file (Grail and Prelude) and Std's closure itself, under
    grail's hash; without this set the store cache is never hit by grail (0 reads in a
    clean-`HOME` probe) and the run writes those entries to the user's cache. With it,
    the build file's and Std's elaboration replay for any package; a module outside
    Std's closure is elaborated once, into the user cache. Warming *every* `lib` module
    in grail's namespace would add another ~4,100 entries and ~50 MB for about 3
    minutes of build time, which is not worth it for the uncommon imports.
  Flags parse left to right: a later `--no-cache` turns both the packaged cache and the
  write cache off, and a user's `--cache-ro DIR` appends another read-only layer
  (`--cache-ro` is repeatable and searched in the order given). The entries are keyed
  by the packaged binary's hash (its bytes) and by `lib`'s text and module names, so
  the Nix build invalidates them automatically; there is no manual invalidation and a
  stale store path is never reused (a new build gets new keys). The cache is
  read-only in the store, so a miss (a user's own module) is elaborated and written to
  the write cache as usual.
* **The Wiz build caches.** Each test shard keeps what the suite builds from Wiz
  programs between runs: the elaboration cache (`lake test -- --cache ~/.cache/wiz …`),
  `.grail`, and the self-hosted checker and compiler that the tests compile
  (`/tmp/wiz-selfhost-*`). The cache key starts with a hash of everything the compiler
  is made of (the `.lean` files, Lean, `flake.lock`), and partial hits only come from the
  same compiler (the elaboration cache's own keys include the wiz binary's hash, but the
  test driver's grail runs use a fixed binary id and the `/tmp` programs a timestamp).
  The elaboration cache may also have read-only layers (`--cache-ro DIR`, repeatable,
  searched in order after the written `--cache DIR`, never written). The Nix package
  can ship one in `$out/share/wiz/cache` for `--cache-ro $out/share/wiz/cache`, so CI and
  users share a warm cache without a writable store path; a run with no write cache
  hashes the wiz executable each time instead of remembering it under `bin/`.
* **Storage.** The repository's Actions cache holds 10 GB and evicts the least recently
  used entries, so pull requests don't keep big entries: the elan toolchain (~770 MB) is
  saved only by `master` (pull requests restore master's), and a pull request's (or merge
  queue entry's) `lake-*` and `exercises-*` entries (~500 MB each), saved only to hand
  the build to its test shards, are deleted by the `CI result` job when the run ends
  (not when it is cancelled). The next push restores master's build and catches up.
  Artifacts are short-lived: test logs 3 days, `test-timings` 7 days on master (2
  elsewhere), `test-timings-baseline` 7 days, the release tarball 90 days for a tag,
  7 for a snapshot (both are also release assets) and 3 for a pull request.
  To see the usage: `gh api repos/wiz-pl/wiz/actions/cache/usage` and
  `gh cache list -R wiz-pl/wiz -S size_in_bytes`.

* **Path filters.** On a pull request the `changes` job (`scripts/ci.py changes`) reads
  the files the PR changes and decides what runs: nothing but `changes`, `docs_style`
  and `CI result` for a docs-only PR (`docs/`, `*.md`, LICENSE); `trust-ledger` runs
  whenever any code did; every shard when a Lean
  file, the build, the runtime, `scripts/` or `.github/` changed; otherwise each shard
  with `"inputs"` in `.github/test-shards.json` only when one of its inputs changed
  (a `lib/X.wiz` input brings the lib files it imports), and the shards without
  `"inputs"` (backends, library) for any non-docs change. So a PR touching only, say, `lib/Json.wiz` skips
  `core` and the selfhost shards. `CI result` counts a job the filter skipped as fine
  and a job it wanted only if it succeeded. Pushes to `master`, the merge queue and
  manual runs always run everything, so a missing input shows up there at the latest.
  A test that starts reading a new file belongs in a shard without `"inputs"`, or add
  the file to its shard's `"inputs"`.
* **A self-hosted runner** for the heavy shards (`"heavy": true` in
  `.github/test-shards.json`): set the repository variable `WIZ_RUNNER_HEAVY` to its
  label; unset, everything runs on `ubuntu-latest`. Pull requests from forks never run
  there. Setup, security and aarch64 notes: [ci-runner.md](ci-runner.md).
* **Merging: the merge queue.** CI also runs on `merge_group` events, so `master` can
  have a GitHub merge queue (it needs an organization-owned repository): a queued PR is
  tested merged onto `master` *and the PRs queued ahead of it* (up to 3 entries build at
  once), and lands only if that run's `CI result` passes. Two PRs that are green alone
  but break together (the selfhost/*.wiz case of 2026-11-11) then never both land. To
  queue a green PR: `gh pr merge N -R wiz-pl/wiz --merge --auto` (it enters
  the queue once its own checks pass; `gh pr merge N --disable-auto` takes it out). A
  queue run that fails drops that PR from the queue and rebuilds the ones behind it
  without it. Without a queue (a user-owned repository), `--auto` waits for the required
  check and merges, and "require branches to be up to date" serialises merges instead.

To run Wiz without a checkout or a Lean toolchain, with the binaries from Cachix:

```
nix run --option extra-substituters https://badlydrawnwizards.cachix.org \
  --option extra-trusted-public-keys badlydrawnwizards.cachix.org-1:TxG+RHY8RMC/AXc0LJbYtYm9LW/XRjfQwgz+EEaAjBI= \
  github:wiz-pl/wiz#wiz -- check hello.wiz
```

or `cachix use badlydrawnwizards` once and then `nix run
github:wiz-pl/wiz#wiz -- …` (`#grail` for grail; `wiz build FILE -o OUT`
works out of the box). Without a branch the flake reference means the default branch,
`master`, whose binaries are on Cachix once its `nix package` job has run. The
`--option`s count only for a trusted Nix user (or with the cache in `nix.conf`);
otherwise Nix builds wiz from source, which takes a few minutes.

`#nvim-wiz` is Neovim with the Wiz plugin (editors/nvim, docs/stages/11-tooling.md
11p) and this wiz on `PATH`: `nix run github:wiz-pl/wiz#nvim-wiz --
file.wiz`. `packages.<system>.wiz-nvim` is the plugin alone, for a Neovim
configuration in Nix.
