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

Every case prints its position among the cases the invocation selected and its wall time
(`[3/42]   ✓ name (12.345 s)`; a shard's total spans its groups), and every group its
total.
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

**A missing toolchain is a skip; a failing program is a failure.** `Build.runGlobal`
returns a `Build.RunError` that says which happened: `.build`, or `.toolchain` when the
compiler, `llc` or GMP's `gmp.h` could not be found (no program ran), and `.run` with the
program's exit code and standard error, `.timeout`, or `.readback` when the program itself
failed. The helpers in `Tests/Elab.lean` (`failRun`, and `cRun`/`ioRun`/`cRunLibs`/…) skip
only a `.toolchain` failure and otherwise fail the case, reporting the exit code and the
program's stderr. Never look for `No such file` in a program's stderr to decide "no
toolchain": a program may print that itself (a missing fixture, a `File.open`, a
`Process.output` of a command not on `PATH`), and the case then failed. The `conc` group
has a case for each half: a run-time ENOENT failure, a pass whose program writes that
text on stderr and exits 0, and a build that cannot find the compiler.

A case whose name claims **linear** time must measure it. `Tests.checkScaling`
(`Tests/Harness.lean`) runs the same action at `n` and `2n` (best of three, the fixed
start-up floor measured at `f 0`), prints both times, and requires
`t(2n) ≤ 3·t(n) + 250 ms` for a linear claim (`bound` 6 for `n log n`, 10 for
quadratic). An absolute millisecond bound is a timeout guard, not a complexity test: a
quadratic implementation passes it. Name a timeout-guarded case accordingly ("… within
N s"), and give a new scaling case the input that grows the suspect dimension
(`Tests/Scaling.lean`).

`tests --run GROUP INDEX` runs one case as `lake test -- '=GROUP#INDEX'` does: in a child
process, with the toolchain of `grail.local.wiz` (toolchain flags after it override it),
printing the case's name and result, a failure's output, and a last line
`GROUP #INDEX: passed|FAILED|SKIPPED`. Build the driver first (`lake build wiz tests`):
plain `lake build` does not, and a stale driver runs whichever case had that index.

**The trust ledger.** `scripts/trust-ledger.sh` walks every declaration of `lib/` (and
`hdl/examples/hdl-verified.wiz`, which must stay axiom-free), runs `#print axioms`, and
compares the trusted base it finds with the checked-in `.github/trust-baseline.tsv`: a
new `axiom`, `sorry`, `native_refl` or SMT axiom, `implemented_by`/`repr:`
implementation, `builtin` registration or `partial` definition fails until the baseline
is updated after review. The `build` job runs the whole check right after the Nix
build and before any shard starts (with `Tests/trust-ledger/run.sh`), so a ledger
regression fails the run early; the `native` group also covers the `lib/` part and
`hdl-verified` the example's inside the shards;
`scripts/trust-ledger.sh --update` regenerates the
baseline (build the driver first). `--print` shows the recorded sources; the baseline's
header explains the format. Two branches that review different ledger rows need no
hand merge: install the local git driver once per checkout with
`scripts/setup-trust-merge.sh` (the committed `.gitattributes` selects it for this
file; the rule and its ambiguity failure are in `docs/trust-ledger.md`). A local
driver is not cloned and CI cannot set it, so run `scripts/trust-ledger.sh --check`
after a merge; `scripts/trust-ledger-merge_test.sh` tests the driver without a build.

**The host-side unsafe ledger.** The trust ledger covers the Wiz sources; the Lean that
implements Wiz has its own escapes from Lean's guarantees (a mutable cell behind a pure
interface, a C function, a value whose type is erased). `scripts/host-unsafe-ledger.py`
finds every declaration under `Wiz/`, `Tests/`, `Grail/` and the root `.lean` files whose
code (not comments or strings) uses `unsafe`, `unsafeBaseIO`, `unsafeIO`, `unsafeEIO`,
`unsafeCast`, or an `implemented_by` or `extern` attribute, and compares them with
`.github/host-unsafe.tsv`: one row per use, with the invariant that keeps it from changing
a result (what is accepted, rechecked or cached). `--check` fails on an unlisted use, a
stale row or a row without an invariant; `--print` lists the uses as rows to fill in.
It needs no build: `scripts/pre-commit.sh --fast` runs it with its fixtures
(`Tests/host-unsafe-ledger/run.sh`).

### The REPL (`wiz repl`)

`wiz repl` reads one Wiz command per line on standard input and elaborates it into one
persistent `CommandState` with the ordinary frontend (the same command loop as
`wiz check`), so definitions, `syntax`, `macro`, `instance` and `import` stay in scope for
later lines; an error is printed and the session continues. The Prelude is imported at the
start. The REPL's own commands are `:type EXPR` (its type, like `#check`), `:load FILE`
(elaborate a file into the session: its definitions stay), `:run NAME` (build and run a
definition, with `--llvm` for LLVM), `:reset`, `:help` and `:quit` (EOF exits too). A
terminal gets a prompt; a pipe is a script, and its output is only the commands' output.
`--prelude MODULE`/`-p MODULE` (repeatable, comma-separated) imports modules after the
Prelude and before the first prompt, composing with `-I`; a missing module is a startup
error. A tool that ships a prelude module can wrap the ordinary REPL instead of forking
it (`scry repl`, run from `scry/`, is
`wiz repl -I src -I ../lib --prelude Scry.Repl`; from the repository root,
`wiz repl -I scry/src -I lib --prelude Scry.Repl`).

Limits: input is one line per command (no continuation, history or line editing, and no
completion or goal display — that is `wiz lsp` and the infoview). The REPL is a frontend
session, not a second evaluator: `#eval` and `:run` are the elaborator's interpreter and
IR. A `link_c` path (also one inside a `:load`ed file) is resolved relative to the current
directory: the session has no file of its own. Tests are the `wiz repl:` cases of the
`tooling` group.

`wiz test-driver [--driver PATH] [GROUPS…] [--jobs N] [--list]` runs `.lake/build/bin/tests`
with the other arguments unchanged; build the driver first. There is no single-file
form yet: `wiz test FILE` is still a proposal, and no stage-11ah section exists.

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

A case of a group that did not opt in is told the driver's `--jobs` when it was given
(`Tests.caseJobs`), and may use N workers of its own inside its one process.
`=selfhost-libdiff` is the one that does: each of its four file-range cases builds the
self-hosted compiler once (unless the job already did), then checks N files at a time
(each file still runs its host and self-hosted sides in child processes, so the verdicts
are the same). With no `--jobs`, N is **auto**: the CPUs
minus one, capped by the free memory at its `--mem` MB per file (4096 by default,
`/proc/meminfo` and any cgroup limit). So a 4 vCPU / 16 GiB CI runner gets 3 workers.
`--jobs N` overrides it (`--jobs 1` is the serial control), and a worker starts its next
file only while that memory is free; a log's records stay in the files' order, so
parallel and sequential runs report the same records. The cases of an opted-in group
get 1 (N already run at once). A file's timeout is per file, not for the pool.

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

### Splitting one case into parts (`--part`)

`--part i/n` (1-based) runs only the files whose index `k` in the case's sorted file list
satisfies `k % n = i - 1`. It is for a case that is too long for the shard's limit but
whose per-file work must not change: the parts are a partition of the same list, so
their union is the case and each file still goes through both compilers with the same
bounds. `=selfhost-libdiff` is the one that uses it; `.github/test-shards.json` says
`"parts": 6` and CI gives each of the six jobs `--part i/6` (the flag is not `--shard`,
which is the `--timings` label). The driver validates it (`1 ≤ i ≤ n`, `n ≥ 1`) and
passes it to the case's process; `tests --libdiff --part 2/6` runs one part locally, and
the case's property test checks the partition for `n = 1…8` without a toolchain.

A part writes `.lake/libdiff/records.jsonl` as each record arrives, so a part killed by
the job timeout still leaves what it finished (a missing file is then named by the
union check, rather than shrinking the green total). That check is the corpus:
`.github/libdiff-corpus.txt` is the manifest of every `*.wiz` under `lib/` and `scry/`,
in `LC_ALL=C` order, with no exclusions, and `scripts/check-libdiff-corpus.sh` (with
`--self-test`, in the static gate) fails when a listed file is absent, a file under the
two trees is unlisted, or an entry is duplicated or out of order. It needs no build.

### Flaky tests and the quarantine

A failure in a CI shard does not say whether it is deterministic. `scripts/flaky.py`
reruns the selected cases (or the cases a failed run reported) several times, with a seed
matrix, and classifies each as **always pass**, **deterministic fail**, **flaky**,
**always skip**, or **incomplete** (the rerun budget ran out). It also runs a failing
case alone and then after a shuffled predecessor, so a case that only fails in sequence
is reported as order dependent. The default budget is 600 seconds; run it under
`heavy --mem 2G` locally.

```sh
scripts/flaky.py '=rig' '=toolchain' --repeats 10 --report flaky.json
scripts/flaky.py --from-log logs/*.log --report flaky.json
scripts/flaky.py --from-timings timings.jsonl --repeats 5
scripts/flaky.py --shard library --order-check suspects
```

`scripts/flaky.py --self-test` exercises the classifier on deliberate fixtures (an
alternating case, a deterministic failure, a skip, and a case that fails only after a
predecessor); it needs no test driver and no build. `scripts/flaky-ci.sh self-test`
does the same for the CI gate: a synthetic failing log against the fixture driver,
including a quarantined flake, a deterministic failure, an unreproduced failure, a
skip, an expired entry, an exhausted budget, and the job verdict.

The seed matrix (`--seeds 11,23,47` or `--seed-base`/`--repeats`) numbers the reruns,
chooses the shuffled predecessor, and is exported as `FLAKY_SEED`. The order check runs
a suspect alone and then after a predecessor from the same group by default
(`--predecessor-scope selected|group|all`); a case that passes alone and fails in
sequence is reported as order dependent and classified as flaky.

The driver has no JUnit output: `--from-log` reads its stdout (the `test-log-*`
artifacts) and `--from-timings` its `--timings` JSONL. `--from-junit` is accepted for a
JUnit file produced elsewhere. A skip is not a pass; a timeout is recorded, never
counted as a pass. A pass beside a timeout is flaky; a pass/skip mixture is incomplete.
A case that failed in the source run and passes every rerun is **flaky** (the failure
did not reproduce), never "always pass"; a source failure that now only skips stays a
failure. Exit status: 0 clean (or only active quarantines), 1 a deterministic failure,
an incomplete measurement, a source failure that only skips, or an expired quarantine,
2 usage/input error, 3 an unquarantined flaky case, 4 the budget ran out.

Known flakes live in `.github/flaky-quarantine.json` (data only; no code). Every entry
has a `group`, a `case`, a fixed `expires` date (`YYYY-MM-DD`) and a `reason`; `owner`,
`issue` and `index` are optional:

```json
{
  "version": 1,
  "entries": [
    {"group": "rig", "case": "a case name", "index": 3,
     "expires": "2026-12-01", "reason": "intermittent, see the linked issue",
     "owner": "the area's maintainer", "issue": "#123"}
  ]
}
```

`scripts/flaky.py --check-quarantine` exits 1 from the expiry date on, so a flake cannot
be parked indefinitely. An active entry makes the verdict of a flaky case exit 0; it
never turns a deterministic failure into a pass. Add an entry in a PR with a reason and
an expiry that leaves time to fix or replace the test; refresh the date only with a new
reason, never by deleting the entry silently.

**In CI: not wired yet.** PR #369 added the classifier and its CI glue, but
`.github/workflows/ci.yml` does not call `scripts/flaky-ci.sh` (nothing under `.github/`
mentions `flaky`), so the shard's `tests` step has no `continue-on-error`: a failed shard
still ends the job and is not classified, no report is written, and no expiry runs. The
glue is ready for the wiring it documents at the top of the script — `shard` on a failed
shard (`scripts/flaky.py --from-log logs/<shard>.log`, `--budget 600`, writing
`logs/<shard>-flaky.json` and a summary), then `verdict` with `if: always()`, then
`expiry` in the `result` job — and with that wiring a shard would be green only when the
tests passed or the classifier cleared every failure (a deterministic failure, an
incomplete measurement, a source failure that only skips, or a flaky case with no active
entry keeps it red). Until then the classifier is a local tool:
`scripts/flaky-ci.sh self-test` (no driver, no build) and the `shard`/`verdict`/`expiry`
modes run by hand.

**What a failed shard costs when the classifier runs.** The classifier reruns each
failing case five times alone and a suspect five more times after a predecessor: about
ten driver runs per failing case, plus two `--list-cases` calls. The whole
classification is capped at 600 seconds of wall time per failed shard (exit 4 if it runs
out, which keeps the shard red). It
runs in the same job as the shard, so it uses that job's store paths, `~/.cache/wiz`
(the helper passes it as `--cache`) and `.grail`; on the self-hosted runner this is the
same incremental path, while a cold cache pays elaboration again for every rerun. A
green shard pays nothing: the classifier only runs after `tests` fails.

**Embedded files.** Lake does not track files a module reads with `include_str`, so each
embedded file gets a library of its own whose `needs` names the file as an
`input_file` (`lakefile.lean`): Lake mixes the file's content hash into that library's
module traces, so editing the file rebuilds the embedding module and its importers, and
the artifact cache never serves a stale one. The only one today is the C runtime,
`runtime/wiz_rt.h` plus `runtime/rt_{core,num,words,data,sys,con}.inc`, embedded by
`runtime/WizRuntime.lean` (library `WizRuntime`, imported by `Wiz/Compiler/C.lean`); the
parts are concatenated in the order of the old single file, so generated C is unchanged.
A new `include_str` goes in such a library too, not in `Wiz` (a `needs` on `Wiz` would
rebuild all of it); `scripts/test-embed.sh` checks the setup (a local
`nix develop -c scripts/test-embed.sh` check, since it needs an incremental Lake build;
CI runs only `scripts/test-runtime.sh`), and `scripts/test-runtime.sh` compiles the
runtime alone with `cc -fsyntax-only -Wall -Wextra`, with `WIZ_API=` and `WIZ_API=static`
(the header's prototypes are checked against the parts), each also with
`-DWIZ_NO_THREADS`, and runs a small C program against the threaded and the one-thread
runtime. The one-thread binary links with stub pthreads (every pthread name it uses is
redirected with `-Wl,--wrap=` to a no-op) and must have no pthread symbols; the program
sends on a channel before receiving, and checks that the waits a second thread would end
stop with their message. It also compiles the header's Emscripten auto-enable with
`-D__EMSCRIPTEN__` (there is no `emcc` in the toolchain, so this is not an Emscripten
build).

## Test layout

Adding a test group touches no shared file:

* **A new group is a new module** `Tests/Groups/<Name>.lean` that ends with
  `builtin_initialize registerGroup myGroup` (`Tests/Harness.lean`). Lake generates
  `Tests/Groups.lean` (an import of every file in `Tests/Groups/`; not committed, see the
  `testGroups` target in `lakefile.lean`) and `Tests/Main.lean` imports it, so the group
  is in the suite as soon as its file exists. Copy a small one (e.g.
  `Tests/Groups/Struct.lean`) to start. Add a selector `=GROUP` to a shard's `select`
  list in `.github/test-shards.json` (or an entry in
  `.github/test-shard-exclusions.json` with the reason it runs in no CI shard);
  `scripts/check-shards.py` fails if the group is in neither. `Group.shard` is only a
  hint shown in the error message now; it does not move a group by itself.
* **New cases of an existing group** go in its module: the group `elab: structural
  types` is `structGroup` in `Tests/Groups/Struct.lean` (`grep -l 'name := "…"'
  Tests/Groups/*.lean` finds a group by name). A helper only one group uses lives in
  that group's module; `Tests/Elab.lean` holds the helpers several groups use (`ok`,
  `fails`, the library loaders, the self-hosted programs, …).
* The older modules (`Tests/Lint.lean`, `Tests/LSP.lean`, …) still list their groups
  (`groups` at their end, concatenated by `Tests/Main.lean`); a new group goes in
  `Tests/Groups/` all the same.

### Differential fuzzing for erasure and optimisation (`=diff-fuzz`)

`scripts/diff-fuzz.py` generates closed Wiz programs from a seed and checks that the
three pipelines that must agree do: the tree interpreter (`#eval`), the IR interpreter
(`#run`, which runs `IR.optimizeProgram` and reference counting) and the C backend
(`wiz run`). It is aimed at the two places where the pipelines differ: **erasure**
(stage 5) and **constant folding and known constructors** (stage 15c). The grammar is
`Nat`/`Bool` arithmetic and the operations `foldNat` treats specially (`Nat.div`/`mod`
by zero, `pow`, `shiftLeft`, the bitwise operations), `if`, `let`, pairs, `Option`,
structural and tail recursion, arrays with a pure list model (compiled only: the
interpreters cannot run the natives), regions as erased type indices, and the
quantity-0 constructs: a `0` argument, `let 0`, a `0` field and a `split` at 0 whose
value diverges, and a function into `Unit` (`erasedFunTy`) stored in a structure and
applied. A program whose erasure is wrong therefore hangs or panics instead of printing.

Programs are batched: one file with many `#eval`s, one with many `#run`s and one C
program printing every result, so 200 programs cost three processes, not 600. A batch
that crashes or times out is bisected to one program; a disagreement is shrunk by
delta-debugging its choice sequence and the minimised source is printed. Exit code 1
means a finding; a missing `wiz`/`python3`/C toolchain is a skip.

```sh
lake test -- '=diff-fuzz'                    # the fast tier: 200 programs, a fixed seed
python3 scripts/diff-fuzz.py --fast          # the same, with the printed report
python3 scripts/diff-fuzz.py --nightly       # today's seed, 2000 programs, shrinking
python3 scripts/diff-fuzz.py --seed 7 --programs 500
python3 scripts/diff-fuzz.py --replay 7 3 12,4,0,...   # one case again
python3 scripts/diff-fuzz.py --self-test     # the detector's panic/timeout paths
python3 scripts/diff-fuzz.py --nightly --pin .lake/diff-fuzz/pins  # keep a finding
```

A campaign is processed in files of `--batch-size` programs (default 200), so a long
run costs three processes per file rather than one enormous C unit; a crash is bisected
inside its file. A missing C toolchain (`cc`, GMP or the GC) makes the compiled pipeline
`SKIPPED`, which the group reports as a skipped case, not a pass.

The group forwards the driver's toolchain flags (`--cc`, `--cflags`, …) to every `wiz`
invocation; a checkout without `grail.local.wiz` therefore needs the toolchain flags on
the command line, or `wiz` must come from a release bundle. The nightly has no workflow
of its own yet: run the `--nightly` command above (or from a scheduled job) with the
checkout's `wiz`. The harness works in a temporary directory under `.lake/diff-fuzz/`
and gives `wiz` a per-run elaboration cache there (removed at the end; `--cache DIR`
keeps one for a series of runs), so a campaign does not grow `~/.cache/wiz`.

### The rejection corpus (`=reject`)

The suite is mostly about programs that must be accepted; `Tests/Groups/Reject.lean` is
the other side: programs the elaborator must turn down, with the diagnostic they must
produce. It covers universe- and level-escapes, `Sort` misuse, missing and looping
instances (an overlapping instance is accepted by design, and an `accept:` case pins
that), ill-typed `implemented_by`, non-structural recursion, missing pattern coverage,
quantity and linearity violations, foreign-function and `glue` mistakes, duplicate
declarations and module names, malformed attributes, bad `deriving`, and private and
opaque-type escapes. A case names the stable error code (or that the error has
none yet) and a fragment of the source its span must cover, so a rejection for the wrong
reason does not pass.

`Tests/Reject.lean` elaborates each program in process through the shared cache
(`/tmp/wiz-reject-corpus-cache`, warmed by the first case) and checks the code, the span
and that no `panic!` was reached. A representative case per class also runs `wiz check`
and requires a nonzero exit (an accepted neighbour requires zero); running it on every
case would add about a second per case. `accept:` cases are neighbours that must stay
accepted, so the corpus cannot be gamed by over-rejection. An `xfail:` case records a
program that is currently accepted but should not be: the reason is in a `Tests.note`
(visible with `--timings`), and the case fails once the elaborator starts rejecting it,
which is when it becomes a `rejected` case. Run the group alone with
`lake test -- '=reject'` (build `wiz` too: `lake build wiz tests`).

## The grail package registry (23m)

`grail update` resolves `Package.require` lines through a **static index** (a directory,
one S-expression file, or a git repository) and writes `grail.lock`; `grail fetch
--locked` materialises that lock and `grail build/test/run/lsp/doc` read only the lock.
`grail update --locked` is a check, not a resolution: it reads the lock, verifies that
the manifest's requirements are pinned, and never reads the index (so a new publication
cannot break CI). CI should run `grail update --locked --require-signature`: that also
refuses a registry lock with no signed index snapshot. (An index without a signed
snapshot is the explicit exception: `--allow-unsigned`, documented in
[install.md](install.md#dependencies); do not use it in CI.) `--offline` makes `update`,
`fetch` and builds use cached index clones and archives only; a missing item is an
error, never a download. `--index URL#COMMIT`
(or `Package.set "index-commit"`) pins the index revision; the lock also records the
index URL and commit that produced it. A URL index must fast-forward from the lock's
commit: a force-pushed/rewritten history is refused unless `--allow-rewind` (TUF's
rollback protection over git's DAG).

`grail.lock` is v3: it records the resolving toolchain, each package's `(size …)`,
`(tree …)` and `(commands …)` as well as its SHA-256, and any `Package.override` from
`grail.local.wiz` (which `--locked` refuses). Entries are flat and sorted; a v1/v2 lock
still parses and `grail update` upgrades it.

Cache layout (under `--cache`, default `~/.cache/wiz`):

| path | contents |
|---|---|
| `grail/downloads/<sha256>` | content-addressed release archives; re-hashed on every use, re-downloaded when corrupt |
| `grail/packages/<sha256>/` | unpacked packages (23n), stamped `.grail-pkg`; `.grail/packages/<name>` links to one |
| `grail/index/` | the cached clone of a URL index (one clone; a directory index is read in place) |

Fetch verifies the SHA-256 **before** unpacking, into a temporary directory, and renames
only after the hash matches, so a bad transfer leaves no partial tree. The archive layout
is one `NAME-VERSION/` with `grail.wiz`; relative `source` paths in a local index are
resolved against the index root (which is what makes the checked-in fixture usable
offline). An index may publish a signed `index/snapshot.sexpr` (+ `.sig`);
`grail update --require-signature --allowed-signers FILE` verifies it offline and pins
its key, sequence and digest in the lock, and `grail index verify` checks one without a
network. `--locked` reads no index, so it checks the signature entry's shape; use
`grail index verify --locked` to re-verify the signature itself. SHA-256 and the lock
still give integrity, the index's git history and review give names, and building a
package still runs its author's code.

`grail vendor [DIR]` (23n) copies the lock's registry archives into `DIR` (default
`vendor/`) as `<sha256>.tar.gz` and writes `DIR/index.sexpr`; the lock is unchanged, so
the same lock works with or without it. `--vendor DIR` (or `Package.set "vendor" "DIR"`) makes
`fetch`/`build`/`test`/`run`/`lsp`/`doc` look archives up by hash in that directory
before the cache or the network. The hermetic CI prelude is:

```sh
grail fetch --locked --offline --vendor vendor   # after `grail vendor` once, committed
grail build
```

`grail cache path|list|verify` inspects the shared cache; `verify` re-hashes every
archive and checks every unpacked tree's stamp, and exits 1 on a corrupt entry.

The hermetic fixture is `Tests/fixtures/fate-index/` (`index/NAME.sexpr`,
`packages/NAME-V.tar.gz`, `sources/` and `make.sh`); `=grail-deps` covers exact/range
versions, the transitive closure, a missing package, a hash mismatch, stale locks,
`fetch --locked` with cold/warm caches, scoped `index/@org/name.sexpr` files, index
rollback, and lock v3 (round-trip, old locks, upgrade, `grail.local.wiz` overrides).
`=grail-vendor` (five cases) covers vendoring, an offline `--locked` fetch from
`vendor/` without a cache, the shared store and the cache commands. `=grail-index`
includes three signed-snapshot cases (a throwaway Ed25519 key via `ssh-keygen`; they
skip when it is absent): the lock records the fingerprint/sequence, offline
verification from the pinned key, and refusal of a tampered or re-signed snapshot, an
expired key, a lower sequence and a same-sequence rewrite. Rebuild the archives with
`cd Tests/fixtures/fate-index && ./make.sh`. There is no network in these tests.

There is also a complete example **index repository** at `examples/fate-index/`
(`index.wiz`, `registry.sexpr`, `index/`, `entries/`, `sources/`, `packages/`, `make.sh`)
and a checker: `scripts/grail-index-check.sh DIR` (also `grail index check DIR`) validates
names, versions, semver requirements, local archive SHA-256s and layouts, `index.wiz`
against the files on disk, and module-prefix conflicts, **offline by default**. CI runs it
on the example; `=grail-index` covers its failure modes. The index repository's layout,
generation rules and the signing/hosting plan (TUF stages; no transparency log yet) are in
`docs/stages/23-grail/index-repository.md`.

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

`wiz build FILE -o OUT --target wasm` is a third path (stage 8f,
[08-backend/wasm.md](stages/08-backend/wasm.md)): it emits a binary WebAssembly module
directly from the IR and does not invoke a C compiler, the C runtime or GMP. Values live
in the module's linear memory; a small checked-in JS host (`web/wasm-host.mjs`) supplies
big integers as `BigInt`s and prints the result. It runs IO-less `main`s over `Nat`/`Int`,
closures, arrays and algebraic data; `wiz run FILE --target wasm` builds and runs it under
Node. The subset boundary is checked at compile time and every module is structurally
validated before it is written; the limits (no reference counting, no IO/FFI, no library
target) are in that section. `--wasm` is the older spelling of the same target.

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

## Reproducible builds

A build is reproducible when the same inputs give the same bytes, wherever the checkout
lives. `scripts/check-repro.sh` tests that by building `Tests/ReproPaths` (pure code, IO,
Unicode, a `link_c` shim, a `--split` build, a `-g` build, the LLVM backend and a grail
package) under two absolute roots, `${TMPDIR}/…/a` and `${TMPDIR}/…/b`. The roots differ
in `PWD`, `HOME`, `TMPDIR`, umask, locale, `TZ`, `SOURCE_DATE_EPOCH`, the cache directory
and `grail -j`; the script compares the generated C, the executables, the `.grail` tree
(including `link.txt`) and the cache entries (names and contents, not the `bin/` memo).

```sh
scripts/check-repro.sh                 # the corpus (needs .lake/build/bin/wiz)
scripts/check-repro.sh --json          # one JSON object on stdout
scripts/check-repro.sh --compiler      # also build wiz and grail under two paths
scripts/check-repro.sh --compiler-a A --compiler-b B
scripts/check-repro.sh --self-test     # the skip and empty-tree rules (no compiler)
python3 scripts/check-repro-report.py [--require-compiler] FILE
                                       # assert a --json result (self-test also)
```

A skip is not a pass: when `wiz` is not built, `grail` is missing or `WIZ_LLC` is not
set, the script exits 2 (with `--json`, `ok:false, status:"skip"`). `--allow-skip`
accepts that explicitly (exit 0, `"allowed":true` in the JSON); CI never passes it. A
label the run must cover cannot be skipped quietly, and a comparison with zero files on
either side is a failure, not `ok, 0 files`. The compiler comparison
keeps `HOME` fixed: elan installs a Lean toolchain per `HOME`, so a different `HOME` is a
different compiler input (and a different `RUNPATH` in the executable), not a path
variation. `--compiler-olean` also compares `.olean` files; Lean stores the absolute
source path in them, so they are expected to differ and are skipped by default.

CI reads the JSON instead of discarding it: `ci.yml`'s corpus step runs
`check-repro.sh --json` and passes the result to `scripts/check-repro-report.py`, which
fails on a run-level skip, an empty check list or any diff/error, and annotates a
skipped compiler comparison as a notice. That PR job does not pass `--compiler` (two
full Lake builds); the nightly `repro.yml` workflow does, on the self-hosted runner, and
runs the reader with `--require-compiler`, so `"compiler": {"status": "skip"}` is a
failure there rather than an invisible pass.

The cheap sources of non-determinism are fixed: `-g` builds map the generated C's
directory and the compilation directory to `.` (`-ffile-prefix-map`, so debug info and
`__FILE__` do not name the checkout); a grail `link_c` file is named relative to the
package in `link.txt`, and its check key hashes its contents rather than its absolute
path; directory walks are sorted; and `scripts/release-tarball.sh` writes a sorted
archive with fixed owners, modes and `SOURCE_DATE_EPOCH`, through `gzip -n`.

The remaining causes are inputs or metadata: diagnostics print the path they were given;
Lean's `.olean`/`.ilean`/`.trace` files store absolute source paths; the Lean toolchain's
`RUNPATH` stores where its libraries are installed; and a split build's parallel tasks
report whichever error finishes first (artifacts are unaffected). The compiler binary,
the generated C and the linked programs are compared byte for byte by the script.

## Build time and memory

### The Lean build (`lake build wiz tests grail`)

The figures in this section are a one-off observation from the parallel-build work on
2026-11-17 (see `wiz-notes/parallel-build.md`). The `wait4` recorder and the run's data
are not committed, so they cannot be reproduced from the tree; treat them as historical,
not as a gate or a baseline.

The build was 530 jobs. On 2026-11-17 it took **1680 s of wall time** with a cold
`.lake` and an empty `LAKE_CACHE_DIR` on the 27 GiB, 32-CPU development host, while
about twenty other agents were building (load average 40–54). The same command with
the shared artifact cache warm is **12 s**, all 530 jobs replayed, so this is the cost
of a new commit or toolchain, not of a fresh worktree. How it was measured: each C
compiler invocation was wrapped in a `wait4` recorder (wall time and `ru_maxrss`),
`lake build -v` gives each Lean job's duration, and the whole process tree's RSS was
sampled every 20 ms for the peak.

| phase | jobs | sum of job wall times |
|---|---:|---:|
| Lean elaboration | 258 | 5110 s |
| C compilation (`:c.o`) | 258 | 4512 s |
| link | 3 | 23 s |

The sum is 9646 s over 1680 s of wall: **Lake 5 has no `-j`, but it does not
serialize** — 43 jobs ran at once at the peak (mean 5.8, because the host, not the
scheduler, was the limit). The peak of the whole tree was 22.0 GiB, but no single job
came near it: the largest were the generated C of `Wiz.LSP` (2.10 GiB) and
`Wiz.Format` (2.02 GiB); the next was 0.78 GiB. The 22 GiB is the sum of roughly
forty concurrent jobs, mostly Lean elaborations of the test modules (0.5–0.9 GiB
each), not one large job. **The 7 GiB cap is a per-compile limit, not the build's**;
a cgroup that small kills the build long before the two big C files.

Those two units were also the tail. They were 29.4 MB and 33.0 MB of C, took 1193 s
and 1203 s to compile (25 % of all job time), and could only start after their Lean
elaboration (297 s and 313 s), so the last 1200 s of the 1680 s wall was waiting on
them. Both hold the same ~630k lines: the compiler specializes the whole elaborator
(the `runFrontend` body and the `Wiz.Elab.Command.elabCommand` cascade) to
`ZeroOneMany` in every module that calls the frontend, and `Wiz.Format` and `Wiz.LSP`
each called it. `@[nospecialize]` on `runFrontend`, its `go`/`go'`/`step`, and
`Query.elaborate`/`go` leaves **one** copy, in `Wiz.Frontend.Frontend`:

| unit | before | after |
|---|---:|---:|
| `Wiz.Format.c` | 29.4 MB, 1193 s, 2.02 GiB | 0.43 MB, 6.4 s, 0.28 GiB |
| `Wiz.LSP.c` | 33.0 MB, 1203 s, 2.10 GiB | 4.6 MB, 57 s, 0.44 GiB |
| `Wiz.Frontend.Frontend.c` | 0.40 MB, 7 s | 29.2 MB, 480 s, 2.55 GiB |
| elaboration of the same modules | 610 s | 379 s |

Two ~30 MB compiles become one, the C of the pair falls from 62.4 MB to 5.0 MB, and
a change to `Wiz.Format` or `Wiz.LSP` no longer costs a twenty-minute compile
(editing the frontend itself still costs one). The cost is dictionary arguments in
the frontend; interleaved A/B of the two binaries on this host, best of five to seven
runs: `wiz check --no-cache lib/Std.wiz` 2.02 → 2.07 s (+2 %), `lib/Text.wiz`
1.42 → 1.50 s (+5 %), `wiz fmt --check lib/Std.wiz` 0.92 → 0.98 s (+6 %). The output
is unchanged: the 25 MB C both binaries emit for the self-hosted compiler (the
fixpoint's stage 1) is byte-identical (`md5 712ae4ca4bfafc63a01767e06ad33022`), and
the `format`, `tooling` and `native` groups and the trust ledger pass. Counting the
changed jobs in the two builds gives 9646 s → about 7600 s (−21 %) of job time; a
cold build after the change was not re-run under the same load, so treat that as the
model's estimate, not a measured whole-build number.

Two other changes were considered and rejected. Compiling the units with narrower
flags (e.g. `-O1`) is the obvious alternative, but Lake gives a module the flags of
its *library* (`Module.leancArgs` is `self.lib.leancArgs`): there is no per-module
`moreLeancArgs`, and a second `lean_lib` for those two modules would rename or
shadow them. Setting `LEAN_CC` to a wrapper would make a plain `lake build` depend
on the environment, which this repository avoids. With the change above there is
only one big unit left, and it is the frontend's.

### The `wiz` memory corpus

Time is not the only way a build dies. A run that peaks at 5 GiB is killed by a
4 GiB memory cgroup whatever its wall time was. The self-hosted checker has a 1 GiB cap
because a `mutual`/`partial` inline-cache change once made its self-check retain far
more; after the `inlineTm` fix `bench/mem-baseline.json` records 412.5 MiB peak in
31.338 s (`python3 scripts/mem-bench.py --update` re-records it). `scripts/mem-bench.py`
measures the peak
resident set of a fixed corpus and gates it two ways:

```sh
python3 scripts/mem-bench.py                 # run, write bench/mem-bench.json
python3 scripts/mem-bench.py --check         # exit 1 on a regression or a cap
python3 scripts/mem-bench.py --update        # re-record bench/mem-baseline.json
python3 scripts/mem-bench.py --self-test     # the thresholds on synthetic series
python3 scripts/mem-bench.py --from-json bench/mem-bench.json --check  # re-check a saved run
```

| invocation | what it measures | cap |
|---|---|---:|
| `check-prelude` | `wiz check --no-cache lib/Prelude.wiz` | 1 GiB |
| `check-std` | `wiz check --no-cache lib/Std.wiz` | 1 GiB |
| `check-text` | `wiz check --no-cache lib/Text.wiz` | 1 GiB |
| `check-json` | `wiz check --no-cache lib/Json.wiz` | 1 GiB |
| `check-example-hdl` | `wiz check --no-cache -I hdl/src hdl/examples/hdl-temporal.wiz` (a large temporal-properties example) | 2 GiB |
| `build-stdlib-bench` | `wiz build --no-cache bench/stdlib-bench.wiz -o bench-out/stdlib-bench` (elaborate, lower, C, `cc`) | 2 GiB |
| `selfhost-checker` | the self-hosted checker checking the whole frontend | 1 GiB |

The `build-stdlib-bench` row is `scripts/mem-bench.py`'s own invocation (its `{out}` is a
temporary path), and `wiz build` accepts only `FILE -o OUT` (`Main.lean`).

The checks are cold (`--no-cache`): a warm content-addressed cache hides the
elaboration a CI runner does on every build. Peak RSS is sampled every 20 ms as the
sum of the process tree's RSS, plus the root's `VmHWM` on every sample, because a
build fans out into `cc`, `as` and `ld`; `ru_maxrss` of the root is the floor for a
process that starts and exits inside one interval. A sampling peak can miss a spike
shorter than the interval: treat a number as ±5 % (the same caveat as the fixpoint's
timings). The self-hosted checker is built once as preparation (`wiz build` of the
concatenated `selfhost/*.wiz`, kept under `bench/.build/mem/`); its *run* is the
corpus entry. `--phases` adds the only phase profiler that exists today: after the
corpus, it runs the test driver's `--probe-checker`, which prints the checker
*build*'s RSS and `VmHWM` after each compiler phase (frontend, erasure, lowering,
hoisting, optimisation, C emission). That breakdown is recorded in the JSON but is
not part of the gate; with a future `wiz build --profile`, the same slot can carry a
per-phase split. It needs the test driver (`lake build tests`) and about 6 GiB for
the in-process checker build, so the nightly job does not pass `--phases`.

There are two limits, and both are failures:

* **relative** — a peak above the baseline's peak by more than 25 % (the baseline
  records the limit; `--tolerance` overrides it for one run). RSS is noisier than
  time, so this is looser than the timing gate's 10 %.
* **hard cap** — the per-invocation budget in the table. `--scope` also wraps each
  invocation in `systemd-run --user --scope -p MemoryMax=<cap>`, so the kernel
  enforces the cap live and an over-cap run exits 137 instead of merely failing
  afterwards. Without `--scope` the measured peak is compared with the cap.

The baseline is `bench/mem-baseline.json`; the run record is `bench/mem-bench.json`.
`--check` also fails when an invocation is missing from the baseline, when the
corpus changed its arguments or cap, or when an invocation exits nonzero — a stale
baseline cannot silently stop checking an entry. `--markdown FILE` appends the table
to a CI step summary.

Absolute RSS depends on the C compiler, the GC version, the page size and what else
shares the machine; the checked-in baseline was recorded on the 27 GiB development
host with about twenty concurrent agents, so the relative limit and the caps are the
decision, not the absolute numbers. Re-record with `--update` after a deliberate
change (a new corpus entry, a new allocator), and keep the old baseline in the PR.

Today's numbers (2026-11-15, 27 GiB host, 32 CPUs, Linux 7.3.3, GCC 16.2,
Boehm GC, about twenty agents sharing the machine; `wiz` built from `627b48f6`,
peak of the recorded samples, ±5 %):

| invocation | peak RSS | cap | wall (median) |
|---|---:|---:|---:|
| `check-prelude` | 99 MiB | 1 GiB | 1.1 s |
| `check-std` | 104 MiB | 1 GiB | 1.7 s |
| `check-text` | 104 MiB | 1 GiB | 1.5 s |
| `check-json` | 105 MiB | 1 GiB | 2.3 s |
| `check-example-hdl` | 140 MiB | 2 GiB | 35 s |
| `build-stdlib-bench` | 222 MiB | 2 GiB | 146 s |
| `selfhost-checker` | 413 MiB | 1 GiB | 31 s |

The worst offender is the self-hosted checker at 413 MiB: it is 40 % of its 1 GiB
cap and an order of magnitude above the module checks, which is why it has its own
entry. The cap exists because of that inline-cache regression; the baseline records
412.5 MiB (`scripts/mem-bench.py --update` re-records it).
The stdlib build is the slow entry (146 s; two samples, because the peak is stable),
not the largest peak. The 164 KiB `hdl-uart-temporal` example is not in the corpus:
a cold check takes over four minutes on this host, so the corpus uses
`hdl-temporal` (294 lines, 35 s cold) instead and keeps the nightly bounded.

The nightly `.github/workflows/bench.yml` runs this as a second job, `mem`, with
`--check --markdown "$GITHUB_STEP_SUMMARY"`. It runs after the timing job `bench`,
whatever that job's result, so the two never share the runner, and it uploads
`bench-out/mem-bench.json` as an artifact. It declares 3 GiB (`WIZ_MEM_BENCH_GIB`).
Its largest step is the preparation, building the self-hosted checker, which peaked
at about 1.8 GB after the `inlineTm` fix. A cold run records that build's peak and
wall time as `checker_build` in the JSON and in the step summary, so the declaration
can be checked against each night's number. The build is not gated. The job's Nix
step only substitutes (`--max-jobs 0`): `wiz` comes from the timing job's build on
the same runner or from Cachix, and a Lean compile never runs under this budget.
`--phases` (about 6 GiB, the in-process checker build) is not part of the nightly.
## Build attestations

`wiz build --attest [FILE]` writes an unsigned in-toto statement (a DSSE-style envelope
with an empty `signatures` array) about the build: the source file and Git commit/dirty
flag, the SHA-256 of every input (the file, imported modules by name, `link_c` files), the
`wiz`/`cc`/`llc` identities, the compiler flags, and the output binary's and generated
C's hashes. The default path is `OUT.attest.json`.

```sh
wiz build hello.wiz -o hello --attest
wiz verify hello                    # reads hello.attest.json; 0 = match
wiz verify --attest hello.attest.json hello
wiz verify --artifact-only hello    # artifact only: the sources need not be present
```

`wiz verify` re-hashes the artifact, the recorded inputs (pass the same `-I` roots; a
module is looked up by name) and the manifest root, and exits 1 on any mismatch. It does
not check a signature: a non-empty `signatures` array is an error, so an unsigned
verifier never accepts a "signed" claim it cannot check. An unsigned statement proves
integrity relative to the statement, not that its author was honest — signing and
independent rebuilds are the next steps (`wiz-notes/build-attest.md`). Absolute paths
appear for toolchain binaries and for inputs outside the invocation directory; no
environment variables or timestamps are recorded. `grail build --attest DIR` writes one
statement per executable.
## Reproducible source tarball

`nix build .#release-tarball` (the same derivation as `.#source-tarball`) writes a
deterministic source tarball and its manifest; `scripts/source-tarball.py` does the same
for any checkout:

```sh
nix build .#release-tarball          # result/ holds the four files below
python3 scripts/source-tarball.py --out dist --mode git
scripts/test-source-tarball.sh       # the check CI runs
```

The output is

```
wiz-<version>-src.tar.gz                 the source tree under one wiz-<version>/ directory
wiz-<version>-src.tar.gz.manifest.json   canonical JSON: every path, size and SHA-256
wiz-<version>-src.tar.gz.sha256          the tarball's sha256sum line
wiz-<version>-src.tar.gz.cdx.json        CycloneDX 1.6 SBOM for the source tree
```

The manifest's `sbom` object records the SBOM's file name, SHA-256 and component count.
The SBOM lists every source file as a component (path, size, mode, SHA-256), plus the
external inputs and build tools: the five `scripts/bundle-cc.sources` downloads with
their licence expressions, the locked Nix inputs in `flake.lock`, `lean-toolchain`, the
release workflow's actions and runner, and Emscripten when the workflow builds the web
infoview. It contains no timestamps or absolute paths, so it is byte-identical for the
same tree.

`<version>` is `Wiz/Version.lean`'s version (`0.1.0-dev` today). The tar entries are
sorted, every mtime is the source date epoch, uid/gid are 0 with empty uname/gname,
files are 0644 (0755 when executable) and directories 0755, and the gzip header carries
the epoch and no file name. `SOURCE_DATE_EPOCH` is honoured; without it the commit time
is used (0 outside a git checkout), and the Nix target passes the flake's commit time.
In git mode (`--mode git`, the default in a checkout) the file list is `git ls-files`,
so an untracked scratch file or build output cannot leak in; in tree mode (`--mode
tree`, what Nix uses) every regular file under the root is taken, and the exclusions
below apply. Symlinks are rejected.

**Included**: all tracked files, except the exclusions below — the Lean sources
(`Wiz/`, `WizMeta/`, `Grail/`, `*.lean`), the runtime (`runtime/`), the C support code
(`c/`), the standard library (`lib/`), the self-hosted toolchain (`selfhost/`), grail
and tower (`tower/`), the editors (`editors/`), the infoview and web sources
(`infoview/`, `web/`), tests and examples (`Tests/`, `examples/`), `docs/`, `scripts/`,
the build files (`lakefile.lean`, `lake-manifest.json`, `lean-toolchain`, `flake.nix`,
`flake.lock`, `devenv.*`, `grail.wiz`), CI (`.github/`) and the licence and prose files
(`LICENSE`, `COPYING.RUNTIME`, `README.md`, `CHANGELOG.md`, `ROADMAP.md`).

**Excluded**: VCS and tool state (`.git/`, `.lake/`, `.grail/`, `.wiz-cache/`,
`.devenv*`, `.direnv/`), caches and package directories (`__pycache__/`, `node_modules/`),
build outputs (`dist/`, `web/out/`, `cc-bundle/`, `bundle-downloads/`, `*.olean`,
`*.ilean`, `*.o`, `*.a`, `*.so`, …), the developer's local files (`grail.local.wiz`,
`wiz-toolchain.local`, `Tests/Groups.lean`), and `drafts/` (wishful code the release
does not build). The manifest lists the exact set, so a reviewer need not trust this
paragraph.

The manifest is canonical JSON: sorted keys, compact separators (`,` and `:`), no
trailing newline, so its bytes depend only on its content (`schema:
wiz-source-tarball/v1`). Shown formatted; the file is one line:

```json
{
  "files": [{ "mode": "0644", "path": "LICENSE", "sha256": "…", "size": 35140 }, …],
  "name": "wiz-0.1.0-dev",
  "version": "0.1.0-dev",
  "revision": "<40-hex commit, or unknown; a dirty checkout ends -dirty>",
  "schema": "wiz-source-tarball/v1",
  "sourceDateEpoch": 1700000000,
  "sbom": { "components": 764, "file": "wiz-0.1.0-dev-src.tar.gz.cdx.json",
            "schema": "CycloneDX-1.6", "sha256": "…" },
  "tarball": { "file": "wiz-0.1.0-dev-src.tar.gz", "sha256": "…", "size": 1234567 },
  "tree": { "bytes": 8700000, "files": 580, "sha256": "…" }
}
```

`tree.sha256` is the SHA-256 of the sorted lines `<file sha256>  <path>\n` over
`files`; it is a content root, independent of the epoch, modes and compression. The
tarball digest in `tarball.sha256` is the artifact's subject digest; an attestation
(the E1 verifier sketched in `wiz-notes/attested-enclave-builds.md`) binds a TPM quote
to the manifest by using the manifest's SHA-256 as the quote's `extraData`, and checks
the file list and tree root against the tarball it was given. Nothing in the manifest is
signed yet.

**What is reproducible.** The source tarball is byte-identical for a commit across
directories, caches, umask, `TZ`, `LANG`, `HOME` and `SOURCE_DATE_EPOCH` (when the
epoch is the same): `scripts/test-source-tarball.sh` builds it twice in different
directories with different environments and compares with `cmp` and `sha256sum`, and CI
runs that check. `nix build .#release-tarball --rebuild` rebuilds the derivation in a
different build directory and compares the output. Changing `SOURCE_DATE_EPOCH`
changes the mtime headers and the gzip stream, hence the tarball's SHA-256, but not the
per-file hashes or `tree.sha256`. The gzip stream also depends on the zlib version that
wrote it; the tar content and the tree root do not.

Generated C is already reproducible (same C for the same program across paths, caches,
environments and even architectures); binaries are reproducible with the same compiler
but differ across C compilers and architectures, so a cross-build's *binary* digest is
not comparable. The binary release tarball (`scripts/release-tarball.sh`, what tower
installs) is not yet deterministic: it copies build outputs and adds files in checkout
order, so its digest can differ between builds of one commit.

## Release SBOM and provenance

`scripts/release-sbom.py` takes the source tarball, its canonical manifest (and the
source SBOM recorded in it) and the binary tarball, and writes:

```
wiz-<arch>-linux.tar.gz.cdx.json   CycloneDX 1.6 for the binary tarball
provenance.intoto.json             in-toto Statement v1, SLSA provenance v1 predicate
```

The binary SBOM lists every file in the tarball with its size, mode and SHA-256; the
bundled C toolchain's `cc/VERSIONS` is recorded, along with the `scripts/bundle-cc.sources`
inputs, the `flake.lock` Nix inputs, `lean-toolchain`, and the release workflow's actions,
runner and Emscripten version. Both SBOMs name their licences (Wiz's GPL-3.0-or-later
with the runtime exception, and the third-party expressions from the NOTICE); the
runtime exception is recorded as a property because it is not an SPDX-registered
exception.

The provenance's `subject` is the source tarball, source manifest, source SBOM, binary
tarball and binary SBOM, each with its SHA-256. Its predicate records the builder id
(the release workflow and ref), commit, source date epoch, channel, the source tree
digest, the Lean toolchain hash, the locked Nix inputs and the bundled C inputs. It is a
**SLSA-style** statement: an in-toto Statement v1 with the SLSA provenance v1 predicate,
not a hosted SLSA build, and **no SLSA level is claimed** (`wiz:slsaLevelClaimed` is
null). Signing is optional and uses the E1 offline Ed25519 path
(`scripts/attest/wiz-attest keygen|sign`): with `--sign-key` the statement is written as
a DSSE envelope (`provenance.intoto.json.dsse`) plus a detached SSHSIG; without a key it
is an unsigned claim. The release workflow reads the key material from the
`WIZ_ATTEST_KEY` secret on pushes and tags, skips signing on pull requests, and skips
it when the secret is absent.

`python3 scripts/test_release_sbom.py -v` builds a tiny source tree and a fake binary
tarball and checks that both SBOMs parse, every component digest matches the archive,
the manifest and provenance digests agree, two runs are byte-identical, a tampered SBOM
is rejected, and the optional signature verifies. CI runs it in the `source-tarball`
job, and `release.yml` runs it before generating the assets. A Nix closure can be added
with `--nix-closure-json` (`nix path-info --json --recursive`); the GitHub release
tarball is built outside Nix, so only the locked inputs are recorded there.

## Continuous integration

`nix develop` (or direnv: `.envrc` is `use flake`) gives the toolchain the tests need
besides Lean (see `flake.nix`): GMP and
LLVM's `llc` for the C and LLVM backends, Boehm GC for the self-hosted backend, a C
compiler, yosys for synthesis, Node for the Wasm modules, and elan, which installs the
Lean in `lean-toolchain`. Entered at the
repository root, it writes this machine's paths to the uncommitted `grail.local.wiz`,
which grail and the test driver read (`Tests/Main.lean`; flags to `lake test -- …` win);
`wiz` takes flags. Nothing reads environment variables.

GitHub Actions (`.github/workflows/ci.yml`) runs on pushes and pull requests to
`master`. The toolchain is built **once**, with Nix: the `build` job runs
`nix build .#wiz .#tests` (nixpkgs' Lean, no Lake artifact cache) and publishes those
two store paths to Cachix with

```sh
nix develop .#ci -c cachix push badlydrawnwizards $(nix path-info .#wiz .#tests)
```

The shell `.#ci` carries `cachix` from the flake's locked nixpkgs, so no global
registry lookup is involved. `CACHIX_AUTH_TOKEN` (the repository secret) is in the
master push step's environment only. A Nix build has no Lake artifact cache: a commit's
first build compiles every module in the sandbox (Lean comes from nixpkgs), and a rerun
of the same commit substitutes the store paths. Only a push to master writes the
trusted cache; a pull request's `build` writes its own untrusted cache instead
(`CACHIX_PR_NAME` and `CACHIX_PR_AUTH_TOKEN`), and without that secret it publishes
nothing and its shards build the paths. A merge-queue run publishes nothing either, so
its shards build too. The `docs` job builds `.#reference` (the standard library's
reference manual, made with the cached `wiz`) on a push, off the shards' critical path.
Every job pulls from Cachix through `cachix-action`, which is set up for substitution
only (`skipPush: true`); on a pull request it reads the trusted cache anonymously, and
the jobs that substitute this commit's store paths (the test shards, `trust-ledger` and
`web`) also add the PR cache as an extra substituter for that job only. No job on the
critical path runs `lake build` directly or saves a
`.lake` Actions cache. The shards run the Nix-built test driver (`packages.tests`), not
`lake test`, and symlink the store `wiz`
and `grail` into the checkout's `.lake/build/bin`, which some cases and
`scripts/trust-ledger.sh` name directly (the driver also carries the wrapped `wiz` and
`grail` beside itself, which `Tests/Groups/Grail*.lean` look for). The dev shell (`nix develop`)
is still what puts `cc`, `llc`, z3, cadical, yosys, Node and Neovim on `PATH`, and it writes
`grail.local.wiz` for the cases that compile C.

The Nix build is about 353 MB for `wiz` (1.8 GB with its closure: Lean, GMP, Boehm GC,
LLVM) and 165 MB for the test driver (2.0 GB with its closure, which includes the wrapped
`wiz` it carries beside itself), so a shard's substitution is a download, not a compile. The store path is content-addressed: the same
sources give the same path, and a shard on another architecture (the aarch64 caveat in
[ci-runner.md](ci-runner.md)) has a different one and builds it there. The weekly
bootstrap fixpoint and the release workflow still use Lake and the elan toolchain, so the
setup action keeps the elan cache for those
(`lean: true`); it is skipped in the Nix jobs (`lean: false`).

* **The test suite** runs in parallel shards, one job per entry of
  `.github/test-shards.json` (each entry is a list of test-driver selectors, the same
  ones `lake test --` takes; the shards run the Nix-built `tests` binary). The plan is
  **total**: every group `tests --list` reports is selected by a shard's selectors, or
  named in `.github/test-shard-exclusions.json` with the reason it runs in no CI shard
  and an owner. A group with neither is an error naming it (and its `Group.shard` hint,
  if any), so a new group cannot silently join another shard's queue; there is no
  default-shard fallback. The build job runs `scripts/ci.py check-shards` (the same
  check as `scripts/check-shards.py`), which also fails on an exclusion whose group does
  not exist or which a shard selects after all, and on a `.github/skip-allowlist.json`
  entry whose group or case no case matches; `check-shards --self-test` checks each of
  those failures on stand-in drivers (`scripts/check-shards.py --groups FILE` runs the
  group-totality half against a captured `lake test -- --list`). The check also runs
  end to end on the matrix the jobs are started from. See "Test layout" below for where
  a new group goes. Each shard's job summary has a table of every case's time
  (three decimals), group subtotals and the shard's total; the `CI result` job sums the
  shards up (a table of shard totals and the grand total, and the 15 slowest cases) and
  uploads every case's time as the `test-timings` artifact.
* **The examples are tests** (the `examples` shard, group `examples`): every
  `examples/*.wiz` is compared with its `.expected` exactly as `grail test` does (the
  same `runTests` helper the tour group uses), in a marker-guard case and three cases
  split by name, so a library change that changes an example's output fails CI instead
  of only a command a contributor runs by hand. An example with `-- test: skip REASON`
  (the benchmarks) is reported as skipped, not passed; one with `-- test: run` has
  `main`'s compiled output as its oracle. The guard fails when an `.expected` is not
  the shape its marker produces: program output (such as a bare digest) under a check
  marker, check messages under a run marker, a check-message path that names another
  file, or a missing `.expected`. The shard runs when `examples/`, `lib/` or
  `drafts/feral/lib/` changes, and (like every shard) when the Lean sources or the
  harness change.
* **Documentation style** (the `docs_style` job): `scripts/check-docs-style.py` fails on
  absolute paths from an agent's scratch tree, internal `agent/...` branch names and AI
  worker roles, U+2705 status checkmarks, and decision/step phrases attributed to
  "the user" in `README.md`, `ROADMAP.md`, `CHANGELOG.md` and `docs/**/*.md`. It runs the
  script's fixtures (`--self-test`) and then the check, on every push and pull request
  (including docs-only ones), and `CI result` requires it. No code block is exempt; a
  reviewed exception goes in the script's `ALLOW` list with a reason.
  The same job runs `scripts/check-doc-links.py`: every relative link and `#anchor` in
  those files and in `docs/**/*.html` must resolve, using GitHub's heading slugs. Links
  to `wiz-notes/...` are reported as external notes (the notes live outside the
  repository) and `http(s)` links are reported but not fetched, so CI needs no network.
* **The preludes** (the `prelude_drift` job): the self-hosted frontend's embedded
  prelude (`preludeText`, `selfhost/Frontend.wiz`) is a hand-written subset of
  `lib/Prelude.wiz`, and the Wasm playground compiles that frontend. Every CI run
  (including docs-only pull requests) runs `scripts/check-prelude-drift.py`, which
  compares the two semantic surfaces
  (names, kinds, constructors and fields), fails a `lib/` prelude value declaration
  that is not mirrored in the embedded copy or reviewed in the script's exception list,
  and fails when a reviewed exception goes stale. It also reports the names the page
  promotes without their library import (`List.map`, `String.length`, the
  `IO`/`Std`/`Bytes` names). No build, well under a second, and `CI result` requires it;
  the copies, the current gaps and what the real fix costs are in
  [stages/21-bootstrap.md](stages/21-bootstrap.md#the-two-preludes-and-the-drift-check).
* **Documentation examples** (the `docs_examples` job, and a step in `build`):
  `scripts/check-docs-examples.py` checks every fenced block marked `wiz` in `README.md`
  and `docs/**/*.md` with `wiz check` and runs the blocks marked `wiz run`, comparing
  their output with the block beside them; a `wiz no-check` block is an explicit
  exception.
  Relative links and `examples/...` references must resolve. On a docs-only pull request
  `docs_examples` substitutes the Nix-built `wiz` from Cachix (the same store path
  `build` publishes); a pull request that changes code runs the same check in `build`.
  Its cache (`.lake/docs-examples`) is keyed by the Lean sources that build `wiz`, so a
  docs-only run is seconds and a toolchain change invalidates it.
* **The documentation site** (the `docs` and `deploy-docs` jobs): on a push to `master`
  only (not a pull request, the weekly run or a manual run), `docs` copies the two Wasm
  modules that `web_modules` built (`wiz-web`, `wiz-playground`), the standard library's
  pages with
  `wiz doc --lib` (source links to the commit; a restored elaboration cache makes this
  a replay, "Documentation site" below) into `doc-site/docs`, and the landing page
  and the static playground around them (`web/build-site.sh`); `web/check-site.sh`
  checks that `/`, `/docs/` and `/playground/` exist and that the landing page's local
  links resolve. It uploads the tree as the artifact `wiz-docs` (3 days, for debugging),
  and `deploy-docs` publishes it to GitHub Pages. Neither job is a required check, so a
  Pages outage does not fail the suite. See "Documentation site" below.
* **The playground and the site's JavaScript** (the `web` job): on a pull request that
  changes `web/**` (and on a push), `web/test.sh` runs with `WIZ_WEB_NO_BROWSER=1`. The
  three Wasm modules (`web/build.sh`, `web/build-playground.sh` and the playground's Loom
  UI, `web/build-playground-ui.sh`) are not built here: the `web_modules` job builds them
  once as the Nix derivations `packages.wiz-web`, `packages.wiz-playground` and
  `packages.wiz-playground-ui` (flake.nix) and publishes them to Cachix, and `web/test.sh`
  copies those directories (`WIZ_WEB_FROM`, `WIZ_PLAYGROUND_FROM`,
  `WIZ_PLAYGROUND_UI_FROM`; `web/modules-from-store.sh` fails the job on a miss instead
  of rebuilding) and then runs its browser-free half: `web/scroll-search_test.mjs`;
  `web/test-bench.sh` (the
  benchmark page's fixtures and the site check's rules for it);
  `web/playground_lsp_test.mjs` and
  `web/infoview_page_test.mjs` (the language client and goals pane shared by the
  playground and the infoview page, and the page's URL rule); `web/selfhost_lsp_test.mjs`
  (the in-page server shim, against stubs); `web/node_test.mjs` and
  `web/playground_test.mjs` (the two modules); `web/playground_ui_test.mjs` (the whole
  page as a Loom app, mounted from the built module with the driver and the DOM double);
  `web/doc_node_test.mjs` (a `wiz doc` page's JSON). `web/framework/test.sh` (the Loom
  framework's browser half, in a Node DOM double, plus the driver's event strings) and
  `web/playground-loom-test.sh` (the output pane and editor components) run beside it.
  `CI result` requires the job when `changes` selects it. The Chromium half
  (`web/chrome_test.mjs` and `web/doc_chrome_test.mjs`: a served page over the DevTools
  protocol) needs a browser and stays local.
* **Source tarball and supply chain** (the `source-tarball` job):
  `scripts/test-source-tarball.sh` builds the release source tarball twice in
  different directories and environments, compares the archives, manifests and
  source SBOM, and checks the exclusions; `scripts/test_release_sbom.py` checks
  that the source and binary SBOMs and the provenance parse, match every archive
  digest and are byte-identical on a second run. The `build` job also runs
  `nix build .#release-tarball --rebuild` ("Reproducible source tarball").
* **Trust ledger** (a step in the `build` job, before any shard):
  `scripts/trust-ledger.sh --check --strict-legacy` runs the
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
  case counts as its group's median, with the programs most of its group uses.
  `"split-cases": true` gives up that first rule for a shard whose cases are siblings
  over disjoint inputs (the four parts of `selfhost-libdiff`, one file range each), where
  spreading them over the jobs is worth a build per part; `part_cost` charges each part
  that build. The baseline holds only the split shards' cases, one per line
  (`selfhost`, `library`, `scaling`, `selfhost-libdiff`; the last is split into four cases
  over `lib/` and `scry/` by file index). `scripts/ci.py plan` shows the parts and their
  estimates. The heavy groups have shards of their own (`hdl`, `semantics`), so adding a
  slow case there does not unbalance `library`.
  To refresh the baseline from a CI run:
  `gh run download RUN -n test-timings && scripts/ci.py baseline timings.jsonl > .github/test-timings.json`.
* **`"parts"`.** A shard with `"parts": N` splits one case's *work*, not a set of cases:
  it runs as N jobs `NAME-1` … `NAME-N` with the same selectors, each carrying
  `"part": "i/N"`, which the workflow passes as the driver's `--part i/N`. The case
  partitions its own file list by index (`libDiffPart`: the file at index `k` of the
  sorted list is in part `k % N + 1`), so the parts are deterministic, disjoint and
  their union is the case, unchanged in what each file is compared against.
  `.github/libdiff-corpus.txt` is the manifest of the files one whole sweep compares:
  every `*.wiz` under `lib/` and `scry/` in `LC_ALL=C` order, with no exclusions, and
  `scripts/check-libdiff-corpus.sh` (in the static gate, with `--self-test`) fails when
  the manifest and the tree disagree, so no file can silently drop out of the sweep.
  `selfhost-libdiff` here is a `split` shard (`"split": 2, "split-cases": true`) of four
  contiguous file-range cases, so it keeps a `.github/test-timings.json` entry per case,
  unlike a `"parts"` shard.
* **Rebalancing.** To re-derive the baseline *and* the `"split"` counts from many runs
  (after a perf fix, or when a group grows), fetch the last runs and rebalance:

  ```sh
  r=$(mktemp -d)
  scripts/ci.py fetch-runs --branch 'master|integration/.*' 14 "$r"
                                               # $r/RUN/timings.jsonl and jobs.json
  scripts/ci.py rebalance "$r"/*               # report only
  scripts/ci.py rebalance --write "$r"/*       # .github/test-timings.json, test-shards.json
  ```

  A case's time is its median over the runs, and each part's prediction is scaled by
  its shard's measured wall time over its case sum (`"jobs"` overlaps cases: `library`
  runs at about 0.86 of its case sum). The split counts grow a part at a time, to the
  shard with the longest part, until the job budget (`--jobs`, default the current
  number of test jobs) is used or another part would not shorten the longest one; a
  long job that cannot be split does not stop it. It exits with an error if the parts
  do not cover every case of the split shards exactly once. The case list is the test driver's (`--bin`), or the last run's; cases that no
  run has measured yet (a case just split) can be given with `--assume TSV`
  (`GROUP<TAB>CASE<TAB>SECONDS`, or `drop` for a case that is gone). It prints the
  predicted time of every job under the current and the new counts.
* **`"jobs"`.** A shard may say `"jobs": N` to give the test driver `--jobs N` (above): its
  opted-in groups run N cases at a time, and a lone case may use N workers itself.
  Only set it on a shard whose groups were verified (and opted in) to be safe in
  parallel; `core`, `library` and `backends` use 4 on the 4-core hosted runner.
  `selfhost-libdiff` needs no `"jobs"`: each of its four cases picks auto (the CPUs minus
  one, capped by the free memory), so a 4 vCPU / 16 GB runner runs 3 files at `--mem`
  (4096 MB) and a 20 GB one could run more; a matrix of heavy shards on 16 GB runners
  cannot OOM it. (`"jobs"` would not help it either: the memory cap stops it below the
  CPU count, and the sweep's cost is per file, so the lever is fewer files per job — the
  split.) A shard of one long case (`grail-selfhost`, `hdl-verified`) and the shards that
  build a shared program (`selfhost`) keep 1. A case's `seconds` stays its own
  process's time, so shard balance is unaffected.
* **Shard order.** `scripts/ci.py matrix` lists the shards longest first, by the same
  estimated case times the split uses (a shard that selects no case goes last, by name).
  GitHub starts a matrix in the listed order and its 20-concurrent-job cap
  leaves the tail waiting: in run 44333554608 `test (prop)` started 16 minutes after the
  wave did, so the long shards must be at the front. Only the split shards' cases are in
  the baseline, so a non-split shard is estimated from the cases it selects (a new case
  counts its group's median, 1 s when the group is unknown); the shards that are one
  long case without an entry (`grail-selfhost`, `semantics`, `hdl-verified`) therefore
  estimate low and sort late, and giving them entries in `.github/test-timings.json`
  would refine the order.
* **Shard balance.** CI's wall time is its longest job, so the invariant is that **no
  test shard's test time is over 1.5× the median shard's**. Every split shard's cases
  have an entry in `.github/test-timings.json`, and no shared program is built by two
  parts of one split shard (a `"split-cases": true` shard excepted: its parts each build
  it by design, and the estimates charge for it). It is tracked in two places:
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
  limit cannot be split by `"split"` alone: `grail-selfhost` is one case of several
  minutes, and `selfhost-libdiff` was one of 45 minutes. Split such a case in its test
  instead, into cases over parts of its input that together check the same things:
  `selfhost-libdiff` is now four cases, each a contiguous range of `lib/` and `scry/` by
  index (`"split-cases": true`, so the splitter may put them in different jobs), about 16
  minutes each including the self-hosted compiler build it must do again, plus one case
  that checks the four ranges cover the file list exactly once. `scaling`'s sweep of the
  induction hypotheses over `lib/` and `examples/` (up to 31 min as one case) was one
  case; it is now nine cases (one for `lib/`, one for the modules checked apart, six
  over the examples, and one that checks that the six cover every example once), measured
  on CI in `.github/test-timings.json` (1330 s in total, the longest 229 s), so the
  shard's parts can each hold one.
* **Shard packing (2026-11-19).** The 20-concurrent-job cap leaves a 32-job matrix with a
  second wave, so it is natural to ask whether packing the cases into at most 20 jobs is
  shorter. It is not, by enough: the current expansion's longest job is 28.6 min of test
  time, a packing that keeps the large shards' path filters and runner classes is 28.1
  min, and even merging shards across filters reaches 25.3 min — under the 5-minute bar,
  and the remaining queueing is other workflows sharing the cap, not this matrix. See
  [ci-shard-packing.md](ci-shard-packing.md) for the numbers, the packing tables and
  what a later attempt would have to change.
* **Skips.** A green run must have run its cases: a skipped case is not a pass, and a
  group that skipped wholesale means CI tested nothing there. The `CI result` job runs
  `scripts/ci.py check-skips` on the shard logs and `--timings` files, and fails when
  * a group's cases all skipped and the group is not in
    `.github/skip-allowlist.json`. Each entry names exactly one `case` (there is no
    whole-group entry), the reason it may skip for, an owner, and an `expires` date
    (`YYYY-MM-DD`); the case matches exactly, the reason matches the start of the
    skip's reason, and an entry past its date is an error until it is renewed with a new
    reason. The self-host parity entries also carry their `parity` code;
  * a skip names a tool the dev shell must provide (`cc`, GMP, Boehm GC, yosys, Node,
    nix, `llc`, z3, cadical, the `wiz`/`grail` binaries): that is a gap in `flake.nix`'s
    `devShells.default`, not an environment skip, even for an allow-listed group. A tool
    that is only needed on some machines (Icarus Verilog, an ARM toolchain) is excused by
    the allow-list instead;
  * a group's unexplained skipped ratio is over 25% (`--max-ratio`), counted over all
    of the group's cases in every shard, so moving cases between shards (a refreshed
    `.github/test-timings.json`) cannot change the verdict;
  * the logs parse no records at all: an empty or unreadable log proves nothing, so
    "No skips: all 0 cases ran" is not a pass.

  Explained skips are reported in the summary (with the reason and the allow-list owner)
  and give a warning annotation, never a failure. Skips that are not whole-group and stay
  under the ratio also warn, so a few skipped cases are visible without blocking. The
  step first runs `scripts/ci.py check-skips --self-test`, which checks the rule on
  synthetic logs (all-skip, partial-skip, clean, an allow-listed group, a required tool,
  an expired or case-less entry, an empty record set) without running the suite. Adding
  an allow-list entry needs a real reason and an expiry date, and the entry names the one
  case it excuses: prefer putting the tool in the dev shell.
* **The Scry tool's own goldens** (`.github/workflows/scry.yml`) run `cd scry && grail
  test` over the 26 `scry/tests/*.expected` files, on changes to `scry/**`,
  `Wiz/**` or `selfhost/**`. The Lean-side `=scry-*` groups test the
  library through the host; this is the package's own suite, and no other job ran it
  (`golden-diff.yml` only *shows* what `--update` would write, after a shard failed for
  another reason). The workflow never passes `--update`: a non-zero `grail test` fails,
  and a later step fails if anything rewrote `scry/tests`. Measured on a loaded 32-core
  box: 11.5 min for `grail build scry` and 14 min for the 26 tests, peak ~220 MiB, so it
  runs on `ubuntu-latest` with a 60-minute job timeout and needs no memory reservation.
  It is not part of `CI result` yet: it is its own required-check candidate.
* **The exercise tree** is checked only for a release tag: the `exercise tree` job of
  `release.yml` generates it with `scripts/mkexercises.py` into a temporary directory
  and builds it (`lake build wiz grail tests`), and the tarball job (which publishes)
  waits for it. Pull requests and master pushes don't build it. It does not run the
  exercise tree's tests (almost all of them fail by design). See
  [exercises.md](exercises.md).
* **The bootstrap fixpoint** (`scripts/fixpoint.sh`) runs **three stages** by default.
  Stage 1 is the self-hosted compiler built by the Lean `wiz build`; it compiles the
  whole toolchain to `self1.c`. Stage 2 is that C compiled with `selfhost/rt.c` and
  Boehm GC, compiling the toolchain to `self2.c`, and stage 3 is `self2.c` compiled the
  same way, compiling to `self3.c`. The script prints every stage's size and md5 and
  marks each stage after the first PASS/FAIL against stage 1; all three C files must be
  byte-identical (`--stages N` for more stages, 2 for the old two-stage check; `--keep`
  keeps the C files and binaries, and `--compare-only` re-checks kept ones).
  Stage 1 = stage 2 shows that the C emitted by the Lean-built compiler is reproduced by
  the compiler that C builds. Stage 2 = stage 3 shows that reproduction is a fixed point
  and not one coincident round. The comparison covers the generated `self.wiz` input in
  the selected mode (`--rc` for reference counting): it shows that code generation is
  deterministic and does not depend on whether the compiler came from Lean or from C. It
  does not show that the C is correct (it is compiled with `-w`), that the compiled
  toolchain behaves correctly (the test suite covers that), or anything about other
  inputs, flags, C compilers or GC versions.
  The self-compile needs about 6 GiB; the script names that requirement if a stage is
  killed for memory (exit 137). Run it locally with `nix develop -c
  scripts/fixpoint.sh` and a 6 GiB reservation.
  The weekly `fixpoint` job in `ci.yml` runs it on `ubuntu-latest`. The separate
  `.github/workflows/fixpoint.yml` runs it nightly on `master` and from "Run workflow" on
  the self-hosted runner named by `WIZ_RUNNER_HEAVY`; it checks for 6 GiB free, is skipped
  when the variable is unset, and is not part of `CI result`.
* **The compiler's own reproducibility** (`.github/workflows/repro.yml`) runs
  `scripts/check-repro.sh --compiler` nightly on `master` on the same self-hosted runner
  (a clean skip when `WIZ_RUNNER_HEAVY` is unset; 5 GiB free). It builds wiz and grail
  under two absolute roots and asserts the JSON with
  `scripts/check-repro-report.py --require-compiler`, so a skipped compiler comparison is
  a failure; the pull-request corpus step in `ci.yml` runs only the corpus and annotates
  the skip as a notice. See [Reproducible builds](#reproducible-builds).
* **The nightly benchmarks** (`.github/workflows/bench.yml`) also run only on
  `master` and from "Run workflow", on the `WIZ_RUNNER_HEAVY` runner (a clean skip
  when it is unset). They use the Nix-built `wiz`/`grail` and need 6 GiB free (the fixpoint's
  reservation; a Cachix miss compiles the toolchain). The
  standard-library A/B (`scripts/stdlib-bench.py --baseline-bin`) alternates one run of
  the previous green night's executable, restored from the Actions cache, with tonight's
  build; the per-mode sizes come from `bench/stdlib-baseline.json`, and the measurement
  is pinned with `taskset` to `WIZ_BENCH_CPUSET` (otherwise two CPUs are left free).
  `scripts/bench-threshold.py` gates on the **median paired ratio** (default 10%, at
  least 5 pairs per mode), not on absolute time, and writes the table to the job
  summary; the run JSON records the machine id, CPU set and CPU model. Against the
  checked-in baseline a "no gate" result (fewer than 5 comparable pairs) is a failure,
  and so is a baseline mode the run no longer contains: neither a mode dropped from the
  run nor an unmeasured one is a pass. `scry bench
  --no-timing --fail-on-regression` is the second, deterministic corpus gate. On a
  green night the current executable becomes the next A side; the first run compares
  the build with itself, and "Run workflow" with `bootstrap: true` does that again
  after a deliberate change to the benchmark program. The JSONs, `bench/history.jsonl`
  (one line per run) and the baseline executable are artifacts, not committed files.
* **The Nix package** (the `build` job; the old separate `nix package` job is folded
  into it): `nix build .#wiz .#tests` builds `wiz` and `grail` with Lake in the Nix
  sandbox and nixpkgs' Lean (the flake checks that it is the version in `lean-toolchain`)
  and the test driver from the same build, and wraps the binaries with the toolchain as
  flags (`--cc`, `--cflags`, `--ldflags`, `--llc`, `--gc-cflags`, `--gc-ldflags`; flags
  you pass come later and win) and, for `wiz`, the packaged standard library as a module
  root after `./lib`. The job then checks the package from a directory with no checkout
  (`nix run "$GITHUB_WORKSPACE#wiz" -- check/build …`, and `#grail` starts), so the
  publication path is exercised before the push. It publishes to the public Cachix cache
  `badlydrawnwizards` from `master` and from this repository's pull requests (which have
  the token); `packages.tests` is `nix run .#tests -- --list`, and `packages.reference` is
the generated reference manual (`result/index.md`, and `result/site`).
* **The packaged read-only elaboration cache.** The `wiz` package prewarms the
  elaboration cache during its build and installs it at `$out/share/wiz/cache`: the
  `.wizc` effects and the `.wizm` seen markers, with no `bin/` memo or `roots/` pointer
  index (both are write-cache aids) and `a-w` permissions. Both wrappers (`wiz` and
  `grail`) add
  `--cache-ro $out/share/wiz/cache --cache-ro-unsigned` after their toolchain flags, so a
  packaged run replays the standard library instead of elaborating it; a user's
  `--cache` (the default `~/.cache/wiz`) is still written, so the store cache is only
  ever read. The opt-in is deliberate: a read-only layer is refused by default because a
  manifest is a self-signed digest, and this layer is the one case where the reader and
  the writer are the same derivation (the store path is content-addressed and the entries
  are keyed by the packaged binary's hash), not a foreign trust domain. The
  warm runs pass the *same* toolchain flags the wrappers add: `Toolchain.tag` hashes
  exactly those fields and is part of every manifest's strong key, so a cache warmed
  with default flags is rejected by every wrapper invocation (it would be a clean miss
  for the whole layer).
  There are two sets of entries in that one directory, because `wiz` and `grail` are
  different executables and the cache mixes the running binary's hash into every key
  (`Cache.binaryId`; an entry written by one is never read by the other):
  * **wiz**: every module of `lib/` (one `wiz check` of a one-line `import M` for each
    module `M`), about 5,000 entries and 50 MB. Checking a module's own file would key
    its commands by the main text, which an importer never looks up, so the warm run
    imports it instead. The checks run concurrently, at most `NIX_BUILD_CORES` (capped
    at 8) at a time, and share the one cache directory: its keys are content-addressed
    and every file is renamed into place, so concurrent writers of one entry write the
    same bytes.
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
  (`--cache-ro` is repeatable and searched in the order given). A layer passed this way
  is refused unless `--cache-ro-unsigned` (or `--cache-verify off`) is also given: its
  manifests are self-signed, so they are integrity, not authenticity. The entries are keyed
  by the packaged binary's hash (its bytes) and by `lib`'s text and module names, so
  the Nix build invalidates them automatically; there is no manual invalidation and a
  stale store path is never reused (a new build gets new keys). The cache is
  read-only in the store, so a miss (a user's own module) is elaborated and written to
  the write cache as usual.
* **The Wiz build caches.** Each test shard keeps what the suite builds from Wiz
  programs between runs: the elaboration cache (`tests --cache ~/.cache/wiz …`),
  `.grail`, and the self-hosted checker and compiler that the tests compile
  (`/tmp/wiz-selfhost-*`). The cache key starts with a hash of everything the compiler
  is made of (the `.lean` files, Lean, `flake.lock`), and partial hits only come from the
  same compiler (the elaboration cache's own keys include the wiz binary's hash, but the
  test driver's grail runs use a fixed binary id and the `/tmp` programs a timestamp).
  The elaboration cache may also have read-only layers (`--cache-ro DIR`, repeatable,
  searched in order after the written `--cache DIR`, never written; refused by default
  unless `--cache-ro-unsigned`). The Nix package
  ships one in `$out/share/wiz/cache` and its wrappers pass both flags, so CI and
  users share a warm cache without a writable store path; a run with no write cache
  hashes the wiz executable each time instead of remembering it under `bin/`.
* **Storage.** CI no longer stores the build in the Actions cache: the build lives in the
  Nix store and is shared through Cachix (~350 MB for `wiz` plus its closure; the test
  driver is ~165 MB, with `wiz` in its closure, on x86_64-linux). The Actions cache now
  holds only the per-shard Wiz build caches (the elaboration cache, `.grail`,
  `/tmp/wiz-selfhost-*`) and the elan toolchain (~770 MB, saved only by `master`; pull
  requests restore master's entry), which only the fixpoint/release jobs still need.
  Artifacts are short-lived: test logs 3 days, `test-timings` 7 days on master (2
  elsewhere), `test-timings-baseline` 7 days, the release tarball 90 days for a tag,
  7 for a snapshot (both are also release assets) and 3 for a pull request.
  To see the usage: `gh api repos/wiz-pl/wiz/actions/cache/usage` and
  `gh cache list -R wiz-pl/wiz -S size_in_bytes`.

* **Path filters.** On a pull request the `changes` job (`scripts/ci.py changes`) reads
  the files the PR changes and decides what runs: nothing but `changes`, `docs_style`,
  `docs_examples` and `CI result` for a docs-only PR (`docs/`, `*.md`, LICENSE);
  `trust-ledger` runs whenever any code did; every shard when a Lean
  file, the build, the runtime, `scripts/`, `.github/` or `web/` changed; otherwise each
  shard with `"inputs"` in `.github/test-shards.json` only when one of its inputs
  changed (a `lib/X.wiz` input brings the lib files it imports), and the shards without
  `"inputs"` (backends, library) for any non-docs change. The `web` job (the playground
  and the site's JavaScript) runs when a `web/` file changed. So a PR touching only,
  say, `lib/Json.wiz` skips `core` and the selfhost shards. `CI result` counts a job the
  filter skipped as fine and a job it wanted only if it succeeded. Pushes to `master`,
  the merge queue and manual runs always run everything, so a missing input shows up
  there at the latest. A test that starts reading a new file belongs in a shard without
  `"inputs"`, or add the file to its shard's `"inputs"`.
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

### Before you push

`scripts/pre-commit.sh` runs the cheap gates CI would run first, in one command, so a
formatting, ledger, prelude or docs problem is found in seconds instead of in CI. It needs no
build for the fast tier:

```sh
scripts/pre-commit.sh --fast           # before a commit
scripts/pre-commit.sh --full           # before a push
scripts/pre-commit.sh --fast --staged  # only the files in `git diff --cached`
scripts/pre-commit.sh --self-test      # the tiers on a throwaway repository
```

| tier | checks |
|---|---|
| `--fast` | docs style and links (`scripts/check-docs-style.py`, `scripts/check-doc-links.py`), the embedded prelude's surface (`scripts/check-prelude-drift.py`), `wiz fmt --check` on the changed `.wiz` files, the trust ledger's fixtures (`Tests/trust-ledger/run.sh`), the host-side unsafe ledger and its fixtures (`scripts/host-unsafe-ledger.py --check`, `Tests/host-unsafe-ledger/run.sh`), `scripts/ci.py check-skips --self-test`, the check-repro and check-repro-report self-tests, and a parse of every YAML file under `.github/` |
| `--full` | everything in `--fast`, then `scripts/trust-ledger.sh --check`, `scripts/check-repro.sh` when a compiler is built, and the formatter's test group (`=fmt`, or `=format` on a tree from before that group was renamed) |

Without `--staged`, the changed files are what the branch adds since its merge base with
`origin/master` plus the working tree's unstaged, staged and untracked files. `--staged`
restricts the file-driven checks (`wiz fmt`) to the index. The docs-style check, the
fixture suites and the ledger are repo-wide either way.

Every check whose tool is missing is skipped with a reason: no `python3`, no PyYAML, no
`wiz` (or an older `wiz` without `fmt --check`), no test driver, no `cc`. A skip is not a
pass. The last line is one summary line. The exit status is 0 when at least one check ran
and none failed, 1 on a real failure, and 3 when every check was skipped (so a hook can
tell "nothing could run" from "all good"). The fast tier took about 6 s on a warm
checkout with the test driver built and one `.wiz` file changed (under 1 s with nothing
built); `--full` took about 8 minutes, almost all of it `check-repro.sh`.

`scripts/install-hooks.sh` writes `.git/hooks/pre-commit` (fast tier, staged files) and
`.git/hooks/pre-push` (full tier); both call the script from the work tree, so editing
the tiers needs no reinstall. It never overwrites a different hook without `--force`, and
running it twice leaves the hooks byte-for-byte unchanged. The same two hooks are
available to the pre-commit framework as the `wiz-fast` and `wiz-full` entries in
`.pre-commit-hooks.yaml`.

What it cannot check: the test suite beyond the formatter group, generated C or LLVM
outside the reproducibility corpus, the docs site, the release workflow, sharding
(`scripts/ci.py check-shards`), or behaviour on another OS or architecture. It is a
local subset of CI, not a replacement for it.

### Golden diffs

A golden failure in CI is a test case whose output no longer matches its `.expected`
file (`grail test`, stage 23f). The `golden-diff` workflow
(`.github/workflows/golden-diff.yml`) runs after a failed `CI` run whose test shard
failed, and makes the diff the artifact a reviewer needs:

* it downloads the run's `test-log-*` artifacts (the shards' `*.log` and `*.jsonl`);
* it checks out the failing commit, builds `grail` from the public Cachix cache (a
  pull request's store path is in the untrusted PR cache, which this workflow does not
  read, so it builds instead), and runs `scripts/golden-diff.py`;
* the script re-runs **only the failing golden cases** with `grail test --update` in a
  temporary copy of the checkout, then prints a one-line-per-case summary and a unified
  diff of every changed `.expected` file (a new `.expected` shows as `/dev/null`);
* the diff job writes that report to the run summary and uploads it as the
  `golden-diff` artifact; on a pull request, a second job posts it as one
  (`pull-requests: write`) comment, replacing that job's earlier comment on a rerun.

The job has two permissions levels on purpose. The `diff` job runs the pull request's
code and its flake, so it has `contents: read` and `actions: read` only and uses no
secrets (Cachix is read anonymously). The `comment` job has
`pull-requests: write` but runs no pull request code; it only posts the uploaded
Markdown.

**What it will not do.** The script never modifies the checkout, commits, or pushes;
the workflow has no write permission outside the comment job. It re-runs only cases
whose name (or failure output) is a `.wiz` under a `Package.tests` root (a group
`examples` case names a name range, but its failure output names the example that
failed), at most 12
files with a 300 s limit each, and it reports a case that fails for another reason
(a build error, a timeout, a missing toolchain) as "not diffed" instead of writing a
`.expected` file: `grail test --update` never records a failure either. The diff is
**advisory** — it is what `--update` would write, not evidence that the new output is
correct.

Locally, after a failing `lake test` run:

```sh
python3 scripts/golden-diff.py logs/shard.log logs/shard.jsonl
python3 scripts/golden-diff.py --case 'tour:examples/tour/00-hello.wiz'
python3 scripts/golden-diff.py --self-test   # the diff engine's synthetic fixtures
```

The script uses `.lake/build/bin/grail` (or `$GRAIL`, or `--grail PATH`); `--keep` keeps
the temporary copy, and `--out FILE` writes the report.

### Running the scry e2e goldens locally

The six end-to-end files (`scry/tests/{e2e-c,e2e-cs,e2e-prover,e2e-egraph,corpus-parse,
workflow-e2e}.wiz`) need three things, and two of them are easy to miss:

```sh
lake build wiz grail tests          # the tree's own grail; the installed one matches nothing

# 1. the C# grammar *as a real directory* (see below)
cp -a /nix/store/<hash>-tree-sitter-c-sharp-0.23.5/. scry/native/tree-sitter-c-sharp/

cd scry
../.lake/build/bin/grail build scry  # 2. gives e2e-c/cs/egraph/prover .grail/bin/scry
../.lake/build/bin/grail test --test-timeout 2400 \
  tests/e2e-c.wiz tests/e2e-cs.wiz tests/e2e-prover.wiz \
  tests/e2e-egraph.wiz tests/corpus-parse.wiz tests/workflow-e2e.wiz
```

* **Do not leave the grammar as the Nix out-link.** `nix build .#tree-sitter-c-sharp
  -o scry/native/tree-sitter-c-sharp` writes a *symlink*; a test run over sshfs cannot
  read it (`Operation not permitted`) and `src/Scry/Native.wiz` then fails with
  `link_c: no file ../../native/tree-sitter-c-sharp/src/parser.c`. Copy the store
  directory into the gitignored path instead (30 MB), and check from the node that
  `scry/native/tree-sitter-c-sharp/src/parser.c` exists — an sshfs negative dentry can
  report it missing for a minute after the copy.
* **Without `grail build scry`** the four golden cases report
  `skip (.grail/bin/scry absent)` and fail on line 1, which reads like a test failure
  but is a missing step.
* Use `grail test`'s own `--test-timeout`; the harness default is 300 s and
  `tests/scale.wiz` needs more.

`e2e-c` and `workflow-e2e` are the two that exercise the C and workflow pipelines; the
other four cover C#, the prover, the e-graph and the corpus parse invariant.

### Documentation site

A push to `master` publishes the site from the `docs` job to GitHub Pages, at
<https://wiz-pl.github.io/wiz/>. The tree has five parts, and every link in it is
relative, so the project-site prefix (or a custom domain root) works either way:

| URL | what it is | built from |
|---|---|---|
| `/` | the landing page: introduction, features, quickstart | `web/landing/index.html`, `web/landing/landing.css` |
| `/docs/` | the standard library's API documentation | `wiz doc --lib` |
| `/guide/` | the repository's prose documentation, as pages | `docs/**/*.md`, `README.md`, `ROADMAP.md`, `CHANGELOG.md`; `web/build-docs.py` |
| `/bench/` | standard-library timings and the Scry taint corpus | `bench/*.json`, `scry/bench/baseline.json`, `web/build-bench.py` |
| `/playground/` | the static playground (stage 11ab) | `web/playground.*`, `web/build-playground.sh` |

The `docs` job copies the two Wasm modules that `web_modules` built from Cachix
(`web/build.sh` for the documentation's interactive signatures,
`web/build-playground.sh` for the playground; the scripts only copy in that mode),
runs `wiz doc
--lib -o doc-site/docs --web web/out` (source links to the commit), copies the
reference manual's Markdown from the flake's `reference` package (`nix build
.#reference`, a Cachix hit when the build job already built it) to
`doc-site/docs/reference.md`, assembles the
landing page, the benchmark page, the playground and the guide with `web/build-site.sh
doc-site web/out`, checks the result with `web/check-site.sh doc-site` (the five entry
points exist; `web/check-links.py` then crawls every page and fails on a Markdown link,
an internal link that does not resolve — fragment included — or a module, guide or
notebook page with no source link), and uploads `doc-site` as the artifact `wiz-docs` (3 days, for
debugging). `deploy-docs` then publishes that artifact.

The guide exists because the site must not link a reader to a repository Markdown file:
a link on the site resolves to a rendered page, and a rendered page may link to its
source `.md` in the repository (its `class="src"` link, the one Markdown link the
checker allows). `web/build-docs.py` renders the subset of Markdown the repository uses
and rewrites a relative `foo.md` link to `foo.html`; a link to any other file (a `.wiz`
source, a directory) becomes an absolute link to the repository, except an exported
notebook, which links to the site's `/notebooks/` copy. It also rewrites the copied
notebook pages' `.md` links, so `/notebooks/tour.html` points at `/guide/docs/…`. Each page's source link names the commit the tree was built from
(`git rev-parse HEAD`); `WIZ_SOURCE_URL` overrides the prefix.

`wiz doc --lib` elaborates the whole library when its cache is cold, and that is the bulk
of the docs job (10-19 min in recent runs). The job therefore restores `wiz`'s
elaboration cache from the Actions cache into `.wiz-doc-cache/ro` and passes it with
`--cache-ro`, a layer `wiz` only ever reads: the job cannot corrupt the published layer,
and this run's misses go to `.wiz-doc-cache/write`. A run that missed publishes its
write cache as the next run's layer; a hit publishes nothing. The key is
`wiz-doc-v1-<os>-<SHA-256 of the wiz binary>-<git tree of lib/>`. The first half is the
cache's own namespace (an entry is named by `binaryId`, a hash of the running binary, and
manifests carry its SHA-256), so an identical build of the same source hits and a changed
compiler misses by construction; the second half only decides when a new snapshot is
saved, and the restore prefix (`wiz-doc-v1-<os>-<binary hash>-`) still serves the modules
a `lib/` change did not touch. `--cache-verify off` is deliberate. The layer is published
by a job that runs with it off, so the layer carries no manifests; with verification on
(the default, `warn`) an entry that no manifest lists is a miss, and a read-only layer is
only read through its manifests — the restored layer would be ignored. The entries are
content-keyed and namespaced by the binary's hash anyway (each module's text is in the
key), and a manifest would also bind each entry to the toolchain's tag, which includes
the `cc` and `llc` paths (`Wiz/Toolchain.lean`): a rebuild of the same ELF against a
different store path would throw its entries away. A miss costs one cold elaboration
(10-19 min on the runner); a hit replays the entries in about 2-4 min. The toolchain's
own `share/wiz/cache` is read as well (the wrapper's default `--cache-ro`).

The benchmark page is **generated, not written**: `web/build-bench.py` renders
`web/bench/index.html` from the JSON, and `web/build-site.sh` runs its `--check` mode
first, so a JSON change that was not regenerated fails the job (and is visible as a diff
in the checked-in page). Regenerate it with `python3 web/build-bench.py`; the fixture
tests and the site-check rules for it are in `web/test-bench.sh`.

The playground itself needs a fourth build, `web/build-playground-ui.sh` (the page's
runtime module, `wiz-playground-ui.mjs`). The `web` job builds and tests it;
`web/build-site.sh` requires it beside `web/build-playground.sh`'s engine, because the
page has no static fallback: a missing runtime module is a playground that cannot start.
The `.#wiz-playground` derivation runs both scripts, so one store path carries the engine
and the page, and the `docs` job's `build-playground.sh --from` copies both.

| path | what it is |
|---|---|
| `index.html`, `landing.css` | the landing page |
| `guide/docs/index.html` | the guide's index: the repository's documentation as pages (one per `docs/**/*.md`, plus the README and what they link to) |
| `guide/**/*.html` | one page per rendered Markdown file: its own source link, and links rewritten from `.md` to `.html` |
| `guide/guide.css` | the guide's stylesheet |
| `bench/index.html` | the benchmark page (generated from the JSON in `bench/` and `scry/bench/`) |
| `docs/index.html` | the documentation index: the documented modules and their summaries |
| `docs/api.html` | the API index: every module and declaration, with signatures and doc summaries |
| `docs/api.json` | the same index as data, for tools |
| `docs/reference.html` | the reference manual: full signatures, doc comments, class instances, the notation table (same data as `docs/reference.md`) |
| `docs/A.B.html` | one page per module (its declarations, signatures, docs, source links) |
| `docs/A.B.json` | the same page's data, for the interactive signatures |
| `docs/reference.md` | the reference manual as Markdown (`nix build .#reference`'s `index.md`; generated, not committed) |
| `docs/search.js`, `docs/scroll.css`, `docs/scroll.js`, `docs/scroll-search.js`, and the search runtime (`wiz-docs-ui.mjs`) | the documentation's scripts and styles (search covers names, doc comments and signatures) |
| `docs/wiz-infoview.mjs`, `docs/wiz-infoview.wasm` | the web module (the documentation's signatures and the Wiz-language infoview), when `web/build.sh` built it |
| `playground/index.html` | the playground page |
| `playground/playground.js`, `playground/playground.css`, `playground/overlays.css` | the page's entry point and styles (the Loom runtime renders the page) |
| `playground/wiz-playground.mjs`, `playground/wiz-playground.wasm` | the playground's engine (the self-hosted checker), when `web/build-playground.sh` built it |
| `playground/wiz-playground-ui.mjs` | the playground's runtime (the whole page as a Loom app), from `web/build-playground-ui.sh`; required |

To build the site locally from a checkout (after `nix develop` and `lake build wiz`):

```sh
sh web/build.sh web/out                         # the web module, the infoview page, scroll assets
sh web/build-playground.sh web/out              # the playground module
sh web/build-playground-ui.sh web/out           # the playground's page (Loom runtime)
.lake/build/bin/wiz doc --lib -o doc-site/docs --web web/out
cp "$(nix build .#reference --no-link --print-out-paths)/index.md" doc-site/docs/reference.md
sh web/build-site.sh doc-site web/out           # landing, /guide/, /bench/ and /playground/
sh web/check-site.sh doc-site                   # five entry points, every link, source links
sh web/test-bench.sh                            # the generator's fixtures and /bench/
python3 -m http.server -d doc-site 8000         # then http://127.0.0.1:8000/
```

With the derivations already in the store (`nix build .#wiz-web .#wiz-playground
.#wiz-playground-ui`), the three module steps can copy them instead of running Emscripten:
pass `--from DIR` (or `WIZ_WEB_FROM`/`WIZ_PLAYGROUND_FROM`/`WIZ_PLAYGROUND_UI_FROM`) the
store path, exactly as CI does.

`wiz doc --jobs N` elaborates and renders N modules at once; the default is 1, and
`--jobs 0` (or `--jobs auto`) takes the CPUs the process may run on, at most 8. The tree
is byte-for-byte the same for every N (the modules' outputs are assembled in the order
`run` was given them); only the `-v` log follows completion order. `-v` writes that log to
**stderr** — stdout and the pages are unchanged — and names each phase, each module's
elaboration and rendering time and cache hits, every 25th declaration, and a summary with
the wall time and peak RSS. `-vv` lists every declaration; `-q` is the quiet default.

**Live documentation (`wiz doc --serve`).** The generated documentation is static by
default; `--serve` additionally serves one output tree over HTTP on `127.0.0.1` (port
8000, `--port N`; `0` takes a free one), and `--lsp PORT` makes the module pages ask a
running `wiz lsp --ws PORT` for a declaration's real type and doc. The panel appears
when the connection is up; hovering or clicking a signature shows

* its type and doc comment (`textDocument/hover`, with the server's own doc comment),
* the goals and expected type at the declaration (`wiz/interactiveGoals` /
  `wiz/interactiveTermGoal`, with the `plainGoal` fallback), and
* the document's diagnostics.

The page fetches its module's source from the server (`/sources/A.B.wiz`) and opens it
with `didOpen`, so the positions are the ones the page was generated from. Start the
language server from the module root, or with `-I` roots, so its imports resolve:

```sh
.lake/build/bin/wiz lsp --ws 8765 --no-stdio -I lib --token-file lsp-token &
.lake/build/bin/wiz doc --lib -o doc-site/docs --web web/out --serve --lsp 8765
# then http://127.0.0.1:8000/?token=T, with T from lsp-token
```

The language server lets in only clients that present its token (`?token=` in the
page's URL is passed on to the socket; docs/playground-lsp.md, "The token"); the pages
never carry it themselves.

`--serve` without `--lsp` writes the same documentation plus the inert client: there is
no socket and no fetch, and the pages read without JavaScript. `?lsp=PORT` (or
`?lsp=ws://HOST:PORT`, or `?lsp=off`) overrides the endpoint for one page. Only module
pages carry the client; `index.html` and `api.html` stay static in either mode. The
server is for development: loopback only, `GET` only, one request per connection, no
TLS or authentication. Live search results and code actions are not part of it — those
need an editor's document and its cursor.

`web/build-playground.sh` compiles the self-hosted frontend to WebAssembly, so it is the
slow part (~10 minutes, with Emscripten's `wasm-opt -O2` as the memory tail); without
`emcc` on `PATH` the script runs Emscripten from nixpkgs. CI does not run it: the
`wiz-playground` derivation in flake.nix does, once, and Cachix serves the result
(`web/build-playground.sh --from "$(nix build .#wiz-playground --no-link
--print-out-paths)"` copies it). That derivation builds at `--opt 1`: at `-O2`
`wasm-opt` peaks at 16.9 GiB on the 7.7 MB module (measured 2026-11-18) and is killed on
a 16 GB CI runner, while `-O1` skips binaryen and peaks at 2.3 GiB, for a module 47 %
larger (11.4 MB). The script's default is still the compiler's `-O2`, so a local build
is unchanged; pass `--opt 1` to it to reproduce what the derivation publishes. Both web
builds (`web/build.sh`, `web/build-playground.sh`) pass `-DWIZ_NO_THREADS`, since they
are compiled without `-pthread` (the header also turns it on by itself for Emscripten
without `-pthread`): the runtime then has one thread, nothing is ever
marked shared (so every count operation is plain), `main` runs on the calling thread,
and `Chan.fork`, or a wait that no other thread could end (taking from an empty `MVar`,
putting into a full one, acquiring a held `Lock`, receiving on an empty channel), stops
the program with `wiz: …: threads are not available in this build (WIZ_NO_THREADS)` and
exit code 3 instead of hanging. `-DWIZ_RC_ATOMIC` is the opposite debugging build:
thread-owned counts change atomically too. `scripts/test-runtime.sh` checks all three;
`scripts/rc-cost-bench.sh` times them against each other (the single-thread cost of
thread-safe counts). Without
`--source-url`, the local documentation's source links are plain paths. `docs` and
`deploy-docs` run only on `push` (`workflow_dispatch` runs do not publish). The artifact
stays for 3 days for debugging; the site keeps the newest deployed tree until the next
successful deployment, and `deploy-docs` serialises deployments (`concurrency: pages`,
`cancel-in-progress: false`) so the site ends at the newest commit.

**One-time repository setting.** Settings → Pages → Build and deployment → Source =
"GitHub Actions". Without it `actions/configure-pages` has no site to configure and
`deploy-docs` fails (the rest of CI is unaffected). An administrator can create or
update the site from the command line instead of the web UI:

```sh
# create it (404 until then) with Actions as the source:
gh api --method POST repos/wiz-pl/wiz/pages -f build_type=workflow
# or, if the site already exists, switch its source:
gh api --method PUT repos/wiz-pl/wiz/pages -f build_type=workflow
# check:
gh api repos/wiz-pl/wiz/pages --jq '{html_url, build_type, status}'
```

Both need repository admin rights; they are settings changes, not part of a normal
development run.

**One site, one tree.** A repository has one Pages site and every deployment replaces
the entire tree, so `deploy-docs` must stay the only Pages publisher. The performance
site (the `perf-site.yml` workflow when it lands) is designed to publish a
self-contained dashboard; when it lands, it belongs *under* this deployment as
`/perf/` — built into `doc-site/perf` before `upload-pages-artifact` — not in a second
deploy job, which would replace the site. Until then its own `deploy` job stays
off (`PERF_SITE_DEPLOY` unset). Once `perf/` is there, link it from the landing page
(`web/landing/index.html`), which is a checked-in source file, not generated.

To run Wiz without a checkout or a Lean toolchain, with the binaries from Cachix:

```
nix run --option extra-substituters https://badlydrawnwizards.cachix.org \
  --option extra-trusted-public-keys badlydrawnwizards.cachix.org-1:TxG+RHY8RMC/AXc0LJbYtYm9LW/XRjfQwgz+EEaAjBI= \
  github:wiz-pl/wiz#wiz -- check hello.wiz
```

or `cachix use badlydrawnwizards` once and then `nix run
github:wiz-pl/wiz#wiz -- …` (`#grail` for grail; `wiz build FILE -o OUT`
works out of the box). Without a branch the flake reference means the default branch,
`master`, whose binaries are on Cachix once its `build` job has pushed them. The
`--option`s count only for a trusted Nix user (or with the cache in `nix.conf`);
otherwise Nix builds wiz from source, which takes a few minutes.

The same store path is a tower toolchain: `/share/wiz` has the layout tower accepts
(`.lake/build/bin/wiz`, `bin/grail`, `lib/`). To use the build under a name:

```sh
wiz=$(nix build .#wiz --no-link --print-out-paths)
tower toolchain link "ci-$(git rev-parse --short HEAD)" "$wiz/share/wiz"
tower run "ci-$(git rev-parse --short HEAD)" -- wiz check hello.wiz
tower run "ci-$(git rev-parse --short HEAD)" -- grail --version
```

`tower settings` can also take future toolchains from this flake rather than building
them with Lake: `tower set source nix`, `tower set flake github:wiz-pl/wiz` (and
`tower set releases wiz-pl/wiz` for the release source), then
`tower toolchain install master@<sha> --source nix` substitutes the Cachix build. CI
does not install a toolchain: it consumes the `nix build` outputs directly.

`#nvim-wiz` is Neovim with the Wiz plugin (editors/nvim, docs/stages/11-tooling.md
11p) and this wiz on `PATH`: `nix run github:wiz-pl/wiz#nvim-wiz --
file.wiz`. `packages.<system>.wiz-nvim` is the plugin alone, for a Neovim
configuration in Nix.

## Merge order and stacked pull requests

CI runs a limited number of jobs, so work lands in **stacks** rather than one pull
request per topic. A stack branch merges several finished component branches in
dependency order and is opened as one integration pull request; that PR is the unit
of review, CI and merge. The component PRs are closed as folded, and their branches
stay: the stack's ancestry is what makes the next restack cheap.

* The first line of a stack PR is `Depends on: #a, #b`, naming every **unmerged** PR
  whose commits the branch contains. The stack does not merge until each of them is
  `MERGED`. A dependency that was closed because another PR superseded it is not
  merged, so rewrite the line when that happens.
* **One ready stack PR per dependency chain.** A dependent stack stays draft or
  local until its base has merged and the branch has been restacked on `master`.
  Opening it earlier only produces an unmergeable PR, and an unmergeable PR gets no
  CI run at all.
* Restack with `git merge origin/master` (or the dependency branch), never by
  rebasing a shared branch. Merge a stack with a merge commit
  (`gh pr merge N --merge`), not squash or rebase.
* While a stack's CI is the critical path, no other top-level PR is opened; a
  docs-only PR may follow the stack's run, not precede it.
* Cancel only superseded runs of the same branch. A conflicting PR has no checks
  to wait for, so restack it instead.

A stack is ready to merge when its merge state is `CLEAN`, the required checks are
green on the current head (not on a superseded one), every `Depends on:` PR is
merged, its component PRs are closed, the test groups it touches have been run with
counts in the PR body, the documentation style check passes, it is not a draft, and
the restack plan for its dependents is written down.

The queue order is kept in a ledger outside the checkout
(`wiz-notes/stack-ledger.json`, or `$WIZ_STACK_LEDGER`). `scripts/stack-status.py
--next 5` prints the next actions with their gates, `--check` rejects a ledger with
two ready PRs in one chain or a ready PR with an unmerged dependency, and `--write`
refreshes the ledger's facts from `gh` and `git`.

## Branch hygiene

`scripts/branch-rot.py` makes branch hygiene a five-minute monthly task (Python 3,
standard library only). It classifies every local branch, and with `--remote` every
`origin/*` tracking ref, into four buckets:

* **redundant** — the tip is an ancestor of `origin/master`, or every commit is
  patch-equivalent to one upstream (`git cherry` reports no `+` lines). Branches with
  merge commits are never called redundant: `git cherry` skips merges, and a merge
  resolution can carry content that is not upstream.
* **in-flight** — an open pull request exists for the branch. These are kept.
* **attic** — unique commits, no open PR, and the tip is older than `--days`
  (default 30).
* **needs-pr** — unique commits and no open PR. This is the conservative default
  whenever the script is unsure.

Run it from a checkout:

```sh
scripts/branch-rot.py                  # table and counts
scripts/branch-rot.py --limit 10       # show at most 10 rows per bucket
scripts/branch-rot.py --json           # machine-readable, for a dashboard
scripts/branch-rot.py --remote         # include origin/* tracking refs
scripts/branch-rot.py --days 30        # attic threshold in days (default 30)
```

The classifier is read-only. Deleting redundant branches is explicit and needs both
flags:

```sh
scripts/branch-rot.py --delete-redundant            # dry run: list what would go
scripts/branch-rot.py --delete-redundant --apply    # actually delete
```

Deletion refuses the current branch, any branch checked out in a worktree (including
another agent's), `master` and `main`, and any branch with an open PR or a PR state it
could not read. `--no-gh` skips GitHub entirely (every PR state becomes unknown, so
nothing is deleted); `--self-test` builds a throwaway repository with a merge, a
cherry-pick, an unmerged branch and a worktree and checks the classification offline.
