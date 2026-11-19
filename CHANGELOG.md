# Changelog

All notable changes to Wiz. Versions follow [Semantic Versioning](https://semver.org/)
in its 0.x form: until 1.0, a minor release (0.1 → 0.2) may break anything; a patch
release (0.1.0 → 0.1.1) fixes bugs only. What a patch release keeps is in
[docs/stability.md](docs/stability.md).

Section numbers (`4c`, `22e`, …) refer to the stage docs: section `NNx` is in
`docs/stages/NN-*.md`. `#n` is a pull request on GitHub.

## [Unreleased]

* playground: an exit no longer costs a Wasm instance. A clean stop — `Process.exit`,
  the one-threaded build's refusal to fork or block, a failed `IO.writeFile` — now
  `longjmp`s back to a boundary armed around each exported call (`wiz_stop_run`,
  `runtime/rt_con.inc`) with its exit code instead of calling `exit`. The runtime still
  prints its `wiz: …` message on stderr, `web/playground-engine.js` returns the code as
  `wiz_playground_exit` (code + 1, 0 for none), and the pane shows it as a failure while
  the module and the page's state survive: the next run works on the same instance.
  Only an out-of-memory `wiz_panic` (an `ExitStatus` outside the boundary) and a trap
  (`unreachable`, out-of-bounds access, stack overflow) still drop and re-instantiate the
  module from the cached Wasm. Native builds are unchanged: with no boundary armed,
  `exit` is still `exit`, so the CLI's status, `atexit` and the stdio flush are as
  before. The guard is covered under Node with a stub module
  (`web/playground_engine_test.mjs`, `web/selfhost_lsp_test.mjs`); the runtime boundary,
  the native exit status and the unarmed `exit` are in `scripts/test-runtime.sh`. No
  emcc, no Wiz build and no browser are needed for the stubs.
* CI: the quadratic-shape lint (`scripts/check-complexity`) takes its excuses inline, on
  the hit's line or the line above it (`-- complexity: ok (why it is bounded)`);
  `scripts/complexity-allow.tsv` is gone. A row in a table keyed by a line hash could not
  survive a move or a reformat — the row went stale, or the moved line read as new — so a
  pull request that touched a reviewed site failed on a defect it had not introduced. The
  reason now travels with the code it excuses and appears in the same diff. `--all` lists
  the remaining backlog (152 sites) rather than hiding it behind rows.
* loom: a form control's live value now reaches a pure `step`. `web/framework/driver.js`
  sends the event string `event "\n" index "\n" payload` — a control's `value` for
  `input`/`change`, the key for `keydown`/`keyup`, nothing otherwise — and
  `lib/Web/Loom.wiz` parses it with `Loom.splitEvent`; an app that reads it is a
  `Loom.LiveApp` (`update msg payload state`, `Loom.LiveApp.step`/`patches`). The driver
  also grew `onStep` (the page's effect hook), `setState` (handing back a state the page
  changed through its own entry point) and a `parse` argument (the DOM double in tests).
  `web/framework/driver_test.mjs` pins the strings, and `web/framework/test.sh` runs it.
* playground: the editor is a Loom component (`lib/Web/Editor.wiz`): the page's
  `section.pane`, `#editor` textarea, its label and hint, `#run` and `#count`, with the
  text arriving as the input event's payload and Run counting requests. It is tested the
  way the output pane is: `web/playground_editor_gen.wiz` renders and steps it and
  `web/playground_editor_test.mjs` applies the patches to the SSR in the DOM double
  (both run in `web/playground-loom-test.sh`).
* playground: `?ui=loom` mounts the whole page as one Loom app (`web/playground-ui.wiz`,
  built by `web/build-playground-ui.sh` into `wiz-playground-ui.mjs`): the header and
  `#status`, the editor, the goals pane's container, the output pane and the footer's
  `#engine`. The page (`web/playground.js`) keeps the effects (the engine, the goals
  client) and reports their results through the module's `wiz_loom_*` entry points; the
  UI is its own Wasm instance, so neither a trap in the engine nor an engine restart
  touches it. The static markup stays the default and the fallback when the module is
  missing. The UI state is one opaque Wasm value passed by ownership (stage 9g's C ABI
  consumes an argument): the driver takes an extra `wiz_retain` for the read-only first
  paint, and the page hands each state to its `wiz_loom_*` calls and keeps the result.
  `web/playground_ui_test.mjs` mounts the real module under Node with the driver and the
  DOM double and checks the panes, the status pair, the count, the value classes and
  the entry points.
* web: the standalone browser infoview (`web/infoview.html`, served by `wiz lsp --ws`)
  now mounts the playground's goals pane (`web/playground-lsp.js` on `web/lsp-client.js`
  and `web/goals.js`) instead of the Wiz program `web/Web.wiz` stepped through
  `wiz_web_step`. One implementation serves both pages and both transports (a WebSocket
  URL or the playground's in-page server); the page's own half (`web/infoview.js`) is
  only its URL rule (`?port=`, `?lsp=`), follow mode (`?follow=1`, no document of its
  own, moved by `wiz/infoview/cursor`), the `#info` box and the status/cursor line.
  Clicking a subterm now selects it the way the arrow keys do (`.sel`), and the page no
  longer loads `wiz-infoview.mjs` — that module is the documentation's renderer now.
  `web/playground_lsp_test.mjs` gains follow mode, the separate `info` box and the
  `onRender` hook; `web/infoview_page_test.mjs` covers the page's URL and status text.
  `wiz lsp --ws` serves the three extra scripts the page needs.
* playground: the output pane's first piece now exists as a Loom component,
  `lib/Web/Playground.wiz`: `Model.ofText` splits a run's output into classified lines
  and produces the page's `#count` text verbatim (`2 lines · 1 error`), `Model.ofFailure`
  does the same for an engine failure with its own count (`exit code 3`), and
  `Model.view` renders the `#output` element. It is pure, so `web/playground_loom_gen.wiz`
  renders and diffs it and `web/playground_loom_test.mjs` applies the patches with the
  same DOM double as the framework test; `web/playground-loom-test.sh` runs both in the
  `web` job. The page still renders the pane by hand: the component needs its own Wasm
  instance, because the engine's is deliberately dropped and re-instantiated after a
  user `exit` (see `wiz-notes/playground-loom-plan.md`).
* scry C#: the frontend survives real code. Re-checked against a real solution's
  `src/Crux.Api` (75 files, every one parses without an `ERROR` or `MISSING` node; 2,483
  files under `src/`), the lowering no longer drops constructs silently. The headline
  find: **all 74 files with a file-scoped namespace (`namespace X;`) lowered to no
  function and no warning** — `typeDecls` recursed into the namespace node, but
  tree-sitter-c-sharp puts the following declarations as its *siblings*, so every type
  in the project was dropped. Fixed, and `lower/{modern,unsupported}` pin it. Top-level
  statements (the whole of a minimal-API `Program.cs`) become `<stem>.Main`
  (`Program.Main` for `Program.cs`); a record's or primary constructor's positional
  parameters become fields and `new R(a)` lowers and stores its arguments instead of
  discarding them; `partial` parts in one file are merged; `: base(…)` / `: this(…)`
  evaluates its arguments and calls the target constructor; an inherited call resolves
  through `base_list`; collection expressions unwrap all three element wrappers;
  `with` initialisers lower their values; `var (a, b) = …` evaluates its right-hand side
  and binds each name to a havoc with a warning; an indexer, an operator, a destructor,
  an event with accessors, a nested delegate and a `#if`-guarded member are each
  reported by name. `switch` expressions, collection expressions, `with` expressions, LINQ query
  syntax and target-typed `new()` in a declaration are lowered with their value flow
  (taint included) instead of havoc'd. New fixtures
  `lower/{modern,toplevel,unsupported}` and `taint/cwe78-modern-{unsafe,safe}`; the
  `silent skip` case fails when any of the out-of-scope warnings disappears
  (`scry/CSHARP.md` §7). `scry/scripts/cs-coverage.sh` reproduces the coverage table
  (frequencies, and per-file parse/lower/taint given a native build).
* scry: **`scry cs PATH`** analyses a directory, `.csproj` or `.sln`/`.slnx` of C# and
  reports a summary with a coverage section: `.cs` files before and after exclusions
  (`bin/`, `obj/`, `node_modules/`, hidden directories, `*.g.cs`, `*.Designer.cs`,
  symbolic links), found/parsed/lowered/failed, findings by rule and severity, and every
  construct or file that was skipped or warned about with a count and one example
  location. `--json` is the same report, `--fail-on error|warning|note` gates findings
  and coverage rows, and the exit status separates `0` clean, `1` gated, `2` usage/IO
  from `3` nothing analysed (no `.cs`, or every file failed). Lowering warnings are
  normalised to constructs, so a first run answers "what didn't you look at?" in one
  screen. The fixture tree `scry/corpus/csharp/repo/` and the `scry-csharp` group pin the
  counts, coverage rows, JSON and every exit status.
* tests: the anti-vacuity pass (`wiz-notes/reviews/2026-11-17-test-vacuity.md`) closed
  the test-side cases: `prop-kernels` now gates the generated normal forms (not only
  accept/reject; a normal form the Lean kernel cannot print is counted as the known
  PH-K2 shape), `hdl` pins the `stall_*`/`t1`–`t5` theorems it names, every `semantics`
  pipeline requires a non-empty cell selection, `selfhost-cli-diff`'s "good file" case
  requires exit 0 in both tools, and the `std` rows for `Nat.mul_assoc`, `Int.mul_add`
  and `Q.lt_ceil` pin the statement as well as the axiom print; the `regions`
  "no projection" check requires the lowering it inspects to exist. The alternate
  `--lib`/`--llvm` skip reasons now start with their allow-list entries' reasons.
* selfhost: a constructor's parameters and fields are named arguments too (A9). The
  self-hosted frontend kept no binder names for a constructor's `Global`, so
  `P.mk (y := 2) (x := 1)` was `no parameter named 'y'`; the names are now the type's
  parameters followed by the constructor's fields, so fields can be given in any order
  (a later field's type may mention an earlier named one), and an implicit field or a
  parameter can be named. An inductive type's own parameters, a dot-constructor and a
  local Π type still keep no names; the `selfhost` and `language` groups pin the accepted
  and rejected constructor forms against the Lean frontend (21ab, 13a).
* runtime/FFI boundary (the 2026-11-17 review, 9h/9k): `Process.exec` saves the
  `SIGPIPE` disposition and restores it when `exec` fails, and a spawn re-asserts the
  ignore every time, so a failed exec no longer leaves the next write to a broken pipe
  able to kill the program (`EPIPE` again). `File.open` sets `FD_CLOEXEC` (children no
  longer inherit every `File`). `Fd.adopt` rejects a number above `INT_MAX` with
  `EINVAL` (an already-closed handle, never fd 1: `4294967297` used to become stdout).
  The sys/IO allocations fail like the runtime's (`wiz: out of memory`, exit 3) or take
  the `ENOMEM` error path, never a NULL dereference; `FS.listDir` reports a `readdir`
  error instead of a truncated listing; `Child.communicate` with input but no stdin
  pipe is `EBADF`; `IO.writeFile` writes the text up to its first NUL and prints
  `wiz: <path>: <message>` and exits 1 when the write fails (it used to ignore every
  failure); `Handle`'s `Child.releaseOwned`/`waitOwned` drain a piped stream before
  waiting (no deadlock), and `Child.communicateOwned` collects it first.
* tests: a compiled program that fails at run time is a **failed case**, not a skipped
  one. `Build.runGlobal` now returns a `Build.RunError` that says whether the failure was
  the build (`.build`, or `.toolchain` when the compiler, `llc` or GMP's `gmp.h` could not
  be found) or the program (`.run` with its exit code and stderr, `.timeout`,
  `.readback`), and the test helpers in `Tests/Elab.lean` skip only a `.toolchain`
  failure. Before, any error containing "No such file" was recorded as
  `⊘ skipped (no toolchain)`, so a `conc`/`Handle` program (or any test program) that
  failed with ENOENT hid as a missing toolchain. The failure now reports the program's
  exit code and stderr. New `conc` cases pin a run-time ENOENT failure, a pass whose
  program writes "No such file" on stderr but exits 0, and the genuine missing-compiler
  skip.
* tooling: the self-hosted frontend's embedded prelude (`preludeText`,
  `selfhost/Frontend.wiz`) is checked against `lib/Prelude.wiz` by
  `scripts/check-prelude-drift.py`, a CI job (`prelude_drift`). It fails when a value
  declaration is added to the library prelude without the embedded copy, when the
  embedded copy invents a name, or when a reviewed exception goes stale; it prints the
  known gaps and the names the page promotes. The two preludes are not meant to be
  equal (the embedded one is a monomorphic model for the self-hosted frontend), so the
  check compares the semantic surface, not bytes (21y, `docs/stages/21-bootstrap.md`).
* web: the UI framework is renamed **React → Loom**. `lib/Web/React.wiz` is
  `lib/Web/Loom.wiz`, the module is `Web.Loom` (so `React.VNode`/`React.App`/… are
  `Loom.*`), the test group and file are `loom`/`Tests/Groups/Loom.lean`, and the
  Wasm exports are `wiz_loom_init`/`wiz_loom_html`/`wiz_loom_step`. There is **no
  compatibility alias**: the framework has not appeared in a tagged release, so
  imports and the documented `React.*` names change with the rename. `Web.Widget`,
  `web/framework`, the Jupyter widget front end, examples and docs use the new
  names (11s, `docs/libraries.md`).
* scroll (11s): the documentation generator shows **every command that declares a name**,
  not only `def`: `def` (equations too), `partial def`, `axiom`, `extern`,
  `foreign_type`, `glue`, `c_struct`, `structure`, `class`, `inductive`, `coinductive`,
  `sealed inductive` and named or anonymous `instance`s, plus a user's own command
  (`syntax … : command`, so `theorem`/`lemma`/`abbrev` written as command macros appear
  with their own kind). Kinds are labelled consistently (`c struct`, `foreign type`, a
  `lemma` as `theorem`), an entry's signature is the declaration's type or statement and
  never its body, and private constructors and fields are left out as private
  declarations already were. The `doc` group has a fixture with one declaration of each
  kind, checking the module page, `api.html`/`api.json`, the search index, the reference
  manual and deterministic output. Wiz has no `abbrev`, `opaque`, `theorem`, `lemma` or
  `namespace` command: `theorem`, `lemma` and `abbrev` written as command macros are
  shown with those kinds (a `lemma` as `theorem`), and dotted names (`T.f`) stay fully
  qualified since there is no namespace syntax.
* examples are a gate (23f): group `examples` runs the root package's
  `examples/*.expected` through the same `runTests` the tour uses, in three cases split
  by name, in a new `examples` shard (`"split": 3`, inputs `examples/`, `lib/` and
  `drafts/feral/lib/`) that `CI result` requires. A library change that shifts an
  example's printed value now fails the suite instead of only a command a person runs.
  The four benchmarks (`closed-table-bench`, `hdl-sim-bench`, `natives-bench`,
  `scry-datalog-bench`) declare `-- test: skip` with a reason; the executable examples
  (`io`, `std`, `effects`, `foreign`, `glue`, `import_c`, and `hdl-spi`/`hdl-stream`,
  whose goldens were program output but were read as `check`s) declare `-- test: run`,
  so their goldens are program output rather than a silent `check`; `plot.wiz`'s SVG is
  compared byte for byte with `docs/assets/plot-example.svg` by group `plot`; and
  `std.wiz`/`foreign.wiz` write to `FS.tempRoot` instead of a hard-coded scratch path,
  so they run on any machine.
* web: the playground's Goals pane is served **in the page by default**
  (`web/selfhost-lsp-shim.js`): the same Wasm engine answers the language-server protocol,
  so diagnostics and `#check`/`#eval` results appear with no server to start. Plain goal
  and term-goal requests answer `null` until the expected-type index lands; `?lsp=ws://…`
  still selects an external server and `?lsp=off` disables the pane.
* tests: CI's wall time is its longest shard. `selfhost-libdiff` was one case of about
  82 min; it now checks files `--jobs` at a time inside that case, building the
  self-hosted compiler once and keeping the records in file order, with the workers
  capped by the CPUs and the free memory at 4 GiB per file. `scaling`'s Desc sweep is
  nine cases over the same inputs (so the shard's parts can hold one each), and the
  light groups of `library` run their cases four at a time; `selfhost` and `library`
  are split eight ways by the measured times. A case of a group that does not opt in
  to `Group.parallel` is told the driver's `--jobs`, for a sweep that runs its own
  workers.
* concurrency (25a, 25d): `Lock` is now tested for mutual exclusion, not just for its
  linear `Guard`. The `conc` group's new cases run eight threads that bump a plain,
  non-atomic C counter a thousand times each under `Lock.with` and assert the exact total
  (`8000`) plus an overlap detector that must stay `0`, and a contended case that holds the
  lock while another thread announces it is acquiring, then pins the order of the printed
  lines (the waiter's first line comes after the holder released) and the same overlap
  detector. The critical sections yield to the scheduler (`sched_yield`), so a lock that
  does not exclude shows up in a one-CPU job too. With `wiz_lock_acquire`/`wiz_lock_release`
  made no-ops the counter case loses increments (`4962` of `8000` in the recorded run) and
  reports `overlap 1`; with `Lock.with l body` replaced by `body` both cases report
  `overlap 1` and fail. `scripts/tsan-conc.sh` is the ThreadSanitizer run that
  `docs/stages/25-concurrency.md` used to claim without a command: it builds the
  `Tests/tsan/` programs with `--cflags "-O1 -g -fsanitize=thread"` and fails on a report or
  a wrong total; the `conc` group also runs those programs under ThreadSanitizer as a case.
  The `signal(SIGPIPE, SIG_IGN)` before a process spawn, which two threads spawning
  children raced on (ThreadSanitizer reported the race on the old one-shot flag), is now
  re-asserted by `wiz_sys_spawn_in` before **every** spawn, with no shared flag at all
  (`wiz_sys_exec` saves the disposition with `sigaction` and restores it if `exec` fails,
  rt-ffi); `Tests/tsan/spawn.wiz` is the case that exercises it under TSan.
* cache: a fresh root file no longer misses the shared `~/.cache/wiz` on every check.
  Its manifest was keyed by its headers only, so every file with the same headers shared
  one manifest (12.7 MB in one cache here): it grew without bound, was parsed and
  rewritten on every root miss, and two concurrent checks of different files lost each
  other's entries, so a fresh file re-elaborated every run. A root file's manifest is now
  keyed by its text too (`wiz-cache/root-manifest-v1`); the command keys and `.wizc`
  entries are unchanged. A run no longer rebuilds `manifest.sexpr` from a full scan of
  `manifest.d` (thousands of files, hundreds of MB, ~a minute per writing run): the index
  is written by `wiz cache manifest` (and sealed by a Nix package), and nothing a run
  reads needs its module list.
  `=tooling` has a case for each (a fresh file hits on the second check, an edit misses
  and keeps its unchanged prefix warm, and two root files get two root manifests).
* selfhost: the driver's cache is per module and keyed on content, not paths (D5). One
  `<key>.mcheck` entry holds a module's tagged output lines; the key is the module's
  name and text, its `import_c` header texts, the contents of its `include_str` files,
  the toolchain id and, recursively, its imports' keys. A changed dependency, header or
  included file is a miss; a path or an mtime is not in the key, so a file edited with
  its mtime kept is a miss and the same text under another `-I` root is a hit. A warm
  `check` reads every module's entry in load order and runs no command; one miss is a
  cold elaboration of the graph (the frontend's globals are not serialized). Entries
  carry their payload's digest, so a truncated or edited entry is a miss, never a wrong
  verdict. Before, one graph-wide key mixed the modules' paths and the root's headers,
  so a dependency's `import_c` header and every `include_str` file were outside it.
* scry: `scry taint` and `scry parse --stats` read C source as `Bytes` and parse it in
  place (`FS.readBytes`, `Scry.Native.parseBytes`, `Scry.Cst.ofStoreBytes`), and
  `parseBlock` sniffs the store format on bytes instead of `String.trim`-ing the whole
  file. A 4 MiB source no longer becomes a `String` (`List Char`, two cons cells per
  character): the memory ratio drops from ~287× to ~8× (a 3 MiB string literal peaks at 23.8 MiB). The summary fixpoint reuses the
  converged round's `FuncResult`s for the results stage (it evaluated every function a
  second time), prepares each function's plan once instead of per round, and indexes a
  point's CFG predecessors (`Scry.Fn.pointPreds`) instead of rebuilding them by scanning
  every point: the 525-byte 128-statement case drops from 12.85 s to 0.32 s (256 statements 2.2 s). Long
  integer literals are parsed by halving the digit list (`Scry.parseDigitsAt`) instead
  of one quadratic-size multiply per digit. New `scry/scripts/dos-check.py` (grail target
  `dos-check`, run by the nightly bench workflow) pins RSS < 20× input and statement
  counts 16/64/128/256 to small time budgets (S1 findings `scrydos-01/02/03`).

* selfhost: a `match` (or `if`) on a closed scrutinee is no longer evaluated while the
  self-hosted frontend compiles (#422). The frontend evaluated elaborated terms it did not
  need: the argument for a non-dependent codomain, every `let` value, `match` scrutinee and
  shared clause body, and a postponed argument (read back as its normal form, which also
  put the match's result in the program). `match Bytes.toUtf8 (Bytes.ofUtf8 "𝄞") with …`
  as an argument took over 200 s and 3.4 GB. The `selfhost` group bounds such a program
  (`fib 40`) at 120 s in `check` and in the one-shot compile.
* The trust ledger's merge driver (`scripts/trust-ledger-merge.sh`) merges three-way
  by key: a row one side deleted and the other left unchanged is deleted (a union kept
  it, so a branch merging master resurrected rows master had removed), and a row one
  side deleted and the other modified is a conflict the driver refuses (22f).
* grail test (23f): `--rerun` runs tests whose pass is recorded again instead of reporting
  the recorded pass; the result replaces the record (a failure removes it). Before, forcing
  a cached test meant `--update` and a `git diff` of the `.expected` files.
* grail test (23f): a test may declare its own time limit, `-- test: run timeout 900`
  (or `check … timeout SECS`); the larger of it and `--test-timeout` applies to the test's
  job and to its program, so one long test no longer needs a large flag on every run.
* `wiz lsp --ws` (breaking for its clients) requires a token: an upgrade without
  `?token=T` or `Authorization: Bearer T` gets `401`, so a local program can no longer
  connect, open documents and have them elaborated as you. The token is fresh per launch
  and printed on stderr, or read from `--token-file FILE` (created 0600 if missing);
  `--ws-insecure` (loopback only) turns the check off. `wiz/browserInfoview`, the web
  infoview, the playground and `wiz doc --serve`'s panel pass it on (11o, #430).
* LSP: references, document highlights, `prepareRename` and rename work with the cursor
  on a declaration's own name (a `def`/`inductive`/`structure` header, a constructor, a
  structure field), with the same answer as from a use; a constructor or field renamed
  within its namespace is edited where it is declared too (11y, #434).
* LSP: two one-shot requests that need no session or ref: `wiz/typeAt` (the innermost
  elaborated term at a position, its type and range) and `wiz/coreTerm` (a
  declaration's type and value as core terms, its kind, native implementation and
  axioms); both are infoview methods too (11, #435).
* `=selfhost-libdiff` reports its progress while it runs: the compiler build, one line per
  file as it finishes (verdict, seconds), a heartbeat every 60 s (files done, elapsed, free
  memory) and the counts at the end. A case's `Tests.progress` lines go to the driver's
  standard error at once, indented; they are not notes or output and change no verdict.
* `=selfhost-libdiff` checks its files N at a time under the driver's `--jobs N` (and
  `tests --libdiff --jobs N`), capped by the CPUs and by the free memory (cgroup-aware) at
  `--mem` per file; each file once, records in file order, the same verdicts (exit 3
  stays `bounded`). A case of a group that runs its cases one at a time now receives
  `--jobs` (`Tests.caseJobs`). The records carry each side's `ms`, the summary the
  slowest runs (21ae).
* `UInt64.ofNat` is total: it reduces the `Nat` modulo 2⁶⁴ in Wiz before the C call
  (`wiz_u64_id` takes a `uint64_t`, and the marshalling panicked above 2⁶⁴); the `ffi`
  group pins 2⁶⁴−1, 2⁶⁴ and 2⁶⁴+1 in C and LLVM. The trust ledger's numeric/container
  FFI rows (`Word`, `WordArray`, `WordMap`, `Intern`) are reviewed per C symbol, and
  `scripts/trust-ffi-audit.sh --check` compiles each extern's generated prototype
  against `runtime/wiz_rt.h` (9g, 22f).
* runtime: `IO.arg` past the end returns `""` without the `i + 1` overflow at 2^64-1;
  `Child.killGroup` after `Child.wait` is `ESRCH` instead of a signal to a possibly
  reused process group; `Pty.name` uses a thread-local buffer (FFI audit).
* scry project: a `compile_commands.json` is repository-supplied, so its flags are now
  filtered by an explicit allowlist before they reach `cc -E`. `-I`, `-isystem`,
  `-iquote`, `-idirafter`, `-include`, `-D`, `-U` and `-std=`/`--std=` are kept (the MCP
  bridge also confines the path-valued ones), the compile driver's `-c`/`-o`/`-M…`
  structure is consumed, and every other word is **refused by name**. A database with
  `-B<dir>` (which selected a committed `cc1`), `-fplugin=`, `-specs=`, `-wrapper`,
  `@file`, `-Xclang` or `-cc1` no longer executes code through `scry_project`, whose
  tools are `readOnlyHint: true`. `Scry.parseCompdbFlags` and the scry-mcp bridge check
  the same list (security-01).
* runtime, tests: the `Proc.runLinked` case is now really differential. `Chan.forks`
  reads a new native counter (`wiz_chan_forks`, the threads `Chan.fork` started), and the
  compiled case prints `45150 forks 1`: removing `implemented_by` leaves the result and
  prints `0`, so the case fails. Both channel layers' differential claim is in the
  docstrings and 25c. The one-thread build (`WIZ_NO_THREADS`, 25k) is exercised further:
  the `conc` group adds abort cases for a full MVar and a held lock, and
  `scripts/test-runtime.sh` links it with stub pthreads (`-Wl,--wrap=`, no pthread
  symbols), runs a channel program that sends before receiving, checks the empty
  channel and full MVar / held lock stops, and compiles the header's Emscripten
  auto-enable's translation unit (there is no `emcc` build; 25k).
* scry: the C parse/lower pipeline is fuzzed (#478). `scry/scripts/fuzz-lower.py` drives
  the native CstStore, `Scry.lowerTU` and the taint pipeline with generated and mutated C
  (122 seed files, 400 executions, 5 s and 256 MiB resident per run), and commits the 25
  regression fixtures under `scry/tests/fixtures/fuzz-regression/`; `--regressions-only`
  replays them. `scry/bench/fuzz.md` records the campaign, the caps and every finding
  (0 crashes, 38 hangs, 19 OOMs, 5 refusals, 338 clean). A clean run is not a safety
  claim: it is a bounded search over the Wiz side, complementary to the tree-sitter
  `fuzz/run.py`.
* trust ledger: the 134 `mutual`/`partial` rows are reviewed as one group, with a reason
  per block (compiled-only general recursion, an inhabited witness at 22f, no
  termination claim, and the de-mutualisation or measure that would remove the row), and
  `docs/trust-ledger.md` states that such a row is a design choice, not an unreviewed
  gap. The two structural fuel loops `Scry.rdLoop`/`Scry.domLoop` are now total, so the
  group was 132 rows at that review (182 today, after later modules). The migration is
  complete: the twenty `Prelude` numeral/`memo`
  registrations, the `PMap`/`Scry` seals and `Proc.runLinked` have individual reasons
  too, no `legacy:` row remains, and CI runs `--strict-legacy` (22f, 13a).
* grail (23n): `grail vendor [DIR]` copies the lock's registry archives into a
  content-addressed vendor directory (`<sha256>.tar.gz` plus `vendor/index.sexpr`) without
  rewriting `grail.lock`; `--vendor DIR` (or `Package.set "vendor" "DIR"`) lets `fetch`, `build`,
  `test`, `run`, `lsp` and `doc` resolve archives by SHA-256 before the cache or the
  network, so `grail fetch --locked --offline --vendor vendor` is hermetic. Unpacked
  registry packages now live in the shared, content-addressed store
  `<cache>/grail/packages/<sha256>/`, linked from `.grail/packages/NAME`, so a second
  project downloads and unpacks nothing; `grail cache path|list|verify` inspects the
  store (`=grail-vendor`). The index and lock formats are unchanged.
* grail (23m): a static package registry. `Package.version/toolchain/require`, an
  S-expression index (`index/NAME.sexpr`, scoped `index/@org/NAME.sexpr`), semver ranges
  (`^0`/`^0.0` included), a flat resolver that retracts constraints of replaced
  versions, lock v2 (index URL+commit and `pkg` entries), `grail update/fetch
  [--locked] [--offline]`, `--index URL#COMMIT`/`index-commit` pins, rollback protection
  over the index's git history (`--allow-rewind`), SHA-256-before-unpack fetching with a
  content-addressed archive cache, `grail publish`, and a hermetic `Tests/fixtures/grail-index`
  fixture (`=grail-deps`).
* grail (23m): **lock v3**. `(version 3)` and the resolving `(toolchain …)`; package
  `(size …)`, `(tree …)` (checked after every unpack) and `(commands …)` digests; flat,
  sorted `(deps "NAME REQ" …)` entries; and `Package.override NAME PATH` in
  `grail.local.wiz` (recorded as `(override NAME PATH HASH)`, refused by `--locked`, used
  with a note by a plain build). v1/v2 locks still parse and render unchanged, and
  `grail update` upgrades them. `grail publish` and the index schema record the size,
  tree and command digest. Tests: the four new `=grail-deps` cases (round-trip, old
  locks, upgrade, override).
* grail (23m), the static index side: a `grail-index` repository layout (static
  `index/NAME.sexpr`, deterministic `packages/NAME-VERSION.tar.gz`, `index.wiz` as the
  index's Wiz manifest and generator templates), a complete `examples/grail-index/` with
  three packages, `grail index check` / `scripts/grail-index-check.sh` (names, versions,
  semver requirements, local archive SHA-256s and layouts, `index.wiz` completeness,
  module-prefix conflicts; offline by default), `(modules …)`/`(prefix …)` in the index
  schema, `grail publish` recording module names, and a resolve-time module-conflict
  check (`=grail-index`). A signed index snapshot (`index/snapshot.sexpr` with
  `(seq)`/`(updated)`/key fingerprint/`(expires)`, plus a detached SSH signature),
  `grail update --require-signature --allowed-signers FILE`, the lock's
  `(index-signature …)` fields (key, fingerprint, sequence, digest) and an offline
  `grail index verify`; later updates re-verify from the pinned key and refuse tampering,
  rollback, a same-sequence rewrite and an expired key. There is no transparency log;
  the TUF/Sigsum staging, key rotation and the remaining gaps are in
  `docs/stages/23-grail/index-repository.md`. `update --locked --require-signature`
  refuses a registry lock with no `(index-signature …)` even when its `(index …)` line
  is absent; `--locked` reads no index, so it checks the entry's shape only, and
  `grail index verify --locked` is the command that re-verifies the signature.
* grail (23f, #390): the root `grail test` run is green (88 passed, 0 failed, 2 skipped).
  A golden may be `-- test: skip REASON` (reported `⊘`, no `.expected`, not a pass); a
  subdirectory with its own `grail.wiz` is a nested package, not a test of the parent; 38
  missing goldens were added and 3 stale ones reviewed. `Package.tests` documents the
  nested-package rule (`docs/stages/23-grail.md:116-125`).
* selfhost: the parser tables are a checked-in Wiz source file (`selfhost/Tables.wiz`,
  rendered by `lake build genSelfhostTables`; the `selfhost` group checks that it is
  current and that its tables accept the same corpus as the Lean parser), and the
  compiler's entry point is `selfhost/Main.wiz` (the checker's is
  `selfhost/Check.wiz`). The fixpoint's input is `selfhost/*.wiz` with no generated Wiz
  text in it: only the build identity (`wizVersion`, `toolchainId`) is passed in (23e).
* `Float64.ofNat` rounds correctly for every `Nat`: it used to abort above `2^64`
  ("a number is too big for a C integer"). The value-level semantics matrix
  (`docs/semantics-matrix.md`, group `=semantics`) pins the numeric and textual
  boundaries across `#eval`, `#run`, Lean → C and Wiz → C (22c).
* Shifts agree for every `Nat` count. `UIntN.shiftLeft` caps the exponent at the
  width (`Word.min k w`), so `k >= w` gives `0` without the model trying to build
  `2^k` (which panicked at `k >= 2^32`); `a >> k` is `0` once `k` passes the bit
  length of `a`. The matrix now pins `0, 1, w-1, w, w+1, 2^32-1, 2^32, 2^64-1`,
  and the rotate composition for `k >= w` (22a, 22c).
* libraries: `lib/Plot.wiz` (#381), data plots as deterministic SVG. `Plot.Frame` takes
  named `Series` (`line`, `scatter`, `bar`, `step`) over exact arithmetic (`Q` over
  `Int`; no `Float64` in the core), so the same input renders byte-identically: no
  timestamps or random ids enter the output. `examples/plot.wiz` is the tour, the `plot`
  group pins four golden SVGs (`Tests/data/plot/{bar,histogram,line,scatter}.svg`), and
  `docs/libraries.md:1979` has the API.
* tower: the Lean reference implementation (`Tower/`, `tests --tower`) is gone; `tower/`
  is the only implementation, and the `tower` test group tests it (26h).
* tower: a `wiz-toolchain.local` next to `wiz-toolchain` (uncommitted; add it to
  `.gitignore`) overrides it with a spec or a path to a toolchain directory or built
  checkout; the shims, `which` and `show` honour it (26a, #281).
* A WebAssembly target (8f): `wiz build FILE -o OUT --target wasm` emits a binary module
  directly from the IR, and `wiz run FILE --target wasm` runs it under Node with
  `web/wasm-host.mjs` (big integers as `BigInt`; values in linear memory). IO-less
  `main`s over `Nat`/`Int`, constructors, closures, join points, codata and `Array` work;
  C and LLVM are unchanged, and `--llvm`/`--wasm` remain aliases. The subset boundary is
  checked at compile time and every module is parsed and type-checked before it is
  written (`Wiz/Compiler/WasmValidate.lean`); golden tests compare the module's result
  with the interpreter's. Limits and the 29-case `wasm` test group are in
  `docs/stages/08-backend/wasm.md`.
* The published site has a `/bench/` page: standard-library timings (with the
  interleaved A/B ratios and the spread of each run) and the Scry taint metrics,
  rendered from the checked-in JSON by `web/build-bench.py`. The page is committed, so a
  JSON change that was not regenerated is a diff, and the docs job refuses it
  (`web/build-site.sh` runs the generator's `--check`).
* The WebAssembly target reclaims memory (8f): `dup`/`drop` maintain the object header's
  reference count, the last drop releases the fields and returns the block to a segregated
  free list, and `reset`/`reuse` refill a unique cell. A long-running program's peak is its
  peak live set, not everything it allocated: the fixed workload in
  `scripts/wasm-workload.wiz` (320 MiB under the bump allocator, 40 iterations) drops from
  320 MiB to 8.1 MiB of linear memory in 0.7× the time (0.19 s reference counting against
  0.27 s bump), and a 1000-iteration run completes
  with the same 8.1 MiB peak where the old allocator would have needed 7.8 GiB. Freeing is
  iterative (through the dead object's own header), so a long chain does not recurse on
  the engine's stack. `scripts/wasm-peak.mjs` reports a module's peak and time.
* wasm (8f, #372): tail calls and CAF caching. A self tail call compiles to `return_call`
  (`return_call_indirect` for an indirect one), so a loop no longer grows the engine
  stack, and a closed definition's value is built once and shared (`wiz_caf_builds`).
  Ten million mutual tail calls run in 36.6 ms at one page of linear memory;
  `web/wasm-host.mjs` implements both, and the `wasm` group checks 200k-deep recursion
  and a CAF built once (`Tests/Groups/Wasm.lean:361-375`). The validator knows the
  tail-call proposal (`docs/stages/08-backend/wasm.md:41-45`).
* `wiz repl` (11ac): one command per line into one persistent frontend session
  (definitions, `syntax`, `macro`, `instance` and `import` stay in scope), with `:type`,
  `:load`, `:run` (C, or LLVM with `--llvm`), `:reset`, `:help` and `:quit`; a pipe is a
  script with no prompt. `--prelude MODULE`/`-p` (repeatable, comma-separated) imports
  modules after the Prelude, so a tool can ship a prelude and wrap the ordinary REPL. The
  test wrapper is `wiz test-driver` (the old `wiz test` name is reserved for the
  proposed single-file form, which is not implemented).
* [`tools/wiz-mcp/`](tools/wiz-mcp/README.md) is a stdlib-only MCP server for the
  toolchain: `version`, `check`, `parse`, `fmt`, `build`, and the language server's
  `diagnostics`, `hover` and `goals` over MCP stdio, with one lazily started
  `wiz lsp --ws` daemon per bridge and worktree (idle unload, a per-call deadline, and
  no sharing between worktrees). It is opt-in (not in the dev shell), and
  `.github/workflows/tools.yml` runs its unit tests on every change under `tools/`,
  with the end-to-end smoke test on manual dispatch.

* scry: a `Wil` e-graph layer (`Scry.EgraphWil`, `Scry.EgraphExtract`,
  `Scry.EgraphTaint`). `wgSaturate` folds constants and identities on a read-only view;
  `wgeRewriteProgram` writes back only checked single-statement rewrites (one-block
  function, operands already registers of the right-hand side with a single earlier
  definition, strictly cheaper extracted term); and `wgeTaintDiff` compares taint alerts
  before and after (`added = 0` by construction, `removed` is a precision gain).
  `scry egraph FILE.c [--fuel N] [--rewrite]` runs it from the CLI. The native-table
  e-graph (`Scry.EgraphNative`, with analyses, explanations, limits and `Option`
  extraction costs) and the equality-sort Datalog planner (`Scry.EqPlan`) are the second
  S12 slice. `Scry.Egraph` and `Scry.EgraphNative` share names but not the record type
  (seven fields against five) or the `applyAt`/`applyMatches` signature, and cannot be
  imported into one program; they are not drop-in replacements. Six of the seventeen
  e-graph examples are differential. Groups `scry-egraph` and `scry-taint` cover them.

## [0.1.0] - unreleased (draft)

The first tagged release. Everything below is new in it; it collects the stage docs 1–30
and 32 (`docs/stages/`; there is no stage 31) and the pull requests merged up to the tag.
The repository is https://github.com/wiz-pl/wiz
(moved from `badly-drawn-wizards/wiz`; GitHub redirects the old URLs).

### Stability

* 0.1 is mostly a fixed toolchain to pin (`wiz-toolchain`: `v0.1.0`). Only these are
  promised for 0.1.z ([docs/stability.md](docs/stability.md)): the `wiz-toolchain` file
  and tower's specs, the release tags and their download URLs, grail's core `Package`
  API (`new`, `lib`, `exe`, `tests`, `check`, `dep`), and the `wiz` command line
  without its experimental flags. Everything else, including the language, the
  standard library, the LSP and infoview protocol and the C FFI, may change in 0.2
  without deprecation aliases. Breaking changes will be listed here.
* **Soundness.** Nothing about Wiz as a whole is proved. [docs/Status.md](docs/Status.md)
  lists what is known: the trusted base, the conjectures (regularity at inert types,
  equality of descriptions) and the open issues. Please report a proof of `False`
  (Status.md, "How to report a soundness bug").

### The core theory and the kernel

* A kernel for quantitative type theory, parametric in the rig (quantities `0`, `1`,
  `ω`), with universe polymorphism, Σ, `Unit`, `Empty` (stages 1, 4a–b), quantity
  polymorphism (4d).
* Observational equality with an impredicative, proof-irrelevant `Prop`: function
  extensionality, `cast` that computes on data (4c); equality of descriptions,
  `μ ≡ μ` compares the codes (4g, #40).
* Data as indexed descriptions with `μ`/`ν`, `inductive` and `structure`, dependent
  pattern matching and structural recursion (4d–e), sized types (4f), codata and
  copatterns.
* Regularity off by default (decision D1 (a), #4, #15); regularity at inert types
  decided by ground equality (#46); `castRefl` as a propositional axiom (#23).
* Proofs are never evaluated by the kernels (P2, #61); `Size`/`Qty` handling, `ULift`
  for small description fields (Q4, #26).
* The trusted base made explicit (22f): partial definitions need a witness the kernel
  checks (#5), `builtin` registrations outside the toolchain's library are axioms (#5),
  a builtin key is registered once (#67), compiled equations are derived from the
  checked value and their agreement is checked by the kernel (T1, #82, #126),
  `#print axioms` lists native implementations (#66).
* Soundness fixes, each with regression tests (docs/Status.md §3–4): propositions
  compared by shape (F1), `∞ < ∞` (F2), partial definitions at an empty index (F3, #5),
  unchecked registrations (F4, #5), quantity variables in type equality (F6, #43), a
  variable captured by a native operation (F7, #59), `absurd` on glued values (F8,
  #59), the eliminators' index levels (F9, #83), K3/Q1/Q2/Q3 (#14), projections only on
  unrestricted pairs (R1, #84), two declarations of one name (#104), a variable out of
  scope (#72), the self-hosted kernel's fast path at universe levels (W1, #76),
  `Size ≡ Size` in the self-hosted kernel (O1), and Π/Σ/`ULift` casts computing only
  when their components are in one sort (D2, #203).
* Kernel lint: every traversal handles every constructor; a panic is not a value (#78).
* WizMeta: a specification of the core theory and a reference checker (#122);
  equations at propositions are `True`, and the Σ rule along a proof component uses
  `reflTy` (NU-TRANSP, #123; the elaborator's `refl a` follows, #130).

### The language and the elaborator

* An extensible parser (stage 2), an elaborator with implicit arguments and unification
  (stage 3), macros by example, procedural macros and tactics written in Wiz (stage 6,
  #88: `trace`, hygienic names, `unfold`/`whnf`/`change`/`rw`, reflection of
  constructors), type classes with tabled resolution and `deriving` (stage 7, #39),
  numeric classes `Add`/`Sub`/`Mul`/`Div`/`Mod`/`Neg`/`OfNat` and `Int` (7e, #85).
* Effects as a library, fusion, one-shot effects (stage 10).
* Named arguments (13a, #33); private declarations, constructors, fields and types,
  per module (13b, #33, #48, #109, #132); `if`/`&&`/`||`/`!`, `Functor`/`Applicative`,
  `∃` binders and ASCII logic, `let` tuple patterns (13c–f, #107); as-patterns,
  structure patterns and `⟨…⟩`, structure update (13g–i, #106); keyword scopes (13j,
  #89); list literals, `++` as `Append`, local notation (13k–m, #115); `rfl` at an
  equation that has computed (13n, #111).
* Phantom fields for unused type parameters (22e, #10); sealed types (22k, #119);
  regions: borrow checking as typing (22g, #19); Feral, a Rust-like surface language as
  a command macro (22j, #125).
* Many elaborator fixes: postponed lambdas, trailing instances, projection functions,
  constructor parameters from the expected type (#25), numeral-sub blowup and computed
  equations (#13), scope escape (#31), unification approximation and do-notation (#92),
  fast-failing unification (#110), `Level.normalize` (#35), linear nested spines (#62),
  a term whose type is the expected definition is unified rather than η-expanded (#116),
  pruning a hole's out-of-scope variables (#158).
* Two modules declaring one name: one error, at the import (#104, #112); private names
  and types are per module (#109, #132).
* Module roots: the toolchain's library first, then `-I` (`./lib` only as a fallback,
  #117).

### Running and compiling programs

* Erasure and an interpreter (`#eval`, stage 5); representations decided by what
  conversion sees (R3, #70).
* An IR with Perceus reference counting and reuse, C and LLVM backends (stage 8),
  borrowed parameters and drop specialisation (8e, #34); optimiser quick wins (#32);
  unboxed structure fields and `attribute [inline]` (22i, #37).
* Numbers for hardware and systems code (stage 22): division, powers and bits,
  `implemented_by`, machine integers, unboxed words (#11), one bit-vector family (#24),
  big numerals (#80).
* The C FFI (stage 9): foreign functions and header import, checked glue, foreign
  pointers and finalizers, `link_c`/`link_lib` (9f, #57), callbacks and exported
  functions (9g, #56), processes, environment and files in `lib/Sys.wiz` (9h, #64), C
  structs by value (9i, #63), bytes on handles, time limits and serial ports (9k, #101).
* Concurrency (stage 25): a thread-safe runtime (#49), session-typed linear channels,
  MVars and locks (#52).

### Self-hosting

* The lexer, parser, kernel, frontend and a backend written in Wiz (`selfhost/*.wiz`,
  stages 12–21). The self-hosted frontend checks its own source, and the bootstrap
  reaches a fixpoint (stage-1 C = stage-2 C).
* Reference counting in the self-hosted backend (#9, #16, #28, #71, #77).
* Parity work: phantom parameters, constructor parameters from the expected type,
  `IO.args`, `--rc` (#44); foreign functions and types (21l, #73); written quantities,
  `private`, `link_c`/`link_lib`/`export` (21m–p, #113).

### Libraries

* The Prelude, `Vec`/`Fin`/`BitVec` (#3), `lib/Json.wiz` and `lib/Infoview.wiz` (#12),
  `lib/Text.wiz` (#103), `lib/Session.wiz` and `lib/MVar.wiz` (#52), `lib/Sys.wiz`
  (#64, #101). See docs/libraries.md.
* Separation logic (stage 24, #65): propositional logic over `Prop`, heaps and heap
  predicates, Hoare triples as a Dijkstra monad, and `x`-tactics (24d, #114, #127).
* HDL (experimental): a hash-consing netlist builder (#30), named ports, registers,
  bundles, composition, reset/enable, Verilog emitters and simulation (#81, #91, #108,
  #118).

### Tooling

* `wiz parse|check|build|run|lsp`.
* A content-addressed elaboration cache shared between projects (11c, #29).
* A language server: info tree, infoview protocol methods, code actions (11d, #6);
  `wiz lsp --infoview SOCK` (11l, #21) and `--ws` (#42); go to definition and hovers
  for syntax, binders, imports and instances (11q, #124); notation-aware printing with
  unexpanders, in messages, hovers and goals (11r, #139).
* Infoview clients in the terminal and in the browser (WebAssembly) (11m–n, #12).
* wiz.nvim, a Neovim plugin (11p, #47, #99).
* grail, a build tool and test runner configured in Wiz (stage 23): modules by path,
  a cache key per module, grail v0 (#7), the self-hosted toolchain as targets and a test
  runner (#17), parallel jobs (#22), git dependencies and `grail.lock` (#27), command
  targets, `grail run` and a job supervisor (#102), `grail lsp` (#95).
* tower, a toolchain manager with `wiz`/`grail` shims and a `wiz-toolchain` file per
  project (stage 26, #54, #90, #93), also written in Wiz (26e, #103). Channels: `stable`
  is the highest `vX.Y.Z` tag; `nightly` is the commit of the tag `nightly` for every
  source, Nix and source builds included (#159).
* `wiz --version`, `grail --version` and `tower --version` (#149), also through the
  toolchain wrappers.

### Distribution

* A Nix flake: `nix develop`, `packages.wiz`, `packages.tower`, `nvim-wiz`, with
  binaries on the Cachix cache `badlydrawnwizards` (#29).
* Release tarballs that need only glibc 2.27 (2.30 for the bundled C compiler), with
  their own C compiler, GMP and Boehm GC (26f, #100); a snapshot release for every
  master commit and a `nightly` tag that moves once CI passes (26g, #97). The bundle's
  downloads are mirrored and retried (#150). The bundle also has CaDiCaL, a SAT solver
  that writes LRAT proofs (the Lean toolchain's copy); z3 is not bundled.
* x86_64 Linux only: glibc 2.27 or later, 2.30 or later for `wiz build` with the bundled
  C compiler (Ubuntu 20.04+, Debian 11+, RHEL 9). Ubuntu 18.04 can check and run.
* CI: a merge queue (#141), heavy shards on a self-hosted runner (#142).

### Licence

* GPL-3.0-or-later, with the Wiz Runtime Library Exception for the runtime and the
  libraries, so programs built with Wiz can be licensed as their authors like (#86).
  Copyright (C) 2026 Reuben Steenekamp.
* The tarball carries `LICENSE`, `COPYING.RUNTIME`, a `NOTICE` listing the third-party
  code in the toolchain, and their licence texts (#150). Programs built with the bundled
  C toolchain link GMP statically: see NOTICE for what the LGPL asks when you
  distribute them.

### Known limitations

From [docs/Status.md](docs/Status.md) (its ledger, §0, has the details and the tests
that pin each one):

* Conjectures, not proved: regularity at inert types (D1; `--inert conv` is
  experimental), `μ` injective in its description (E1), and the rest of the core
  theory's combination (Status §1–2).
* Open issues: the neutral case of NU-TRANSP; Σ unboxing is not stable under
  substitution, so `--unbox-structs` stays off (R3 open 1); duplicating a `&mut` and
  borrowing one local twice in Feral are not rejected (pinned "KNOWN GAP" tests).
* "Stuck but sound" cases (Status §5) are incompleteness: some true equations don't
  compute.
* No mechanised model. A bounded search for `False` exists: `tests --false-fuzz` builds
  closed terms that claim to inhabit `Empty` and asks both kernels, and the `false-fuzz`
  group (20 samples per shape) runs in the `selfhost` shard
  (`.github/test-shards.json:2,8`). A campaign of 1000 samples per shape (seed 20261114)
  found no accepted closed `Empty` in either kernel and no verdict difference beyond the
  known quantity-only `Σ` observations (`Tests/FalseFuzz.lean:1-26`).
* Not yet in Wiz: termination by measure, machine-integer and vector literals.
* selfhost: a constructor's parameters and fields are named arguments too (A9). The
  self-hosted frontend kept no binder names for a constructor's `Global`, so
  `P.mk (y := 2) (x := 1)` was `no parameter named 'y'`; the names are now the type's
  parameters followed by the constructor's fields, so fields can be given in any order
  (a later field's type may mention an earlier named one), and an implicit field or a
  parameter can be named. An inductive type's own parameters, a dot-constructor and a
  local Π type still keep no names; the `selfhost` and `language` groups pin the accepted
  and rejected constructor forms against the Lean frontend (21ab, 13a).
