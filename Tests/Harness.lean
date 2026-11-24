import Wiz.Toolchain
import Tests.Loader

/-!
# A tiny test harness

Each group is tagged with the exercise it exercises. `lake test -- <group>...` runs only
the named groups. Unimplemented `sorry`s fail at runtime with "executed 'sorry'".

## Two rules for every case

**Prove the injection, then the detection.** A case that asserts an outcome must also
show that its input reached the code under test; an anti-vacuity or meta case must read
back the effective value it injected and fail unless that is what ran
(`Tests.checkInjection` in `Tests/Groups/SelfHost.lean` reads
`selfhost-override … source=env path=<stub>` lines). The stub meta-case shipped vacuous
for a night because nothing read the children's stderr: 211 of 211 children ran the real
compiler and passed. Every such case also needs a mutation self-test that must fail
(`WIZ_SELFHOST_STUB_MUTATION=env|flag`); docs/building.md, "Anti-vacuity".

**Every case runs under a printed wall limit** (`--test-timeout`, default
`defaultCaseTimeoutS`, `timeout --kill-after=10`), and its result line says
`(12.3 s / limit 3600 s)` or `limit none`. A case that runs past it fails with that
sentence; `scripts/ci.py timings` warns at 80 % of the limit. A timeout raised where it
never takes effect is then visible as the old limit instead of looking like a fix.
-/

namespace Tests

/-- The toolchain the suite builds with (C compiler, GMP and collector flags), set once by
`Tests/Main.lean` and passed to everything that compiles. -/
initialize toolchainRef : IO.Ref Wiz.Toolchain ← IO.mkRef {}
/-- The toolchain flags, given again to each case's process. -/
initialize flagsRef : IO.Ref (List String) ← IO.mkRef []

/-- `--selfhost-cache DIR`: where the self-hosted compiler/checker are built and kept.
A flag rather than an environment variable, and the value is forwarded to each case's
process with the other driver flags, so a run that gives it keeps every case on the same
cache. Default: the system temp directory (`/tmp`). -/
initialize selfhostCacheRef : IO.Ref (Option System.FilePath) ← IO.mkRef none

/-- `--selfhost-compiler PATH` / `--selfhost-checker PATH`: use this binary instead of
building one. The flag wins over the `WIZ_SELFHOST_*` environment variables, which are
kept for the stub-compiler case that sets them for a child process. -/
initialize selfhostCompilerRef : IO.Ref (Option System.FilePath) ← IO.mkRef none
initialize selfhostCheckerRef : IO.Ref (Option System.FilePath) ← IO.mkRef none
/-- The driver's `--jobs N`, for a case that runs alone (a group that did not opt in to
`Group.parallel`): such a case may use up to N workers of its own (`=selfhost-libdiff`
checks its files N at a time). `Group.run` passes it to each case's process; the cases
of a parallel group (`Group.runJobs`) get 1, since N of them already run at once. -/
initialize caseJobsRef : IO.Ref Nat ← IO.mkRef 1
/-- Whether the driver was given `--jobs` (so a case can tell an explicit `--jobs 1`
from the default, which means "choose for yourself"). -/
initialize caseJobsSetRef : IO.Ref Bool ← IO.mkRef false
/-- The driver's `--part i/n`, for a case that is one part of a split sweep
(`=selfhost-libdiff`): `Group.run` passes it to each case's process. Empty when it was
not given, which is the whole sweep (`1/1`). -/
initialize casePartRef : IO.Ref String ← IO.mkRef ""

/-- How many workers a case may use (`caseJobsRef`); at least 1. -/
def caseJobs : IO Nat := do pure (max 1 (← caseJobsRef.get))

/-- Whether `--jobs` was given on the command line. -/
def caseJobsGiven : IO Bool := caseJobsSetRef.get

/-- The driver's `--part i/n` as it was given, or `""`. -/
def casePart : IO String := casePartRef.get

def toolchain : IO Wiz.Toolchain := toolchainRef.get

/-- The tests' loaders serve the toolchain's `lib/` (and test modules standing in for
it): their `builtin` registrations are trusted, as `wiz` trusts `lib/`. The main file
never is. -/
def libModule (m : String) : Bool := m != ""

structure Case where
  name : String
  run  : Unit → IO Unit  -- a thunk: test bodies must not run at start-up

structure Group where
  name     : String
  exercise : String
  cases    : List Case
  /-- Whether `tests --jobs N` may run this group's cases concurrently. Opt-in: the
  default is `false`, so a group runs its cases one at a time (as before). A group may
  say `true` only if its cases touch no state that two cases share (a fixed path must
  belong to one case, and there is no port, driver environment variable or build
  directory in the work tree), and none of them assert on wall time or on the machine's
  load: see "Running cases in parallel" in `docs/building.md`. `tests --list-parallel`
  prints the groups that opted in (`scripts/ci.py` simulates their `--jobs` pool). -/
  parallel : Bool := false
  /-- A hint at the shard that is meant to run the group (`.github/test-shards.json`).
  It is not a fallback: `scripts/check-shards.py` fails when no shard's selectors pick
  the group, and shows this hint in the error so the fix is a selector or an exclusion.
  `tests --list-shards` prints it. -/
  shard    : String := ""

/-- The groups of the modules under `Tests/Groups/`, in their import order: each module
registers its own (`builtin_initialize registerGroup myGroup`), and `Tests/Groups.lean`, which
Lake generates from the directory's files (`lakefile.lean`), imports them all. So a new
group is a new file and touches no shared one. -/
initialize groupRegistry : IO.Ref (Array Group) ← IO.mkRef #[]

/-- Add a group to the suite: `builtin_initialize registerGroup myGroup` in its module.
`builtin_`: it runs when the test driver starts, never while Lean elaborates a module
that imports the group (a plain `initialize` would, and in the exercise tree, where the
code under test has `sorry`s, that is an error). -/
def registerGroup (g : Group) : IO Unit := groupRegistry.modify (·.push g)

def check (cond : Bool) (msg : String) : IO Unit :=
  unless cond do throw (IO.userError msg)

def checkEq {α : Type} [BEq α] [ToString α] (expected actual : α) : IO Unit :=
  unless expected == actual do
    throw (IO.userError s!"expected {expected}\n      got {actual}")

/-- The wall time of `f k` in milliseconds, best of `runs` (a shared machine stalls one
run, not all of them). -/
def bestMs (f : Nat → IO Unit) (k : Nat) (runs : Nat := 3) : IO Nat := do
  let mut best := 1_000_000_000
  for _ in [0:runs] do
    let t0 ← IO.monoMsNow
    f k
    best := min best ((← IO.monoMsNow) - t0)
  pure best

/-- `checkScaling name f n bound`: a claim of "linear" measured at `n` and `2n`, not an
absolute millisecond bound.

Runs `f 0` once to measure the fixed floor (process start-up and the like; `f 0` must
be a valid, minimal input), then `f n` and `f (2 * n)` best of three each, subtracts the
floor, and requires `t(2n) ≤ bound * t(n) + slackMs`.  `bound` 3 is a claim of linear,
6 of `n log n`, 10 of quadratic.  The measured pair is printed on success and repeated
in the failure, so a failure can be diagnosed without re-running (and no timing claim
depends on one machine's absolute numbers).

The floor matters: a ~1 s start-up otherwise hides a 2× ratio at small `n`.  The
`slackMs` allowance (default 250 ms) absorbs scheduler noise in the net times; it is
not a subsidy for a real superlinear shape, which doubles with `n`. -/
def checkScaling (name : String) (f : Nat → IO Unit) (n bound : Nat)
    (slackMs : Nat := 250) : IO (Nat × Nat) := do
  let floor ← bestMs f 0 1
  let a ← bestMs f n
  let b ← bestMs f (2 * n)
  let na := max 1 (a - floor)
  let nb := max 1 (b - floor)
  IO.println s!"  {name}: {n} → {2 * n} took {na} → {nb} ms net (raw {a} → {b} ms, floor {floor} ms, best of 3, bound {bound}×)"
  unless nb ≤ bound * na + slackMs do
    throw (IO.userError s!"{name}: {n} → {2 * n} took {na} → {nb} ms net (raw {a} → {b} ms, floor {floor} ms): more than {bound}× plus {slackMs} ms")
  pure (a, b)

/-- Run one case in-process; used by the child process. -/
def Case.runHere (c : Case) : IO UInt32 := do
  try
    c.run ()
    pure 0
  catch e =>
    IO.eprintln e
    pure 1

/-- What a case's process tells the driver besides passing or failing, one line each on
its standard output after this marker: `uses R` (it needs the shared program `R`, such as
the self-hosted checker) and `built R SECONDS` (it built `R`, which took that long). The
driver strips these lines and records them with the case's time (`--timings`), so that CI
can balance the cases of a split shard (`scripts/ci.py`). -/
def noteMarker : String := "@@wiz-test-note "

def note (line : String) : IO Unit := do
  IO.println (noteMarker ++ line)
  (← IO.getStdout).flush

/-- What a case's process prints on its standard error, before a line, to have the driver
pass that line on at once (`progress`). -/
def progressMarker : String := "@@wiz-test-progress "

/-- A progress line from a long case (`=selfhost-libdiff`): the driver prints it on its
own standard error while the case is still running, indented and without the marker, so
a CI log shows the case moving. It is not part of the case's result: not a note, not its
output, and it cannot change whether the case passes. -/
def progress (line : String) : IO Unit := do
  let err ← IO.getStderr
  err.putStrLn (progressMarker ++ line)
  err.flush

/-- Read a case's standard error to its end: pass its `progress` lines on to the driver's
standard error as they come (indented by four spaces, which no line of the suite's
summary format starts with), and give back the rest. -/
partial def readCaseStderr (h : IO.FS.Handle) : IO String := do
  let out ← IO.getStderr
  let rec go (acc : String) : IO String := do
    let l ← h.getLine
    if l.isEmpty then return acc
    if l.startsWith progressMarker then
      let text := (l.drop progressMarker.length).toString
      out.putStr ("    " ++ (if text.endsWith "\n" then text else text ++ "\n"))
      out.flush
      go acc
    else go (acc ++ l)
  go ""

/-- Mark the running case as skipped (it could not run here, e.g. without a C toolchain),
with the reason; the case then returns normally. The driver shows it as skipped, not
passed (`Group.run`), and records the note `skipped REASON` (`--timings`). A skipped case
is not evidence that the case passes.

This is for a skip the case *declares* --- a documented gap or a `-- test: skip` marker;
an environment skip goes through `skipMissing`. -/
def skip (reason : String) : IO Unit := note s!"skipped {reason}"

/-- Whether a missing dependency may be reported as a skip rather than a failure. Set by
`Tests/Main.lean` from `--allow-missing-deps` or the environment variable
`--allow-missing-deps` only: it is explicit, visible in the argv of the run that used it,
and off by default. There is no environment variable. -/
initialize allowMissingDepsRef : IO.Ref Bool ← IO.mkRef false

def setAllowMissingDeps (on : Bool) : IO Unit := allowMissingDepsRef.set on

/-- Whether missing dependencies are being reported as skips (an explicit opt-out). -/
def allowMissingDeps : IO Bool := allowMissingDepsRef.get

/-- The note a `skipMissing` case records when the missing dependency was allowed as a
skip: `missing-dep REASON`. It is separate from the `skipped REASON` note so the driver
and `scripts/ci.py check-skips` can count the environment skips, and so a CI job cannot
hide an unexpected missing dependency behind `--allow-missing-deps`: the skip lint
requires an `.github/skip-allowlist.json` entry for it. -/
def missingDepMarker : String := "missing-dep "

/-- A case that cannot run because a dependency is absent (no `cc`, GMP, Boehm GC,
`node`, `yosys`, `iverilog`, `z3`, `llc`, a `wiz`/`grail` binary, a self-host toolchain,
...). By default this **fails**, naming the dependency: a green suite must not be green
because the machine could not run the test. The explicit `--allow-missing-deps` flag turns
it into a reported skip --- the shard driver sets that only for a shard whose environment
lacks a documented optional tool, and the skip lint still requires an allow-list entry for
it. There is no environment variable: a variable that can turn a failure into a skip is the
same defect as a `PATH` that silently finds the wrong compiler. A declared gap stays
`skip`, not this. -/
def skipMissing (reason : String) : IO Unit := do
  if ← allowMissingDeps then
    note s!"skipped {reason}"
    note (missingDepMarker ++ reason)
  else
    throw (IO.userError s!"missing dependency: {reason}\n      this case cannot run without it; install it, or pass --allow-missing-deps to report it as a skip")

/-- The reason a passing case's process gave for skipping: its `skipped` note, or a line
in the old style (`(skipped: REASON)`, `(no X: skipped)`) that a case printed itself. -/
def skipReason (notes : List String) (stdout : String) : Option String :=
  match notes.find? (·.startsWith "skipped ") with
  | some n => some (n.drop "skipped ".length).toString
  | none => (stdout.splitOn "\n").findSome? fun l =>
    let l := l.trimAscii.toString
    if l.startsWith "(skipped: " && l.endsWith ")" then some ((l.drop "(skipped: ".length).dropEnd 1).toString
    else if l.startsWith "(" && l.endsWith ": skipped)" then some ((l.drop 1).dropEnd ": skipped)".length).toString
    else none

/-- Milliseconds as seconds with three decimals, e.g. `12.345`. -/
def showMs (ms : Nat) : String :=
  let frac := toString (ms % 1000)
  s!"{ms / 1000}.{"".pushn '0' (3 - frac.length)}{frac}"

/-- The default per-case wall limit, in seconds (see `testTimeLimitRef`).  3600 is above
every case in `.github/test-timings.json` (the longest is ~1430 s), so the first thing it
bites is a genuine hang or a case that grew far past its measured time -- not a case that
is merely slow today. -/
def defaultCaseTimeoutS : Nat := 3600

/-- The wall limit each case's process is given, in seconds: `--test-timeout N` (default
`3600`, `0` for no limit).  `Group.run` wraps the case in
`timeout --kill-after=10 N`, so a case that hangs is killed and named, instead of
holding its shard until the job's 120-minute timeout.

The limit is printed in every case line (`(12.3 s / limit 3600 s)`) and recorded in
`--timings` ("limit"), so a timeout that never takes effect -- an option after a
subcommand (the hdl case, 9ee24e52b) -- is visible as the old limit, not assumed to
have worked; `scripts/ci.py timings` warns at 80 % of it. -/
initialize testTimeLimitRef : IO.Ref (Option Nat) ← IO.mkRef (some defaultCaseTimeoutS)

def setTestTimeLimit (limit : Option Nat) : IO Unit := testTimeLimitRef.set limit

/-- The run's wall limit per case (`none`: no limit). -/
def testTimeLimit : IO (Option Nat) := testTimeLimitRef.get

/-- Whether `timeout` is on PATH (coreutils), asked once.  Without it the limit cannot be
enforced, and every case line says `limit none` rather than claiming one. -/
initialize timeoutAvailableRef : IO.Ref (Option Bool) ← IO.mkRef none

def timeoutAvailable : IO Bool := do
  if let some b ← timeoutAvailableRef.get then return b
  let b ← try
    let o ← IO.Process.output { cmd := "timeout", args := #["--version"] }
    pure (o.exitCode == 0)
  catch _ => pure false
  timeoutAvailableRef.set (some b)
  return b

/-- The limit a case's line reports: the configured one, unless this machine cannot
enforce it. -/
def effectiveLimit : IO (Option Nat) := do
  if ← timeoutAvailable then testTimeLimit else pure none

/-- The command and arguments that run one case: the driver under `timeout` when the
run has a wall limit (`timeout --kill-after=10 N SELF --run-case GROUP I …`), so the
grandchildren a case starts are killed with it. -/
def caseCommand (self : System.FilePath) (g : Group) (i : Nat) (flags : Array String) :
    IO (String × Array String) := do
  let args := #["--run-case", g.name, toString i] ++ flags
  if let some secs ← effectiveLimit then
    return ("timeout", #["--kill-after=10", toString secs, self.toString] ++ args)
  return (self.toString, args)

/-- The exit codes `timeout` uses: 124 for the limit, 137 for the `SIGKILL` ten seconds
after the `SIGTERM` (a case that ignores the first signal). -/
def timedOut (code : UInt32) : Bool := code == 124 || code == 137

/-- What a case that ran past its limit reports: the limit, and the two honest causes
(a hang, or a case that got much slower), so raising it stays a decision. -/
def limitMessage (limit : Option Nat) : String :=
  s!"the case ran past its wall limit of {limit.getD 0} s (`timeout` killed it):" ++
  " it hung, or it is far slower than .github/test-timings.json says." ++
  " Check with `scripts/ci.py timings` before raising --test-timeout."


/-- One case's result: its index in the group, its name, whether it passed (a skipped
case did not fail: `ok`, with the reason in `skipped`), its wall time in milliseconds, the
notes it printed (`note`), and, for a failure, its output (indented, as the suite prints
it). -/
structure CaseResult where
  index : Nat
  name : String
  ok : Bool
  ms : Nat
  notes : List String
  skipped : Option String := none
  output : String := ""

/-- A case's result as the suite prints it: its position `[n/failed/total]` among the
cases this run selected - the case number, how many have failed so far in this
invocation (this case included when it is the failure), and the size of the selection -
then `✓` passed, `✗` failed (with its output), or `⊘` skipped (with the reason). The
middle number is what makes a long shard readable while it runs: it says whether the run
is currently losing cases without waiting for the final count.

`(SECONDS s / limit N s)` is the case's effective timeout (Guard C): a case run without
one says `limit none`, so a timeout that never took effect cannot look like one that
did. -/
def renderResult (r : CaseResult) (n failed total : Nat) (limit : Option Nat := none) :
    String :=
  let num := s!"[{n}/{failed}/{total}] "
  let when := match limit with
    | some secs => s!" ({showMs r.ms} s / limit {secs} s)"
    | none => s!" ({showMs r.ms} s / limit none)"
  if let some why := r.skipped then
    s!"{num}  ⊘ {r.name}{when}\n      skipped ({why})"
  else if r.ok then
    s!"{num}  ✓ {r.name}{when}"
  else
    s!"{num}  ✗ {r.name}{when}\n      {r.output}"

/-- The result of a case's process: its child's exit code and output, and the time the
child ran for (`now` - `start`, measured in the process, not around a queue). -/
def caseResult (c : Case) (index : Nat) (exitCode : UInt32) (stdout stderr : String) (ms : Nat) :
    CaseResult :=
  let lines := stdout.splitOn "\n"
  let notes := lines.filterMap fun l => if l.startsWith noteMarker then some (l.drop noteMarker.length).toString else none
  let stdoutText := "\n".intercalate (lines.filter (!·.startsWith noteMarker))
  -- A skip is only ever a case that **passed and declared it**. Two guards, because an
  -- environment skip must not be able to absorb a real failure:
  --  * a non-zero exit is a failure, whatever it said about skipping;
  --  * a case that reported an error on stderr cannot be recorded as skipped, even with
  --    `--allow-missing-deps` - `selfhost-2` reported `unknown identifier Desc` and was
  --    still counted as a missing-dependency skip, which reads as "the environment could
  --    not run it" when the truth was "the code does not compile".
  let reportedError := (stderr ++ stdoutText).contains "error:"
  let skipped := if exitCode == 0 && !reportedError then skipReason notes stdoutText else none
  let output := if exitCode == 0 then "" else
    if (stderr ++ stdoutText).contains "executed 'sorry'" then
      "not implemented yet (hit a `sorry`)"
    else (stderr ++ stdoutText).trimAscii.toString.replace "\n" "\n      "
  { index, name := c.name, ok := exitCode == 0, ms, notes, skipped, output }

/-- (13b) The `--trace-guess-fallback` lines of a case's process (its stderr), on the
driver's stderr, with the case's own file (module `_`) named `GROUP#INDEX`:
`scripts/guess-fallback-stats.sh --tests` counts them. Only a traced run has such lines. -/
def forwardGuessLines (g : Group) (index : Nat) (stderr : String) : IO Unit := do
  let tag := "guess-fallback: "
  for l in stderr.splitOn "\n" do
    if l.startsWith tag then
      let rest := (l.drop tag.length).toString
      let rest := if rest.startsWith "_ " then s!"{g.name}#{index} " ++ (rest.drop 2).toString else rest
      IO.eprintln (tag ++ rest)

/-- Run each case in a child process (`<self> --run-case <group> <index>`), because an
executed `sorry` aborts the whole process; `only` restricts the run to the cases with
these indices. Prints each case with its position in the run (`[n/failed/total]`) and wall time
(`✓` passed, `✗` failed, with its output, `⊘` skipped, with the reason) and gives its
result to `onResult` as soon as it finishes. `start` is the first case's position in the
whole invocation's selection (the driver runs several groups) and `total` that selection's
size; both default to this group's own selected cases. -/
def Group.run (g : Group) (only : Option (List Nat) := none)
    (onResult : CaseResult → IO Unit := fun _ => pure ())
    (start : Nat := 1) (total : Option Nat := none) : IO (List CaseResult) := do
  let selected := (List.range g.cases.length).filter fun i => only.all (·.contains i)
  let total := total.getD selected.length
  IO.println s!"── {g.name} ({g.exercise})"
  let stdout ← IO.getStdout
  stdout.flush
  let self ← IO.appPath
  -- a case of a group that runs its cases one at a time may use the driver's `--jobs`;
  -- `runJobs` does not pass it, so N cases at once do not each start N workers
  let given ← caseJobsGiven
  let jobs ← caseJobs
  let jobArgs := if given then #["--jobs", toString jobs] else #[]
  -- `--part i/n` is the split sweep's part (a case of a non-parallel group that opted
  -- into it); the other cases ignore it
  let part ← casePart
  let partArgs := if part.isEmpty then #[] else #["--part", part]
  let limit ← effectiveLimit
  let mut results := #[]
  let mut n := start
  -- failures printed so far (skips are not failures: a skip is a pass with a reason)
  let mut failed := 0
  for c in g.cases, i in [0:g.cases.length] do
    if let some ixs := only then
      unless ixs.contains i do continue
    let began ← IO.monoMsNow
    let (cmd, args) ← caseCommand self g i (jobArgs ++ partArgs ++ (← flagsRef.get).toArray)
    let child ← IO.Process.spawn
      { cmd, args, stdin := .null, stdout := .piped, stderr := .piped }
    let outT ← IO.asTask child.stdout.readToEnd Task.Priority.dedicated
    let errT ← IO.asTask (readCaseStderr child.stderr) Task.Priority.dedicated
    let code ← child.wait
    let ms := (← IO.monoMsNow) - began
    let out ← IO.ofExcept outT.get
    let err ← IO.ofExcept errT.get
    forwardGuessLines g i err
    let r := caseResult c i code out err ms
    let r := if timedOut code && !r.ok then { r with output := limitMessage limit } else r
    let failedNow := if r.ok then failed else failed + 1
    IO.println (renderResult r n failedNow total limit)
    stdout.flush
    failed := failedNow
    onResult r
    results := results.push r
    n := n + 1
  pure results.toList

/-! ## Running cases in parallel (`--jobs N`, opt-in per group)

Each case already runs in its own child process, so concurrency is a bounded pool of
child processes: at most `jobs` are alive at once, and their output is printed (and
handed to `onResult`, so `--timings` lines too) in the group's case order, so a run's
log is the same as a sequential run's apart from the wall times. -/

/-- A case's process that `runJobs` has started and not collected yet. -/
private structure Live where
  index : Nat
  /-- Kill the case's process (`SIGTERM`). -/
  kill  : IO Unit
  /-- The exit code, and the wall time from just before `spawn` to the process's exit. -/
  code  : Task (Except IO.Error (UInt32 × Nat))
  out   : Task (Except IO.Error String)
  err   : Task (Except IO.Error String)

/-- Start a case's process and the tasks that collect it: one reads each pipe (so the
child never blocks on a full pipe) and one waits for it (so its wall time does not
include the time it waits in the pool's queue). The child stays in the driver's process
group, as it was sequentially: `Ctrl-C` at the terminal reaches the running cases too.
The process is the run's `timeout` wrapper when there is a wall limit (`caseCommand`). -/
private def startCase (self : System.FilePath) (g : Group) (i : Nat) (flags : Array String) : IO Live := do
  let start ← IO.monoMsNow
  let (cmd, args) ← caseCommand self g i flags
  let child ← IO.Process.spawn
    { cmd, args, stdin := .null, stdout := .piped, stderr := .piped }
  let out ← IO.asTask child.stdout.readToEnd Task.Priority.dedicated
  let err ← IO.asTask (readCaseStderr child.stderr) Task.Priority.dedicated
  let code ← IO.asTask (do pure (← child.wait, (← IO.monoMsNow) - start)) Task.Priority.dedicated
  pure { index := i, kill := child.kill, code, out, err }

/-- Run the cases of `g` that `only` picks with a bounded pool of `jobs` child processes
at a time, printing each case's result (and calling `onResult`) in the group's case
order, so the log is deterministic; the `[n/failed/total]` position is assigned when the
result is printed (not in the child), so parallel cases cannot interleave numbers.
`start` and `total` are the whole invocation's first position and size, as in
`Group.run`. A group must opt in with `parallel := true`.

A case's failure does not stop the other cases (the suite reports every failure, as it
does sequentially); an exception (such as a pipe that could not be read) kills the
processes still alive before it propagates. -/
def Group.runJobs (g : Group) (jobs : Nat) (only : Option (List Nat) := none)
    (onResult : CaseResult → IO Unit := fun _ => pure ())
    (start : Nat := 1) (total : Option Nat := none) : IO (List CaseResult) := do
  if jobs <= 1 then return ← g.run only onResult start total
  IO.println s!"── {g.name} ({g.exercise})"
  (← IO.getStdout).flush
  let self ← IO.appPath
  let part ← casePart
  let flags := (if part.isEmpty then #[] else #["--part", part]) ++ (← flagsRef.get).toArray
  let todo := (List.range g.cases.length).filter fun i => only.all (·.contains i)
  let total := total.getD todo.length
  let limit ← effectiveLimit
  let pending ← IO.mkRef todo
  let live ← IO.mkRef ([] : List Live)
  let results ← IO.mkRef ([] : List CaseResult)
  -- failures among the results printed so far (the pool prints in case order)
  let failedRef ← IO.mkRef 0
  -- start the next case off `pending`, unless the pool is full
  let rec fill : Nat → IO Unit
    | 0 => pure ()
    | n + 1 => do
      match ← pending.get with
      | [] => pure ()
      | i :: rest => do
        pending.set rest
        let l ← startCase self g i flags
        live.modify (· ++ [l])
        fill n
  -- wait for the first case in order, print it, and start the next
  let rec drain : Nat → IO Unit
    | 0 => pure ()
    | fuel + 1 => do
      match ← live.get with
      | [] => pure ()
      | l :: rest => do
        let (code, ms) ← IO.ofExcept l.code.get
        let stdout ← IO.ofExcept l.out.get
        let stderr ← IO.ofExcept l.err.get
        live.set rest
        let some c := g.cases[l.index]?
          | throw (IO.userError s!"no case {l.index} in {g.name}")
        forwardGuessLines g l.index stderr
        let r := caseResult c l.index code stdout stderr ms
        let r := if timedOut code && !r.ok then { r with output := limitMessage limit } else r
        -- cases are printed in `todo` order, so the results collected so far are the
        -- numbers just before this one; numbering here (not in the child) keeps the
        -- pool's parallel processes from interleaving numbers
        let n := start + (← results.get).length
        let failedNow ← if r.ok then failedRef.get else do
          failedRef.modify (· + 1); failedRef.get
        IO.println (renderResult r n failedNow total limit)
        (← IO.getStdout).flush
        results.modify (· ++ [r])
        onResult r
        fill 1
        drain fuel
  try
    fill jobs
    drain (todo.length + 1)
  finally
    -- an interrupted run leaves no case processes behind
    for l in ← live.get do
      try l.kill catch _ => pure ()
  pure (← results.get)

/-- Cases with known outcomes for the test driver's own tests (`Tests/Groups/GrailTestRunner.lean`,
`testrunner`): `--run` finds this group, but no selector picks it, so it is never part
of a suite run. -/
def driverFixtures : Group where
  name := "driver-fixtures"
  exercise := "the test driver"
  cases := [
    { name := "fixture: passes", run := fun _ => pure () },
    { name := "fixture: fails", run := fun _ => do
        IO.println "fixture output before the failure"
        throw (IO.userError "fixture failure") },
    { name := "fixture: skips", run := fun _ => skip "fixture reason" },
    { name := "fixture: skips (old style)", run := fun _ => IO.println "    (skipped: old fixture reason)" },
    -- the environment-skip policy: a missing dependency fails by default and is a
    -- reported skip only under the explicit `--allow-missing-deps` flag
    { name := "fixture: missing dependency", run := fun _ => skipMissing "no fixture-dep on PATH" }
  ]

end Tests
