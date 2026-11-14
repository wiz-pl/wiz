import Tests.Rig
import Tests.Eval
import Tests.Check
import Tests.Parser
import Tests.Elab
import Tests.Groups
import Tests.ElabFix
import Tests.Grail
import Tests.LSP
import Tests.Meta
import Tests.Lint
import Tests.Allocs
import Tests.Scaling
import Tests.FalseFuzz
import Tests.Feral
import Tests.Tower
import Tests.Native
import Tests.Smt
import Tests.Doc

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

open Tests

/-- The groups of the older modules that list their own (`groups` at their end). New
groups are modules of their own under `Tests/Groups/` (`registerGroup`). -/
def moduleGroups : List Group :=
  Check.groups ++
  Doc.groups ++
  ElabFix.groups ++
  Feral.groups ++
  Eval.groups ++
  Grail.groups ++
  Lint.groups ++
  LSP.groups ++
  Meta.groups ++
  Native.groups ++
  Smt.groups ++
  Parser.groups ++
  Rig.groups ++
  Scaling.groups ++
  Tower.groups ++
  []

/-- Every test group: the modules' and the registered ones (`Tests/Groups/`). -/
def allGroups : IO (List Group) := do
  return moduleGroups ++ (← groupRegistry.get).toList

/-- Whether a command-line selector picks a group: `=NAME` exactly, anything else as a
prefix of the group's name. `=NAME#I,J,…` picks only the cases with those indices
(counting from 0) of the group `NAME`; CI splits a long group this way
(`scripts/ci.py`). -/
def selects (g : Group) (arg : String) : Bool :=
  if arg.startsWith "=" then "=" ++ g.name == (arg.splitOn "#")[0]! else g.name.startsWith arg

/-- The cases of `g` that the selectors pick: `none` for all of them. -/
def selectedCases (g : Group) (args : List String) : Option (List Nat) := Id.run do
  let mut ixs : List Nat := []
  if !args.any (selects g) then return none
  for arg in args.filter (selects g) do
    match arg.splitOn "#" with
    | [_, list] => ixs := ixs ++ (list.splitOn ",").filterMap String.toNat?
    | _ => return none
  return some ixs

/-- The group named `name`, among the suite's and the driver's fixtures (`--run` finds
these; no selector picks them). -/
def findGroup (name : String) : IO (Option Group) := do
  return ((← allGroups) ++ [driverFixtures]).find? (·.name == name)

/-- The arguments of a suite run, checked: an argument that is neither a toolchain flag
nor `--timings`/`--shard` (an unknown or misspelt flag), a selector that picks no group
and a case index that the group does not have are errors (exit code 2), not an empty run
that passes. -/
def checkSelectors (args : List String) : IO (Option UInt32) := do
  let groups ← allGroups
  for arg in args do
    if arg.startsWith "--" then
      IO.eprintln s!"unknown flag (or a flag without its value): {arg}"
      return some 2
    let picked := groups.filter (selects · arg)
    if picked.isEmpty then
      IO.eprintln s!"no test group matches {arg} (`tests --list` lists them; `=NAME` is exact, anything else a prefix)"
      return some 2
    if let [_, list] := arg.splitOn "#" then
      for g in picked do
        for ix in list.splitOn "," do
          unless ix.toNat?.any (· < g.cases.length) do
            IO.eprintln s!"no case {ix} in {g.name}: it has {g.cases.length} (0 to {g.cases.length - 1}; `tests --list-cases '={g.name}'`)"
            return some 2
  return none

/-- `tests --run GROUP INDEX` (also `GROUP#INDEX`, and `=GROUP`): the case with that
index (from 0) of the group named `GROUP`, run as `lake test -- '=GROUP#INDEX'` runs it,
in a child process with the suite's toolchain (`grail.local.wiz`, then any toolchain
flags). Prints the case's name and result (and a failure's output) and exits 0 if it
passed, 1 if it failed, 2 on a usage error and 3 if it was skipped: a skipped case is not
a pass. -/
def runOne (args : List String) : IO UInt32 := do
  let usage := "usage: tests --run GROUP INDEX [toolchain flags] (INDEX from 0: `tests --list-cases '=GROUP'`)"
  let args := match args with
    | [one] => one.splitOn "#"
    | args => args
  let [group, ix] := args
    | IO.eprintln s!"unexpected arguments: {" ".intercalate args}\n{usage}"; return 2
  let group := if group.startsWith "=" then (group.drop 1).toString else group
  let some g ← findGroup group
    | IO.eprintln s!"no test group named {group} (`tests --list`)\n{usage}"; return 2
  let some i := ix.toNat?
    | IO.eprintln s!"not a case index: {ix}\n{usage}"; return 2
  unless i < g.cases.length do
    IO.eprintln s!"no case {i} in {group}: it has {g.cases.length} (0 to {g.cases.length - 1}; `tests --list-cases '={group}'`)"
    return 2
  let [r] ← g.run (some [i])
    | IO.eprintln s!"{group} #{i} did not run"; return 1
  if !r.ok then
    IO.println s!"\n{group} #{i}: FAILED"; return 1
  if let some why := r.skipped then
    IO.println s!"\n{group} #{i}: SKIPPED ({why}); a skipped case is not a pass"; return 3
  IO.println s!"\n{group} #{i}: passed"
  return 0

/-- A JSON string literal. -/
def jsonStr (s : String) : String := Id.run do
  let mut out := "\""
  for c in s.toList do
    out := match c with
      | '"' => out ++ "\\\""
      | '\\' => out ++ "\\\\"
      | '\n' => out ++ "\\n"
      | c => if c.toNat < 0x20 then
          let h := String.ofList (Nat.toDigits 16 c.toNat)
          out ++ "\\u00" ++ (if h.length < 2 then "0" ++ h else h)
        else out.push c
  return out.push '"'

/-- The `--timings` record of a case: one line of JSON. -/
def timingLine (shard group : String) (r : CaseResult) : String :=
  let notes := ", ".intercalate (r.notes.map jsonStr)
  s!"\{\"shard\": {jsonStr shard}, \"group\": {jsonStr group}, \"index\": {r.index}, \"case\": {jsonStr r.name}, " ++
  s!"\"seconds\": {showMs r.ms}, \"ok\": {r.ok}, \"notes\": [{notes}]}"

/-- Remove `--FLAG VALUE` from the arguments; the value, if it was there. -/
def takeFlag (flag : String) : List String → Option String × List String
  | f :: v :: rest => if f == flag then (some v, rest) else
    let (x, r) := takeFlag flag (v :: rest); (x, f :: r)
  | args => (none, args)

/-- Remove `--FLAG` from the arguments; whether it was there. -/
def takeSwitch (flag : String) : List String → Bool × List String
  | f :: rest => if f == flag then (true, rest) else
    let (b, r) := takeSwitch flag rest; (b, f :: r)
  | args => (false, args)

/-- This machine's toolchain settings, from the uncommitted `grail.local.wiz` that the nix
dev shell writes (`flake.nix`), as grail reads them. -/
def localToolchain : IO Wiz.Toolchain := do
  let file : System.FilePath := "grail.local.wiz"
  unless ← file.pathExists do
    IO.eprintln "note: no grail.local.wiz (`nix develop` writes it): tests that compile C use `cc` without GMP's paths"
    return {}
  let settings ← match ← Grail.evalBuildFile {} 0 ["lib", "."] file "Settings.render settings" with
    | .error e => throw (IO.userError e)
    | .ok x => match Grail.decodeSettings x with
      | .error e => throw (IO.userError s!"{file}: {e}")
      | .ok ss => pure ss
  settings.foldlM (init := {}) fun tc (k, v) => match tc.set k v with
    | some tc => pure tc
    | none => throw (IO.userError s!"{file}: unknown setting {k}")

/-- The suite's toolchain: `grail.local.wiz`, then the toolchain flags given to
`lake test -- …`, which win. The top-level run reads the file and passes the result to
each case's process as flags (`readLocal := false` there). -/
def suiteToolchain (args : List String) (readLocal : Bool) : IO (Wiz.Toolchain × List String) := do
  let base ← if readLocal then localToolchain else pure {}
  pure (base.parseFlags args)

/-- `lake test` runs everything; `lake test -- conv rig` runs only groups whose name
starts with one of the arguments, `lake test -- =c` only the group named `c`, and
`lake test -- =selfhost#0,3` only cases 0 and 3 of the group `selfhost`.
`lake test -- --list` prints the group names, one per line (CI checks its shards
against them), and `lake test -- --list-cases SELECTOR…` the selected cases, as
`GROUP<tab>INDEX<tab>NAME` lines; `lake test -- --run GROUP INDEX` runs one case and
exits with its result (`runOne`). A selector that picks nothing, a case index the group
lacks and an unknown flag are errors. A skipped case (`Tests.skip`) shows as `⊘` and is
counted apart. `--timings FILE` appends one line of JSON per case to
FILE (its group, index, name, wall time in seconds, whether it passed, and its notes:
`Tests.note`), labelled with `--shard NAME`.

`--jobs N` (default 1) runs the cases of a group that opted in (`Group.parallel`, see
"Running cases in parallel" in docs/building.md) N at a time in child processes, printing
each case's output and `--timings` line in the group's case order; groups that did not opt
in still run one case at a time. `--jobs-all` also parallelizes groups that did not opt in
(for auditing a group's isolation, not for CI). -/
def main (args : List String) : IO UInt32 := do
  -- a `panic!` fails the case that hits it (each case runs in its own process), as it
  -- fails `wiz check`; `--panic-probe continue` turns it off again
  Wiz.exitOnPanic
  -- (23k) a grail job's supervisor, and grail itself (the job-hygiene tests run it)
  if let "--grail-exec" :: rest := args then return ← Grail.execMain rest
  if let "--grail" :: rest := args then return ← Grail.cliMain rest
  -- the processes the suite starts get the toolchain as flags
  let child := match args with
    | "--run-case" :: _ | "--prop-long" :: _ | "--prop-replay" :: _ | ["--prop-no-sizes"] | ["--prop-trace"] | "--check" :: _ | "--check-libs" :: _ | "--probe-reuse" :: _ | "--probe-reuse-ir" :: _ | "--panic-probe" :: _ | "--grail-job" :: _ | "--trust-ledger" :: _ | ["--list"] | ["--list-shards"] | "--list-cases" :: _ | "--allocs" :: _ => true
    | _ => false
  let (tc, args') ← suiteToolchain args (readLocal := !child)
  toolchainRef.set tc
  flagsRef.set tc.toFlags
  match args' with
  -- one case in this process: what `Group.run` starts for each case
  | ["--run-case", group, ix] =>
    match (← findGroup group) >>= fun g => ix.toNat? >>= (g.cases[·]?) with
    | some c => c.runHere
    | none => do IO.eprintln s!"no such case: {group} #{ix}"; pure 2
  | "--run" :: rest => runOne rest
  -- (D1) check a file with the given regularity mode, in a child process that the test
  -- can time out: `Elab.checkDiverges`
  | ["--check", mode, file] => do
    let input ← IO.FS.readFile file
    -- `MODE+eager`: without `lazyProofs` (P2: the evaluator runs proofs, as before)
    let (mode, lazyProofs) := match mode.splitOn "+" with
      | [m, "eager"] => (m, false)
      | _ => (mode, true)
    let s := Wiz.runFrontend (R := Wiz.ZeroOneMany) input { globals := { regularity := Elab.regularityMode mode, lazyProofs } }
    let errs := s.messages.filter (·.severity == .error)
    for m in errs do IO.eprintln (m.render input)
    pure (if errs.isEmpty then 0 else 1)
  -- check a file with every library importable, in a child process that the test can
  -- time out: `Elab.failsLibsWithin`
  | ["--check-libs", file] => do
    let input ← IO.FS.readFile file
    let s := Wiz.runFrontend (R := Wiz.ZeroOneMany) input { trustedModule := libModule, loader := ← Elab.libLoader }
    let errs := s.messages.filter (·.severity == .error)
    for m in errs do IO.eprintln (m.render input)
    pure (if errs.isEmpty then 0 else 1)
  -- a job of a grail build that a test runs (`Grail/Graph.lean`)
  | ["--grail-job", job] => Grail.jobMain tc job
  -- (kernel hygiene, `Tests/Lint.lean`) hit a `panic!` of the evaluator, with or without
  -- `exitOnPanic`
  | ["--panic-probe", mode, site] => Lint.panicProbe mode site
  | "--probe-checker" :: opts => do Scaling.probeChecker opts; pure 0
  -- the soundness audit's tests on their large grids (`Tests/Groups/Audit.lean`)
  | ["--audit-long"] => Audit.longMain
  | ["--audit-hurkens"] => Audit.hurkensMain
  | "--audit-query" :: ixs => Audit.queryMain ixs
  -- the property harness's long run (`Tests/Groups/Prop.lean`)
  | "--prop-long" :: rest => Prop.longMain rest
  | "--prop-replay" :: rest => Prop.replayMain rest
  | "--false-fuzz" :: rest => FalseFuzz.main rest
  | "--false-fuzz-replay" :: rest => FalseFuzz.replayMain rest
  | "--false-fuzz-check" :: rest => FalseFuzz.checkMain rest
  | ["--prop-no-sizes"] => Prop.flagMain true false
  | ["--prop-trace"] => Prop.flagMain false true
  | ["--probe-reuse"] => Scaling.probeReuse
  | "--probe-reuse-ir" :: files => Scaling.probeReuseIR files
  -- allocation counts and IR of definitions of a file (`Tests/Allocs.lean`)
  | "--allocs" :: rest => Allocs.allocsMain rest
  -- the trust ledger (`Tests/Native.lean`, scripts/trust-ledger.sh)
  | "--trust-ledger" :: rest => Native.trustLedgerMain rest
  | ["--list"] => do
    for g in ← allGroups do IO.println g.name
    pure 0
  -- each group's shard hint (`Group.shard`; empty for the default), for `scripts/ci.py`
  | ["--list-shards"] => do
    for g in ← allGroups do IO.println s!"{g.name}\t{g.shard}"
    pure 0
  | "--list-cases" :: sels => do
    for g in ← allGroups do
      let only := selectedCases g sels
      if sels.isEmpty || sels.any (selects g) then
        for c in g.cases, i in [0:g.cases.length] do
          if only.all (·.contains i) then IO.println s!"{g.name}\t{i}\t{c.name}"
    pure 0
  | args => do
    let (timings, args) := takeFlag "--timings" args
    let (shard, args) := takeFlag "--shard" args
    let (jobsArg, args) := takeFlag "--jobs" args
    let (jobsAll, args) := takeSwitch "--jobs-all" args
    let jobs : Option Nat := match jobsArg with
      | none => some 1
      | some s => match s.toNat? with
        | some 0 => none
        | n => n
    let some jobs := jobs
      | IO.eprintln "--jobs needs a count of at least 1"; return 2
    let shard := shard.getD ""
    if let some code ← checkSelectors args then return code
    let groups ← allGroups
    let selected := if args.isEmpty then groups
      else groups.filter fun g => args.any (selects g)
    let record (g : Group) (r : CaseResult) : IO Unit := do
      if let some file := timings then
        let h ← IO.FS.Handle.mk file .append
        h.putStrLn (timingLine shard g.name r)
    let mut passed := 0
    let mut failed := 0
    let mut skipped := 0
    for g in selected do
      let start ← IO.monoMsNow
      let results ← if jobs > 1 && (g.parallel || jobsAll) then
          g.runJobs jobs (selectedCases g args) (record g)
        else g.run (selectedCases g args) (record g)
      let cases := results.foldl (· + ·.ms) 0
      IO.println s!"  ({g.name}: {showMs ((← IO.monoMsNow) - start)} s; cases {showMs cases} s)"
      let p := (results.filter (·.ok)).length
      let k := (results.filter (·.skipped.isSome)).length
      passed := passed + (p - k)
      skipped := skipped + k
      failed := failed + (results.length - p)
    IO.println s!"\n{passed} passed, {failed} failed{if skipped == 0 then "" else s!", {skipped} skipped"}"
    pure (if failed == 0 then 0 else 1)
