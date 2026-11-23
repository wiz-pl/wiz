import Std.Data.HashMap
import Wiz.Smt.Sha256

/-!
# Calling solvers from the (pure) elaborator (stage 28)

The elaborator is a pure function (`ElabM` is a state monad over `Except`), but the
`sat_decide` tactic asks an external solver. `runSolver` runs one as a process,
through `unsafeBaseIO` behind an `opaque`, as the module cache does (`isoGet`,
Frontend.lean). It stays a function of its arguments in the sense that matters:

* the answer is kept in a cache file named by the SHA-256 of the solver's identity (its
  path and `--version` output), its arguments and the whole input, and the entry stores
  all three, compared on every read: a second run with the same query replays the same
  answer (and needs no solver), and nothing else does;
* only answers the caller calls final are kept (a crash or a timeout is not);
* without a cache directory (`--no-cache`), the solver runs every time (in a temporary
  directory, removed afterwards).

The deadline is the host's. `-T:`/`-t` only ask the solver to stop; `runIO` also kills
the child (its whole process group: SIGTERM, then SIGKILL) when `--solver-timeout`
elapses, so a solver that ignores its own limit cannot hang the elaborator. A cache
entry is parsed defensively: a truncated or corrupt `.ans` is a miss (the query is
answered again), never a panic.

`sat_decide` checks the solver's LRAT proof in the kernel, so a wrong, stale or
nondeterministic answer can only make the tactic fail; the trusted `smt` (28a) believes
`unsat`, so for it the cache is part of the trusted base (hence the digest and the check).
-/

namespace Wiz.Smt

/-- How the elaborator reaches solvers (from the toolchain: `--sat-solver`,
`--solver-timeout`, and the cache directory). -/
structure Config where
  /-- (28a) `--trust-smt`: the `smt` tactic may close goals on a solver's word -/
  trust : Bool := false
  /-- (28a) the SMT solver (Z3's command line), and its identity (`--version`), which the
  command and module cache keys include: an acceptance is not replayed for another version -/
  solver : String := "z3"
  solverId : String := ""
  /-- (28e) `--trust-native` and `--native-fuel`, as the command has them: `sat_decide_native`
  runs the LRAT check compiled (native_refl's evaluator) -/
  trustNative : Bool := false
  nativeFuel : Nat := 20000000000
  /-- the SAT solver (CaDiCaL's command line: `cadical IN OUT --lrat --no-binary`) -/
  satSolver : String := "cadical"
  /-- milliseconds per query -/
  timeoutMs : Nat := 10000
  /-- where answers are kept (`<cache>/smt`); none: not kept -/
  cacheDir : Option String := none
  deriving Repr, Inhabited, BEq, Hashable

/-- What a process run gave: its exit code, its standard output, and the contents of the
file it was asked to write (if any). -/
structure Answer where
  exitCode : UInt32
  stdout : String
  outFile : String
  deriving Repr, Inhabited

private def sep : String := "\n\x00wiz-smt\x00\n"

/-- Per process: the identity of each solver (`path --version`), computed once. -/
initialize solverIds : IO.Ref (Std.HashMap String String) ← IO.mkRef {}

/-- What one process run gave, and whether the host's deadline killed it. -/
private structure ProcOutput where
  exitCode : UInt32
  stdout : String
  stderr : String
  timedOut : Bool
  deriving Inhabited

/-- Read a pipe after the child is gone, but not forever: a process the kill did not
reach (an unkillable `D` state, a grandchild holding the pipe) must not hang the host. -/
private def drain (t : Task (Except IO.Error String)) : IO String := do
  let mut i := 0
  let mut done := false
  done ← IO.hasFinished t
  while !done && i < 100 do
    IO.sleep 2
    i := i + 1
    done ← IO.hasFinished t
  if done then
    match t.get with
    | .ok s => pure s
    | .error _ => pure ""
  else pure ""

/-- Run `cmd` with `args` (stdin empty, `stdout`/`stderr` captured) and enforce
`timeoutMs` here. The child is started in its own process group (`setsid`), so the
timeout kills the solver *and* anything it forked: SIGTERM first, then SIGKILL if it is
still alive after a short grace, and the child is reaped (`tryWait`) either way. A run
that the deadline killed is reported with `timedOut := true`. -/
private def runProcessTimed (timeoutMs : Nat) (cmd : String) (args : Array String) :
    IO ProcOutput := do
  let child ← IO.Process.spawn
    { cmd, args, stdin := .null, stdout := .piped, stderr := .piped, setsid := true }
  let stdoutTask ← IO.asTask child.stdout.readToEnd .dedicated
  let stderrTask ← IO.asTask child.stderr.readToEnd .dedicated
  let start ← IO.monoMsNow
  let mut code? ← child.tryWait
  let mut now ← IO.monoMsNow
  -- (`-T:`/`-t` ask; this is the deadline that holds)
  while code?.isNone && now - start < timeoutMs do
    IO.sleep 5
    code? ← child.tryWait
    now ← IO.monoMsNow
  let timedOut := code?.isNone
  if timedOut then
    try child.kill catch _ => pure ()
    -- a polite SIGTERM to the group; most solvers stop here
    for _ in [0:10] do
      if code?.isNone then
        IO.sleep 10
        code? ← child.tryWait
    -- a solver that ignores SIGTERM still gets no more than the grace: SIGKILL the
    -- group through a shell (Lean's `kill` is SIGTERM only). `kill` returns at once, so
    -- this little run needs no deadline of its own.
    if code?.isNone then
      try
        -- (a negative pid is the process group: dash takes it as an operand directly,
        -- bash accepts `--`; try the portable spelling first)
        let pid := child.pid
        let kill := s!"kill -9 -{pid} 2>/dev/null || kill -9 -- -{pid} 2>/dev/null"
        let _ ← IO.Process.output { cmd := "/bin/sh", args := #["-c", kill] }
        pure ()
      catch _ => pure ()
      for _ in [0:20] do
        if code?.isNone then
          IO.sleep 5
          code? ← child.tryWait
  let stdout ← drain stdoutTask
  let stderr ← drain stderrTask
  pure { exitCode := code?.getD 137, stdout, stderr, timedOut }

private def solverId (timeoutMs : Nat) (cmd : String) : IO String := do
  if let some v := (← solverIds.get).get? cmd then return v
  let v ← try
      let out ← runProcessTimed timeoutMs cmd #["--version"]
      if out.timedOut then pure s!"{cmd} (version timed out after {timeoutMs} ms)"
      else pure s!"{cmd} {out.stdout.trimAscii.toString}"
    catch _ => pure s!"{cmd} (not found)"
  solverIds.modify (·.insert cmd v)
  pure v

/-- An `.ans` entry's answer, or `none` when it is truncated or corrupt: a cache miss
(the query is answered again), never a `toNat!` panic on a split field of a file that
was not checked. -/
private def parseAnswer (ans : String) : Option Answer :=
  match ans.splitOn sep with
  | [code, out, file] =>
    match code.toNat? with
    | some n => if n < 4294967296 then some { exitCode := n.toUInt32, stdout := out, outFile := file } else none
    | none => none
  | _ => none

private def runIO (cfg : Config) (cmd : String) (args : List String) (input : String) (inExt : String)
    (wantOut : Bool) (keep : Answer → Bool) : IO (Except String (String × Answer)) := do
  let id ← solverId cfg.timeoutMs cmd
  if id.endsWith "(not found)" then
    return .error s!"the solver `{cmd}` is not installed (not on PATH)"
  let query := s!"{id}{sep}{sep.intercalate args}{sep}{input}"
  let key := Sha256.hex query
  let (dir, temp) ← match cfg.cacheDir with
    | some d => pure (System.FilePath.mk d / "smt", false)
    | none => do pure ((← IO.FS.createTempDir), true)
  IO.FS.createDirAll dir
  let base := dir / key
  let ansFile := base.addExtension "ans"
  if !temp && (← ansFile.pathExists) then
    -- (an unreadable or corrupt entry is a miss: the file is not a checked artifact)
    let txt? ← try some <$> IO.FS.readFile ansFile catch _ => pure none
    match txt? with
    | some txt =>
      -- (the answer, then the query it answers: replayed only for exactly this query)
      match txt.splitOn s!"{sep}query{sep}" with
      | [ans, q] => if q == query then
          match parseAnswer ans with
          | some a => return .ok (id, a)
          | none => pure ()
      | _ => pure ()
    | none => pure ()
  let inFile := base.addExtension inExt
  let outPath := base.addExtension "out"
  IO.FS.writeFile inFile input
  let args := args.map fun a => if a == "{in}" then inFile.toString else if a == "{out}" then outPath.toString else a
  let r ← try
      let out ← runProcessTimed cfg.timeoutMs cmd args.toArray
      if out.timedOut then
        pure (Except.error s!"the solver `{cmd}` timed out after {cfg.timeoutMs} ms" :
          Except String (String × Answer))
      else
        let file ← if wantOut && (← outPath.pathExists) then IO.FS.readFile outPath else pure ""
        pure (Except.ok (id, { exitCode := out.exitCode, stdout := out.stdout, outFile := file }))
    catch e => pure (Except.error s!"running `{cmd}` failed: {e}")
  try IO.FS.removeFile inFile catch _ => pure ()
  try IO.FS.removeFile outPath catch _ => pure ()
  if temp then try IO.FS.removeDirAll dir catch _ => pure ()
  match r with
  | .ok (id, a) =>
    if !temp && keep a then
      IO.FS.writeFile ansFile s!"{a.exitCode}{sep}{a.stdout}{sep}{a.outFile}{sep}query{sep}{query}"
    pure (.ok (id, a))
  | .error e => pure (.error e)

private unsafe def runSolverImpl (cfg : Config) (cmd : String) (args : List String) (input : String)
    (inExt : String) (wantOut : Bool) (keep : Answer → Bool) : Except String (String × Answer) :=
  match unsafeBaseIO (runIO cfg cmd args input inExt wantOut keep).toBaseIO with
  | .ok r => r
  | .error e => .error s!"running `{cmd}` failed: {e}"

/-- Run solver `cmd` with `args` (`{in}`: a file holding `input`, with extension `inExt`;
`{out}`: a file it writes, read back if `wantOut`). The solver's identity and the answer,
or why there is none. Cached (see above) when `keep` says the answer is final. -/
@[implemented_by runSolverImpl]
opaque runSolver (cfg : Config) (cmd : String) (args : List String) (input : String)
    (inExt : String) (wantOut : Bool) (keep : Answer → Bool) : Except String (String × Answer)
/-- A solver's identity in a few words, for an axiom's name: the command's base name and
the first version-looking word of its `--version` (`z3 4.13.0`). -/
def shortId (id : String) : String :=
  let ws := (id.splitOn " ").filter (· ≠ "")
  let cmd := ((ws.headD "solver").splitOn "/").getLast!
  match ws.drop 1 |>.find? (fun w => w.any Char.isDigit && w.contains '.') with
  | some v => s!"{cmd} {v}"
  | none => cmd

/-- The configuration with the SMT solver's identity filled in (when `--trust-smt`). -/
def Config.resolve (c : Config) : IO Config := do
  if c.trust then
    let id ← Wiz.Smt.solverId c.timeoutMs c.solver
    pure { c with solverId := id }
  else pure c

end Wiz.Smt
