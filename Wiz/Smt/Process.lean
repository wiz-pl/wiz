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

private def solverId (cmd : String) : IO String := do
  if let some v := (← solverIds.get).get? cmd then return v
  let v ← try
      let out ← IO.Process.output { cmd, args := #["--version"] }
      pure s!"{cmd} {out.stdout.trimAscii.toString}"
    catch _ => pure s!"{cmd} (not found)"
  solverIds.modify (·.insert cmd v)
  pure v

private def runIO (cfg : Config) (cmd : String) (args : List String) (input : String) (inExt : String)
    (wantOut : Bool) (keep : Answer → Bool) : IO (Except String (String × Answer)) := do
  let id ← solverId cmd
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
    let txt ← IO.FS.readFile ansFile
    -- (the answer, then the query it answers: replayed only for exactly this query)
    match txt.splitOn s!"{sep}query{sep}" with
    | [ans, q] => if q == query then
        match ans.splitOn sep with
        | [code, out, file] => return .ok (id, { exitCode := code.toNat!.toUInt32, stdout := out, outFile := file })
        | _ => pure ()
    | _ => pure ()
  let inFile := base.addExtension inExt
  let outPath := base.addExtension "out"
  IO.FS.writeFile inFile input
  let args := args.map fun a => if a == "{in}" then inFile.toString else if a == "{out}" then outPath.toString else a
  let r ← try
      let out ← IO.Process.output { cmd, args := args.toArray }
      let file ← if wantOut && (← outPath.pathExists) then IO.FS.readFile outPath else pure ""
      pure (Except.ok { exitCode := out.exitCode, stdout := out.stdout, outFile := file : Answer } : Except String Answer)
    catch e => pure (Except.error s!"running `{cmd}` failed: {e}")
  try IO.FS.removeFile inFile catch _ => pure ()
  try IO.FS.removeFile outPath catch _ => pure ()
  if temp then try IO.FS.removeDirAll dir catch _ => pure ()
  match r with
  | .ok a =>
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
    let id ← Wiz.Smt.solverId c.solver
    pure { c with solverId := id }
  else pure c

end Wiz.Smt
