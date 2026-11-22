import Std.Data.HashMap
import Wiz.Smt.Sha256

/-!
# Calling solvers from the (pure) elaborator (stage 28)

The elaborator is a pure function (`ElabM` is a state monad over `Except`), but the
`sat_decide` tactic asks an external solver. `runSolver` runs one as a process,
through `unsafeBaseIO` behind an `opaque`, as the module cache does (`isoGet`,
Frontend.lean). It stays a function of its arguments in the sense that matters:

* the answer is kept in a cache file named by the SHA-256 of the solver's identity (its
  path, `--version` output and binary SHA-256), its arguments and the whole input, and the
  entry stores all three, compared on every read: a second run with the same query
  replays the same answer (and needs no solver), and nothing else does;
* only answers the caller calls final are kept (a crash or a timeout is not);
* without a cache directory (`--no-cache`), the solver runs every time (in a temporary
  directory, removed afterwards).

**R5 (wiz-notes/sota-numerics.md §5.5): the cache stores certificates, never verdicts.**
An entry is written only when the caller asked for the solver's output file
(`wantOut`) and that file is non-empty — for `sat_decide` this is CaDiCaL's LRAT proof —
and the entry records its SHA-256. On a read the proof's digest is recomputed and must
match, and the proof is then parsed and checked again (the LRAT parser here, then
`Sat.lratCheck` in the kernel): a bad cached proof can only make the tactic fail. A
caller that has no certificate (the trusted `smt` tactic: Z3's output file is empty)
gets no cached answer at all, and a legacy/forged entry without a certificate is refused
rather than replayed — a cached verdict would be an axiom in the trusted base, not a
hint.

`sat_decide` checks the solver's LRAT proof in the kernel, so a wrong, stale or
nondeterministic answer can only make the tactic fail; the trusted `smt` (28a) believes
`unsat`, so it must not cache (hence `wantOut` is the gate, not just `keep`).
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

/-- The cache entry's format marker: entries written before R5 (a bare verdict, or a
proof without a digest) do not have it and are refused. -/
private def cacheMagic : String := "wiz-smt-cache-v2"

/-- Per process: the identity of each solver (`path --version` and the binary's
SHA-256), computed once. -/
initialize solverIds : IO.Ref (Std.HashMap String String) ← IO.mkRef {}

/-- The file `cmd` names: as given when it contains a `/`, else the first match on
`PATH`. (`Wiz.Attest.findOnPath` does the same; importing it here would be a cycle.) -/
private def resolveCmd (cmd : String) : IO (Option String) := do
  if cmd.contains '/' then
    let p := System.FilePath.mk cmd
    return if ← p.pathExists then some p.toString else none
  let path := (← IO.getEnv "PATH").getD ""
  for d in path.splitOn ":" do
    if d.isEmpty then continue
    let p := System.FilePath.mk d / cmd
    if ← p.pathExists then return some p.toString
  pure none

/-- A file's SHA-256, or none if it cannot be read. -/
private def fileDigest? (p : String) : IO (Option String) := do
  try
    if ← (System.FilePath.mk p).pathExists then
      return some (Sha256.hexBytes (← IO.FS.readBinFile (System.FilePath.mk p)))
    else return none
  catch _ => pure none

/-- A solver's identity: its command, its `--version` output, and its binary's SHA-256.
The version line alone is not an identity (a rebuilt or repackaged solver can keep it);
the digest is part of every cache key, so an answer is never replayed across a changed
binary. -/
private def solverId (cmd : String) : IO String := do
  if let some v := (← solverIds.get).get? cmd then return v
  let v ← try
      let out ← IO.Process.output { cmd, args := #["--version"] }
      let path? ← resolveCmd cmd
      let dig ← match path? with
        | some p => pure ((← fileDigest? p).getD "")
        | none => pure ""
      pure s!"{cmd} {out.stdout.trimAscii.toString} sha256:{dig}"
    catch _ => pure s!"{cmd} (not found)"
  solverIds.modify (·.insert cmd v)
  pure v

/-- The cache key of a query: SHA-256 over the solver's identity, its arguments and the
whole input. Pure for the tests (`runSolver` adds the identity itself). -/
def queryKey (id : String) (args : List String) (input : String) : String :=
  Sha256.hex s!"{id}{sep}{sep.intercalate args}{sep}{input}"

/-- A solver's identity, for a test that plants or inspects a cache entry. -/
def solverIdentity (cmd : String) : IO String := solverId cmd

/-- The metadata lines of a cache entry (`meta ++ sep ++ outFile`), or none if it is not
the current format, does not carry a proof, or the proof's bytes do not match the
recorded digest. -/
private def readCached (meta outFile query stdout query' : String) : Option Answer :=
  if query' != query || outFile.isEmpty then none else
  match meta.splitOn "\n" with
  | [magic, kind, exitLine, shaLine] =>
    if magic != cacheMagic || kind != "kind proof" then none else
    let code? := (exitLine.splitOn " ").getLast?.bind fun s => s.toNat?
    let recorded? := shaLine.splitOn " " |>.getLast?
    match code?, recorded? with
    | some code, some recorded =>
      -- re-check the certificate on load: a truncated or edited proof is a miss, not a hit
      if recorded != Sha256.hexBytes outFile.toUTF8 then none
      else some { exitCode := code.toUInt32, stdout, outFile }
    | _, _ => none
  | _ => none

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
  -- (R5) only a certificate is replayed: `wantOut` says the caller reads a proof file.
  -- A verdict-only caller (`smt`) always runs the solver, and an entry without a proof
  -- is refused even if one was planted for the key.
  if !temp && wantOut then
    if ← ansFile.pathExists then
      let txt ← IO.FS.readFile ansFile
      -- (the metadata and proof, then the query it answers and the solver's stdout)
      match txt.splitOn s!"{sep}query{sep}" with
      | [metaAndProof, rest] =>
        match rest.splitOn s!"{sep}stdout{sep}" with
        | [q, out] =>
          match metaAndProof.splitOn sep with
          | [meta, file] =>
            if let some a := readCached meta file query out q then return .ok (id, a)
          | _ => pure ()
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
    -- (R5) store only a proof: the answer must be `unsat` (exit 20 in the SAT
    -- protocol) with a non-empty output file. A SAT model (exit 10) is never cached
    -- even if the solver left bytes in the file: a cached counterexample would be a
    -- verdict too, and it is cheap to ask again.
    if !temp && wantOut && a.exitCode == 20 && keep a && !a.outFile.isEmpty then
      let digest := Sha256.hexBytes a.outFile.toUTF8
      IO.FS.writeFile ansFile
        s!"{cacheMagic}\nkind proof\nexit {a.exitCode}\nout-sha256 {digest}{sep}{a.outFile}{sep}query{sep}{query}{sep}stdout{sep}{a.stdout}"
    pure (.ok (id, a))
  | .error e => pure (.error e)

private unsafe def runSolverImpl (cfg : Config) (cmd : String) (args : List String) (input : String)
    (inExt : String) (wantOut : Bool) (keep : Answer → Bool) : Except String (String × Answer) :=
  match unsafeBaseIO (runIO cfg cmd args input inExt wantOut keep).toBaseIO with
  | .ok r => r
  | .error e => .error s!"running `{cmd}` failed: {e}"

/-- Run solver `cmd` with `args` (`{in}`: a file holding `input`, with extension `inExt`;
`{out}`: a file it writes, read back if `wantOut`). The solver's identity and the answer,
or why there is none. Cached (see above) when the answer is a certificate — `wantOut` and
a non-empty output file — and `keep` says it is final; a verdict without one is never
stored or replayed. -/
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
