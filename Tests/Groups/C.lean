import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-- (15k) A program large enough to split by hand: 64 definitions whose calls cross
translation-unit boundaries. -/
def splitSrc : String :=
  "import Prelude\n" ++
  String.join ((List.range 64).map fun i => s!"def sf{i} : Nat := {i} * 3\n") ++
  "\ndef main : Nat := " ++
  String.intercalate " + " ((List.range 64).map fun i => s!"sf{i}") ++ "\n"

/-- (15k) The same program compiled as four C units (the split path): the result and the
generated code must be the single-unit ones. -/
def splitCase : Case :=
  { name := "a C program in four translation units", run := fun _ => cRun splitSrc "6048" false 4 }

/-- (15k) Build `main` of `src` with `--split`, and return its generated C (the whole
program, written by both paths) and what the program printed. -/
def splitBuild (src : String) (dir : System.FilePath) (name : String) (split : Nat) :
    IO (String × String) := do
  let s := runFrontend (R := ZeroOneMany) src { trustedModule := Tests.libModule, loader := ← preludeLoader }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
  unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
  let exe := dir / name
  match ← Build.build (← toolchain) s "main" exe false false (split := split) with
  | .error e =>
    let missing := ["gmp.h", "No such file"].any fun m => (e.splitOn m).length > 1
    if missing then
      skip "no toolchain"
      pure ("", "")
    else throw (IO.userError e)
  | .ok _ =>
    let out ← IO.Process.output { cmd := exe.toString }
    unless out.exitCode == 0 do throw (IO.userError s!"the program failed ({out.exitCode}): {out.stderr.take 500}")
    pure (← IO.FS.readFile (exe.withExtension "c"), out.stdout)

/-- (15k) Single, `--split 1`, 2, 4 and automatic write the same C and print the same. -/
def splitSameCase : Case :=
  { name := "split 1, 2, 4 and automatic: the same generated C and program output", run := fun _ => do
      let dir ← IO.FS.createTempDir
      let (c1, out1) ← splitBuild splitSrc dir "single" 1
      for (name, k) in [("two", 2), ("four", 4), ("auto", 0)] do
        let (c, out) ← splitBuild splitSrc dir name k
        check (c == c1) s!"{name}: the generated C differs"
        check (out == out1) s!"{name}: the output differs" }

/-- (15k) A second split build to the same output reuses every part object (the stamps of
their C text and flags); only the link runs again. -/
def splitReuseCase : Case :=
  { name := "a split build reuses its part objects (stamped by C text and flags)", run := fun _ => do
      let dir ← IO.FS.createTempDir
      let (out1, _) ← splitBuild splitSrc dir "reuse" 4
      let splitDir := dir / "reuse.split"
      let objects : IO (Array System.FilePath) := do
        let es ← splitDir.readDir
        let names := (es.filter fun e => e.fileName.endsWith ".o").map (·.path)
        pure (names.qsort (fun a b => a.toString < b.toString))
      let before ← objects
      check (before.size >= 3) s!"{before.size} objects (support and parts): {before}"
      let stamps ← before.mapM fun f => do let md ← f.metadata; pure s!"{md.modified.sec}.{md.modified.nsec}"
      let (out2, _) ← splitBuild splitSrc dir "reuse" 4
      checkEq out1 out2
      let after ← objects
      checkEq before.size after.size
      let stamps2 ← after.mapM fun f => do let md ← f.metadata; pure s!"{md.modified.sec}.{md.modified.nsec}"
      check (stamps == stamps2) "a part was compiled again" }

/-- (15k) The automatic part count is deterministic and measured from the generated C. -/
def splitAutoCase : Case :=
  { name := "--split 0 is automatic: declaration count and bytes, capped at 8", run := fun _ => do
      checkEq 1 (Build.autoPartsFor 127 10000000) -- too few declarations
      checkEq 1 (Build.autoPartsFor 128 999999)  -- under 1 MB
      checkEq 2 (Build.autoPartsFor 1000 1000000)
      checkEq 4 (Build.autoPartsFor 1000 4000000)
      checkEq 8 (Build.autoPartsFor 1000 16000000) }

def cGroup : Group where
  name := "c"
  exercise := "Exercise 8.2"
  cases := nativeCases false ++ [splitCase, splitSameCase, splitReuseCase, splitAutoCase]

builtin_initialize registerGroup cGroup

end Tests.Elab
