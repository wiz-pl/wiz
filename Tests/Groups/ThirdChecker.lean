import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-- TT-11: the independent third checker over the self-hosted kernel's proof terms
(`tools/third-checker/`).  The kernel verdicts are in the committed `corpus.dump`, so
these cases need only Python; regenerating the dump needs `wiz run` and is manual. -/
def thirdCheckerRun (args : Array String) : IO String := do
  let out ← IO.Process.output { cmd := "python3", args := args }
  unless out.exitCode == 0 do
    throw (IO.userError s!"python3 {args} failed ({out.exitCode}):\n{out.stdout}\n{out.stderr}")
  pure (out.stdout ++ out.stderr)

def thirdCheckerGroup : Group where
  name := "third-checker"
  exercise := "TT-11 (independent third checker)"
  cases := [
    { name := "the independent checker agrees with the committed selfhost dump", run := fun _ => do
        let out ← thirdCheckerRun #["tools/third-checker/harness.py"]
        check ((out.splitOn "0 mismatches").length > 1) out },
    { name := "corpus verdicts, split/level/quantity rules and mismatch detection", run := fun _ => do
        let out ← thirdCheckerRun #["tools/third-checker/test_checker.py", "-v"]
        check ((out.splitOn "Ran 30 tests").length > 1) out }
  ]

builtin_initialize registerGroup thirdCheckerGroup

end Tests.Elab
