import Tests.Elab

open Wiz

/-!
# `diff-fuzz`: the erasure/optimisation differential

The campaign itself is `scripts/diff-fuzz.py` (its docstring has the grammar and the
three pipelines).  It runs outside the driver so that a generated program that hangs or
crashes takes a subprocess down, not the suite; the group only starts it with this
worktree's `wiz` and the driver's toolchain flags.

The fast case is the cheap CI tier: 200 programs through `#eval`, `#run` and the C
backend, in three batched processes (a disagreement is bisected and shrunk).  The
self-test proves the detector reacts to a panic and to a non-terminating program, so a
green campaign does not silently mean "the harness stopped looking".
-/

namespace Tests.DiffFuzz

/-- The checkout root (the driver is `.lake/build/bin/tests`). -/
def repoRoot : IO System.FilePath := do
  let cwd ← IO.currentDir
  if ← (cwd / "scripts" / "diff-fuzz.py").pathExists then return cwd
  let exe ← IO.appPath
  return (((exe.parent.bind (·.parent)).bind (·.parent)).bind (·.parent)).getD cwd

/-- Run the campaign; `none` when python3, `timeout` or `wiz` is missing (a skip). -/
def runCampaign (extra : List String) : IO (Option (UInt32 × String)) := do
  let root ← repoRoot
  let wiz := root / ".lake" / "build" / "bin" / "wiz"
  unless ← wiz.pathExists do
    skip "no .lake/build/bin/wiz"
    return none
  let tc ← toolchain
  -- (`--wiz-arg=VALUE`: a separate argument would be read as an option)
  let flags := tc.toFlags.map fun f => s!"--wiz-arg={f}"
  let args : Array String := #["300", "python3", (root / "scripts" / "diff-fuzz.py").toString,
    "--wiz", wiz.toString] ++ (extra ++ flags).toArray
  let out ← try
    IO.Process.output { cmd := "timeout", args, cwd := some root }
  catch e =>
    skip s!"cannot run python3: {e}"
    return none
  if out.exitCode == 2 && (out.stderr.splitOn "diff-fuzz: wiz not found").length > 1 then
    skip "diff-fuzz: no wiz binary"
    return none
  if out.exitCode == 3 then
    -- (a skipped pipeline is not a pass: the group shows as skipped, not green)
    IO.print (out.stdout ++ out.stderr)
    skip "diff-fuzz skipped a pipeline (no C toolchain)"
    return none
  return some (out.exitCode, out.stdout ++ out.stderr)

def diffFuzzGroup : Group where
  name := "diff-fuzz"
  exercise := "Stage 5 (erasure) and 15c (constant folding)"
  cases := [
    { name := "200 random programs: #eval, #run and the C backend agree", run := fun _ => do
        match ← runCampaign ["--fast"] with
        | none => pure ()
        | some (code, out) =>
          IO.print out
          unless code == 0 do
            throw (IO.userError s!"the differential found a disagreement (exit {code})") },
    { name := "the detector reports a panic and a non-terminating program", run := fun _ => do
        match ← runCampaign ["--self-test"] with
        | none => pure ()
        | some (code, out) =>
          IO.print out
          unless code == 0 do
            throw (IO.userError "the differential's own detector is broken") }
  ]

builtin_initialize registerGroup diffFuzzGroup

end Tests.DiffFuzz
