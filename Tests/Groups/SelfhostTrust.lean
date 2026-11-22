import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-!
# `=selfhost-trust`: the release gate's own tests

The compiler-trust recommendations (`wiz-notes/sota-compiler-trust.md`) added four
checks that live outside the Lean suite:

* R1/R2: `scripts/check-wizc-release.sh` runs the **packed** `wizc` from a release
  tarball on a frozen fixture (compile, run, compare), requires a one-byte variant to
  disagree, and checks `scripts/wizc-seed.json` against the seed derivation. The two
  cases here run its self-tests, so the gate cannot silently stop comparing.
* R7: `scripts/diff-fuzz.py --cross` feeds the generator through the Lean frontend and
  the self-hosted one and compares the programs' stdout. The `--cross-self-test` case
  proves the comparison reacts to a one-value difference; the campaign case runs a
  bounded, seeded set (the driver builds the self-hosted compiler once).

A toolchain problem is a skip, not a pass, as in the `selfhost` group.
-/

/-- The checkout root (the driver is `.lake/build/bin/tests`). -/
def trustRoot : IO System.FilePath := do
  let cwd ← IO.currentDir
  if ← (cwd / "scripts" / "check-wizc-release.sh").pathExists then return cwd
  let exe ← IO.appPath
  return (((exe.parent.bind (·.parent)).bind (·.parent)).bind (·.parent)).getD cwd

/-- Run `timeout SECS CMD...` from the checkout; the exit code and the combined output. -/
def trustRun (secs : Nat) (cmd : String) (args : Array String) : IO (UInt32 × String) := do
  let root ← trustRoot
  let out ← IO.Process.output
    { cmd := "timeout", args := #[toString secs, cmd] ++ args, cwd := some root }
  pure (out.exitCode, out.stdout ++ out.stderr)

def selfhostTrustGroup : Group where
  name := "selfhost-trust"
  exercise := "the release gate: packed wizc behaviour, the seed pin, and the cross-frontend fuzz"
  shard := "selfhost"
  cases := [
    { name := "R1: the packed wizc gate compiles and runs its fixture, and the one-byte control fails", run := fun _ => do
        match ← trustRun 300 "scripts/check-wizc-release.sh" #["--self-test-behaviour"] with
        | (0, out) => IO.print out
        | (code, out) =>
          IO.print out
          throw (IO.userError s!"the packed-wizc gate's self-test failed (exit {code})") },
    { name := "R2: the seed pin names a changed file and both hashes", run := fun _ => do
        match ← trustRun 300 "scripts/check-wizc-release.sh" #["--self-test-pin"] with
        | (0, out) => IO.print out
        | (code, out) =>
          IO.print out
          throw (IO.userError s!"the seed-pin self-test failed (exit {code})") },
    { name := "R7: the cross-frontend comparison reports a one-value disagreement", run := fun _ => do
        match ← trustRun 120 "python3" #["scripts/diff-fuzz.py", "--cross-self-test"] with
        | (0, out) => IO.print out
        | (code, out) =>
          IO.print out
          throw (IO.userError s!"the cross-frontend self-test failed (exit {code})") },
    { name := "R7: 12 generated programs agree through both frontends and backends (seed 20261119)", run := fun _ => do
        let root ← trustRoot
        let wiz := root / ".lake" / "build" / "bin" / "wiz"
        unless ← wiz.pathExists do
          skip "no .lake/build/bin/wiz"
          return
        match ← selfhostCompiler with
        | .error e =>
          if (e.splitOn "gmp.h").length > 1 then skip "no C toolchain" else
            throw (IO.userError s!"no self-hosted compiler: {e}")
        | .ok exe =>
          let tc ← toolchain
          let wizArgs := tc.toFlags.map (fun f => s!"--wiz-arg={f}")
          -- the self-hosted driver accepts --cc/--cflags/--ldflags (not the host's
          -- --gc-cflags spelling), so the collector's include and link flags go there
          let cflags := String.intercalate " " (tc.cflags ++ tc.gcCflags)
          let ldflags := String.intercalate " " (tc.ldflags ++ tc.gcLdflags)
          let mut selfArgs : Array String := #["--selfhost-arg=--cc", s!"--selfhost-arg={tc.cc}"]
          if !cflags.isEmpty then
            selfArgs := selfArgs ++ #["--selfhost-arg=--cflags", s!"--selfhost-arg={cflags}"]
          if !ldflags.isEmpty then
            selfArgs := selfArgs ++ #["--selfhost-arg=--ldflags", s!"--selfhost-arg={ldflags}"]
          let args : Array String :=
            #["scripts/diff-fuzz.py", "--cross", "--wiz", wiz.toString,
              "--selfhost", exe.toString, "--seed", "20261119", "--cross-programs", "12",
              "--timeout", "20"] ++ wizArgs.toArray ++ selfArgs
          match ← trustRun 1200 "python3" args with
          | (0, out) => IO.print out
          | (3, out) =>
            IO.print out
            skip "diff-fuzz skipped a pipeline (no C toolchain)"
          | (code, out) =>
            IO.print out
            throw (IO.userError s!"the cross-frontend campaign found a disagreement (exit {code})") }
  ]

builtin_initialize registerGroup selfhostTrustGroup

end Tests.Elab
