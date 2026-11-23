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
  the self-hosted one and compares the programs' stdout. Its first campaign found a real
  frontend gap (all 12 programs rejected at the shared preamble, `unknown identifier
  dfSumL`: recursion inside a lambda body); the campaign case therefore asserts the
  committed classification (`Tests/data/selfhost-trust-cross.tsv`): a program that
  becomes `agree` is forward, a different cause is a new finding, and the number of
  known disagreements may not grow. `--cross-self-test` proves the comparison reacts to
  a one-value difference.

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

/-! ## The cross-fuzz classification

R7's campaign found a real gap on its first run: all 12 generated programs are rejected by
the self-hosted frontend at the shared preamble (`unknown identifier dfSumL`, recursion
written inside a lambda body), so none reaches a runtime comparison. Gating CI red on a
known frontend gap would make the case noise; hiding it would make the case empty. The
committed table `Tests/data/selfhost-trust-cross.tsv` classifies each program (agree /
disagree + cause), like `Tests/libdiff-baseline.tsv`: a program that becomes `agree` is
forward; a disagreement with a *different* cause is a new finding and fails; the number
of known disagreements may not grow. The generator is deliberately not restricted to the
selfhost-supported fragment. -/

structure CrossRow where
  program : Nat
  shape : String
  status : String
  cause : String
  deriving Inhabited, BEq

def CrossRow.ofJson (j : Lean.Json) : Option CrossRow := do
  let program ← (j.getObjValAs? Nat "program").toOption
  let shape ← (j.getObjValAs? String "shape").toOption
  let status ← (j.getObjValAs? String "status").toOption
  let cause ← (j.getObjValAs? String "cause").toOption
  pure { program, shape, status, cause }

def readCrossJson (f : String) : IO (Array CrossRow) := do
  let mut rows := #[]
  for line in (← IO.FS.readFile f).splitOn "\n" do
    if line.trimAscii.isEmpty then continue
    match Lean.Json.parse line with
    | .ok j => match CrossRow.ofJson j with
      | some r => rows := rows.push r
      | none => throw (IO.userError s!"{f}: not a cross row: {line}")
    | .error e => throw (IO.userError s!"{f}: {e}")
  pure rows

def readCrossBaseline (f : String) : IO (Array CrossRow) := do
  let mut rows := #[]
  for line in (← IO.FS.readFile f).splitOn "\n" do
    let line := line.trimAscii.toString
    if line.isEmpty || line.startsWith "#" then continue
    match line.splitOn "\t" with
    | [p, shape, status, cause] =>
      match p.toNat? with
      | some n => rows := rows.push { program := n, shape, status, cause }
      | none => throw (IO.userError s!"{f}: program column is not a number: {line}")
    | _ => throw (IO.userError s!"{f}: not program<TAB>shape<TAB>status<TAB>cause: {line}")
  pure rows

/-- Compare one run with the classification: forward moves pass, new kinds fail, and the
known-gap count may not grow. -/
def checkCrossClassification (base got : Array CrossRow) : IO Unit := do
  checkEq 12 base.size
  checkEq base.size got.size
  check ((base.map (·.program)) == (got.map (·.program)))
    "the programs are not the classified set (seed or count changed)"
  let known := (base.filter (·.status == "disagree")).size
  let current := (got.filter (·.status == "disagree")).size
  check (current ≤ known)
    s!"the known cross-fuzz gap grew: {current} disagreements, classification has {known}"
  for i in [0:base.size] do
    let b := base[i]!
    let g := got[i]!
    check (b.shape == g.shape)
      s!"p{b.program}: shape changed from {b.shape} to {g.shape} (regenerate the classification?)"
    if b.status == "agree" then
      check (g.status == "agree") s!"p{b.program} regressed: now {g.status} ({g.cause})"
    else if b.status == "disagree" then
      if g.status == "agree" then
        note s!"cross-fuzz forward: p{b.program} ({b.shape}) now agrees"
      else
        check (g.status == "disagree") s!"p{b.program} is now {g.status}, not a disagreement"
        check (g.cause == b.cause)
          s!"p{b.program} ({b.shape}): a new disagreement kind: {g.cause} (known: {b.cause})"
    else
      check (g.status == b.status) s!"p{b.program}: {b.status} became {g.status}"

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
    { name := "R7: the 12 cross programs match the committed classification (known gap counted)", run := fun _ => do
        let root ← trustRoot
        let wiz := root / ".lake" / "build" / "bin" / "wiz"
        unless ← wiz.pathExists do
          skipMissing "no .lake/build/bin/wiz"
          return
        match ← selfhostCompiler with
        | .error e =>
          if (e.splitOn "gmp.h").length > 1 then skipMissing "no C toolchain" else
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
          let dir ← IO.FS.createTempDir
          let json := dir / "cross.json"
          let args : Array String :=
            #["scripts/diff-fuzz.py", "--cross", "--wiz", wiz.toString,
              "--selfhost", exe.toString, "--seed", "20261119", "--cross-programs", "12",
              "--timeout", "20", "--cross-json", json.toString]
              ++ wizArgs.toArray ++ selfArgs
          match ← trustRun 1800 "python3" args with
          | (0, out) =>
            IO.print out
            let base ← readCrossBaseline "Tests/data/selfhost-trust-cross.tsv"
            let got ← readCrossJson json.toString
            IO.FS.removeDirAll dir
            checkCrossClassification base got
          | (code, out) =>
            IO.print out
            IO.FS.removeDirAll dir
            throw (IO.userError s!"the cross-frontend campaign could not run (exit {code})") }
  ]

builtin_initialize registerGroup selfhostTrustGroup

end Tests.Elab
