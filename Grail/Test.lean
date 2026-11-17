import Grail.Build

/-!
# The test runner (stage 23f)

A `tests` target names a directory; every `.wiz` file under it is a test (except inside
a nested package, a subdirectory with its own `grail.wiz`), and `F.expected` beside
`F.wiz` is its expected output. The first line says what kind of
test it is (default `check`):

* `-- test: check`: the messages of elaborating the file, as `wiz check` prints them
  (`path:line:col: severity: text`, the path relative to the package);
* `-- test: run`: what `main` prints, compiled through C (an `IO` program's output, or
  `main`'s value read back with its type, as `wiz run` prints it);
* `-- test: skip REASON`: not run (an example that needs a flag `grail test` does not
  pass, or costs too much for the package-wide run); it is reported as skipped and needs
  no `.expected` file. The reason is shown with the skip.

A `check` or `run` line may end in `timeout SECS` (`-- test: run timeout 900`): the test's
time limit, when it needs more than `--test-timeout` (default 300 s) gives every test. The
larger of the two applies, to the test's job and, for `run`, to its program.

A test is a job like any other (`Grail/Graph.lean`), run in its own process with a time
limit: its key covers the file's key (its text and its imports'), the kind, the toolchain
for `run`, and the expected output, and a passing test is recorded under
`.grail/build/<key>/`, so `grail test` again runs nothing. A failing test isn't recorded.
`grail test --update` writes the actual output to `.expected`; `grail test --rerun` runs the
tests with a recorded pass again, and records what it finds (a new pass, or none).
-/

namespace Grail
open Wiz

inductive TestKind where
  | check
  | run
  /-- not run: an example that `grail test` cannot check (a flag, a cost), with the why -/
  | skip (reason : String)
  deriving BEq, Repr

/-- The `-- test:` line's kind and its declared time limit in seconds (`timeout SECS` at
the end of a `check` or `run` line). -/
def TestKind.parseLine (src : String) : Except String (TestKind × Option Nat) :=
  let first := (src.splitOn "\n").headD ""
  if !first.startsWith "-- test:" then .ok (.check, none) else
  let k := (first.drop 8).trimAscii.toString
  if k == "skip" then .ok (.skip "", none)
  else if k.startsWith "skip " then .ok (.skip (k.drop 5).trimAscii.toString, none)
  else
    let kind (w : String) : Except String TestKind := match w with
      | "check" => .ok .check
      | "run" => .ok .run
      | _ => .error s!"unknown test kind {k} (check, run, skip REASON; check and run may end in timeout SECS)"
    match (k.splitOn " ").filter (· != "") with
    | [w] => (kind w).map (·, none)
    | [w, "timeout", n] => match n.toNat? with
      | some secs => if secs == 0 then .error s!"a test's timeout must be positive: {k}" else (kind w).map (·, some secs)
      | none => .error s!"timeout wants a number of seconds: {k}"
    | _ => .error s!"unknown test kind {k} (check, run, skip REASON; check and run may end in timeout SECS)"

def TestKind.ofSource (src : String) : Except String TestKind :=
  (TestKind.parseLine src).map (·.1)

/-- A test's time limit in milliseconds: `--test-timeout`'s (`base`), or the larger
`timeout SECS` its `-- test:` line declares. -/
def testLimitMs (base : Nat) (src : String) : Nat :=
  match TestKind.parseLine src with
  | .ok (_, some secs) => max base (1000 * secs)
  | _ => base

/-- What a failing test without a `-- test:` line is told (it was taken for a `check`,
which compares the messages of elaborating the file: a program's output never shows up). -/
def TestKind.defaultNote (src : String) : String :=
  if ((src.splitOn "\n").headD "").startsWith "-- test:" then "" else
  "\n      (no `-- test:` line, so this was a `check` test: the expected output is the " ++
  "messages of checking the file; for what `main` prints, make `-- test: run` the first line)"

def TestKind.name : TestKind → String
  | .check => "check" | .run => "run" | .skip _ => "skip"

structure TestResult where
  file : String
  ok : Bool
  /-- came from a recorded pass -/
  cached : Bool := false
  /-- reported as skipped (`-- test: skip`), not run -/
  skipped : Bool := false
  message : String := ""

/-- The first line where two texts differ, for the report. -/
def firstDifference (expected actual : String) : String := Id.run do
  let es := expected.splitOn "\n"
  let as := actual.splitOn "\n"
  for i in [0:max es.length as.length] do
    let e := es[i]?.getD "<end>"
    let a := as[i]?.getD "<end>"
    if e != a then return s!"line {i + 1}:\n      expected: {e}\n      actual:   {a}"
  pure "(the same)"

/-- What the test prints (in the job's process); `exe` is the test's executable, for `run`. -/
def Runner.testOutput (r : Runner) (file : String) (kind : TestKind) (exe : System.FilePath) :
    IO (Except String String) := do
  match kind with
  | .skip _ => pure (.ok "")
  | .check =>
    let l ← r.load file
    let s ← r.elab file
    pure (.ok (render file l s))
  | .run =>
    let s ← r.elab file
    let secs := testLimitMs r.testTimeoutMs (← IO.FS.readFile (r.ctx.dir / file)) / 1000
    let out ← IO.Process.output { cmd := "timeout", args := #[toString secs, exe.toString] }
    if out.exitCode == 124 then return .error s!"timed out ({secs} s)"
    if out.exitCode != 0 then return .error s!"exited with {out.exitCode}: {out.stderr}"
    match Build.irProgram s "main" with
    | .error e => pure (.error e)
    | .ok (_, ty) =>
      if Build.isIO ty then return .ok out.stdout
      match Build.parseValue out.stdout with
      | none => pure (.error s!"could not read the result: {out.stdout}")
      | some v => pure (.ok ((readback s.globals s.builtins (eval s.globals [] ty) v).pretty ++ "\n"))

/-- A test's key: the file's key (its text and its imports'), the kind, the toolchain for
`run`, and the expected output. -/
def Runner.testKey (r : Runner) (file : String) (kind : TestKind) (expected : Option String) : IO UInt64 := do
  let l ← r.load file
  pure (mixHash (hash "test") (hash (toString [toString r.ctx.binId, toString l.key, kind.name,
    if kind == .run then toString r.ctx.tc.id else "", expected.getD "\x00none"])))

/-- The expected output of a test, and where it lives. -/
def expectedOf (dir : System.FilePath) (file : String) : IO (System.FilePath × Option String) := do
  let expFile := dir / ((System.FilePath.mk file).withExtension "expected")
  pure (expFile, ← if ← expFile.pathExists then some <$> IO.FS.readFile expFile else pure none)

/-- Is `rel` (a file's path under `base`) inside a nested package, a directory below
`base` with its own `grail.wiz`? Such a package has its own dependencies and tests
(`examples/grail-index/sources/*` are packages a registry fixture publishes), so its
files are not tests of the enclosing one. -/
def inNestedPackage (base : System.FilePath) (rel : String) : IO Bool := do
  let dirs := (rel.splitOn "/").dropLast
  let mut d := base
  for c in dirs do
    d := d / c
    if ← (d / "grail.wiz").pathExists then return true
  return false

/-- The test files of a `tests` target, relative to the package, sorted. A directory
with its own `grail.wiz` below the root is another package and is left out. -/
def testFiles (dir : System.FilePath) (root : String) : IO (Array String) := do
  let files ← Module.listRoot (dir / root)
  let mut out := #[]
  let base := (dir / root).toString ++ "/"
  for (m, path) in files do
    -- (the listed path, not `relPath m`: a directory such as `base-0.1.0` has dots)
    let underBase := (path.toString.dropPrefix? base).map (·.toString)
    if ← inNestedPackage (dir / root) (underBase.getD "") then continue
    out := out.push (System.FilePath.mk root / Module.relPath m).toString
  pure out

end Grail
