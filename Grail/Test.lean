import Grail.Build
import Wiz.Test

/-!
# The test runner (stage 23f)

A `tests` target names a directory; every `.wiz` file under it is a test, and
`F.expected` beside `F.wiz` is its expected output. The first line says what kind of
test it is (default `check`):

* `-- test: check`: the messages of elaborating the file, as `wiz check` prints them
  (`path:line:col: severity: text`, the path relative to the package);
* `-- test: run`: what `main` prints, compiled through C (an `IO` program's output, or
  `main`'s value read back with its type, as `wiz run` prints it).

A test is a job like any other (`Grail/Graph.lean`), run in its own process with a time
limit: its key covers the file's key (its text and its imports'), the kind, the toolchain
for `run`, and the expected output, and a passing test is recorded under
`.grail/build/<key>/`, so `grail test` again runs nothing. A failing test isn't recorded.
`grail test --update` writes the actual output to `.expected`.
-/

namespace Grail
open Wiz

structure TestResult where
  file : String
  ok : Bool
  /-- came from a recorded pass -/
  cached : Bool := false
  message : String := ""

/-- What the test prints (in the job's process); `exe` is the test's executable, for `run`. -/
def Runner.testOutput (r : Runner) (file : String) (kind : TestKind) (exe : System.FilePath) :
    IO (Except String String) := do
  match kind with
  | .check =>
    let l ← r.load file
    let s ← r.elab file
    pure (.ok (render file l s))
  | .run =>
    let s ← r.elab file
    let out ← IO.Process.output { cmd := "timeout", args := #["60", exe.toString] }
    if out.exitCode == 124 then return .error "timed out (60 s)"
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

/-- The test files of a `tests` target, relative to the package, sorted. -/
def testFiles (dir : System.FilePath) (root : String) : IO (Array String) := do
  let files ← Module.listRoot (dir / root)
  pure (files.map fun (m, _) => (System.FilePath.mk root / Module.relPath m).toString)

end Grail
