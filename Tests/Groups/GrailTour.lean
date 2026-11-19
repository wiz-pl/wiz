import Tests.Grail

namespace Tests.Grail
open Wiz Tests

/-- The language tour's examples (docs/tour.md): every file in `examples/tour/`, run as
`grail test` runs it (its messages, or with `-- test: run` what `main` prints, against
its `.expected`), in a package of its own so that only that file runs. -/
def tourFiles : List String :=
  ["00-hello", "01-basics", "02-data", "03-structures", "04-classes", "05-vec", "06-proofs",
   "06b-calc", "07-quantities", "08-codata", "09-ffi", "10-hdl", "11-mistakes", "12-scry"]

def tourCase (f : String) : Case :=
  { name := s!"examples/tour/{f}.wiz", run := fun _ => do
      let p := s!"examples/tour/{f}"
      let dir ← mkTree [
        ("grail.wiz", "import Grail\ndef package : Package := Package.new \"tour\" |> Package.tests \"tour\" \"examples/tour\"\n"),
        (p ++ ".wiz", ← IO.FS.readFile (p ++ ".wiz")),
        (p ++ ".expected", ← IO.FS.readFile (p ++ ".expected"))]
      let tc ← toolchain
      let tc : Toolchain := { tc with cacheDir := some (← tc.cacheDir.getDM IO.FS.createTempDir) }
      let (res, _) ← runTests dir tc
      checkEq 1 res.size
      for t in res do
        if !t.ok && (t.message.splitOn "gmp.h").length > 1 then
          skip "no toolchain"; return
        check t.ok s!"{t.file}: {t.message}" }

/-- Section 11's command: `grail new` writes the `exe` template, and its package tests
pass. -/
def tourNewCase : Case :=
  { name := "docs/tour: grail new writes a package that tests", run := fun _ => do
      let root ← IO.FS.createTempDir
      let dir := root / "hello"
      let exe := (← IO.FS.realPath ".lake/build/bin/grail").toString
      let o ← IO.Process.output {
        cmd := exe, args := #["new", "hello", "--dir", dir.toString] }
      if o.exitCode != 0 then throw (IO.userError s!"grail new failed: {o.stderr}")
      check ((o.stdout.splitOn "grail new: wrote").length > 1) o.stdout
      for f in ["grail.wiz", "src/Main.wiz", "tests/hello.wiz", "tests/hello.expected",
                "README.md", ".gitignore"] do
        check (← (dir / f).pathExists) s!"missing {f}"
      let tc ← toolchain
      let tc : Toolchain := { tc with cacheDir := some (← IO.FS.createTempDir) }
      let (res, _) ← runTests dir tc
      checkEq 1 res.size
      for t in res do
        if !t.ok && (t.message.splitOn "gmp.h").length > 1 then
          skip "no toolchain"; return
        check t.ok s!"{t.file}: {t.message}" }

def tourGroup : Group where
  name := "tour"
  exercise := "docs/tour.md"
  parallel := true
  cases :=
    { name := "examples/tour/ has exactly the files the group knows", run := fun _ => do
        let mut names : Array String := #[]
        for e in ← System.FilePath.readDir "examples/tour" do
          names := names.push e.fileName
        let want := tourFiles.flatMap fun f => [f ++ ".expected", f ++ ".wiz"]
        checkEq (want.toArray.qsort (· < ·)).toList (names.qsort (· < ·)).toList } ::
    (tourFiles.map tourCase ++ [tourNewCase])

builtin_initialize registerGroup tourGroup

end Tests.Grail
