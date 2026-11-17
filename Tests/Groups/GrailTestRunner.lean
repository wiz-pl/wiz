import Tests.Grail

namespace Tests.Grail
open Wiz Tests

def testPkg : List (String × String) :=
  [("grail.wiz", "import Grail\ndef package : Package := Package.new \"t\" |> Package.tests \"tests\" \"tests\"\n"),
   ("tests/two.wiz", "import Prelude\n#eval 1 + 1\n"),
   ("tests/sub/bad.wiz", "import Prelude\ndef b : Nat := true\n")]

def testRunnerGroup : Group where
  name := "testrunner"
  exercise := "Stage 23f"
  cases := [
    { name := "tests are files with expected output; --update writes it", run := fun _ => do
        let dir ← mkTree testPkg
        let tc : Toolchain := { cacheDir := some (← IO.FS.createTempDir) }
        let (res, _) ← runTests dir tc
        checkEq 2 res.size
        check (res.all (!·.ok)) "a test without .expected passed"
        let (res, _) ← runTests dir tc (update := true)
        check (res.all (·.ok)) "--update failed"
        checkEq "tests/two.wiz:2:1: info: 2\n" (← IO.FS.readFile (dir / "tests/two.expected"))
        let bad ← IO.FS.readFile (dir / "tests/sub/bad.expected")
        check ((bad.splitOn "tests/sub/bad.wiz:2:").length > 1 && (bad.splitOn "error").length > 1) s!"bad.expected: {bad}"
        let (res, _) ← runTests dir tc
        check (res.all (·.ok)) "the tests failed after --update"
        -- `--update` with nothing to update records its passes too (docs-tour: "0 recorded
        -- passes" on the run after it)
        let cache2 ← IO.FS.createTempDir
        let dir2 ← mkTree testPkg
        let tc2 : Toolchain := { cacheDir := some cache2 }
        let _ ← runTests dir2 tc2 (update := true)
        let (res, _) ← runTests dir2 tc2 (update := true)
        check (res.all (·.ok)) "the second --update failed"
        let (res, st) ← runTests dir2 tc2
        check (res.all (·.cached)) "an unchanged --update pass was not recorded"
        checkEq 0 st.ran
        -- passes are recorded: nothing runs again
        let (res, st) ← runTests dir tc
        check (res.all (·.cached)) "a pass was not recorded"
        checkEq 0 st.ran },
    { name := "a wrong output fails, with the first difference", run := fun _ => do
        let dir ← mkTree (testPkg ++ [("tests/two.expected", "tests/two.wiz:2:1: info: 3\n")])
        let tc : Toolchain := { cacheDir := some (← IO.FS.createTempDir) }
        let (res, _) ← runTests dir tc
        let some two := res.find? (·.file == "tests/two.wiz") | throw (IO.userError "no test two")
        check (!two.ok) "a wrong output passed"
        check ((two.message.splitOn "info: 3").length > 1 && (two.message.splitOn "info: 2").length > 1) two.message },
    { name := "a failing test without a `-- test:` line says it was a check (icestick-cpu C8)", run := fun _ => do
        -- the program's expected output, but no `-- test: run`: it was compared with the
        -- (empty) messages of checking the file, and nothing said why
        let dir ← mkTree [("grail.wiz", "import Grail\ndef package : Package := Package.new \"t\" |> Package.tests \"tests\" \"tests\"\n"),
          ("tests/hello.wiz", "import IO\ndef main : IO Unit := IO.println \"hi\"\n"),
          ("tests/hello.expected", "hi\n"),
          ("tests/two.wiz", "-- test: check\nimport Prelude\n#eval 1 + 1\n"),
          ("tests/two.expected", "tests/two.wiz:3:1: info: 3\n")]
        let tc : Toolchain := { cacheDir := some (← IO.FS.createTempDir) }
        let (res, _) ← runTests dir tc
        let some hello := res.find? (·.file == "tests/hello.wiz") | throw (IO.userError "no test hello")
        check (!hello.ok) "it passed"
        check ((hello.message.splitOn "-- test: run").length > 1) hello.message
        -- with the line, a failure is only the difference
        let some two := res.find? (·.file == "tests/two.wiz") | throw (IO.userError "no test two")
        check (!two.ok) "two passed"
        check ((two.message.splitOn "-- test:").length == 1) two.message },
    { name := "-- test: skip reports a skip and needs no .expected", run := fun _ => do
        let dir ← mkTree [("grail.wiz", "import Grail\ndef package : Package := Package.new \"t\" |> Package.tests \"tests\" \"tests\"\n"),
          ("tests/on-demand.wiz", "-- test: skip needs --trust-native\nimport Prelude\ndef x : Nat := 1\n")]
        let tc : Toolchain := { cacheDir := some (← IO.FS.createTempDir) }
        for update in [false, true] do
          let (res, _) ← runTests dir tc update
          let some t := res.find? (·.file == "tests/on-demand.wiz") | throw (IO.userError "no result for the skipped test")
          check t.ok s!"the skipped test failed: {t.message}"
          check t.skipped "the skipped test was not reported as skipped"
          check ((t.message.splitOn "needs --trust-native").length > 1) t.message
          check (!(← (dir / "tests/on-demand.expected").pathExists)) "--update wrote a skipped test's .expected" },
    { name := "a nested package under the tests root is not a test", run := fun _ => do
        -- examples/grail-index/sources/*: packages with their own grail.wiz (and a
        -- directory name with dots), whose modules import each other's packages
        let dir ← mkTree [("grail.wiz", "import Grail\ndef package : Package := Package.new \"t\" |> Package.tests \"tests\" \"tests\"\n"),
          ("tests/one.wiz", "import Prelude\ndef x : Nat := 1\n"), ("tests/one.expected", ""),
          ("tests/fixture/pkg-0.1.0/grail.wiz", "import Grail\ndef package : Package := Package.new \"p\" |> Package.lib \"p\" \"src\"\n"),
          ("tests/fixture/pkg-0.1.0/src/P.wiz", "import Missing\ndef y : Nat := missing\n")]
        let tc : Toolchain := { cacheDir := some (← IO.FS.createTempDir) }
        let (res, _) ← runTests dir tc false
        check (res.size == 1) s!"expected one test, got {res.toList.map (·.file)}"
        check (res.all (·.ok)) s!"{res.toList.map (·.message)}" },
    { name := "-- test: run compiles and runs main", run := fun _ => do
        let dir ← mkTree [("grail.wiz", "import Grail\ndef package : Package := Package.new \"t\" |> Package.tests \"tests\" \"tests\"\n"),
          ("tests/hello.wiz", "-- test: run\nimport IO\ndef main : IO Unit := IO.println \"hi\"\n"),
          ("tests/hello.expected", "hi\n"),
          ("tests/value.wiz", "-- test: run\nimport Prelude\ndef main : Nat := 6 * 7\n"),
          ("tests/value.expected", "42\n")]
        let tc : Toolchain := { (← toolchain) with cacheDir := some (← IO.FS.createTempDir) }
        let (res, _) ← runTests dir tc
        if res.any fun t => (t.message.splitOn "gmp.h").length > 1 then
          skip "no toolchain"; return
        for t in res do check t.ok s!"{t.file}: {t.message}" },
    { name := "--update never records a failure: a program that doesn't build, fails or times out", run := fun _ => do
        let tc : Toolchain := { (← toolchain) with cacheDir := some (← IO.FS.createTempDir) }
        let failed (res : Array Grail.TestResult) (file needle : String) : IO Unit := do
          match res.find? (·.file == file) with
          | none => throw (IO.userError s!"no result for {file}")
          | some t =>
            check (!t.ok) s!"{file} passed: {t.message}"
            check ((t.message.splitOn needle).length > 1) s!"{file}: {t.message}"
        -- its program doesn't check (the run test's check job fails)
        let dir ← mkTree [("grail.wiz", "import Grail\ndef package : Package := Package.new \"t\" |> Package.tests \"tests\" \"tests\"\n"),
          ("tests/broken.wiz", "-- test: run\nimport Prelude\ndef main : Nat := Nat.zero Nat.zero\n")]
        for update in [true, false] do
          let (res, _) ← runTests dir tc update
          failed res "tests/broken.wiz" "does not build"
          check (!(← (dir / "tests/broken.expected").pathExists)) "--update recorded the failure"
        -- a time limit
        let dir ← mkTree [("grail.wiz", "import Grail\ndef package : Package := Package.new \"t\" |> Package.tests \"tests\" \"tests\"\n"),
          ("tests/slow.wiz", "import Prelude\ndef n : Nat := 1\n")]
        let (res, _) ← runTests dir tc (update := true) (testTimeoutMs := some 1)
        failed res "tests/slow.wiz" "timed out"
        check (!(← (dir / "tests/slow.expected").pathExists)) "--update recorded the time-out"
        -- a program that fails when it runs
        let dir ← mkTree [("grail.wiz", "import Grail\ndef package : Package := Package.new \"t\" |> Package.tests \"tests\" \"tests\"\n"),
          ("tests/exit.wiz", "-- test: run\nimport Sys\ndef main : IO Unit := Process.exit 3\n")]
        let (res, _) ← runTests dir tc (update := true)
        if res.any fun t => (t.message.splitOn "gmp.h").length > 1 then
          skip "no toolchain"; return
        failed res "tests/exit.wiz" "exited with 3"
        check (!(← (dir / "tests/exit.expected").pathExists)) "--update recorded the failed run" },
    -- the suite's own driver (`Tests/Main.lean`): `tests --run GROUP INDEX` ran a case
    -- in-process and printed nothing for a pass, so a stale binary or a wrong index that
    -- ran another (passing) case looked like a pass; a selector that picked nothing
    -- passed with 0 cases. Run against the cases with known outcomes `driverFixtures`.
    { name := "tests --run: a failing case exits 1 with its output, a skipped one 3, a bad selector 2", run := fun _ => do
        let self ← IO.appPath
        let run (args : Array String) : IO (UInt32 × String) := do
          let o ← IO.Process.output { cmd := self.toString, args }
          pure (o.exitCode, o.stdout ++ o.stderr)
        let has (out s : String) : IO Unit := check ((out.splitOn s).length > 1) s!"no {s} in:\n{out}"
        let (code, out) ← run #["--run", "driver-fixtures", "0"]
        checkEq 0 code; has out "✓ fixture: passes"; has out "driver-fixtures #0: passed"
        let (code, out) ← run #["--run", "driver-fixtures", "1"]
        checkEq 1 code; has out "✗ fixture: fails"; has out "fixture failure"
        has out "fixture output before the failure"; has out "FAILED"
        let (code, out) ← run #["--run", "driver-fixtures#2"]
        checkEq 3 code; has out "⊘ fixture: skips"; has out "skipped (fixture reason)"; has out "SKIPPED"
        let (code, out) ← run #["--run", "=driver-fixtures", "3"]
        checkEq 3 code; has out "skipped (old fixture reason)"
        for bad in [#["--run", "driver-fixtures", "4"], #["--run", "driver-fixtures", "x"],
            #["--run", "no-such-group", "0"], #["--run", "driver-fixtures"],
            #["--run", "driver-fixtures", "0", "extra"], #["=no-such-group"], #["=testrunner#99"],
            #["testrunner", "--no-such-flag"], #["=rig", "--jobs", "0"], #["=rig", "--jobs", "x"]] do
          let (code, out) ← run bad
          check (code == 2) s!"tests {" ".intercalate bad.toList}: exit code {code}, not 2:\n{out}" },
    -- `--jobs N` runs an opted-in group's cases in a bounded pool; its log is the
    -- sequential log but for the times (the cases are printed in case order, whether
    -- they finished in that order or not)
    { name := "--jobs N: an opted-in group's log is the --jobs 1 log, in case order", run := fun _ => do
        let self ← IO.appPath
        let run (args : Array String) : IO (UInt32 × String) := do
          let o ← IO.Process.output { cmd := self.toString, args }
          pure (o.exitCode, o.stdout)
        let (c1, one) ← run #["--jobs", "1", "=rig"]
        let (c4, four) ← run #["--jobs", "4", "=rig"]
        checkEq 0 c1; checkEq 0 c4
        -- the case lines, without their times (`(0.032 s)`); the group total too
        let norm (out : String) : List String :=
          (out.splitOn "\n").filterMap fun l =>
            if l.startsWith "── " then some l
            else if l.startsWith "  ✓ " || l.startsWith "  ⊘ " || l.startsWith "  ✗ " then some (l.splitOn " (").head!
            else none
        check ((norm four).length > 4) "no cases in the --jobs 4 log"
        checkEq (norm one) (norm four)
        -- and the same result
        checkEq (one.splitOn "\n" |>.find? (·.endsWith " passed, 0 failed"))
          (four.splitOn "\n" |>.find? (·.endsWith " passed, 0 failed")) }
  ]

builtin_initialize registerGroup testRunnerGroup

end Tests.Grail
