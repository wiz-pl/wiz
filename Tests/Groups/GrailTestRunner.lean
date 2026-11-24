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
  parallel := true
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
    { name := "--rerun runs recorded passes again and records the new result", run := fun _ => do
        let dir ← mkTree testPkg
        let tc : Toolchain := { cacheDir := some (← IO.FS.createTempDir) }
        let _ ← runTests dir tc (update := true)
        let _ ← runTests dir tc
        let (res, st) ← runTests dir tc
        check (res.all fun t => t.ok && t.cached) s!"not recorded: {res.toList.map (·.message)}"
        checkEq 0 st.ran
        let expected ← IO.FS.readFile (dir / "tests/two.expected")
        -- every test runs again, none is reported from the record, and the passes are
        -- recorded again (the plain run after it runs nothing)
        let (res, st) ← runTests dir tc (rerun := true)
        check (res.all (·.ok)) s!"the rerun failed: {res.toList.map (·.message)}"
        check (res.all (!·.cached)) "--rerun reported a recorded pass"
        checkEq 2 st.ran
        let (res, st) ← runTests dir tc
        check (res.all (·.cached)) "--rerun did not record its passes"
        checkEq 0 st.ran
        -- a rerun that fails (here: under a 1 ms limit) leaves no pass behind: the next
        -- plain run runs the tests instead of reporting the old record
        let (res, _) ← runTests dir tc (rerun := true) (testTimeoutMs := some 1)
        check (res.all (!·.ok)) s!"the 1 ms rerun passed: {res.toList.map (·.message)}"
        let (res, st) ← runTests dir tc
        check (res.all (·.ok)) s!"{res.toList.map (·.message)}"
        check (res.all (!·.cached)) "a pass survived a failed rerun"
        checkEq 2 st.ran
        -- --rerun leaves the .expected files alone
        checkEq expected (← IO.FS.readFile (dir / "tests/two.expected")) },
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
        -- examples/fate-index/sources/*: packages with their own grail.wiz (and a
        -- directory name with dots), whose modules import each other's packages
        let dir ← mkTree [("grail.wiz", "import Grail\ndef package : Package := Package.new \"t\" |> Package.tests \"tests\" \"tests\"\n"),
          ("tests/one.wiz", "import Prelude\ndef x : Nat := 1\n"), ("tests/one.expected", ""),
          ("tests/fixture/pkg-0.1.0/grail.wiz", "import Grail\ndef package : Package := Package.new \"p\" |> Package.lib \"p\" \"src\"\n"),
          ("tests/fixture/pkg-0.1.0/src/P.wiz", "import Missing\ndef y : Nat := missing\n")]
        let tc : Toolchain := { cacheDir := some (← IO.FS.createTempDir) }
        let (res, _) ← runTests dir tc false
        check (res.size == 1) s!"expected one test, got {res.toList.map (·.file)}"
        check (res.all (·.ok)) s!"{res.toList.map (·.message)}" },
    { name := "-- test: … timeout SECS: parsed, and a declared limit over --test-timeout applies", run := fun _ => do
        let parse (src : String) := Grail.TestKind.parseLine src
        check (parse "-- test: run timeout 900\n" matches .ok (.run, some 900)) "run timeout 900"
        check (parse "-- test: check  timeout 5\n" matches .ok (.check, some 5)) "check timeout 5"
        check (parse "-- test: run\n" matches .ok (.run, none)) "run"
        check (parse "-- test: skip slow, timeout 900\n" matches .ok (.skip _, none)) "a skip's reason is kept"
        check (parse "-- test: run timeout x\n" matches .error _) "timeout x"
        check (parse "-- test: run timeout 0\n" matches .error _) "timeout 0"
        check (parse "-- test: run slowly\n" matches .error _) "run slowly"
        checkEq 900000 (Grail.testLimitMs 300000 "-- test: run timeout 900\n")
        checkEq 300000 (Grail.testLimitMs 300000 "-- test: run timeout 5\n")
        checkEq 300000 (Grail.testLimitMs 300000 "-- test: run\n")
        -- under a 1 ms --test-timeout the undeclared test times out, the declared one passes
        let tc : Toolchain := { (← toolchain) with cacheDir := some (← IO.FS.createTempDir) }
        let dir ← mkTree [("grail.wiz", "import Grail\ndef package : Package := Package.new \"t\" |> Package.tests \"tests\" \"tests\"\n"),
          ("tests/slow.wiz", "import Prelude\ndef n : Nat := 1\n"),
          ("tests/declared.wiz", "-- test: check timeout 600\nimport Prelude\ndef n : Nat := 1\n")]
        let (res, _) ← runTests dir tc (update := true) (testTimeoutMs := some 1)
        match res.find? (·.file == "tests/slow.wiz"), res.find? (·.file == "tests/declared.wiz") with
        | some slow, some declared =>
          check (!slow.ok && (slow.message.splitOn "timed out").length > 1) s!"slow: {slow.message}"
          check declared.ok s!"declared: {declared.message}"
        | _, _ => throw (IO.userError s!"results: {res.toList.map (·.file)}") },
    { name := "-- test-timeout SECS: both positions reach the runner (a leading flag was discarded)", run := fun _ => do
        -- `grail --test-timeout 900 test` parsed 900 into the leading options, and the
        -- `test` branch re-parsed from `{}`, so the runner kept 300 s: an example that
        -- needs 222 s timed out at exactly 300 s *with the flag set*. `testOpts` seeds the
        -- parse from the leading options, and the flag after the subcommand still wins.
        let leading := ["--test-timeout", "900"]
        let outer := (Grail.grailOpts {} leading).1
        checkEq (some 900) (Grail.testOpts outer []).1.testTimeout
        checkEq (some 900) (Grail.testOpts {} ["--test-timeout", "900"]).1.testTimeout
        checkEq (some 5) (Grail.testOpts outer ["--test-timeout", "5"]).1.testTimeout
        checkEq (some 900) (Grail.testOpts outer ["--update"]).1.testTimeout
        -- the flag is consumed, not left in the filters
        checkEq ["--update"] (Grail.testOpts outer ["--test-timeout", "5", "--update"]).2 },
    { name := "-- test-timeout SECS: the dispatcher keeps a flag written before `test`", run := fun _ => do
        -- The regression was at the CALL SITE (the `test` branch re-parsed from `{}`), so a
        -- unit test of the parse cannot catch it: the test passes the options in itself and
        -- stays green when the dispatcher drops them (a mutation survivor). This drives
        -- `Grail.main`, the same entry point CI runs: with `--test-timeout 1` before `test`
        -- the case must fail; if the flag is discarded the runner keeps 300 s and it passes.
        --
        -- The tree needs a `*.expected` for the control run (a test without one is skipped,
        -- so the 900 s run "fails" for the wrong reason - run 45335632454), and its content
        -- must be what the test produces: with no `-- test:` line this is a `check` test,
        -- whose output is the messages of checking the file (none here), not stdout - run
        -- 45354517903 said exactly that.
        let dir ← mkTree [("grail.wiz", "import Grail\ndef package : Package := Package.new \"t\" |> Package.tests \"tests\" \"tests\"\n"),
          ("tests/slow.wiz", "import Prelude\ndef n : Nat := 1\n"),
          ("tests/slow.expected", "")]
        -- (i) the same invocation with a limit the case cannot reach must SUCCEED: that half
        -- is what stops this test being vacuous. Without it, any failure of `Grail.main` in a
        -- test process (`self := IO.appPath` re-invoke, a missing fixture) would look like
        -- proof that the flag arrived.
        let ok ← Grail.cliMain ["-C", dir.toString, "--test-timeout", "900", "test"]
        check (ok == 0) s!"the 900 s run must pass (rc {ok}), or this test proves nothing"
        -- (ii) with the 1 s limit the case must fail. A failure is only accepted as proof
        -- because (i) passed: the two runs differ in the flag alone.
        let rc ← Grail.cliMain ["-C", dir.toString, "--test-timeout", "1", "test"]
        check (rc != 0) s!"a 1 s limit written before `test` must fail the case (rc {rc}): the leading options were dropped" },
    { name := "-- test: run compiles and runs main", run := fun _ => do
        let dir ← mkTree [("grail.wiz", "import Grail\ndef package : Package := Package.new \"t\" |> Package.tests \"tests\" \"tests\"\n"),
          ("tests/hello.wiz", "-- test: run\nimport IO\ndef main : IO Unit := IO.println \"hi\"\n"),
          ("tests/hello.expected", "hi\n"),
          ("tests/value.wiz", "-- test: run\nimport Prelude\ndef main : Nat := 6 * 7\n"),
          ("tests/value.expected", "42\n")]
        let tc : Toolchain := { (← toolchain) with cacheDir := some (← IO.FS.createTempDir) }
        let (res, _) ← runTests dir tc
        if res.any fun t => (t.message.splitOn "gmp.h").length > 1 then
          skipMissing "no toolchain"; return
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
          skipMissing "no toolchain"; return
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
        checkEq 0 code; has out "[1/0/1]   ✓ fixture: passes"; has out "driver-fixtures #0: passed"
        let (code, out) ← run #["--run", "driver-fixtures", "1"]
        checkEq 1 code; has out "✗ fixture: fails"; has out "fixture failure"
        has out "fixture output before the failure"; has out "FAILED"
        let (code, out) ← run #["--run", "driver-fixtures#2"]
        checkEq 3 code; has out "⊘ fixture: skips"; has out "skipped (fixture reason)"; has out "SKIPPED"
        let (code, out) ← run #["--run", "=driver-fixtures", "3"]
        checkEq 3 code; has out "skipped (old fixture reason)"
        for bad in [#["--run", "driver-fixtures", "5"], #["--run", "driver-fixtures", "x"],
            #["--run", "no-such-group", "0"], #["--run", "driver-fixtures"],
            #["--run", "driver-fixtures", "0", "extra"], #["=no-such-group"], #["=testrunner#99"],
            #["testrunner", "--no-such-flag"], #["=rig", "--jobs", "0"], #["=rig", "--jobs", "x"]] do
          let (code, out) ← run bad
          check (code == 2) s!"tests {" ".intercalate bad.toList}: exit code {code}, not 2:\n{out}" },
    -- The missing-dependency policy (`Tests.skipMissing`): by default a case whose
    -- dependency is absent FAILS, naming it; `--allow-missing-deps` (or the shard driver's
    -- `WIZ_ALLOW_MISSING_DEPS=1`) reports it as a skip; a declared skip is a skip either
    -- way. The driver's own fixture, so it needs neither a toolchain nor a build.
    { name := "a missing dependency fails by default, skips with --allow-missing-deps / WIZ_ALLOW_MISSING_DEPS, and a declared skip still skips", run := fun _ => do
        let self ← IO.appPath
        let run (args : Array String) (env : Array (String × Option String)) : IO (UInt32 × String) := do
          let o ← IO.Process.output { cmd := self.toString, args, env }
          pure (o.exitCode, o.stdout ++ o.stderr)
        let unset := #[("WIZ_ALLOW_MISSING_DEPS", none)]
        -- default: a failure that names the dependency and the one flag
        let (code, out) ← run #["--run", "driver-fixtures", "4"] unset
        checkEq 1 code
        check ((out.splitOn "missing dependency: no fixture-dep on PATH").length > 1) out
        check ((out.splitOn "--allow-missing-deps").length > 1) out
        check ((out.splitOn "FAILED").length > 1) out
        -- the flag: a reported skip, with the reason and exit 3
        let (code, out) ← run #["--allow-missing-deps", "--run", "driver-fixtures", "4"] unset
        checkEq 3 code
        check ((out.splitOn "⊘ fixture: missing dependency").length > 1) out
        check ((out.splitOn "skipped (no fixture-dep on PATH)").length > 1) out
        check ((out.splitOn "SKIPPED").length > 1) out
        -- the shard driver's environment equivalent
        let (code, out) ← run #["--run", "driver-fixtures", "4"] #[("WIZ_ALLOW_MISSING_DEPS", some "1")]
        checkEq 3 code
        check ((out.splitOn "SKIPPED (no fixture-dep on PATH)").length > 1) out
        -- a declared skip is unaffected by either spelling
        for args in [#["--run", "driver-fixtures", "2"], #["--allow-missing-deps", "--run", "driver-fixtures", "2"]] do
          let (code, out) ← run args unset
          checkEq 3 code
          check ((out.splitOn "skipped (fixture reason)").length > 1) out },
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
        -- the case lines, without their times (`(0.032 s)`) but with their `[n/failed/total]`
        -- position (which `--jobs` must not change); the group total too
        let norm (out : String) : List String :=
          (out.splitOn "\n").filterMap fun l =>
            if l.startsWith "── " then some l
            else
              let body := match l.splitOn "] " with
                | [num, rest] => if num.startsWith "[" then rest else l
                | _ => l
              if body.startsWith "  ✓ " || body.startsWith "  ⊘ " || body.startsWith "  ✗ " then some (l.splitOn " (").head!
              else none
        check ((norm four).length > 4) "no cases in the --jobs 4 log"
        checkEq (norm one) (norm four)
        -- and the same result
        checkEq (one.splitOn "\n" |>.find? (·.endsWith " passed, 0 failed"))
          (four.splitOn "\n" |>.find? (·.endsWith " passed, 0 failed")) }
  ]

builtin_initialize registerGroup testRunnerGroup

end Tests.Grail
