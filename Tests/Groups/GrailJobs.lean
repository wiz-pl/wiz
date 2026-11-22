import Tests.Grail

namespace Tests.Grail
open Wiz Tests

/-- A diamond: `B` and `C` import `A`, `D` imports both, and `app.wiz` imports `D`. -/
def diamondFiles : List (String × String) :=
  [("grail.wiz", "import Grail\ndef package : Package := Package.new \"diamond\"\n  |> Package.lib \"lib\" \"src\"\n  |> Package.check \"app\" \"app.wiz\"\n"),
   ("src/A.wiz", "import Prelude\ndef a : Nat := 1\n"),
   ("src/B.wiz", "import A\ndef b : Nat := a + 1\n"),
   ("src/C.wiz", "import A\ndef c : Nat := a + 2\n"),
   ("src/D.wiz", "import B\nimport C\ndef d : Nat := b + c\n"),
   ("app.wiz", "import D\n#eval d\n")]

def grailJobsGroup : Group where
  name := "grail-jobs"
  exercise := "Stage 23g"
  cases := [
    { name := "a diamond builds with -j 4 as with -j 1, and again runs nothing", run := fun _ => do
        let cache ← IO.FS.createTempDir
        let tc : Toolchain := { cacheDir := some cache }
        let d1 ← mkTree diamondFiles
        let (s1, ok1, log1) ← buildLog d1 tc (jobs := 1)
        check ok1 s!"-j 1 failed:\n{log1}"
        let d4 ← mkTree diamondFiles
        let (s4, ok4, log4) ← buildLog d4 tc (jobs := 4)
        check ok4 s!"-j 4 failed:\n{log4}"
        checkEq 5 s1.ran
        checkEq 5 s4.ran
        -- the same report, in the graph's order, and the same outputs
        checkEq log1 log4
        checkEq "[check src/A.wiz]\n[check src/B.wiz]\n[check src/C.wiz]\n[check src/D.wiz]\n[check app.wiz]\napp.wiz:2:1: info: 5\n" log4
        checkEq (← buildDirs d1) (← buildDirs d4)
        let (s, ok, _) ← buildLog d4 tc (jobs := 4)
        check ok "the second build failed"
        checkEq 0 s.ran
        checkEq 5 s.upToDate },
    { name := "a failed job stops what depends on it, only", run := fun _ => do
        let dir ← mkTree (diamondFiles.map fun (p, t) => if p == "src/B.wiz" then (p, "import A\ndef b : Nat := Nat.zero Nat.zero\n") else (p, t))
        let tc : Toolchain := { cacheDir := some (← IO.FS.createTempDir) }
        let (s, ok, log) ← buildLog dir tc (jobs := 4)
        check (!ok) "the build succeeded"
        -- A and C ran; B failed; D and app were skipped
        checkEq 2 s.ran
        checkEq 1 s.failed
        checkEq 2 s.skipped
        check ((log.splitOn "✗ check src/B.wiz\n  src/B.wiz:2:").length == 2) log
        check ((log.splitOn "- check src/D.wiz: skipped (check src/B.wiz failed)").length == 2) log
        check ((log.splitOn "- check app.wiz: skipped (check src/B.wiz failed)").length == 2) log
        -- nothing half-written is left
        let tmp := dir / ".grail" / "tmp"
        if ← tmp.pathExists then checkEq 0 (← tmp.readDir).size },
    { name := "a job has a time limit", run := fun _ => do
        let dir ← mkTree diamondFiles
        let tc : Toolchain := { cacheDir := some (← IO.FS.createTempDir) }
        let (s, ok, log) ← buildLog dir tc (jobs := 2) (timeoutMs := some 1)
        check (!ok) "the build succeeded"
        checkEq 0 s.ran
        check ((log.splitOn "timed out after 0.001 s").length > 1) log },
    { name := "the supervisor keeps a child's status, and a huge limit does not wrap", run := fun _ => do
        let self ← IO.appPath
        -- an ordinary status survives the supervisor
        let ok ← Grail.runSupervised self 60000 "sh" #["-c", "exit 42"]
        checkEq 42 ok.code
        -- a time limit still reports 124
        let timed ← Grail.runSupervised self 1 "sh" #["-c", "sleep 5"]
        checkEq 124 timed.code
        -- the status is clamped to the 8 bits POSIX has, never wrapped to 0 (success)
        checkEq 0 (Grail.exitStatus8 0)
        checkEq 137 (Grail.exitStatus8 137)
        checkEq 255 (Grail.exitStatus8 255)
        checkEq 255 (Grail.exitStatus8 256)
        checkEq 255 (Grail.exitStatus8 4294967295)
        -- a limit above UInt32.max is slept in chunks rather than truncated to nothing
        checkEq [] (Grail.sleepChunks 0)
        checkEq [5] (Grail.sleepChunks 5)
        checkEq [4294967295] (Grail.sleepChunks 4294967295)
        checkEq [4294967295, 1] (Grail.sleepChunks 4294967296) },
    { name := "the ready queue starts jobs in the graph's order, not in the order they became ready", run := fun _ => do
        -- node 3 depends on node 0; 1, 2, 4 and 5 are ready from the start. With one job
        -- at a time the scheduler prepares 3 when 0 finishes; the old FIFO queue appended
        -- it behind 1, 2, 4 and 5, so it started last: 0,1,2,4,5,3. Ready jobs start in
        -- node-index order.
        let dir ← IO.FS.createTempDir
        let nodes : Array Grail.Node := #[
          { label := "0", action := .check "0", deps := #[] },
          { label := "1", action := .check "1", deps := #[] },
          { label := "2", action := .check "2", deps := #[] },
          { label := "3", action := .check "3", deps := #[0] },
          { label := "4", action := .check "4", deps := #[] },
          { label := "5", action := .check "5", deps := #[] }]
        let order ← IO.mkRef (#[] : Array Nat)
        let log ← IO.mkRef ""
        let r ← runner dir { cacheDir := some (← IO.FS.createTempDir) }
          { name := "scheduler", targets := [], settings := [] } 1 log
        let prep := fun (nd : Grail.Node) (_ : Array (Except String Grail.Done)) => do
          let i := nd.label.toNat!
          pure (.job { key := i.toUInt64, timeoutMs := 1000,
                       how := .here fun _ => do
                         order.modify (·.push i)
                         pure (.ok ()) })
        let res ← r.schedule { nodes } prep
        check (res.all (· matches some (.ok _))) "a node failed"
        checkEq [0, 1, 2, 3, 4, 5] (← order.get).toList }
  ]

builtin_initialize registerGroup grailJobsGroup

end Tests.Grail
