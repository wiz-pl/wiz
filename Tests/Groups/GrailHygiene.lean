import Tests.Grail

namespace Tests.Grail
open Wiz Tests

/-- A process is gone (or a zombie) within `ms` milliseconds. -/
partial def goneWithin (pid : String) (ms : Nat) : IO Bool := do
  let stat := System.FilePath.mk "/proc" / pid / "stat"
  let alive ← try pure (((← IO.FS.readFile stat).splitOn ") ")[1]?.map (·.take 1 |>.toString) != some "Z") catch _ => pure false
  if !alive then return true
  if ms == 0 then return false
  IO.sleep 100
  goneWithin pid (ms - min ms 100)

/-- Wait for a file to appear (a job writes its pid there). -/
partial def waitFor (f : System.FilePath) (ms : Nat) : IO String := do
  if ← f.pathExists then
    let t := (← IO.FS.readFile f).trimAscii.toString
    if !t.isEmpty then return t
  if ms == 0 then throw (IO.userError s!"{f} did not appear")
  IO.sleep 100
  waitFor f (ms - min ms 100)

/-- A command that starts a grandchild (`sleep`), writes its pid, and waits. -/
def slowFiles (secs : String) : List (String × String) :=
  [("grail.wiz", "import Grail\ndef package : Package := Package.new \"s\"\n" ++
     s!"  |> Package.command (Command.new \"slow\" (Tool.path \"sh\") |> Command.arg \"-c\" |> Command.arg \"sleep {secs} & echo $! > slow.pid; wait\")\n")]

/-- Start grail (this test driver, `--grail`) building `slow`, and kill it with `signal`
once the job has started: the job's grandchild must go too. -/
def killGrailCase (signal : String) : Case :=
    { name := s!"killing grail (SIG{signal}) kills its jobs", run := fun _ => do
        let dir ← mkTree (slowFiles (if signal == "KILL" then "298" else "297"))
        let cache ← IO.FS.createTempDir
        let self ← IO.appPath
        let args := #["--grail", "-C", dir.toString, "--cache", cache.toString, "build", "slow"]
        let child ← IO.Process.spawn { cmd := self.toString, args, stdout := .null, stderr := .null }
        let pid ← waitFor (dir / "slow.pid") 60000
        let o ← IO.Process.output { cmd := "kill", args := #[s!"-{signal}", toString child.pid] }
        checkEq 0 o.exitCode
        let _ ← child.wait
        check (← goneWithin pid 5000) s!"the job's process {pid} outlived grail" }

def grailHygieneGroup : Group where
  name := "grail-hygiene"
  exercise := "Stage 23k"
  cases := [
    killGrailCase "KILL",
    killGrailCase "TERM",
    { name := "a time limit kills the job's whole process group", run := fun _ => do
        let dir ← mkTree (slowFiles "296")
        let (_, ok, log) ← buildLog dir (← cmdTc) (timeoutMs := some 1500)
        check (!ok) "the build succeeded"
        check (has log "timed out after 1.500 s (its process group was killed)") log
        let pid ← waitFor (dir / "slow.pid") 1000
        check (← goneWithin pid 5000) s!"the job's process {pid} outlived its time limit" }
  ]

builtin_initialize registerGroup grailHygieneGroup

end Tests.Grail
