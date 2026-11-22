/-!
# Running a job's process (stage 23k)

Every job process (a `--grail-job`, the C compiler, a command target's program) runs
under a **supervisor**, `<grail> --grail-exec MS [--cwd DIR] [--env K=V]… -- CMD ARGS…`:
the grail binary itself (or the test driver), which

* starts `CMD` in a new session and process group, its stdin `/dev/null`, its stdout and
  stderr the supervisor's own (pipes to grail);
* waits for it, and when `MS` milliseconds have passed kills its whole process group and
  exits with 124;
* reads its own stdin, a pipe from grail that grail never writes to: end of file means
  grail has died (by any signal, `SIGKILL` included), and the supervisor kills the job's
  process group and exits;
* otherwise exits with the job's status (`128+N` if it died of signal `N`).

grail starts each supervisor in a session of its own as well, so a Ctrl-C or a signal to
grail's process group reaches grail only; the supervisors then see the end of their
pipe. (Lean's pipes are close-on-exec, so one supervisor doesn't hold another's pipe
open.) Before this, jobs ran under `timeout`, which makes a process group of its own:
killing grail left its jobs running.
-/

namespace Grail

/-- How a job process ended. -/
structure Outcome where
  code : UInt32
  stdout : String
  stderr : String

def secs (ms : Nat) : String :=
  let f := toString (ms % 1000)
  s!"{ms / 1000}.{String.ofList (List.replicate (3 - f.length) '0')}{f}"

def signalName : Nat → String
  | 1 => "SIGHUP" | 2 => "SIGINT" | 3 => "SIGQUIT" | 4 => "SIGILL" | 6 => "SIGABRT"
  | 7 => "SIGBUS" | 8 => "SIGFPE" | 9 => "SIGKILL" | 11 => "SIGSEGV" | 13 => "SIGPIPE"
  | 14 => "SIGALRM" | 15 => "SIGTERM" | n => s!"signal {n}"

/-- How a process ended, in words: `exit code 3`, `killed by signal 9 (SIGKILL: …)`. -/
def describeExit (code : UInt32) (timeoutMs : Nat) : String :=
  let c := code.toNat
  if c == 124 then s!"timed out after {secs timeoutMs} s (its process group was killed)"
  else if c > 128 && c < 160 then
    let n := c - 128
    s!"killed by signal {n} ({signalName n}{if n == 9 then ": out of memory, or killed by hand?" else ""})"
  else s!"exit code {c}"

/-- The last `n` lines of a text. -/
def tailLines (s : String) (n : Nat := 20) : String :=
  let ls := (s.trimAsciiEnd.toString.splitOn "\n")
  let ls := if ls == [""] then [] else ls
  let cut := ls.length - min n ls.length
  (if cut > 0 then s!"… ({cut} lines before)\n" else "") ++ "\n".intercalate (ls.drop cut)

/-- A failed job's report: how it ended, and the end of what it printed. A job that
failed by itself (exit code 1) with something to say is reported by what it said (a
check's error messages). -/
def failureMessage (o : Outcome) (timeoutMs : Nat) : String :=
  let out := if o.stderr.isEmpty then o.stdout else o.stderr
  if o.code == 1 && !out.trimAscii.isEmpty then out
  else
    let all := o.stdout ++ o.stderr
    describeExit o.code timeoutMs ++ (if all.trimAscii.isEmpty then ", and printed nothing" else "; the end of its output:\n" ++ tailLines all)

/-- `_exit` (c/proc.c): the supervisor's stdin watcher is blocked in a read, and Lean's
own exit would wait for it. -/
@[extern "grail_exit_now"] opaque exitNow (code : UInt8) : IO Unit

@[export grail_ok_unit] def okUnit : IO Unit := pure ()
@[export grail_ok_bool] def okBool (b : Bool) : IO Bool := pure b
@[extern "grail_path_clear"] opaque pathClear : IO Unit
@[extern "grail_path_push"] opaque pathPush (b : UInt8) : IO Unit
@[extern "grail_path_executable"] opaque pathExecutableRaw : IO Bool

/-- Is the file executable by its owner? (c/proc.c: Lean's library can't read a mode.)
Not thread-safe: the scheduler's thread calls it. -/
def isExecutable (p : System.FilePath) : IO Bool := do
  pathClear
  for b in p.toString.toUTF8 do pathPush b
  pathExecutableRaw

/-- `ms` milliseconds in `UInt32`-sized sleeps, longest first. `IO.sleep` takes a
`UInt32`, so `ms.toUInt32` would wrap a limit at or above 2^32 ms (~49.7 days), and the
supervisor would time the job out at once. -/
partial def sleepChunks (ms : Nat) : List UInt32 :=
  if ms == 0 then []
  else
    let chunk := min ms 4294967295
    chunk.toUInt32 :: sleepChunks (ms - chunk)

/-- Sleep `ms` milliseconds without wrapping. -/
def sleepMs (ms : Nat) : IO Unit := do
  for chunk in sleepChunks ms do
    IO.sleep chunk

/-- The 8-bit status the supervisor exits with. A POSIX wait status is 8 bits, so a code
above 255 cannot be reported as-is; clamp it to 255 instead of letting `toUInt8` wrap it
(a 256 would become 0, a false success). -/
def exitStatus8 (code : UInt32) : UInt8 :=
  if code > 255 then 255 else code.toUInt8

/-- `--grail-exec MS [--cwd DIR] [--env K=V]… -- CMD ARGS…` -/
def execMain (args : List String) : IO UInt32 := do
  let usage : IO UInt32 := do IO.eprintln s!"grail --grail-exec: bad arguments {args}"; pure 2
  let ms :: rest := args | usage
  let some ms := ms.toNat? | usage
  let mut cwd : Option String := none
  let mut env : Array (String × Option String) := #[]
  let mut rest := rest
  repeat
    match rest with
    | "--cwd" :: d :: r => cwd := some d; rest := r
    | "--env" :: kv :: r =>
      match kv.splitOn "=" with
      | k :: vs => env := env.push (k, some ("=".intercalate vs)); rest := r
      | [] => return ← usage
    | _ => break
  let "--" :: cmd :: cargs := rest | usage
  let child ← try
      IO.Process.spawn { cmd, args := cargs.toArray, cwd := cwd.map (System.FilePath.mk ·), env,
                         setsid := true, stdin := .null, stdout := .inherit, stderr := .inherit }
    catch e =>
      IO.eprintln s!"{cmd}: {e}"
      return 127
  let finished ← IO.mkRef false
  let timedOut ← IO.mkRef false
  let killOnce : IO Unit := do
    unless ← finished.get do
      try child.kill catch _ => pure ()
  -- grail's end: the end of our stdin
  let _ ← IO.asTask (prio := .dedicated) do
    let stdin ← IO.getStdin
    repeat
      let b ← (try stdin.read 4096 catch _ => pure ByteArray.empty)
      if b.isEmpty then break
    killOnce
  -- the time limit
  let _ ← IO.asTask (prio := .dedicated) do
    sleepMs ms
    unless ← finished.get do
      timedOut.set true
      killOnce
  let code ← child.wait
  finished.set true
  let code := if ← timedOut.get then 124 else code
  (← IO.getStdout).flush
  (← IO.getStderr).flush
  exitNow (exitStatus8 code)
  pure code

/-- Run `cmd args` under a supervisor (`self --grail-exec …`), capturing its output. -/
def runSupervised (self : System.FilePath) (ms : Nat) (cmd : String) (args : Array String)
    (cwd : Option System.FilePath := none) (env : List (String × String) := []) : IO Outcome := do
  let sargs := #[toString ms] ++ (match cwd with | some d => #["--cwd", d.toString] | none => #[]) ++
    (env.toArray.flatMap fun (k, v) => #["--env", s!"{k}={v}"]) ++ #["--", cmd] ++ args
  try
    let child ← IO.Process.spawn { cmd := self.toString, args := #["--grail-exec"] ++ sargs, setsid := true,
                                   stdin := .piped, stdout := .piped, stderr := .piped }
    let errTask ← IO.asTask (prio := .dedicated) child.stderr.readToEnd
    let out ← child.stdout.readToEnd
    let err ← IO.ofExcept errTask.get
    let code ← child.wait
    pure { code, stdout := out, stderr := err }
  catch e => pure { code := 127, stdout := "", stderr := s!"{cmd}: {e}" }

end Grail
