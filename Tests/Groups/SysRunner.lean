import Tests.Elab
import Tests.Groups.Sys

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-! The test runner's natives (TR2, `lib/Sys.wiz`'s last section; docs/stages/33-test-runner.md):
`FS.hashFile` (BLAKE3), `Child.waitRusage`/`tryWaitRusage` (`wait4`),
`Process.spawnInCgroup`, and `Sys.onInterrupt`. Each runs on the C and the LLVM backend
(`sysRun`). -/

/-- Helpers: an exit status in words, and polling a child until it ends. -/
def sysRunnerShow : String := sysShow ++ r#"def showSt : ExitStatus → String
  | .exited n => String.append "exited " (Nat.toString n)
  | .signaled s => String.append "signaled " (Nat.toString s)
def pollEnd (c : Child) : Nat → EIO String
  | .zero => EIO.pure "still running"
  | .succ n => do
    r ← Child.tryWaitRusage c;
    match r with
    | .some x => EIO.pure (showSt x.1)
    | .none => do
      EIO.lift (Clock.sleep (Duration.millis 20));
      pollEnd c n
"#

def sysRunnerGroup : Group where
  name := "sys-runner"
  exercise := "lib/Sys.wiz: the test runner's natives (TR2)"
  cases := [
    { name := "FS.hashFile: BLAKE3 of an empty file, \"abc\" and 1 MiB + 1 (libblake3's digests); a missing file", run := fun _ =>
        sysRun ["d ← FS.createTempDir", r#"FS.writeFile (Path.join d "e") """#, r#"FS.writeFile (Path.join d "a") "abc""#,
          r#"o ← Process.output "sh" ["-c", "yes x | head -c 1048577 > \"$0\"", Path.join d "big"] """#,
          r#"h1 ← FS.hashFile (Path.join d "e")"#, "say h1",
          r#"h2 ← FS.hashFile (Path.join d "a")"#, "say h2",
          r#"h3 ← FS.hashFile (Path.join d "big")"#, "say h3",
          r#"r ← EIO.lift (FS.hashFile "/nonexistent/x")"#, "say (match r with | .ok s => s | .error m => m)",
          "FS.removeAll d"]
          ("af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262\n" ++
           "6437b3ac38465133ffb63b75273a8db548c558465d79db03fd359c6cd5bd9d85\n" ++
           "89dc2ba4afa85d39ad4b50b8b742bfe4d641036b58734aa6e49ef2ed72821ecc\n" ++
           "/nonexistent/x: No such file or directory\n")
          sysRunnerShow },
    { name := "Child.waitRusage and tryWaitRusage: exit codes, signals, a peak, polling, and ECHILD after Child.wait", run := fun _ =>
        sysRun [r#"c ← Process.spawn "sh" ["-c", "exit 3"] .null .null .null"#, "r ← Child.waitRusage c",
          "say (showSt r.1)", "say (yesNo (Nat.lt 0 r.2.maxRssKiB))",
          r#"c2 ← Process.spawn "sh" ["-c", "kill -9 $$"] .null .null .null"#, "r2 ← Child.waitRusage c2",
          "say (showSt r2.1)",
          r#"c3 ← Process.spawn "sleep" ["1"] .null .null .null"#, "t ← Child.tryWaitRusage c3",
          r#"say (match t with | .none => "running" | .some _ => "ended?")"#,
          "e ← pollEnd c3 500", "say e",
          r#"c4 ← Process.spawn "true" .nil .null .null .null"#, "st ← Child.wait c4",
          "w ← EIO.lift (Child.waitRusage c4)", "say (match w with | .ok _ => \"usage?\" | .error m => m)"]
          "exited 3\nyes\nsignaled 9\nrunning\nexited 0\nwait: No child processes\n"
          sysRunnerShow },
    { name := "Sys.onInterrupt: SIGINT and SIGTERM arrive as bytes on a descriptor, and the program goes on", run := fun _ =>
        sysRun ["fd ← Sys.onInterrupt", "me ← EIO.lift Process.id",
          r#"s ← Process.run "kill" ["-INT", Nat.toString me]"#,
          "ok ← Fd.readableWithin fd (Duration.seconds 5)", "say (yesNo ok)",
          "b ← Fd.read fd 1", r#"say (match b with | .some x => Bytes.show x | .none => "end")"#,
          r#"s2 ← Process.run "kill" ["-TERM", Nat.toString me]"#,
          "b2 ← Fd.read fd 1", r#"say (match b2 with | .some x => Bytes.show x | .none => "end")"#,
          "fd2 ← Sys.onInterrupt", "ok2 ← Fd.readableWithin fd2 (Duration.millis 50)", "say (yesNo ok2)",
          r#"say "still running""#]
          "yes\n[2]\n[15]\nno\nstill running\n"
          sysRunnerShow },
    { name := "Process.spawnInCgroup: a missing cgroup is an error naming the command", run := fun _ =>
        sysRun [r#"r ← EIO.lift (Process.spawnInCgroup "true" .nil SpawnOptions.default "/nonexistent/cg")"#,
          r#"say (match r with | .ok _ => "spawned?" | .error m => m)"#]
          "true: No such file or directory\n"
          sysRunnerShow },
    { name := "Process.spawnInCgroup: the child (and what it starts) is in the cgroup (needs WIZ_TEST_CGROUP, a delegated cgroup)", run := fun _ => do
        let some cg ← IO.getEnv "WIZ_TEST_CGROUP"
          | skip "no delegated cgroup (set WIZ_TEST_CGROUP to a writable cgroup v2 directory)"
        let rel := match cg.splitOn "/sys/fs/cgroup" with
          | ["", r] => r
          | _ => cg
        sysRun [r#"c ← Process.spawnInCgroup "sh" ["-c", "cat /proc/self/cgroup"] (SpawnOptions.withStdio .null .piped .inherit SpawnOptions.default) ""# ++ cg ++ "\"",
          "out ← Child.readStdout c", "st ← Child.wait c",
          "say (yesNo (String.endsWith (String.trim out) \"" ++ rel ++ "\"))"]
          "yes\n"
          ("import Text\n" ++ sysRunnerShow) }
  ]

builtin_initialize registerGroup sysRunnerGroup

end Tests.Elab
