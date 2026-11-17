import Tests.Grail

namespace Tests.Grail
open Wiz Tests

/-! ## Command targets (23i), `grail run` (23j), job hygiene (23k) -/

/-- A package of commands: `upper` makes `build/up.txt` from `src/in.txt` (through a
shell), `copy` copies it (an edge by path), `show` (phony) prints it. -/
def cmdGrail (extra : String := "") : String :=
  "import Grail\ndef package : Package := Package.new \"c\"\n" ++
  "  |> Package.command (Command.new \"upper\" (Tool.path \"sh\") |> Command.arg \"-c\" |> Command.arg \"tr a-z A-Z < \\\"$1\\\"\" |> Command.arg \"sh\" |> Command.input \"src/in.txt\" |> Command.stdout \"build/up.txt\")\n" ++
  "  |> Package.command (Command.new \"copy\" (Tool.path \"cp\") |> Command.input \"build/up.txt\" |> Command.output \"build/copy.txt\")\n" ++
  "  |> Package.phony (Command.new \"show\" (Tool.path \"cat\") |> Command.input \"build/copy.txt\")\n" ++ extra

def cmdFiles (extra : String := "") : List (String × String) :=
  [("grail.wiz", cmdGrail extra), ("src/in.txt", "hello\n")]

def grailCommandsGroup : Group where
  name := "grail-commands"
  exercise := "Stage 23i–j, 23o"
  cases := [
    { name := "commands chain through their outputs; a second build runs nothing", run := fun _ => do
        let dir ← mkTree (cmdFiles)
        let tc ← cmdTc
        let (s, ok, log) ← buildLog dir tc ["upper", "copy"]
        check ok log
        checkEq 2 s.ran
        checkEq "[command upper]\n[command copy]\n" log
        checkEq "HELLO\n" (← IO.FS.readFile (dir / "build/copy.txt"))
        let (s, ok, _) ← buildLog dir tc ["copy"]
        check ok "the second build failed"
        checkEq 0 s.ran
        checkEq 2 s.upToDate },
    { name := "an edit reruns; going back and deleting an output restore it from the store", run := fun _ => do
        let dir ← mkTree (cmdFiles)
        let tc ← cmdTc
        let _ ← buildLog dir tc ["copy"]
        IO.FS.writeFile (dir / "src/in.txt") "world\n"
        let (s, _, _) ← buildLog dir tc ["copy"]
        checkEq 2 s.ran
        checkEq "WORLD\n" (← IO.FS.readFile (dir / "build/copy.txt"))
        IO.FS.writeFile (dir / "src/in.txt") "hello\n"
        let (s, _, _) ← buildLog dir tc ["copy"]
        checkEq 0 s.ran
        checkEq "HELLO\n" (← IO.FS.readFile (dir / "build/copy.txt"))
        IO.FS.removeFile (dir / "build/copy.txt")
        IO.FS.writeFile (dir / "build/up.txt") "changed by hand\n"
        let (s, _, _) ← buildLog dir tc ["copy"]
        checkEq 0 s.ran
        checkEq "HELLO\n" (← IO.FS.readFile (dir / "build/copy.txt"))
        checkEq "HELLO\n" (← IO.FS.readFile (dir / "build/up.txt")) },
    { name := "the tool's identity and the command line are in the key", run := fun _ => do
        let script := "#!/bin/sh\necho one > \"$1\"\n"
        let g (arg : String) := "import Grail\ndef package : Package := Package.new \"c\"\n" ++
          s!"  |> Package.command (Command.new \"t\" (Tool.path \"./tool.sh\") |> Command.output \"out.txt\" |> Command.arg \"{arg}\")\n"
        let dir ← mkTree [("grail.wiz", g "a"), ("tool.sh", script)]
        IO.setAccessRights (dir / "tool.sh") { user := { read := true, write := true, execution := true } }
        let tc ← cmdTc
        let (s, ok, log) ← buildLog dir tc
        check ok log
        checkEq 1 s.ran
        checkEq "one\n" (← IO.FS.readFile (dir / "out.txt"))
        IO.FS.writeFile (dir / "tool.sh") "#!/bin/sh\necho two > \"$1\"\n"
        let (s, _, _) ← buildLog dir tc
        checkEq 1 s.ran
        checkEq "two\n" (← IO.FS.readFile (dir / "out.txt"))
        IO.FS.writeFile (dir / "grail.wiz") (g "b")
        let (s, _, _) ← buildLog dir tc
        checkEq 1 s.ran },
    { name := "outputs are checked: declared but not made, made but not declared, declared twice", run := fun _ => do
        let liar := "  |> Package.command (Command.new \"liar\" (Tool.path \"sh\") |> Command.arg \"-c\" |> Command.arg \"touch \\\"$1\\\"x\" |> Command.arg \"sh\" |> Command.output \"build/l.txt\")\n"
        let dir ← mkTree (cmdFiles liar)
        let (s, ok, log) ← buildLog dir (← cmdTc) ["liar"]
        check (!ok) "the build succeeded"
        checkEq 1 s.failed
        check (has log "the declared output build/l.txt was not made") log
        check (has log "build/l.txtx was made in the output directory but is not a declared output") log
        check (!(← (dir / "build/l.txtx").pathExists)) "the undeclared file was installed"
        let twice := "  |> Package.command (Command.new \"again\" (Tool.path \"cp\") |> Command.input \"src/in.txt\" |> Command.output \"build/up.txt\")\n"
        let dir ← mkTree (cmdFiles twice)
        let (_, ok, log) ← buildLog dir (← cmdTc) ["copy"]
        check (!ok) "the build succeeded"
        check (has log "commands upper and again both declare the output build/up.txt") log
        let missing := "  |> Package.command (Command.new \"m\" (Tool.path \"cp\") |> Command.input \"src/nope.txt\" |> Command.output \"o.txt\")\n"
        let dir ← mkTree (cmdFiles missing)
        let (_, ok, log) ← buildLog dir (← cmdTc) ["m"]
        check (!ok) "the build succeeded"
        check (has log "the input src/nope.txt does not exist, and no target makes it") log },
    { name := "a failed command says how it ended, with the end of its log", run := fun _ => do
        let bad := "  |> Package.command (Command.new \"bad\" (Tool.path \"sh\") |> Command.arg \"-c\" |> Command.arg \"echo working; echo oops >&2; kill -9 $$\")\n"
        let dir ← mkTree (cmdFiles bad)
        let (_, ok, log) ← buildLog dir (← cmdTc) ["bad"]
        check (!ok) "the build succeeded"
        check (has log "✗ command bad\n  killed by signal 9 (SIGKILL: out of memory, or killed by hand?); the end of its output:\n  working\n  oops\n") log
        check (has (← IO.FS.readFile (dir / ".grail/log/bad.txt")) "oops") "no log file"
        -- a job (a check) killed with nothing to say: no longer an empty message
        checkEq "killed by signal 9 (SIGKILL: out of memory, or killed by hand?), and printed nothing"
          (Grail.failureMessage { code := 137, stdout := "", stderr := "" } 1000)
        checkEq "exit code 3; the end of its output:\nx"
          (Grail.failureMessage { code := 3, stdout := "x\n", stderr := "" } 1000)
        -- a check's own error (exit 1) is its messages, as before
        checkEq "f.wiz:1:1: error: e\n" (Grail.failureMessage { code := 1, stdout := "", stderr := "f.wiz:1:1: error: e\n" } 1000) },
    { name := "a phony command always runs, is not recorded, and is not a default target", run := fun _ => do
        let dir ← mkTree (cmdFiles)
        let tc ← cmdTc
        let (s, ok, log) ← buildLog dir tc ["show"]
        check ok log
        checkEq 3 s.ran
        check (has log "[command show]\nHELLO\n") log
        let (s, _, _) ← buildLog dir tc ["show"]
        checkEq 1 s.ran
        checkEq 2 s.upToDate
        match ← Grail.readConfig tc (← binId tc) "lib" dir with
        | .error e => throw (IO.userError e)
        | .ok (pkg, _) => checkEq ["upper", "copy"] ((pkg.targets.filter (·.isDefault)).map (·.name)) },
    { name := "stale installed outputs are removed (changed ones kept); grail clean", run := fun _ => do
        let dir ← mkTree (cmdFiles)
        let tc ← cmdTc
        let _ ← buildLog dir tc ["copy"]
        IO.FS.writeFile (dir / "grail.wiz") ((cmdGrail).replace "build/copy.txt" "build/copy2.txt")
        let (_, ok, log) ← buildLog dir tc ["copy"]
        check ok log
        check (has log "removed build/copy.txt (installed by an earlier build; no target makes it any more)") log
        check (!(← (dir / "build/copy.txt").pathExists)) "the stale output is still there"
        IO.FS.writeFile (dir / "build/copy2.txt") "mine\n"
        let ctx : Grail.Ctx := { dir, std := "lib", tc, binId := 0 }
        let report ← Grail.cleanInstalled ctx
        check (has report "kept build/copy2.txt: changed since grail installed it") report
        check (has report "removed build/up.txt") report
        checkEq "mine\n" (← IO.FS.readFile (dir / "build/copy2.txt"))
        check (!(← (dir / "build/up.txt").pathExists)) "grail clean left an installed output" },
    { name := "grail run: a command's needs are built, its arguments appended, its exit code returned", run := fun _ => do
        let ex := "  |> Package.command (Command.new \"exit\" (Tool.path \"sh\") |> Command.arg \"-c\" |> Command.arg \"test -f build/copy.txt && exit $1\" |> Command.arg \"sh\" |> Command.needs \"build/copy.txt\")\n"
        let dir ← mkTree (cmdFiles ex)
        let tc ← cmdTc
        match ← Grail.readConfig tc (← binId tc) "lib" dir with
        | .error e => throw (IO.userError e)
        | .ok (pkg, _) =>
          let log ← IO.mkRef ""
          let r ← runner dir tc pkg 1 log
          let some t := pkg.targets.find? (·.name == "exit") | throw (IO.userError "no target")
          checkEq 7 (← r.runTarget pkg.targets t #["7"])
          checkEq "[command upper]\n[command copy]\n" (← log.get) },
    { name := "an exe of the package as a command's tool", run := fun _ => do
        let tc : Toolchain := { (← toolchain) with cacheDir := some (← IO.FS.createTempDir) }
        let dir ← mkTree [("grail.wiz", "import Grail\ndef package : Package := Package.new \"p\" |> Package.exe \"hello\" \"hello.wiz\"\n" ++
                            "  |> Package.command (Command.new \"say\" (Tool.exe \"hello\") |> Command.stdout \"said.txt\")\n"),
                          ("hello.wiz", "import IO\ndef main : IO Unit := IO.println \"hello from grail\"\n")]
        let (s, ok, log) ← buildLog dir tc ["say"]
        if !ok && (has log "obj") then
          skip "no toolchain"
          return
        check ok log
        checkEq 4 s.ran
        checkEq "hello from grail\n" (← IO.FS.readFile (dir / "said.txt"))
        -- a comment: the program is rebuilt as far as its C, which doesn't change
        IO.FS.writeFile (dir / "hello.wiz") "import IO\n-- c\ndef main : IO Unit := IO.println \"hello from grail\"\n"
        let (s, _, _) ← buildLog dir tc ["say"]
        checkEq 1 s.ran },
    { name := "an installed output keeps its executable bit", run := fun _ => do
        let mk := "  |> Package.command (Command.new \"script\" (Tool.path \"sh\") |> Command.arg \"-c\" |> Command.arg \"printf '#!/bin/sh\\\\necho ran\\\\n' > \\\"$1\\\"; chmod +x \\\"$1\\\"; echo data > \\\"$2\\\"\" |> Command.arg \"sh\" |> Command.output \"bin/run.sh\" |> Command.output \"bin/data.txt\")\n"
        let dir ← mkTree (cmdFiles mk)
        let (_, ok, log) ← buildLog dir (← cmdTc) ["script"]
        check ok log
        checkEq "ran\n" (← IO.Process.output { cmd := (dir / "bin/run.sh").toString }).stdout
        check (← Grail.isExecutable (dir / "bin/run.sh")) "the script is not executable"
        check (!(← Grail.isExecutable (dir / "bin/data.txt"))) "the data file is executable" },
    { name := "two targets with one name are refused", run := fun _ => do
        let dir ← mkTree [("grail.wiz", "import Grail\ndef package : Package := Package.new \"p\" |> Package.lib \"x\" \"src\" |> Package.check \"x\" \"a.wiz\"\n")]
        let tc ← cmdTc
        match ← Grail.readConfig tc (← binId tc) "lib" dir with
        | .ok _ => throw (IO.userError "accepted")
        | .error e => check (has e "two targets are called x") e },
    { name := "new: the generated package builds, runs and tests; a non-empty directory is refused", run := fun _ => do
        let root ← IO.FS.createTempDir
        let self ← IO.appPath
        let grail (args : List String) : IO (UInt32 × String × String) := do
          let o ← IO.Process.output { cmd := self.toString, args := ("--grail" :: args).toArray }
          pure (o.exitCode, o.stdout, o.stderr)
        let demo := root / "demo"
        let (c, out, _) ← grail ["new", "demo", "--dir", demo.toString]
        checkEq 0 c
        check (has out "grail new: wrote") out
        for f in ["grail.wiz", "src/Main.wiz", "README.md", ".gitignore", "tests/hello.wiz", "tests/hello.expected"] do
          check (← (demo / f).pathExists) s!"missing {f}"
        checkEq ".grail/\n" (← IO.FS.readFile (demo / ".gitignore"))
        -- never overwrite a non-empty directory, and check the name
        let (c2, _, err2) ← grail ["new", "demo", "--dir", demo.toString]
        checkEq 1 c2
        check (has err2 "is not empty") err2
        let (c3, _, err3) ← grail ["new", "9bad", "--dir", (root / "x").toString]
        checkEq 1 c3
        check (has err3 "is not a package name") err3
        -- build, run and test it with the suite's toolchain flags (as `nix develop` writes them)
        let tc ← toolchain
        let (c4, _, err4) ← grail (tc.toFlags ++ ["-C", demo.toString, "build"])
        if c4 != 0 && (has err4 "could not execute external process" || has err4 "gmp.h") then
          skip "no toolchain"
          return
        checkEq 0 c4
        let (c5, out5, _) ← grail (tc.toFlags ++ ["-C", demo.toString, "run", "demo"])
        checkEq 0 c5
        check (has out5 "hello from demo") out5
        let (c6, out6, err6) ← grail (tc.toFlags ++ ["-C", demo.toString, "test"])
        checkEq 0 c6
        check (has out6 "1 passed, 0 failed") (out6 ++ err6) }
  ]

builtin_initialize registerGroup grailCommandsGroup

end Tests.Grail
