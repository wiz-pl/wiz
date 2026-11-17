import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-- A `Sys` program, on the C backend and on the LLVM backend: `body` is the lines of an
`EIO` do block. -/
def sysRun (body : List String) (expected : String) (defs : String := "") (cflags : List String := []) : IO Unit := do
  let src := "import Sys\n" ++ defs ++ "def main : IO Unit := EIO.toIO (do\n" ++
    ";\n".intercalate (body.map ("  " ++ ·)) ++ ")"
  ioRun src expected (cflags := cflags)
  ioRun src expected (llvm := true) (cflags := cflags)

def sysBytesCases : List Case := [
    { name := "bytes: slices, lists and explicit encodings", run := fun _ =>
        sysRun ["let all := Bytes.range 256", "say (Nat.toString (Bytes.size all))",
          "say (Bytes.show (Bytes.slice all 250 10))",
          "say (Bytes.show (Bytes.append (Bytes.take all 3) (Bytes.drop all 254)))",
          "say (yesNo (Bytes.eq (Bytes.ofList (Bytes.toList all)) all))",
          r#"let u := Bytes.ofUtf8 (String.append "aλ✓" (String.append (String.mk (.cons (Char.mk 0) .nil)) "𝄞"))"#,
          "say (Bytes.show u)", "say (Nat.toString (Bytes.size (Bytes.ofUtf8 (utf8 u))))",
          "say (utf8 all)", "say (utf8 (Bytes.ofList (.cons 237 (.cons 160 (.cons 128 .nil)))))",
          "say (utf8 (Bytes.ofList (.cons 192 (.cons 128 .nil))))",
          r#"say (match Bytes.ofLatin1 (Bytes.toLatin1 all) with | .ok b => yesNo (Bytes.eq b all) | .error e => e)"#,
          r#"say (match Bytes.ofLatin1 "aλ" with | .ok b => "?" | .error e => e)"#,
          r#"say (match Bytes.at all 300 with | .some x => "?" | .none => "none")"#]
          ("256\n[250, 251, 252, 253, 254, 255]\n[0, 1, 2, 254, 255]\nyes\n[97, 206, 187, 226, 156, 147, 0, 240, 157, 132, 158]\n11\n" ++
           "invalid UTF-8 at byte 128\ninvalid UTF-8 at byte 0\ninvalid UTF-8 at byte 0\nyes\nnot Latin-1: character 1 is U+955\nnone\n")
          sysBytesShow },
    { name := "descriptors: every byte value through a pipe, end of file, a time limit", run := fun _ =>
        sysRun ["p ← Fd.pipe", "let all := Bytes.range 256", "Fd.write p.2 all", "Fd.write p.2 all",
          "g ← Fd.readExactly p.1 256", "say (gotShow all g)",
          "h ← Fd.readExactlyWithin p.1 256 (Duration.seconds 5)", "say (gotShow all h)",
          "t0 ← EIO.lift Clock.monotonic", "r ← Fd.readWithin p.1 10 (Duration.millis 200)",
          "t1 ← EIO.lift Clock.monotonic",
          r#"say (match r with | .timedOut => "timed out" | .ready _ => "data?")"#,
          "say (yesNo (Duration.lt (Duration.millis 150) (Duration.sub t1 t0)))",
          "ok ← Fd.readableWithin p.1 (Duration.millis 10)", "say (yesNo ok)",
          "Fd.write p.2 (Bytes.take all 5)",
          "k ← Fd.readExactlyWithin p.1 10 (Duration.millis 100)", "say (gotShow all k)",
          "Fd.write p.2 (Bytes.take all 3)", "Fd.close p.2",
          "e ← Fd.readExactly p.1 10", "say (gotShow all e)",
          r#"z ← Fd.read p.1 10"#, r#"say (match z with | .none => "end" | .some _ => "data?")"#,
          "Fd.close p.1", "c ← EIO.lift (Fd.close p.1)",
          r#"say (match c with | .ok _ => "closed twice?" | .error m => m)"#,
          "q ← EIO.lift (Fd.read p.1 1)", r#"say (match q with | .ok _ => "read?" | .error m => m)"#]
          ("all yes\nall yes\ntimed out\nyes\nno\ntimeout after 5\neof after 3\nend\nclose: Bad file descriptor\nread: Bad file descriptor\n")
          sysBytesShow },
    { name := "files: bytes, seek, the end", run := fun _ =>
        sysRun ["d ← FS.createTempDir", "f ← File.open (Path.join d \"bin\") \"w+\"",
          "File.writeBytes f (Bytes.range 256)", "n ← File.seek f (.start 250)", "say (Nat.toString n)",
          r#"b ← File.readBytes f 100"#, r#"say (match b with | .some x => Bytes.show x | .none => "end")"#,
          r#"b2 ← File.readBytes f 100"#, r#"say (match b2 with | .some x => Bytes.show x | .none => "end")"#,
          "m ← File.seek f (.fromEnd 3)", "say (Nat.toString m)", "n2 ← File.seek f (.back 1)",
          r#"b3 ← File.readBytes f 2"#, r#"say (match b3 with | .some x => Bytes.show x | .none => "end")"#,
          "File.close f", "x ← FS.readBytes (Path.join d \"bin\")", "say (yesNo (Bytes.eq x (Bytes.range 256)))",
          "g ← Fd.open (Path.join d \"bin\") .read OpenFlags.none", "n3 ← Fd.seek g (.start 254)",
          "y ← Fd.readExactly g 4", "say (gotShow x y)", "FS.removeAll d"]
          "250\n[250, 251, 252, 253, 254, 255]\nend\n253\n[252, 253]\nyes\neof after 2\n"
          sysBytesShow },
    { name := "spawn options: directory, environment, process groups, try-wait", run := fun _ =>
        sysRun [r#"Env.set "WIZ_T_HOME" "set""#, r#"o ← Process.outputWith "sh" (.cons "-c" (.cons "pwd; echo $A $B; echo ${WIZ_T_HOME:-unset}" .nil)) "" (SpawnOptions.default |> SpawnOptions.inDir "/" |> SpawnOptions.setEnv "A" "x" |> SpawnOptions.setEnv "B" "y" |> SpawnOptions.setEnv "A" "z" |> SpawnOptions.unsetEnv "WIZ_T_HOME")"#,
          "EIO.lift (IO.print o.stdout)",
          r#"e ← Process.outputWith "/usr/bin/env" .nil "" (SpawnOptions.default |> SpawnOptions.emptyEnv |> SpawnOptions.setEnv "ONLY" "1")"#,
          "EIO.lift (IO.print e.stdout)",
          r#"c ← Process.spawnWith "sh" (.cons "-c" (.cons "sleep 30 & sleep 30; true" .nil)) (SpawnOptions.default |> SpawnOptions.withGroup .newGroup)"#,
          r#"w ← Child.tryWait c"#, r#"say (match w with | .none => "running" | .some s => ExitStatus.toString s)"#,
          "Child.killGroup c 15", "s ← Child.wait c", "say (ExitStatus.toString s)",
          r#"w2 ← Child.tryWait c"#, r#"say (match w2 with | .none => "running" | .some s => ExitStatus.toString s)"#,
          r#"r ← Process.runWith "true" .nil (SpawnOptions.default |> SpawnOptions.withGroup .newSession)"#,
          "say (ExitStatus.toString r)"]
          "/\nz y\nunset\nONLY=1\nrunning\nsignal 15\nsignal 15\nexit code 0\n"
          sysBytesShow },
    -- (26f) spawning in a directory without posix_spawn_file_actions_addchdir_np (glibc
    -- < 2.29, as the release toolchain's sysroot): fork, chdir, exec; and its errors
    { name := "spawn in a directory: posix_spawn and the fork fallback (-DWIZ_NO_SPAWN_CHDIR)", run := fun _ => do
        let body := [r#"o ← Process.outputWith "sh" (.cons "-c" (.cons "pwd; echo $A" .nil)) "" (SpawnOptions.default |> SpawnOptions.inDir "/" |> SpawnOptions.setEnv "A" "x")"#,
          "EIO.lift (IO.print o.stdout)",
          r#"p ← Process.outputWith "pwd" .nil "" (SpawnOptions.default |> SpawnOptions.inDir "/tmp")"#,
          "EIO.lift (IO.print p.stdout)",
          r#"c ← Process.spawnWith "sh" (.cons "-c" (.cons "read x; echo got $x; pwd" .nil)) (SpawnOptions.default |> SpawnOptions.inDir "/" |> SpawnOptions.withStdio .piped .piped .inherit |> SpawnOptions.withGroup .newGroup)"#,
          r#"Child.write c "line\n""#, "Child.closeStdin c", "out ← Child.readStdout c", "EIO.lift (IO.print out)",
          "s ← Child.wait c", "say (ExitStatus.toString s)",
          r#"r ← EIO.lift (Process.spawnWith "pwd" .nil (SpawnOptions.default |> SpawnOptions.inDir "/wiz-no-such-dir"))"#,
          r#"say (match r with | .ok c => "spawned" | .error e => e)"#,
          r#"q ← EIO.lift (Process.spawnWith "wiz-no-such-program" .nil (SpawnOptions.default |> SpawnOptions.inDir "/"))"#,
          r#"say (match q with | .ok c => "spawned" | .error e => e)"#]
        let want := "/\nx\n/tmp\ngot line\n/\nexit code 0\npwd: No such file or directory\nwiz-no-such-program: No such file or directory\n"
        sysRun body want sysBytesShow
        sysRun body want sysBytesShow (cflags := ["-DWIZ_NO_SPAWN_CHDIR"]) },
    { name := "poll, and a child's pipe as a descriptor", run := fun _ =>
        sysRun ["a ← Fd.pipe", "z ← Fd.pipe",
          "r0 ← Fd.poll (.cons (a.1, .readable) (.cons (z.1, .readable) .nil)) (Duration.millis 50)",
          r#"say (String.append "poll: " (showR r0))"#, r#"Fd.writeUtf8 z.2 "hi""#, "Fd.close a.2",
          "r1 ← Fd.poll (.cons (a.1, .readable) (.cons (z.1, .readable) .nil)) (Duration.millis 50)",
          r#"say (String.append "poll: " (showR r1))"#,
          r#"ch ← Process.spawn "echo" (.cons "piped" .nil) .null .piped .null"#,
          "out ← Child.takePipe ch 1", "rr ← Fd.readWithin out 100 (Duration.seconds 5)",
          r#"say (match rr with | .ready (.some x) => utf8 x | _ => "?")"#,
          "st ← Child.wait ch", "say (ExitStatus.toString st)",
          r#"again ← EIO.lift (Child.readStdout ch)"#, r#"say (match again with | .ok _ => "?" | .error m => m)"#,
          "Fd.close z.1", "Fd.close a.1", "Fd.close z.2"]
          "poll: \npoll: 0noyes;1yesno;\npiped\n\nexit code 0\nread child stdout: Bad file descriptor\n"
          sysBytesShow },
    { name := "paths and clocks", run := fun _ =>
        sysRun ["d ← FS.createTempDir", "FS.writeFile (Path.join d \"f\") \"x\"",
          r#"FS.symlink "f" (Path.join d "l")"#,
          r#"a ← FS.realPath (Path.join d "l")"#,
          r#"b ← FS.realPath (Path.join (Path.join d ".") "f")"#, "say (yesNo (strEq a b))",
          r#"m ← EIO.lift (FS.realPath "/nonexistent/x")"#, r#"say (match m with | .ok _ => "?" | .error e => e)"#,
          "p ← IO.appPath", "s ← FS.stat p", "say (match s.kind with | .file => \"file\" | _ => \"?\")",
          "w ← EIO.lift Clock.wall", "say (yesNo (Nat.lt 1700000000 (Nat.div w.ns 1000000000)))",
          "t0 ← EIO.lift Clock.monotonic", "EIO.lift (Clock.sleep (Duration.millis 20))", "t1 ← EIO.lift Clock.monotonic",
          "say (yesNo (Duration.lt (Duration.millis 19) (Duration.sub t1 t0)))", "FS.removeAll d"]
          "yes\n/nonexistent/x: No such file or directory\nfile\nyes\nyes\n"
          (sysBytesShow ++ "def chEq : List Char → List Char → Bool\n  | .nil, .nil => .true\n  | .cons a xs, .cons b ys => Bool.and (Nat.beq (Char.code a) (Char.code b)) (chEq xs ys)\n  | _, _ => .false\n" ++
            "def strEq : String → String → Bool\n  | .mk a, .mk b => chEq a b\n") },
    -- (rtffi-03) `Fd.adopt` does not narrow the Nat: 2^32 + 1 is not fd 1 (stdout)
    { name := "Fd.adopt rejects a number above INT_MAX instead of wrapping it", run := fun _ =>
        sysRun ["x ← EIO.lift (Fd.adopt 4294967297)", "e ← EIO.lift (Fd.closeRaw x)",
          r#"say (match Sys.status "close" e with | .ok _ => "closed?" | .error m => m)"#,
          "say \"stdout still open\""]
          "close: Bad file descriptor\nstdout still open\n" sysShow }
  ]

/-- (rtffi-04) A C shim: cap the address space at the current size plus `margin` bytes
(Linux `/proc/self/statm`), and put the old soft limit back. The hard limit is untouched. -/
def capShim : String :=
  "#define _GNU_SOURCE\n#include <stdint.h>\n#include <stdio.h>\n#include <unistd.h>\n" ++
  "#include <sys/resource.h>\n" ++
  "static struct rlimit wiz_cap_saved;\nstatic int wiz_cap_have = 0;\n" ++
  "uint64_t rtffi_test_cap(uint64_t margin) {\n" ++
  "  FILE *f = fopen(\"/proc/self/statm\", \"r\");\n  unsigned long pages = 0;\n" ++
  "  if (!f) return 1;\n" ++
  "  if (fscanf(f, \"%lu\", &pages) != 1) { fclose(f); return 1; }\n" ++
  "  fclose(f);\n" ++
  "  if (getrlimit(RLIMIT_AS, &wiz_cap_saved) < 0) return 1;\n" ++
  "  wiz_cap_have = 1;\n" ++
  "  struct rlimit r = wiz_cap_saved;\n" ++
  "  r.rlim_cur = (rlim_t)pages * (rlim_t)sysconf(_SC_PAGESIZE) + (rlim_t)margin;\n" ++
  "  return setrlimit(RLIMIT_AS, &r) == 0 ? 0 : 1;\n}\n" ++
  "uint64_t rtffi_test_uncap(void) {\n" ++
  "  return wiz_cap_have && setrlimit(RLIMIT_AS, &wiz_cap_saved) == 0 ? 0 : 1;\n}\n"

/-- (rtffi-06) A C shim for `readdir`: fail the (n+1)-th call with `EIO`, then pass through
again (`rtffi_test_readdir_ok` stops the failure early). -/
def readdirShim : String :=
  "#define _GNU_SOURCE\n#include <stdint.h>\n#include <dirent.h>\n#include <dlfcn.h>\n" ++
  "#include <errno.h>\n" ++
  "static struct dirent *(*wiz_real_readdir)(DIR *) = 0;\nstatic long wiz_fail_after = -1;\n" ++
  "static struct dirent *wiz_readdir(DIR *d) {\n" ++
  "  if (!wiz_real_readdir) wiz_real_readdir = (struct dirent *(*)(DIR *))dlsym(RTLD_NEXT, \"readdir\");\n" ++
  "  if (wiz_fail_after >= 0) {\n" ++
  "    if (wiz_fail_after == 0) { wiz_fail_after = -1; errno = EIO; return 0; }\n" ++
  "    wiz_fail_after--;\n  }\n" ++
  "  return wiz_real_readdir ? wiz_real_readdir(d) : 0;\n}\n" ++
  "struct dirent *readdir(DIR *d) { return wiz_readdir(d); }\n" ++
  "struct dirent64 *readdir64(DIR *d) { return (struct dirent64 *)wiz_readdir(d); }\n" ++
  "uint64_t rtffi_test_readdir_fail(uint64_t n) { wiz_fail_after = (long)n; return 0; }\n" ++
  "uint64_t rtffi_test_readdir_ok(void) { wiz_fail_after = -1; return 0; }\n"

def sysGroup : Group where
  name := "sys"
  exercise := "Stage 9h"
  cases := [
    { name := "spawn echo and collect its output", run := fun _ =>
        sysRun ["o ← Process.output \"echo\" (.cons \"hello\" (.cons \"world\" .nil)) \"\"",
          "EIO.lift (IO.print o.stdout)", "say (ExitStatus.toString o.status)",
          "say (yesNo (ExitStatus.success o.status))"]
          "hello world\nexit code 0\nyes\n" sysShow },
    { name := "a pipe through cat, and stderr apart", run := fun _ =>
        sysRun ["o ← Process.output \"cat\" .nil \"piped through cat\\nline two\\n\"", "EIO.lift (IO.print o.stdout)",
          "e ← Process.output \"sh\" (.cons \"-c\" (.cons \"echo out; echo err >&2; exit 3\" .nil)) \"\"",
          "say (String.append \"stdout: \" e.stdout)", "say (String.append \"stderr: \" e.stderr)",
          "say (ExitStatus.toString e.status)"]
          "piped through cat\nline two\nstdout: out\n\nstderr: err\n\nexit code 3\n" sysShow },
    { name := "communicate doesn't deadlock on big output", run := fun _ =>
        -- 200 KB on stdout and 100 KB on stderr: more than a pipe buffer each
        sysRun ["o ← Process.output \"sh\" (.cons \"-c\" (.cons \"yes abcdefghi | head -c 200000; yes x | head -c 100000 >&2\" .nil)) \"\"",
          "say (Nat.toString (strLen o.stdout))", "say (Nat.toString (strLen o.stderr))"]
          "200000\n100000\n" (sysShow ++ "def strLen : String → Nat\n  | .mk cs => List.length cs\n") },
    { name := "a child, step by step", run := fun _ =>
        sysRun ["c ← Process.spawn \"cat\" .nil .piped .piped .inherit", "Child.write c \"one\\n\"",
          "Child.write c \"two\\n\"", "Child.closeStdin c", "out ← Child.readStdout c", "EIO.lift (IO.print out)",
          "st ← Child.wait c", "say (ExitStatus.toString st)",
          "k ← Process.spawn \"sleep\" (.cons \"10\" .nil) .null .null .null", "Child.kill k 9",
          "ks ← Child.wait k", "say (ExitStatus.toString ks)",
          "r ← Process.run \"true\" .nil", "say (ExitStatus.toString r)"]
          "one\ntwo\nexit code 0\nsignal 9\nexit code 0\n" sysShow },
    { name := "spawning a missing program is an error", run := fun _ =>
        sysRun ["r ← EIO.lift (Process.spawn \"wiz-no-such-program\" .nil .null .null .null)",
          "say (match r with | .ok c => \"spawned\" | .error e => e)"]
          "wiz-no-such-program: No such file or directory\n" sysShow },
    { name := "environment variables round-trip", run := fun _ =>
        sysRun ["Env.set \"WIZ_SYS_TEST\" \"v1\"", "a ← EIO.lift (Env.get \"WIZ_SYS_TEST\")", "say (orUnset a)",
          "Env.set \"WIZ_SYS_TEST\" \"v2 = λ\"", "b ← EIO.lift (Env.get \"WIZ_SYS_TEST\")", "say (orUnset b)",
          "all ← EIO.lift Env.list", "say (orUnset (lookup all))",
          "o ← Process.output \"sh\" (.cons \"-c\" (.cons \"echo $WIZ_SYS_TEST\" .nil)) \"\"", "EIO.lift (IO.print o.stdout)",
          "Env.unset \"WIZ_SYS_TEST\"", "c ← EIO.lift (Env.get \"WIZ_SYS_TEST\")", "say (orUnset c)",
          "r ← EIO.lift (Env.set \"A=B\" \"x\")", "say (match r with | .ok u => \"set\" | .error e => e)"]
          "v1\nv2 = λ\nv2 = λ\nv2 = λ\n(unset)\nsetenv A=B: Invalid argument\n"
          (sysShow ++ "def chEq : List Char → List Char → Bool\n  | .nil, .nil => .true\n  | .cons a xs, .cons b ys => Bool.and (Nat.beq (Char.code a) (Char.code b)) (chEq xs ys)\n  | _, _ => .false\n" ++
            "def strEq : String → String → Bool\n  | .mk a, .mk b => chEq a b\n" ++ "def lookup : List (String × String) → Option String\n  | .nil => .none\n" ++
            "  | .cons (k, v) rest => match strEq k \"WIZ_SYS_TEST\" with\n    | .true => .some v\n    | .false => lookup rest\n") },
    { name := "a temporary directory: files, links, stat, listing, removal", run := fun _ =>
        sysRun ["d ← FS.createTempDir", "FS.createDir (Path.join d \"sub\")",
          "FS.writeFile (Path.join d \"a.txt\") \"alpha\\n\"", "FS.appendFile (Path.join d \"a.txt\") \"beta\\n\"",
          "FS.rename (Path.join d \"a.txt\") (Path.join d \"b.txt\")", "FS.symlink \"b.txt\" (Path.join d \"link\")",
          "FS.writeFile (Path.join (Path.join d \"sub\") \"deep\") \"x\"",
          "t ← FS.readLink (Path.join d \"link\")", "say t",
          "xs ← FS.listDir d", "say (showList xs)",
          "s ← FS.stat (Path.join d \"link\")", "say (Nat.toString s.size)",
          "l ← FS.linkStat (Path.join d \"link\")", "say (match l.kind with | .symlink => \"link\" | _ => \"not a link\")",
          "say (yesNo (Nat.lt 1600000000 s.mtime))",
          "txt ← FS.readFile (Path.join d \"link\")", "EIO.lift (IO.print txt)",
          "a ← EIO.lift (FS.isDir (Path.join d \"sub\"))", "b ← EIO.lift (FS.isFile (Path.join d \"sub\"))",
          "say (String.append (yesNo a) (yesNo b))",
          "r ← EIO.lift (FS.removeDir (Path.join d \"sub\"))", "say (match r with | .ok u => \"removed\" | .error e => \"not empty\")",
          "FS.setMode (Path.join d \"b.txt\") 384", "m ← FS.stat (Path.join d \"b.txt\")", "say (Nat.toString m.mode)",
          "FS.removeFile (Path.join d \"link\")", "ys ← FS.listDir d", "say (showList ys)",
          "FS.removeAll d", "e ← EIO.lift (FS.exists d)", "say (yesNo e)"]
          "b.txt\nb.txt;link;sub;\n11\nlink\nyes\nalpha\nbeta\nyesno\nnot empty\n384\nb.txt;sub;\nno\n" sysShow },
    { name := "the working directory", run := fun _ =>
        sysRun ["d ← FS.createTempDir", "FS.setCurrentDir d", "FS.writeFile \"here.txt\" \"hi\"",
          "c ← FS.currentDir", "x ← FS.readFile (Path.join c \"here.txt\")", "say x",
          "o ← Process.output \"ls\" .nil \"\"", "EIO.lift (IO.print o.stdout)",
          "FS.setCurrentDir \"/\"", "FS.removeAll d"]
          "hi\nhere.txt\n" sysShow },
    { name := "errors carry errno messages", run := fun _ =>
        sysRun ["r ← EIO.lift (FS.readFile \"/nonexistent/x\")", "say (match r with | .ok s => s | .error m => m)",
          "q ← EIO.lift (FS.listDir \"/nonexistent\")", "say (match q with | .ok s => \"listed\" | .error m => m)",
          "w ← EIO.lift (FS.createDir \"/\")", "say (match w with | .ok s => \"made\" | .error m => m)"]
          "/nonexistent/x: No such file or directory\n/nonexistent: No such file or directory\n/: File exists\n" sysShow },
    { name := "file handles and bytes", run := fun _ =>
        sysRun ["d ← FS.createTempDir", "let p := Path.join d \"f.txt\"",
          "f ← File.open p \"w\"", "File.write f \"first\\n\"", "File.write f \"second\\n\"", "File.close f",
          "g ← File.open p \"r\"", "a ← File.readLine g", "b ← File.readLine g", "c ← File.readLine g",
          "say (String.append (orUnset a) (String.append \",\" (String.append (orUnset b) (String.append \",\" (orUnset c)))))",
          "FS.writeBytes (Path.join d \"bin\") (Bytes.push (Bytes.push (Bytes.push Bytes.empty 0) 255) 7)",
          "bs ← FS.readBytes (Path.join d \"bin\")",
          "say (String.append (Nat.toString (Bytes.size bs)) (String.append \" \" (Nat.toString (Bytes.get bs 1))))",
          "o ← EIO.lift File.stdout", "File.write o \"to stdout\\n\"", "File.flush o",
          "FS.removeAll d"]
          "first,second,(unset)\n3 255\nto stdout\n" sysShow },
    -- (rtffi-01) `Process.exec` sets SIGPIPE to its default action for the program it
    -- replaces; when `exec` fails it must put this program's ignore back, or the next
    -- write to a pipe with no reader kills the process instead of returning EPIPE.
    { name := "a failed exec leaves SIGPIPE ignored: a write to a dead child is EPIPE", run := fun _ =>
        sysRun ["c ← Process.spawn \"cat\" .nil .piped .piped .inherit", "Child.kill c 9",
          "st ← Child.wait c", "say (ExitStatus.toString st)",
          "r1 ← EIO.lift (Child.write c \"x\")",
          "say (match r1 with | .ok _ => \"wrote?\" | .error m => m)",
          "e ← EIO.lift (Process.exec \"wiz-no-such-program\" .nil)",
          "say (match e with | .ok _ => \"exec?\" | .error m => m)",
          "r2 ← EIO.lift (Child.write c \"y\")",
          "say (match r2 with | .ok _ => \"wrote?\" | .error m => m)"]
          ("signal 9\nwrite to child: Broken pipe\nwiz-no-such-program: No such file or directory\n" ++
           "write to child: Broken pipe\n") sysShow },
    -- (rtffi-02) a `File` handle is close-on-exec: the child does not inherit it
    { name := "File.open is close-on-exec: a child does not see the handle", run := fun _ =>
        sysRun ["d ← FS.createTempDir", "let p := Path.join d \"leak.txt\"",
          "FS.writeFile p \"x\"", "f ← File.open p \"r\"",
          r#"o ← Process.outputWith "sh" (.cons "-c" (.cons "ls -l /proc/self/fd | grep -c -F $WIZ_T_FILE" .nil)) "" (SpawnOptions.default |> SpawnOptions.setEnv "WIZ_T_FILE" p)"#,
          "EIO.lift (IO.print o.stdout)", "File.close f", "FS.removeAll d"]
          "0\n" sysShow },
    -- (rtffi-08) `input` with no stdin pipe is an error, not silently dropped
    { name := "communicate without a stdin pipe reports the lost input", run := fun _ =>
        sysRun ["c ← Process.spawn \"cat\" .nil .null .piped .inherit",
          "r ← EIO.lift (Child.communicate c \"dropped input\")",
          "say (match r with | .ok _ => \"dropped?\" | .error m => m)",
          "o ← Child.readStdout c", "say (Nat.toString (strLen o))",
          "st ← Child.wait c", "say (ExitStatus.toString st)"]
          "communicate: Bad file descriptor\n0\nexit code 0\n"
          (sysShow ++ "def strLen : String → Nat\n  | .mk cs => List.length cs\n") },
    -- (rtffi-04) an allocation failure in `File.readAll` is `read: …`, not a SIGSEGV
    { name := "allocation failure in File.readAll is an error, not a crash", run := fun _ => do
        let files : List (String × String) :=
          [("main.wiz", "import Sys\nlink_c \"c/cap.c\"\n" ++ sysShow ++
            "extern \"rtffi_test_cap\" testCap : Nat → IO Nat\nextern \"rtffi_test_uncap\" testUncap : IO Nat\n" ++
            "def main : IO Unit := EIO.toIO (do\n" ++
            "  d ← FS.createTempDir;\n" ++
            "  let p := Path.join d \"big\";\n" ++
            "  o ← Process.output \"sh\" (.cons \"-c\" (.cons (String.append \"head -c 64000000 /dev/zero > \" p) .nil)) \"\";\n" ++
            "  say (ExitStatus.toString o.status);\n" ++
            "  n ← EIO.lift (testCap 2097152);\n" ++
            "  say (Nat.toString n);\n" ++
            "  f ← File.open p \"r\";\n" ++
            "  r ← EIO.lift (File.readAll f);\n" ++
            "  say (match r with | .ok _ => \"read?\" | .error m => m);\n" ++
            "  File.close f;\n" ++
            "  u ← EIO.lift testUncap;\n" ++
            "  say (Nat.toString u);\n" ++
            "  say \"survived\";\n" ++
            "  FS.removeAll d)\n"),
           ("c/cap.c", capShim)]
        let want := "exit code 0\n0\nread: Cannot allocate memory\n0\nsurvived\n"
        linkRun files want
        linkRun files want (llvm := true) },
    -- (rtffi-05) `IO.writeFile` writes the text up to the first NUL and reports a failure
    { name := "IO.writeFile: text up to a NUL, and a failure stops the program", run := fun _ => do
        let files : List (String × String) :=
          [("main.wiz", "import Sys\nimport Std\n" ++ sysShow ++
            "def main : IO Unit := EIO.toIO (do\n" ++
            "  d ← FS.createTempDir;\n" ++
            "  let p := Path.join d \"w.txt\";\n" ++
            "  EIO.lift (IO.writeFile p (String.append \"ab\" (String.append (String.mk (.cons (Char.mk 0) .nil)) \"cd\")));\n" ++
            "  b ← FS.readBytes p;\n" ++
            "  say (Nat.toString (Bytes.size b));\n" ++
            "  say (yesNo (Bytes.eq b (Bytes.ofUtf8 \"ab\")));\n" ++
            "  FS.removeAll d;\n" ++
            "  say \"done\")\n")]
        linkRun files "2\nyes\ndone\n"
        linkRun files "2\nyes\ndone\n" (llvm := true)
        let bad : List (String × String) :=
          [("main.wiz", "import Std\ndef main : IO Unit := do\n  IO.writeFile \"/nonexistent-dir/w\" \"x\";\n  IO.println \"after\"\n")]
        linkRunFails bad "/nonexistent-dir/w: No such file or directory"
        linkRunFails bad "/nonexistent-dir/w: No such file or directory" (llvm := true) },
    -- (rtffi-06) a `readdir` error is the listing's error, not the end of the directory
    { name := "FS.listDir reports a readdir error, not a truncated listing", run := fun _ => do
        let files : List (String × String) :=
          [("main.wiz", "import Sys\nlink_c \"c/readdir.c\"\nlink_lib \"dl\"\n" ++ sysShow ++
            "extern \"rtffi_test_readdir_fail\" failAfter : Nat → IO Nat\n" ++
            "extern \"rtffi_test_readdir_ok\" readdirOk : IO Nat\n" ++
            "def main : IO Unit := EIO.toIO (do\n" ++
            "  d ← FS.createTempDir;\n" ++
            "  FS.writeFile (Path.join d \"a\") \"x\";\n" ++
            "  FS.writeFile (Path.join d \"b\") \"x\";\n" ++
            "  FS.writeFile (Path.join d \"c\") \"x\";\n" ++
            "  n ← EIO.lift (failAfter 2);\n" ++
            "  say (Nat.toString n);\n" ++
            "  r ← EIO.lift (FS.listDir d);\n" ++
            "  say (match r with | .ok _ => \"listed?\" | .error _ => \"error\");\n" ++
            "  u ← EIO.lift readdirOk;\n" ++
            "  say (Nat.toString u);\n" ++
            "  xs ← FS.listDir d;\n" ++
            "  say (showList xs);\n" ++
            "  FS.removeAll d)\n"),
           ("c/readdir.c", readdirShim)]
        linkRun files "0\nerror\n0\na;b;c;\n"
        linkRun files "0\nerror\n0\na;b;c;\n" (llvm := true) },
    -- (rtffi-07) the owned release drains a piped stream before it waits
    { name := "spawnOwned + waitOwned drains 200 KB of piped output (no deadlock)", run := fun _ => do
        let files : List (String × String) :=
          [("main.wiz", "import Sys\nimport Handle\n" ++ sysShow ++
            "def main : IO Unit := EIO.toIO (do\n" ++
            "  s ← Process.spawnOwned \"sh\" (.cons \"-c\" (.cons \"yes abcdefghi | head -c 200000\" .nil)) .null .piped .inherit\n" ++
            "        (fun c o => Child.releaseOwned c o (fun r => IO.pure r));\n" ++
            "  say (ExitStatus.toString s))\n")]
        linkRun files "exit code 0\n"
        linkRun files "exit code 0\n" (llvm := true) }
  ] ++ sysBytesCases

builtin_initialize registerGroup sysGroup

end Tests.Elab
