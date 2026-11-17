import Tests.Grail

namespace Tests.Grail
open Wiz Tests

/-- A package: a library with two modules, and a file that checks against it. -/
def pkgFiles : List (String × String) :=
  [("grail.wiz", "import Grail\ndef package : Package := Package.new \"demo\"\n  |> Package.lib \"mylib\" \"src\"\n  |> Package.check \"app\" \"app.wiz\"\n"),
   ("src/Demo/Two.wiz", "import Prelude\ndef two : Nat := 2\n"),
   ("src/Demo/Three.wiz", "import Prelude\ndef three : Nat := 3\n"),
   ("app.wiz", "import Demo.Two\n#eval two + two\n")]

/-- Run `grail build app` in a package directory through this driver's grail (a child
process, so its jobs are separate processes too). -/
def grailBuild (dir : System.FilePath) (flags : List String) : IO IO.Process.Output := do
  let self ← IO.appPath
  let args := #["--grail", "-C", dir.toString] ++ flags.toArray ++ #["build", "app"]
  IO.Process.output { cmd := self.toString, args }

/-- (9f) An executable with a `link_c` file: editing the C file relinks it (only). -/
def linkCCase : Case :=
    { name := "an executable with link_c: a C edit reruns the link only", run := fun _ => do
        let tc : Toolchain := { (← toolchain) with cacheDir := some (← IO.FS.createTempDir) }
        let dir ← mkTree [("grail.wiz", "import Grail\ndef package : Package := Package.new \"p\" |> Package.exe \"hi\" \"app/hi.wiz\"\n"),
                          ("app/hi.wiz", "import IO\nlink_c \"hi.c\"\nextern \"hi_num\" hiNum : IO Nat\n" ++
                             "def main : IO Unit := do\n  n ← hiNum;\n  IO.println (Nat.toString n)\n"),
                          ("app/hi.c", "#include <stdint.h>\nuint64_t hi_num(void) { return 1; }\n")]
        let (s, ok) ← build dir tc
        if !ok then
          skip "no toolchain"
          return
        checkEq 3 s.ran
        let exe := (dir / ".grail" / "bin" / "hi").toString
        checkEq "1\n" (← IO.Process.output { cmd := exe }).stdout
        let (s, _) ← build dir tc
        checkEq 0 s.ran
        IO.FS.writeFile (dir / "app" / "hi.c") "#include <stdint.h>\nuint64_t hi_num(void) { return 2; }\n"
        let (s, _) ← build dir tc
        checkEq 1 s.ran
        checkEq "2\n" (← IO.Process.output { cmd := exe }).stdout
        -- a deleted file: the check reruns and says so
        IO.FS.removeFile (dir / "app" / "hi.c")
        let (_, ok, log) ← buildLog dir tc
        check (!ok) "built without its C file"
        check ((log.splitOn "link_c: no file hi.c").length > 1) s!"no error for the missing file:\n{log}" }

/-- `grail lsp` (this test driver's sibling `grail`) in `dir`: the diagnostics of `file`
after an initialize and a didOpen; `none` if there is no grail binary. -/
def grailLspDiagnostics (dir : System.FilePath) (file : String) : IO (Option (List String)) := do
  let grail := ((← IO.appPath).parent.getD ".") / "grail"
  unless ← grail.pathExists do return none
  let cache ← IO.FS.createTempDir
  let args := #["-C", dir.toString, "--cache", cache.toString, "lsp"]
  let child ← IO.Process.spawn { cmd := grail.toString, args, stdin := .piped, stdout := .piped, stderr := .piped }
  let (stdin, child) ← child.takeStdin
  let input := IO.FS.Stream.ofHandle stdin
  let output := IO.FS.Stream.ofHandle child.stdout
  -- a time limit that doesn't keep the test's process alive once the test is done
  let done ← IO.mkRef false
  let _ ← IO.asTask (prio := .dedicated) do
    for _ in [0:1200] do
      if ← done.get then return
      IO.sleep 100
    child.kill
  let path ← IO.FS.realPath (dir / file)
  let uri := s!"file://{path}"
  LSP.writeMessage input (Lean.Json.mkObj [("jsonrpc", "2.0"), ("id", (1 : Nat)), ("method", "initialize"),
    ("params", Lean.Json.mkObj [("capabilities", Lean.Json.mkObj [])])])
  LSP.writeMessage input (Lean.Json.mkObj [("jsonrpc", "2.0"), ("method", "textDocument/didOpen"),
    ("params", Lean.Json.mkObj [("textDocument", Lean.Json.mkObj [("uri", uri), ("languageId", "wiz"),
      ("version", (1 : Nat)), ("text", ← IO.FS.readFile path)])])])
  let mut diags := none
  repeat
    let some m ← LSP.readMessage output | break
    if LSP.getStr m ["method"] == "textDocument/publishDiagnostics" then
      let ds := match LSP.get? m ["params", "diagnostics"] with
        | some (.arr ds) => ds.toList.map (LSP.getStr · ["message"])
        | _ => []
      diags := some ds
      break
  done.set true
  child.kill
  let _ ← child.wait
  match diags with
  | some ds => pure (some ds)
  | none => throw (IO.userError s!"grail lsp ended without diagnostics: {← child.stderr.readToEnd}")

def grailLspCase : Case :=
    { name := "grail lsp: the server knows the package's modules", run := fun _ => do
        let dir ← mkTree (pkgFiles ++ [("main.wiz", "import Demo.Two
#eval two
")])
        let some ds ← grailLspDiagnostics dir "main.wiz"
          | skip "no grail beside the test driver; lake build grail"
        check (ds.any (· == "2")) s!"diagnostics: {ds}"
        check (!ds.any fun d => (d.splitOn "unknown module").length > 1) s!"diagnostics: {ds}"
        -- a broken grail.wiz: the server still starts, with the package directory as a root
        IO.FS.writeFile (dir / "grail.wiz") "import Grail\ndef package : Package := 3\n"
        IO.FS.writeFile (dir / "Root.wiz") "import Prelude\ndef r : Nat := 5\n"
        IO.FS.writeFile (dir / "main.wiz") "import Root\n#eval r\n"
        let some ds ← grailLspDiagnostics dir "main.wiz" | return
        check (ds.any (· == "5")) s!"diagnostics with a broken grail.wiz: {ds}" }

def grailGroup : Group where
  name := "grail"
  exercise := "Stage 23d"
  cases := [
    { name := "the build file is Wiz", run := fun _ => do
        let dir ← mkTree (pkgFiles ++ [("grail.local.wiz", "import Grail\ndef settings : Settings := Settings.empty |> Settings.set \"cflags\" \"-I \\\"x\\\"\"\n")])
        let cache ← IO.FS.createTempDir
        match ← Grail.readConfig { cacheDir := some cache } (← binId { cacheDir := some cache }) "lib" dir with
        | .error e => throw (IO.userError e)
        | .ok (pkg, localSettings) =>
          checkEq "demo" pkg.name
          check (pkg.targets == [Grail.Target.lib "mylib" "src", .check "app" "app.wiz"]) s!"targets: {repr pkg.targets}"
          checkEq [("cflags", "-I \"x\"")] localSettings },
    { name := "a second build runs no jobs", run := fun _ => do
        let dir ← mkTree pkgFiles
        let tc : Toolchain := { cacheDir := some (← IO.FS.createTempDir) }
        let (s1, ok1) ← build dir tc
        check ok1 "the first build failed"
        checkEq 3 s1.ran
        let (s2, ok2) ← build dir tc
        check ok2 "the second build failed"
        checkEq 0 s2.ran
        checkEq 3 s2.upToDate },
    { name := "--cache-ro is forwarded; a build replays from a read-only cache", run := fun _ => do
        let dir ← mkTree pkgFiles
        let self ← IO.appPath
        -- config: the read caches are rendered in order, then the write cache
        let ro1 ← IO.FS.createTempDir
        let ro2 ← IO.FS.createTempDir
        let w ← IO.FS.createTempDir
        let cfgArgs := #["--grail", "-C", dir.toString, "--cache-ro", ro1.toString,
                         "--cache-ro", ro2.toString, "--cache", w.toString, "config"]
        let cfg ← IO.Process.output { cmd := self.toString, args := cfgArgs }
        checkEq 0 cfg.exitCode
        check ((cfg.stdout.splitOn s!"cache-ro {ro1}\ncache-ro {ro2}\ncache {w}\n").length > 1) cfg.stdout
        -- a warm cache, written by a build through this binary
        let warm ← IO.FS.createTempDir
        let (_, ok) ← build dir ({ cacheDir := some warm } : Toolchain) ["app"]
        check ok "the warm build failed"
        -- a fresh package: only the read-only cache and an empty write cache
        let dir2 ← mkTree pkgFiles
        let write ← IO.FS.createTempDir
        let buildArgs := #["--grail", "-C", dir2.toString, "--cache-ro", warm.toString,
                           "--cache", write.toString, "build", "app"]
        let out ← IO.Process.output { cmd := self.toString, args := buildArgs }
        checkEq 0 out.exitCode
        check ((out.stdout.splitOn "jobs run").length > 1) s!"{out.stdout}{out.stderr}" },
    { name := "grail build --region-cache: jobs write regions, and a warm build matches the text cache", run := fun _ => do
        let cache ← IO.FS.createTempDir
        -- the text-only reference, in its own package tree
        let text ← mkTree pkgFiles
        let o0 ← grailBuild text ["--cache", cache.toString]
        checkEq 0 o0.exitCode
        checkEq 0 (← regionFiles cache).size
        -- a first region build: each package module's effects become one .wizr
        let cold ← mkTree pkgFiles
        let o1 ← grailBuild cold ["--cache", cache.toString, "--region-cache"]
        checkEq 0 o1.exitCode
        check ((← regionFiles cache).size > 0) "the region build wrote no .wizr"
        -- a warm region build in a fresh tree: the same report and job keys as the text build
        let warm ← mkTree pkgFiles
        let o2 ← grailBuild warm ["--cache", cache.toString, "--region-cache"]
        checkEq 0 o2.exitCode
        checkEq o0.stdout o2.stdout
        checkEq (← buildDirs text) (← buildDirs warm) },
    { name := "grail build --region-cache: a corrupt region falls back, and a read-only layer serves regions", run := fun _ => do
        let cache ← IO.FS.createTempDir
        let dir ← mkTree pkgFiles
        let o0 ← grailBuild dir ["--cache", cache.toString, "--region-cache"]
        checkEq 0 o0.exitCode
        let regs ← regionFiles cache
        check (regs.size > 0) "no regions were written"
        -- corrupt every region: the text entries answer and the region is rewritten
        for f in regs do IO.FS.writeFile f ""
        let dir2 ← mkTree pkgFiles
        let o1 ← grailBuild dir2 ["--cache", cache.toString, "--region-cache"]
        checkEq 0 o1.exitCode
        checkEq o0.stdout o1.stdout
        for f in ← regionFiles cache do
          check ((← f.metadata).byteSize > 0) s!"{f} was not rewritten"
        -- a read-only cache serves regions: the fresh write cache gets none, and `ro` is untouched
        let ro ← IO.FS.createTempDir
        let roPkg ← mkTree pkgFiles
        let o2 ← grailBuild roPkg ["--cache", ro.toString, "--region-cache"]
        checkEq 0 o2.exitCode
        check ((← regionFiles ro).size > 0) "no region was written to the read-only source"
        let before ← snapshot ro
        let write ← IO.FS.createTempDir
        let pkg ← mkTree pkgFiles
        let o3 ← grailBuild pkg ["--cache-ro", ro.toString, "--cache", write.toString, "--region-cache"]
        checkEq 0 o3.exitCode
        checkEq o0.stdout o3.stdout
        checkEq before (← snapshot ro)
        checkEq 0 (← regionFiles write).size },
    { name := "an edit reruns the checks that depend on it", run := fun _ => do
        let dir ← mkTree pkgFiles
        let tc : Toolchain := { cacheDir := some (← IO.FS.createTempDir) }
        let _ ← build dir tc
        IO.FS.writeFile (dir / "src/Demo/Two.wiz") "import Prelude\ndef two : Nat := 1 + 1\n"
        let (s, ok) ← build dir tc
        check ok "the build failed"
        -- Demo.Two and app.wiz; not Demo.Three
        checkEq 2 s.ran
        checkEq 1 s.upToDate },
    { name := "a failed check is reported and not recorded", run := fun _ => do
        let dir ← mkTree (pkgFiles.map fun (p, t) => if p == "app.wiz" then (p, "import Demo.Two\ndef bad : Nat := true\n") else (p, t))
        let tc : Toolchain := { cacheDir := some (← IO.FS.createTempDir) }
        let (s, ok) ← build dir tc ["app"]
        check (!ok) "the build succeeded"
        checkEq 1 s.failed
        let (s, _) ← build dir tc ["app"]
        checkEq 1 s.failed
        -- nothing half-written is left
        let tmp := dir / ".grail" / "tmp"
        if ← tmp.pathExists then checkEq 0 (← tmp.readDir).size },
    { name := "an executable: build (check, IR and C in one job), object, link", run := fun _ => do
        let tc : Toolchain := { (← toolchain) with cacheDir := some (← IO.FS.createTempDir) }
        let dir ← mkTree [("grail.wiz", "import Grail\ndef package : Package := Package.new \"p\" |> Package.exe \"hello\" \"hello.wiz\"\n"),
                          ("hello.wiz", "import IO\ndef main : IO Unit := IO.println \"hello from grail\"\n")]
        let (s, ok) ← build dir tc
        if !ok then
          skip "no toolchain"
          return
        checkEq 3 s.ran
        let out ← IO.Process.output { cmd := (dir / ".grail" / "bin" / "hello").toString }
        checkEq "hello from grail\n" out.stdout
        let (s, _) ← build dir tc
        checkEq 0 s.ran
        -- a change that doesn't change the program's code: only the one build job reruns
        IO.FS.writeFile (dir / "hello.wiz") "import IO\n-- a comment\ndef main : IO Unit := IO.println \"hello from grail\"\n"
        let (s, _) ← build dir tc
        checkEq 1 s.ran
        checkEq 2 s.upToDate },
    linkCCase,
    grailLspCase
  ]

builtin_initialize registerGroup grailGroup

end Tests.Grail
