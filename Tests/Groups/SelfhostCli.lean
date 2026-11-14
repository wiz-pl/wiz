import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-!
# The self-hosted toolchain's driver (stage 21, D2-D7)

The `selfhost` group tests the toolchain's language; this group tests its *command line*:
`selfhost/Cli.wiz`, the driver that `Wiz/Selfhost.compilerSource` puts after the parser
tables. The cases run the compiler binary built by `selfhostCompiler` (the same binary
the `selfhost` group uses, so a job builds it once) in a fresh directory.
-/

/-- Run the self-hosted compiler with `args` in a fresh directory holding `files`
(name → text; a name with a `/` makes the directory): the directory, its exit code, its
standard output and its standard error. -/
def cliRunDir (exe : System.FilePath) (files : Array (String × String)) (args : Array String) :
    IO (System.FilePath × UInt32 × String × String) := do
  let dir ← IO.FS.createTempDir
  for (name, text) in files do
    if let some sub := (System.FilePath.mk name).parent then IO.FS.createDirAll (dir / sub)
    IO.FS.writeFile (dir / name) text
  let out ← IO.Process.output { cmd := "timeout", args := #["120", exe.toString] ++ args, cwd := dir }
  pure (dir, out.exitCode, out.stdout, out.stderr)

/-- `cliRunDir`, without the directory. -/
def cliRun (exe : System.FilePath) (files : Array (String × String)) (args : Array String) :
    IO (UInt32 × String × String) := do
  let (_, c, out, err) ← cliRunDir exe files args
  pure (c, out, err)

/-- `want` occurs in `s`. -/
def cliHas (s want : String) : Bool := (s.splitOn want).length > 1

def cliCheck (s want msg : String) : IO Unit :=
  unless cliHas s want do throw (IO.userError s!"{msg}: {want} not in:\n{s}")

/-- The compiler, or a skip (no C toolchain) or the build's error. -/
def withSelfhostCli (k : System.FilePath → IO Unit) : IO Unit := do
  match ← selfhostCompiler with
  | .error e =>
    if (e.splitOn "gmp.h").length > 1 then skip "no toolchain" else throw (IO.userError e)
  | .ok exe => k exe

def cliHello : String := "import Prelude
def main : IO Unit := do
  IO.println \"hello from the selfhost driver\";
  IO.println (Nat.toString (Nat.add 40 2))
"

def cliGood : String := "import Prelude
def one : Nat := 1
def two : Nat := Nat.add one one
"

def cliBad : String := "import Prelude
def one : Nat := 1
def two : Nat := nope
"

/-- The `run` options for this checkout's C toolchain (garbage collector flags included);
`none` without a collector. -/
def cliRunOptions : IO (Option (Array String)) := do
  let tc ← toolchain
  if tc.gcCflags.isEmpty then return none
  return some (#["--rt", (← IO.currentDir) / "selfhost" |>.toString] ++
    #["--cflags", " ".intercalate tc.gcCflags] ++ #["--ldflags", " ".intercalate tc.gcLdflags])

def cliGroup : Group where
  name := "selfhost-cli"
  exercise := "stage 21 (D2-D7): the self-hosted driver"
  shard := "selfhost"
  cases := [
    { name := "usage: help and version print, exit 0", run := fun _ => withSelfhostCli fun exe => do
        let (c, out, _) ← cliRun exe #[] #["--help"]
        checkEq 0 c
        cliCheck out "wiz-selfhost check FILE" "help"
        let (c, out, _) ← cliRun exe #[] #["help"]
        checkEq 0 c
        cliCheck out "wiz-selfhost run FILE" "help"
        let want := s!"wiz-selfhost {Wiz.version}\n"
        let (c, out, _) ← cliRun exe #[] #["--version"]
        checkEq 0 c
        checkEq want out
        -- the same version from the subcommand (one source: `Wiz.Version.version`)
        let (c, out, _) ← cliRun exe #[] #["version"]
        checkEq 0 c
        checkEq want out },
    { name := "usage: an unknown command, an unknown option, a missing FILE: exit 2", run := fun _ =>
        withSelfhostCli fun exe => do
        let (c, _, err) ← cliRun exe #[] #["nonsense"]
        checkEq 2 c
        cliCheck err "unknown command nonsense" "unknown command"
        let (c, _, err) ← cliRun exe #[] #["check", "--bogus", "x.wiz"]
        checkEq 2 c
        cliCheck err "unknown option --bogus" "unknown option"
        let (c, _, err) ← cliRun exe #[] #["check"]
        checkEq 2 c
        cliCheck err "no FILE" "missing FILE"
        let (c, _, err) ← cliRun exe #[] #["check", "a.wiz", "b.wiz"]
        checkEq 2 c
        cliCheck err "check takes one FILE" "two files" },
    { name := "a missing file: one diagnostic, exit 1, no stack trace", run := fun _ =>
        withSelfhostCli fun exe => do
        let (c, out, err) ← cliRun exe #[] #["check", "no.wiz"]
        checkEq 1 c
        checkEq "" out
        checkEq "no.wiz:1:1: error: no such file\n" err },
    { name := "check reports diagnostics only; build writes the C", run := fun _ =>
        withSelfhostCli fun exe => do
        let files := #[("good.wiz", cliGood)]
        let (c, out, err) ← cliRun exe files #["check", "good.wiz"]
        checkEq 0 c
        checkEq "" out
        checkEq "" err
        -- `--types`: the frontend's own output, positioned
        let (c, out, _) ← cliRun exe files #["check", "good.wiz", "--types"]
        checkEq 0 c
        cliCheck out "good.wiz:2:1: info: one : Nat" "types"
        cliCheck out "good.wiz:3:1: info: two : Nat" "types"
        -- `build`: the C, to a file, and no C on standard output
        let (dir, c, out, _) ← cliRunDir exe #[("good.wiz", cliHello)] #["build", "good.wiz", "-o", "out.c"]
        checkEq 0 c
        checkEq "" out
        let ctext ← IO.FS.readFile (dir / "out.c")
        Tests.check (cliHas ctext "int main(") "build's C"
        Tests.check (cliHas ctext "/* main : ") "build's comments"
        -- an error: no file written, exit 1, the diagnostic on standard error
        let (dir, c, out, err) ← cliRunDir exe #[("bad.wiz", cliBad)] #["build", "bad.wiz", "-o", "out.c"]
        checkEq 1 c
        checkEq "" out
        cliCheck err "bad.wiz:3:1: error: unknown identifier nope" "build's diagnostic"
        unless !(← (dir / "out.c").pathExists) do throw (IO.userError "build wrote the C of a bad file") },
    { name := "run: the program's output, and -o keeps the C", run := fun _ => do
        match ← cliRunOptions with
        | none => skip "no garbage collector, --gc-cflags"
        | some opts => withSelfhostCli fun exe => do
          let cacheDir ← IO.FS.createTempDir
          let cache := (cacheDir / "c").toString
          let files := #[("prog.wiz", cliHello)]
          let (c, out, err) ← cliRun exe files (#["run", "prog.wiz", "--cache", cache] ++ opts)
          checkEq 0 c
          checkEq "hello from the selfhost driver\n42\n" out
          checkEq "" err
          -- `-o` keeps the C, and a second run is a warm cache hit
          let (dir, c, out, err) ← cliRunDir exe files (#["run", "prog.wiz", "-o", "kept.c", "--cache", cache] ++ opts)
          checkEq 0 c
          checkEq "hello from the selfhost driver\n42\n" out
          checkEq "" err
          let ctext ← IO.FS.readFile (dir / "kept.c")
          Tests.check (cliHas ctext "int main(") "run's -o C"
          let (_, c, out, err) ← cliRunDir exe files (#["run", "prog.wiz", "-v", "--cache", cache] ++ opts)
          checkEq 0 c
          checkEq "hello from the selfhost driver\n42\n" out
          cliCheck err "cache hit: " "run's warm cache" },
    { name := "-I: a module root, and a module's errors at its own position", run := fun _ =>
        withSelfhostCli fun exe => do
        let files := #[("lib/M.wiz", "import Prelude\ndef one : Nat := 1\n"), ("main.wiz", cliGood.replace "def one : Nat := 1" "import M")]
        -- without -I the module is not found (exit 1, `unknown-module`): the loader
        -- searches the -I roots and then the working directory, not the importer's
        let (c, _, err) ← cliRun exe files #["check", "main.wiz"]
        checkEq 1 c
        cliCheck err "main.wiz:2:1: error: cannot find module M [unknown-module]" "unknown module"
        -- with -I it is read, and both files' declarations are reported where they are
        let (c, out, err) ← cliRun exe files #["check", "-I", "lib", "main.wiz", "--types"]
        checkEq 0 c
        checkEq "" err
        cliCheck out "lib/M.wiz:2:1: info: one : Nat" "-I module"
        cliCheck out "main.wiz:3:1: info: two : Nat" "-I main"
        -- an error inside the module has the module's position
        let files := #[("lib/M.wiz", "import Prelude\ndef one : Nat := 1\ndef bad : Nat := nope\n"), ("main.wiz", "import Prelude\nimport M\ndef two : Nat := one\n")]
        let (c, _, err) ← cliRun exe files #["check", "-I", "lib", "main.wiz"]
        checkEq 1 c
        cliCheck err "lib/M.wiz:3:1: error: unknown identifier nope [unknown-identifier]" "module's position" },
    { name := "diagnostics: file:line:col, severity, a code", run := fun _ =>
        withSelfhostCli fun exe => do
        let (c, out, err) ← cliRun exe #[("bad.wiz", cliBad)] #["check", "bad.wiz"]
        checkEq 1 c
        checkEq "" out
        checkEq "bad.wiz:3:1: error: unknown identifier nope [unknown-identifier]\n" err
        -- a duplicate declaration
        let dup := "import Prelude\ndef one : Nat := 1\ndef one : Nat := 2\n"
        let (c, _, err) ← cliRun exe #[("dup.wiz", dup)] #["check", "dup.wiz"]
        checkEq 1 c
        cliCheck err "dup.wiz:3:1: error: 'one' has already been declared [duplicate-declaration]" "duplicate"
        -- the loader's errors carry their codes too
        let cyc := #[("c.wiz", "import Prelude\nimport D\n"), ("D.wiz", "import Prelude\nimport c\n")]
        let (c, _, err) ← cliRun exe cyc #["check", "c.wiz"]
        checkEq 1 c
        cliCheck err "c.wiz:2:1: error: import cycle: " "cycle position"
        cliCheck err "[import-cycle]" "cycle code"
        -- the parser's error, at the command that starts it
        let (c, _, err) ← cliRun exe #[("parse.wiz", "import Prelude\ndef one : Nat := 1\ndef two : Nat :=\n")] #["check", "parse.wiz"]
        checkEq 1 c
        cliCheck err "parse.wiz:3:1: error: " "parse position"
        cliCheck err "[parse-error]" "parse code" },
    { name := "the cache: cold, warm, then invalidated by an edit", run := fun _ =>
        withSelfhostCli fun exe => do
        -- (one cache directory across the runs: each run gets a fresh working directory)
        let cacheDir ← IO.FS.createTempDir
        let cache := (cacheDir / "c").toString
        let files := #[("c.wiz", cliGood)]
        let (c, _, err) ← cliRun exe files #["check", "c.wiz", "--cache", cache, "-v"]
        checkEq 0 c
        cliCheck err "cache miss: " "cold"
        let (c, _, err) ← cliRun exe files #["check", "c.wiz", "--cache", cache, "-v"]
        checkEq 0 c
        cliCheck err "cache hit: " "warm"
        unless !(cliHas err "error:") do throw (IO.userError s!"a warm run of a good file reports no diagnostics:\n{err}")
        -- an error is cached with its exit status, and replayed
        let (c, _, err) ← cliRun exe #[("c.wiz", cliBad)] #["check", "c.wiz", "--cache", cache, "-v"]
        checkEq 1 c
        cliCheck err "cache miss: " "cold after an edit"
        let (c, _, err) ← cliRun exe #[("c.wiz", cliBad)] #["check", "c.wiz", "--cache", cache, "-v"]
        checkEq 1 c
        cliCheck err "cache hit: " "warm error"
        cliCheck err "c.wiz:3:1: error: unknown identifier nope [unknown-identifier]" "replayed"
        -- `--no-cache` never reads the entry
        let (c, _, err) ← cliRun exe #[("c.wiz", cliGood)] #["check", "c.wiz", "--cache", cache, "--no-cache", "-v"]
        checkEq 0 c
        cliCheck err "cache miss: " "no-cache" },
    { name := "the one-shot mode (input.wiz to standard output) still works", run := fun _ =>
        withSelfhostCli fun exe => do
        let (c, out, _) ← cliRun exe #[("input.wiz", cliHello)] #[]
        checkEq 0 c
        cliCheck out "/* main : " "comments"
        cliCheck out "int main(" "C main"
        -- an error: the errors on standard error, no C, exit 1
        let (c, out, err) ← cliRun exe #[("input.wiz", "import Prelude\ndef bad : Nat := nope\n")] #[]
        checkEq 1 c
        checkEq "" out
        cliCheck err "error: unknown identifier nope" "one-shot error" }
  ]

builtin_initialize registerGroup cliGroup

end Tests.Elab
