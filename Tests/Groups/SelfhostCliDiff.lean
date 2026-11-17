import Tests.Elab
import Tests.Groups.SelfhostCli

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-!
# The self-hosted driver against the Lean-hosted `wiz` (stage 21, D2-D7)

`=selfhost-cli` tests the Wiz-hosted driver's own promises; this group runs **both**
toolchains over the same input tree in a fresh directory and compares what a user sees:
the exit code, standard output, standard error, the cache entries and the artifacts.
The cases are picked by what a user hits first — `check` on a bad file, `build` on a good
one, the cache flags — and by the driver items of the self-hosting parity audit, whose
labels the cases cite: D2 subcommands, D3 flags, D4 build artifacts, D5 the elaboration
cache, D6 diagnostics, D7 exit codes (and, for the skips, A14 modules, C5 the LLVM/IR
backends, C9 `--lib`/`--no-main`, C12 the native operations, D8 LSP/doc). The host's newer
flags are covered too: `--target c` works in both, `--target llvm|wasm` and
`--cache-verify strict` are the host's backend/manifest features the self-hosted
toolchain has not got (C5, D5), and each is an asserted skip rather than a silent pass.

## What "normalised" means here

The two frontends are different elaborators, so their *wording* differs (`unknown
identifier 'nope'` against `unknown identifier nope`) and the self-hosted one carries a
stable `[code]` the Lean-hosted CLI does not print (`Msg.render`). A diagnostic line

    file:line:col: severity: message [code]

is therefore compared as `file:line:col: severity: kind`, where `kind` is the code (or,
for the host, the same `ErrorCode` derived from its wording). Driver lines that are not
diagnostics (`unknown flag: …`, the version line) are compared verbatim, with
`wiz-selfhost` read as `wiz`. Two blocks are not compared:

* **the usage text** after a usage error (everything from the line that starts `usage`):
  the driver documents the subset it has (no `parse`/`doc`/`fmt`/`lsp`, no `--llvm`);
  the cases check the message line and the exit code, and the help case says so;
* **indented continuation lines** of a message (`type mismatch`'s `expected:` /
  `inferred:` lines), since the host's elaborator and the self-hosted one split a
  message differently.

`columns := false` compares `file:line` only: the self-hosted frontend reports what
failed at the start of its **command** (D6), the host at the failing term. Such a case
asserts the code, streams, line, severity and kind, then records a `skip` with the
reason — a difference that is known is never silent. A case whose artifact legitimately
differs (D4: `build` writes C, not an executable) asserts what it can and skips the same
way.

Every case gives both tools a private `HOME` (the default cache is `~/.cache/wiz` for
both), so the host's shared cache is never touched.
-/

/-- One tool's run in a directory. -/
structure CliDiffRun where
  dir : System.FilePath
  code : UInt32
  out : String
  err : String

/-- The same input for both tools. `hostArgs`/`shArgs` are the toolchain flags a
compiling command needs (the C compiler, GMP, the collector), which differ. -/
structure CliDiffSpec where
  files : Array (String × String) := #[]
  args : Array String := #[]
  hostArgs : Array String := #[]
  shArgs : Array String := #[]
  /-- Compare the diagnostic's column too (false: the self-hosted frontend's granularity) -/
  columns : Bool := true

/-- The Lean-hosted `wiz`, beside the test driver. -/
def cliDiffHost : IO System.FilePath := do
  let p := (← IO.appPath).parent.getD "." / "wiz"
  unless ← p.pathExists do
    throw (IO.userError s!"no wiz beside the test driver ({p}): lake build wiz tests")
  pure p

/-- The toolchain flags both `wiz build`/`wiz run` and the self-hosted `run` need. -/
def cliDiffHostToolchain : IO (Array String) := do
  let tc ← toolchain
  let mut a : Array String := #["--cc", tc.cc]
  if tc.llc != "llc" then a := a ++ #["--llc", tc.llc]
  if !tc.cflags.isEmpty then a := a ++ #["--cflags", " ".intercalate tc.cflags]
  if !tc.ldflags.isEmpty then a := a ++ #["--ldflags", " ".intercalate tc.ldflags]
  if !tc.libs.isEmpty then a := a ++ #["--libs", " ".intercalate tc.libs]
  if tc.gmp != ["-lgmp"] then a := a ++ #["--gmp", " ".intercalate tc.gmp]
  -- (the collector a `build`/`run` links: the suite's own child processes get these
  -- through `Toolchain.toFlags`, which also passes `--no-cache`; the cache cases need
  -- the host's cache, so the flags are spelled out here instead)
  if !tc.gcCflags.isEmpty then a := a ++ #["--gc-cflags", " ".intercalate tc.gcCflags]
  if !tc.gcLdflags.isEmpty then a := a ++ #["--gc-ldflags", " ".intercalate tc.gcLdflags]
  pure a

/-- A fresh working directory with `files` (a name with a `/` makes the directory) and a
private `home` (for `$HOME`). -/
def cliDiffInit (files : Array (String × String)) : IO System.FilePath := do
  let dir ← IO.FS.createTempDir
  for (name, text) in files do
    if let some sub := (System.FilePath.mk name).parent then IO.FS.createDirAll (dir / sub)
    IO.FS.writeFile (dir / name) text
  IO.FS.createDirAll (dir / "home")
  pure dir

/-- Run one tool in `dir` (its `HOME` is `dir/home`, which `cliDiffInit` made). -/
def cliDiffExec (exe : System.FilePath) (dir : System.FilePath) (extra : Array String)
    (args : Array String) : IO CliDiffRun := do
  let out ← IO.Process.output
    { cmd := "timeout", args := #["120", exe.toString] ++ extra ++ args, cwd := dir
      env := #[("HOME", some (dir / "home").toString)] }
  pure { dir, code := out.exitCode, out := out.stdout, err := out.stderr }

/-- Both tools on the same tree, each in its own directory. -/
def cliDiffBoth (host exe : System.FilePath) (spec : CliDiffSpec) :
    IO (CliDiffRun × CliDiffRun) := do
  let hdir ← cliDiffInit spec.files
  let sdir ← cliDiffInit spec.files
  let h ← cliDiffExec host hdir spec.hostArgs spec.args
  let s ← cliDiffExec exe sdir spec.shArgs spec.args
  pure (h, s)

/-- The tool's own name is the one deliberate difference in the text. -/
def cliDiffTool (l : String) : String := l.replace "wiz-selfhost" "wiz"

/-- Drop the usage block: from the first line that starts `usage` (the driver's subset). -/
def cliDiffBeforeUsage : List String → List String
  | [] => []
  | l :: rest => if l.startsWith "usage" then [] else l :: cliDiffBeforeUsage rest

/-- The Lean frontend's codes (`Wiz/Core/ErrorCode.lean`), for the host's wording. -/
def cliDiffCodes : List (String × String) :=
  [("has already been declared", "duplicate-declaration"),
   ("unknown identifier", "unknown-identifier"),
   ("is private to module", "private"),
   ("type mismatch", "type-mismatch"),
   ("no field ", "no-such-field"),
   ("cannot infer", "cannot-infer"),
   ("unknown declaration", "unknown-declaration"),
   ("unsupported command ", "unknown-syntax"),
   ("unsupported syntax ", "unknown-syntax"),
   ("cannot find module ", "unknown-module"),
   ("unknown module ", "unknown-module"),
   ("import cycle", "import-cycle"),
   ("no such file", "no-such-file")]

def cliDiffKindText (msg : String) : String :=
  match cliDiffCodes.find? (fun p => (msg.splitOn p.1).length > 1) with
  | some p => p.2
  | none =>
    -- (the two parsers word it differently: the host's "unexpected 'x'; expected 'y'"
    -- and the self-hosted frontend's "expected 'y'")
    if msg.startsWith "unexpected " || msg.startsWith "expected "
        || (msg.splitOn "; expected ").length > 1 then "parse-error"
    else msg

/-- A diagnostic's kind: its `[code]` when it has one, else the host's code for the
wording (and the wording itself when neither names a known kind, so an unexpected
difference fails the case). -/
def cliDiffKind (msg : String) : String :=
  let parts := msg.splitOn " ["
  match parts.reverse with
  | last :: _ =>
    if parts.length > 1 && last.endsWith "]" then (last.dropEnd 1).toString
    else cliDiffKindText msg
  | [] => cliDiffKindText msg

/-- One line, normalised: a diagnostic to `file:level: severity: kind` (or
`file:line:col: severity: kind`), anything else verbatim with the tool name unified. -/
def cliDiffLine (columns : Bool) (l : String) : String :=
  match l.splitOn ": " with
  | loc :: sev :: rest =>
    if rest.isEmpty || !(["error", "warning", "info"].contains sev) then cliDiffTool l
    else
      let msg := ": ".intercalate rest
      match loc.splitOn ":" with
      | [f, ln, col] =>
        if columns then s!"{f}:{ln}:{col}: {sev}: {cliDiffKind msg}"
        else s!"{f}:{ln}: {sev}: {cliDiffKind msg}"
      | _ => cliDiffTool l
  | _ => cliDiffTool l

/-- A stream, normalised (see the module docs). -/
def cliDiffNormal (columns : Bool) (s : String) : String :=
  let ls := cliDiffBeforeUsage (s.splitOn "\n")
  let ls := ls.filterMap fun l =>
    if l.isEmpty || l.startsWith "  " then none else some (cliDiffLine columns l)
  "\n".intercalate ls

def cliDiffOneStream (spec : CliDiffSpec) (name ho so : String) : IO Unit := do
  let hn := cliDiffNormal spec.columns ho
  let sn := cliDiffNormal spec.columns so
  unless hn == sn do
    throw (IO.userError s!"{name} differs (args {" ".intercalate spec.args.toList}):\n-- wiz\n{hn}\n-- wiz-selfhost\n{sn}\n-- raw wiz\n{ho}\n-- raw wiz-selfhost\n{so}")

/-- Compare a run of each tool: exit code, standard output, standard error. -/
def cliDiffSame (spec : CliDiffSpec) (h s : CliDiffRun) : IO Unit := do
  unless h.code == s.code do
    throw (IO.userError s!"exit code differs (args {" ".intercalate spec.args.toList}): wiz {h.code}, wiz-selfhost {s.code}\n-- wiz stdout\n{h.out}\n-- wiz stderr\n{h.err}\n-- wiz-selfhost stdout\n{s.out}\n-- wiz-selfhost stderr\n{s.err}")
  cliDiffOneStream spec "stdout" h.out s.out
  cliDiffOneStream spec "stderr" h.err s.err

/-- A file of a run, if it was produced. -/
def cliDiffRead (r : CliDiffRun) (name : String) : IO (Option String) := do
  let p := r.dir / name
  if ← p.pathExists then pure (some (← IO.FS.readFile p)) else pure none

/-- A file of a run as bytes (a `build` artifact is an executable, not UTF-8 text: the
host's `readFile` would refuse it). -/
def cliDiffReadBin (r : CliDiffRun) (name : String) : IO (Option ByteArray) := do
  let p := r.dir / name
  if ← p.pathExists then pure (some (← IO.FS.readBinFile p)) else pure none

/-- Does the artifact start like an executable (ELF, Mach-O, or a `#!` script)? -/
def cliDiffIsExe (b : ByteArray) : Bool :=
  let byteAt (i : Nat) (v : UInt8) := i < b.size && b.get! i == v
  (byteAt 0 0x7f && byteAt 1 0x45 && byteAt 2 0x4c && byteAt 3 0x46)      -- \x7fELF
    || (byteAt 0 0xcf && byteAt 1 0xfa && byteAt 2 0xed && byteAt 3 0xfe) -- Mach-O (64-bit, LE)
    || (byteAt 0 0xfe && byteAt 1 0xed && byteAt 2 0xfa && byteAt 3 0xce) -- Mach-O (64-bit, BE)
    || (byteAt 0 0x23 && byteAt 1 0x21)                                   -- #!

/-- Is the artifact a relocatable object (an ELF `ET_REL`, or a Mach-O `MH_OBJECT`)?
The host's `--lib` is `cc -c`, the driver's now too. -/
def cliDiffIsObject (b : ByteArray) : Bool :=
  let byteAt (i : Nat) (v : UInt8) := i < b.size && b.get! i == v
  -- ELF: e_type (2 bytes at 16, little-endian) is 1 for ET_REL
  (byteAt 0 0x7f && byteAt 1 0x45 && byteAt 2 0x4c && byteAt 3 0x46
    && byteAt 16 0x01 && byteAt 17 0x00)
    -- Mach-O 64-bit: filetype (4 bytes at 12) is 1 for MH_OBJECT
    || (byteAt 0 0xcf && byteAt 1 0xfa && byteAt 2 0xed && byteAt 3 0xfe
      && byteAt 12 0x01 && byteAt 13 0x00 && byteAt 14 0x00 && byteAt 15 0x00)

def cliDiffExists (r : CliDiffRun) (name : String) : IO Bool := (r.dir / name).pathExists

/-- The entries of a directory (0 when it does not exist). -/
def cliDiffEntries (p : System.FilePath) : IO Nat := do
  if ← p.isDir then pure (← p.readDir).size else pure 0

/-- (a cache is something both tools write; the entries' *names* differ: the host's are
per-module content-addressed `.wizc`, the driver's are one `.check`/`.c` per graph) -/
def cliDiffCacheEntries (r : CliDiffRun) (rel : String) : IO Nat := cliDiffEntries (r.dir / rel)

def cliParseFile : String := "import Prelude
def one : Nat := 1
def two : Nat := )
"

def cliDiffHello : String := "import Prelude
import IO
def main : IO Unit := do
  IO.println \"hello from the selfhost driver\";
  IO.println (Nat.toString (Nat.add 40 2))
"

def cliMissingModule : String := "import Prelude
import M
"

def cliMissingModuleUse : String := "import Prelude
import M
def two : Nat := one
"

def cliBadModule : String := "import Prelude
def one : Nat := 1
def bad : Nat := nope
"

def cliExports : String := "import Prelude
def square (n : Nat) : Nat := Nat.mul n n
export \"wiz_square\" square : Nat → Nat
"

def cliDiffGroup : Group where
  name := "selfhost-cli-diff"
  exercise := "stage 21 (D2-D7): the self-hosted driver against the Lean-hosted wiz"
  shard := "selfhost"
  cases := [
    { name := "check: a good file is silent, exit 0, in both", run := fun _ => withSelfhostCli fun exe => do
        let host ← cliDiffHost
        let spec : CliDiffSpec := { files := #[("good.wiz", cliGood)]
                                    args := #["check", "good.wiz"] }
        let (h, s) ← cliDiffBoth host exe spec
        cliDiffSame spec h s
        checkEq "" s.out
        checkEq "" s.err },
    { name := "check: `#check` prints an info line without --types in both", run := fun _ => withSelfhostCli fun exe => do
        let host ← cliDiffHost
        let src := "import Prelude\ndef two : Nat := Nat.add 1 1\n#check two\n"
        let spec : CliDiffSpec := { files := #[("f.wiz", src)], args := #["check", "f.wiz"] }
        let (h, s) ← cliDiffBoth host exe spec
        cliDiffSame spec h s
        checkEq 0 s.code
        checkEq "f.wiz:3:1: info: two : Nat\n" s.out },
    { name := "check: a parse error is at its token in both", run := fun _ => withSelfhostCli fun exe => do
        let host ← cliDiffHost
        let spec : CliDiffSpec := { files := #[("parse.wiz", cliParseFile)]
                                    args := #["check", "parse.wiz"] }
        let (h, s) ← cliDiffBoth host exe spec
        cliDiffSame spec h s
        checkEq 1 s.code
        checkEq "" s.out
        -- and at the end of the input (both report the position after the last token)
        let eof := "import Prelude\ndef one : Nat := 1\ndef two : Nat :=\n"
        let spec2 : CliDiffSpec := { files := #[("eof.wiz", eof)], args := #["check", "eof.wiz"] }
        let (h2, s2) ← cliDiffBoth host exe spec2
        cliDiffSame spec2 h2 s2
        checkEq 1 s2.code },
    { name := "check: a bad file has the same line, severity and kind (the column is the command's start)",
      run := fun _ => withSelfhostCli fun exe => do
        let host ← cliDiffHost
        -- unknown identifier and duplicate declaration: the host reports the failing term
        -- and the declared name, the self-hosted frontend the command's start (D6)
        let spec : CliDiffSpec := { files := #[("bad.wiz", cliBad)]
                                    args := #["check", "bad.wiz"] , columns := false }
        let (h, s) ← cliDiffBoth host exe spec
        cliDiffSame spec h s
        checkEq 1 s.code
        checkEq "bad.wiz:3:1: error: unknown identifier nope [unknown-identifier]\n" s.err
        let dup := "import Prelude\ndef one : Nat := 1\ndef one : Nat := 2\n"
        let spec2 : CliDiffSpec := { files := #[("dup.wiz", dup)], args := #["check", "dup.wiz"]
                                     columns := false }
        let (h2, s2) ← cliDiffBoth host exe spec2
        cliDiffSame spec2 h2 s2
        checkEq 1 s2.code
        -- (the host's message is identical; only the position differs)
        cliCheck s2.err "'one' has already been declared" "duplicate text"
        -- a type mismatch: the host's expected/inferred lines are indented and dropped
        let spec3 : CliDiffSpec := { files := #[("tm.wiz", "import Prelude\ndef bad : Nat := Bool.true\n")]
                                     args := #["check", "tm.wiz"], columns := false }
        let (h3, s3) ← cliDiffBoth host exe spec3
        cliDiffSame spec3 h3 s3
        checkEq 1 s3.code
        cliCheck s3.err "tm.wiz:2:1: error: type mismatch" "type mismatch"
        skip "column: the host reports the failing term and the declared name; the self-hosted frontend reports the command's start (D6)" },
    { name := "prelude surface: `import Prelude` alone carries `IO` in the self-hosted toolchain only", run := fun _ => withSelfhostCli fun exe => do
        let host ← cliDiffHost
        -- (the selfhost loader canonicalises `IO`/`Std`/`Sys` to its one embedded prelude,
        -- so `IO.println` resolves without `import IO`; the host has a module for it)
        let src := "import Prelude\ndef main : IO Unit := do\n  IO.println \"hi\"\n"
        let spec : CliDiffSpec := { files := #[("p.wiz", src)], args := #["check", "p.wiz"] }
        let (h, s) ← cliDiffBoth host exe spec
        checkEq 1 h.code
        cliCheck h.err "unknown identifier 'IO'" "the host's Prelude"
        checkEq 0 s.code
        checkEq "" s.err
        skip "prelude: the self-hosted Prelude is one embedded module that includes the IO natives, and `import IO` is canonicalised to it; the host's `lib/Prelude.wiz` has no `IO`, so a file that omits `import IO` compiles only there (A14/C12)" },
    { name := "usage: a missing FILE, extra arguments and an unknown command agree (exit 2)", run := fun _ => withSelfhostCli fun exe => do
        let host ← cliDiffHost
        for args in [#["check"], #["nonsense"], #["check", "--bogus", "x.wiz"],
                     #["check", "a.wiz", "b.wiz"], #["nonsense", "x.wiz"]] do
          let spec : CliDiffSpec := { args := args }
          let (h, s) ← cliDiffBoth host exe spec
          cliDiffSame spec h s
          checkEq 2 s.code },
    { name := "flags: --json does not exist in either (a usage error, exit 2)", run := fun _ => withSelfhostCli fun exe => do
        let host ← cliDiffHost
        -- (the toolchain has no JSON diagnostics: before or after the command, both
        -- tools name it as an unknown flag)
        for args in [#["--json", "check", "x.wiz"], #["check", "x.wiz", "--json"],
                     #["check", "x.wiz", "--version"]] do
          let spec : CliDiffSpec := { args := args }
          let (h, s) ← cliDiffBoth host exe spec
          cliDiffSame spec h s
          checkEq 2 s.code
          cliCheck s.err "unknown flag: " "unknown flag"
        -- (toolchain flags alone: the host's usage, exit 0; a value-taking flag's word
        -- is its value, never a command)
        for args in [#["--no-cache"], #["--cc", "cc"], #["-I", "."]] do
          let spec : CliDiffSpec := { files := #[("x.wiz", cliGood)], args := args }
          let (h, s) ← cliDiffBoth host exe spec
          cliDiffSame spec h s
          checkEq 0 s.code
          checkEq 0 h.code },
    { name := "--target c: both accept it, before or after the command, and reject a bad name alike", run := fun _ => withSelfhostCli fun exe => do
        let host ← cliDiffHost
        let files := #[("good.wiz", cliGood)]
        for args in [#["check", "good.wiz", "--target", "c"],
                     #["--target", "c", "check", "good.wiz"]] do
          let spec : CliDiffSpec := { files := files, args := args }
          let (h, s) ← cliDiffBoth host exe spec
          cliDiffSame spec h s
          checkEq 0 s.code
        -- (the host's `takeTarget` errors: the message alone, exit 1, in both)
        for args in [#["check", "good.wiz", "--target", "bogus"],
                     #["check", "good.wiz", "--target"]] do
          let spec : CliDiffSpec := { files := files, args := args }
          let (h, s) ← cliDiffBoth host exe spec
          cliDiffSame spec h s
          checkEq 1 s.code
          checkEq 1 h.code },
    { name := "--target llvm|wasm: the host selects the backend, the self-hosted one emits C only (C5)", run := fun _ => withSelfhostCli fun exe => do
        let host ← cliDiffHost
        let files := #[("good.wiz", cliGood)]
        for target in ["llvm", "wasm"] do
          let args := #["check", "good.wiz", "--target", target]
          let spec : CliDiffSpec := { files := files, args := args }
          let (h, s) ← cliDiffBoth host exe spec
          checkEq 0 h.code
          checkEq 1 s.code
          checkEq "" s.out
          cliCheck s.err s!"unsupported target {target}" "the driver's rejection"
        skip "backend: --target llvm/wasm selects LLVM/WebAssembly in the host (C5); the self-hosted backend emits C, so the driver refuses the name (exit 1) instead of silently building C" },
    { name := "--cache-verify: the modes are accepted and the outputs agree (strict cannot be a hit here)", run := fun _ => withSelfhostCli fun exe => do
        let host ← cliDiffHost
        let files := #[("cv.wiz", cliGood)]
        -- (off and warn: both read the entry; the output is the same warm or cold)
        -- (the `=` form is a *leading* flag in the host: as the last word its
        -- `parseFlags` leaves it over as an unknown flag, so it goes before `check`)
        for args in [#["check", "cv.wiz", "--cache", "c", "--cache-verify", "off"],
                     #["check", "cv.wiz", "--cache", "c", "--cache-verify", "warn"],
                     #["--cache-verify=strict", "check", "cv.wiz", "--cache", "c"]] do
          let spec : CliDiffSpec := { files := files, args := args }
          let (h, s) ← cliDiffBoth host exe spec
          cliDiffSame spec h s
          checkEq 0 s.code
        -- (an unknown mode: the message and exit 2 agree; the host prints no usage, and
        -- the driver's is not compared. Also with no command: the host validates the
        -- mode before its usage, and a flag's word is its value, not a command.)
        for args in [#["check", "cv.wiz", "--cache-verify", "bogus"],
                     #["--cache-verify", "bogus"]] do
          let spec : CliDiffSpec := { files := files, args := args }
          let (h, s) ← cliDiffBoth host exe spec
          cliDiffSame spec h s
          checkEq 2 s.code
          checkEq 2 h.code
          cliCheck s.err "--cache-verify: unknown mode bogus (off, warn, strict)" "the mode's error"
        skip "cache verification: the host writes output manifests, so a second `--cache-verify strict` run is a hit there; the self-hosted cache has none, so strict never trusts an entry (a miss, same output, no saved work) (D5)" },
    { name := "flags: a backend flag is not a `check` option in either (exit 2)", run := fun _ => withSelfhostCli fun exe => do
        let host ← cliDiffHost
        for args in [#["check", "--lib", "x.wiz"], #["check", "x.wiz", "-o", "out.c"],
                     #["check", "--rc", "x.wiz"]] do
          let spec : CliDiffSpec := { args := args }
          let (h, s) ← cliDiffBoth host exe spec
          cliDiffSame spec h s
          checkEq 2 s.code },
    { name := "-I: a module root is searched in both", run := fun _ => withSelfhostCli fun exe => do
        let host ← cliDiffHost
        let files := #[("lib/M.wiz", "import Prelude\ndef one : Nat := 1\n"),
                       ("main.wiz", "import Prelude\nimport M\ndef two : Nat := one\n")]
        let spec : CliDiffSpec := { files := files, args := #["check", "-I", "lib", "main.wiz"] }
        let (h, s) ← cliDiffBoth host exe spec
        cliDiffSame spec h s
        checkEq 0 s.code
        checkEq "" s.out
        -- the flags may come before the command, as in the host (`wiz -I src check f.wiz`)
        let spec2 : CliDiffSpec := { files := files, args := #["-I", "lib", "check", "main.wiz"] }
        let (h2, s2) ← cliDiffBoth host exe spec2
        cliDiffSame spec2 h2 s2
        checkEq 0 s2.code },
    { name := "-I: a missing module is at the import in both", run := fun _ => withSelfhostCli fun exe => do
        let host ← cliDiffHost
        let spec : CliDiffSpec := { files := #[("main.wiz", cliMissingModule)]
                                    args := #["check", "main.wiz"] }
        let (h, s) ← cliDiffBoth host exe spec
        cliDiffSame spec h s
        checkEq 1 s.code
        checkEq "main.wiz:2:1: error: cannot find module M [unknown-module]\n" s.err },
    { name := "a failed import: both also report the commands after it", run := fun _ => withSelfhostCli fun exe => do
        let host ← cliDiffHost
        let spec : CliDiffSpec := { files := #[("main.wiz", cliMissingModuleUse)]
                                    args := #["check", "main.wiz"], columns := false }
        let (h, s) ← cliDiffBoth host exe spec
        cliDiffSame spec h s
        checkEq 1 s.code
        -- both name the missing module and go on to the next command (`one` unknown)
        cliCheck h.err "main.wiz:2:1: error: unknown module M" "host import"
        cliCheck h.err "main.wiz:3:18: error: unknown identifier 'one'" "host cascade"
        cliCheck s.err "main.wiz:2:1: error: cannot find module M [unknown-module]" "driver import"
        cliCheck s.err "main.wiz:3:1: error: unknown identifier one [unknown-identifier]" "driver cascade" },
    { name := "-I: an error inside a module (the host nests it under the import)", run := fun _ => withSelfhostCli fun exe => do
        let host ← cliDiffHost
        let files := #[("lib/M.wiz", cliBadModule),
                       ("main.wiz", "import Prelude\nimport M\ndef two : Nat := one\n")]
        let spec : CliDiffSpec := { files := files, args := #["check", "-I", "lib", "main.wiz"] }
        let (h, s) ← cliDiffBoth host exe spec
        checkEq 1 h.code
        checkEq 1 s.code
        -- both name the module and its own line; the host prints it under the import's
        -- message, the self-hosted loader at the module's own file and line
        cliCheck h.err "module M has errors" "host nesting"
        cliCheck s.err "lib/M.wiz:3:1: error: unknown identifier nope" "module's own position"
        skip "structure: the host nests a module's errors under its import (`module M has errors:`); the self-hosted loader reports each at its own module and position (D6/A14)" },
    { name := "cache: --cache DIR is written by both, and a warm run agrees", run := fun _ => withSelfhostCli fun exe => do
        let host ← cliDiffHost
        let spec : CliDiffSpec := { files := #[("c.wiz", cliGood)]
                                    args := #["check", "c.wiz", "--cache", "c"] }
        let (h, s) ← cliDiffBoth host exe spec
        cliDiffSame spec h s
        checkEq 0 s.code
        check ((← cliDiffCacheEntries h "c") > 0) "the host wrote no cache entry"
        check ((← cliDiffCacheEntries s "c") > 0) "the driver wrote no cache entry"
        -- the same directories again: both read their entry and say the same thing
        let h2 ← cliDiffExec host h.dir spec.hostArgs spec.args
        let s2 ← cliDiffExec exe s.dir spec.shArgs spec.args
        cliDiffSame spec h2 s2
        checkEq 0 s2.code },
    { name := "cache: the default is ~/.cache/wiz in both", run := fun _ => withSelfhostCli fun exe => do
        let host ← cliDiffHost
        let spec : CliDiffSpec := { files := #[("d.wiz", cliGood)], args := #["check", "d.wiz"] }
        let (h, s) ← cliDiffBoth host exe spec
        cliDiffSame spec h s
        checkEq 0 s.code
        check ((← cliDiffCacheEntries h "home/.cache/wiz") > 0) "the host wrote no default cache entry"
        check ((← cliDiffCacheEntries s "home/.cache/wiz") > 0) "the driver did not use ~/.cache/wiz"
        unless !(← cliDiffExists s ".wiz-cache") do
          throw (IO.userError "the driver wrote `.wiz-cache` in the working directory") },
    { name := "cache: --no-cache writes nothing in either", run := fun _ => withSelfhostCli fun exe => do
        let host ← cliDiffHost
        let spec : CliDiffSpec := { files := #[("n.wiz", cliGood)]
                                    args := #["check", "n.wiz", "--no-cache"] }
        let (h, s) ← cliDiffBoth host exe spec
        cliDiffSame spec h s
        checkEq 0 s.code
        check ((← cliDiffCacheEntries h "home/.cache/wiz") == 0) "the host wrote a cache entry"
        check ((← cliDiffCacheEntries s "home/.cache/wiz") == 0) "the driver wrote a cache entry"
        unless !(← cliDiffExists s ".wiz-cache") do
          throw (IO.userError "the driver wrote `.wiz-cache` with --no-cache") },
    { name := "cache: --cache-ro is a host layer the driver has not got (a named difference)", run := fun _ => withSelfhostCli fun exe => do
        let host ← cliDiffHost
        let files := #[("ro/.keep", ""), ("r.wiz", cliGood)]
        let spec : CliDiffSpec := { files := files, args := #["check", "r.wiz", "--cache-ro", "ro"] }
        let (h, s) ← cliDiffBoth host exe spec
        checkEq 0 h.code
        checkEq 2 s.code
        cliCheck s.err "unknown flag: --cache-ro" "the driver's rejection"
        skip "cache: `--cache-ro DIR` adds a read-only layer (a Nix package's share/wiz/cache) in the host; the driver's one-file cache has no layers, so it rejects the flag (D5)" },
    { name := "cache: an edit is a miss in both (an error becomes clean)", run := fun _ => withSelfhostCli fun exe => do
        let host ← cliDiffHost
        let spec : CliDiffSpec := { files := #[("m.wiz", cliMissingModule)]
                                    args := #["check", "m.wiz", "--cache", "c"] }
        let (h, s) ← cliDiffBoth host exe spec
        cliDiffSame spec h s
        checkEq 1 s.code
        IO.FS.writeFile (h.dir / "m.wiz") cliGood
        IO.FS.writeFile (s.dir / "m.wiz") cliGood
        let h2 ← cliDiffExec host h.dir spec.hostArgs spec.args
        let s2 ← cliDiffExec exe s.dir spec.shArgs spec.args
        cliDiffSame spec h2 s2
        checkEq 0 s2.code },
    { name := "build: a bad file writes no artifact in either (exit 1)", run := fun _ => withSelfhostCli fun exe => do
        let host ← cliDiffHost
        let spec : CliDiffSpec := { files := #[("bad.wiz", cliMissingModule)]
                                    args := #["build", "bad.wiz", "-o", "out"] }
        let (h, s) ← cliDiffBoth host exe spec
        cliDiffSame spec h s
        checkEq 1 s.code
        unless !(← cliDiffExists h "out") do throw (IO.userError "the host wrote an artifact")
        unless !(← cliDiffExists s "out") do throw (IO.userError "the driver wrote an artifact") },
    { name := "build: a good file is silent and exit 0 (the artifact is C, not an executable)", run := fun _ => withSelfhostCli fun exe => do
        let host ← cliDiffHost
        let tc ← cliDiffHostToolchain
        let spec : CliDiffSpec := { files := #[("good.wiz", cliDiffHello)]
                                    args := #["build", "good.wiz", "-o", "out"]
                                    hostArgs := tc }
        let (h, s) ← cliDiffBoth host exe spec
        cliDiffSame spec h s
        checkEq 0 s.code
        let hc ← cliDiffReadBin h "out"
        let sc ← cliDiffRead s "out"
        check hc.isSome "the host wrote no executable"
        check sc.isSome "the driver wrote no C"
        -- (an ELF (`\x7fELF`) or a Mach-O; the driver's artifact is C)
        check ((hc.map cliDiffIsExe).getD false) "the host's artifact is not executable"
        check (cliHas (sc.getD "") "int main(") "the driver's artifact is not C"
        skip "artifact: `build` writes an executable (via C), the self-hosted `build` the generated C (D4)" },
    { name := "build --lib: the object, its header and the C match the host's shapes", run := fun _ => do
        match ← cliRunOptions with
        | none => skip "no garbage collector, --gc-cflags"
        | some shOpts => withSelfhostCli fun exe => do
          let host ← cliDiffHost
          let tc ← cliDiffHostToolchain
          let spec : CliDiffSpec := { files := #[("lib.wiz", cliExports)]
                                      args := #["build", "lib.wiz", "-o", "out.o", "--lib"]
                                      hostArgs := tc, shArgs := shOpts }
          let (h, s) ← cliDiffBoth host exe spec
          cliDiffSame spec h s
          checkEq 0 s.code
          -- (both write the object at -o, the C at `-o`'s `.c` and the header at `.h`)
          check (← cliDiffExists h "out.o") "the host wrote no object file"
          check (← cliDiffExists s "out.o") "the driver wrote no object file"
          check (← cliDiffExists h "out.h") "the host wrote no header"
          check (← cliDiffExists s "out.h") "the driver wrote no header"
          check (← cliDiffExists h "out.c") "the host wrote no C"
          check (← cliDiffExists s "out.c") "the driver wrote no C"
          let ho ← cliDiffReadBin h "out.o"
          let so ← cliDiffReadBin s "out.o"
          check ((ho.map cliDiffIsObject).getD false) "the host's artifact is not an object"
          check ((so.map cliDiffIsObject).getD false) "the driver's artifact is not an object"
          -- the header's shape: the handle functions, and the export's prototype
          let hh := (← cliDiffRead h "out.h").getD ""
          let sh := (← cliDiffRead s "out.h").getD ""
          for hdr in [hh, sh] do
            cliCheck hdr "uintptr_t wiz_val;" "the header's handle type"
            cliCheck hdr "void wiz_release(void *v);" "the header's release"
            cliCheck hdr "void wiz_retain(void *v);" "the header's retain"
            cliCheck hdr "uint64_t wiz_square(uint64_t a0);" "the export's prototype"
          -- the C is the library (no `main`) and defines the export's wrapper
          let hc := (← cliDiffRead h "out.c").getD ""
          let sc := (← cliDiffRead s "out.c").getD ""
          for c in [hc, sc] do
            cliCheck c "wiz_square" "the export's wrapper"
            unless !(cliHas c "int main(") do throw (IO.userError "the library's C has a `main`")
          -- a second run is a hit (the cache holds both texts) and writes the same shapes
          let h2 ← cliDiffExec host h.dir spec.hostArgs spec.args
          let s2 ← cliDiffExec exe s.dir spec.shArgs spec.args
          cliDiffSame spec h2 s2
          checkEq 0 s2.code
          check (← cliDiffExists s2 "out.o") "the driver's warm build wrote no object"
          -- `--no-main`: an executable without a `main` (or the C for one; the host links
          -- without a `main` only where the C toolchain allows it: emcc --no-entry)
          let spec2 : CliDiffSpec := { files := #[("lib.wiz", cliExports)]
                                       args := #["build", "lib.wiz", "-o", "nom", "--no-main"]
                                       hostArgs := tc, shArgs := shOpts }
          let (h3, s3) ← cliDiffBoth host exe spec2
          if h3.code != 0 then
            skip "artifact: --lib's object/header/C match the host's shapes now; --no-main does not link without a `main` on this platform (the host's Wasm path), the driver writes the C (D4/C9)"
          else do
            cliDiffSame spec2 h3 s3
            checkEq 0 s3.code
            skip "artifact: --no-main links an executable without a `main` in the host; the driver writes the C for one (D4/C9)" },
    { name := "build --lib without an export: the host's error, the same text and exit", run := fun _ => withSelfhostCli fun exe => do
        let host ← cliDiffHost
        let tc ← cliDiffHostToolchain
        let spec : CliDiffSpec := { files := #[("good.wiz", cliGood)]
                                    args := #["build", "good.wiz", "-o", "out.o", "--lib"]
                                    hostArgs := tc }
        let (h, s) ← cliDiffBoth host exe spec
        cliDiffSame spec h s
        checkEq 1 s.code
        checkEq 1 h.code
        checkEq "a library must export something (`export \"name\" f`)\n" s.err
        -- (the error comes before the artifacts: nothing is written)
        unless !(← cliDiffExists h "out.o") do throw (IO.userError "the host wrote an object")
        unless !(← cliDiffExists s "out.o") do throw (IO.userError "the driver wrote an object")
        unless !(← cliDiffExists s "out.h") do throw (IO.userError "the driver wrote a header") },
    { name := "build: -o is required in both (the host's unknown command, exit 2)", run := fun _ => withSelfhostCli fun exe => do
        let host ← cliDiffHost
        let spec : CliDiffSpec := { files := #[("good.wiz", cliGood)], args := #["build", "good.wiz"] }
        let (h, s) ← cliDiffBoth host exe spec
        cliDiffSame spec h s
        checkEq 2 s.code
        checkEq 2 h.code
        cliCheck s.err "unknown command: build good.wiz" "the missing -o" },
    { name := "build -o: a missing directory fails in both (exit 1, no artifact)", run := fun _ => withSelfhostCli fun exe => do
        let host ← cliDiffHost
        let spec : CliDiffSpec := { files := #[("good.wiz", cliGood)]
                                    args := #["build", "good.wiz", "-o", "nodir/out"] }
        let (h, s) ← cliDiffBoth host exe spec
        checkEq 1 h.code
        checkEq 1 s.code
        unless !(← cliDiffExists h "nodir/out") do throw (IO.userError "the host wrote an artifact")
        unless !(← cliDiffExists s "nodir/out") do throw (IO.userError "the driver wrote an artifact")
        skip "message: a missing `-o` directory is an uncaught `IO.FS.writeFile` exception in the host (a machine-dependent trace on stderr); the driver writes one line (`error: cannot write …`). Both exit 1 and write nothing (D4/D7)" },
    { name := "build --header: the driver's header-only mode (the host has no such flag)", run := fun _ => withSelfhostCli fun exe => do
        let host ← cliDiffHost
        let spec : CliDiffSpec := { files := #[("lib.wiz", cliExports)]
                                    args := #["build", "lib.wiz", "--header", "-o", "out.h"] }
        let (h, s) ← cliDiffBoth host exe spec
        checkEq 2 h.code
        checkEq 0 s.code
        cliCheck h.err "unknown flag: --header" "the host's rejection"
        -- (the driver writes the exports' header at OUT; no C and no object)
        let sh := (← cliDiffRead s "out.h").getD ""
        cliCheck sh "uint64_t wiz_square(uint64_t a0);" "the export's prototype"
        unless !(← cliDiffExists s "out.c") do throw (IO.userError "the driver wrote a C file")
        unless !(← cliDiffExists s "out.o") do throw (IO.userError "the driver wrote an object")
        skip "artifact: `--header` is the driver's header-only output (the one-shot `--header` mode, reused by `build`); the host has no such flag (`--lib` writes OUT.h itself), so it rejects it (D4)" },
    { name := "build --llvm: the host has it, the self-hosted backend is C only (C5)", run := fun _ => withSelfhostCli fun exe => do
        let host ← cliDiffHost
        let tc ← cliDiffHostToolchain
        let spec : CliDiffSpec := { files := #[("good.wiz", cliDiffHello)]
                                    args := #["build", "good.wiz", "-o", "out", "--llvm"]
                                    hostArgs := tc }
        let (h, s) ← cliDiffBoth host exe spec
        -- (the driver has no LLVM path at all: it always refuses the flag, C5)
        checkEq 2 s.code
        cliCheck s.err "unknown flag: --llvm" "the driver's rejection"
        if h.code == 0 then do
          check (← cliDiffExists h "out") "the host's LLVM build wrote no artifact"
          skip "backend: the host builds through textual LLVM IR (`--llvm`); the self-hosted backend is C only (C5)"
        else do
          let why := " ".intercalate ((cliDiffNormal false h.err).splitOn "\n")
          skip s!"backend: --llvm selects the host's LLVM path (exit {h.code} here: {why}); the self-hosted backend is C only (C5)" },
    { name := "extensions: --include, --types and -v are the driver's own (the host rejects them)", run := fun _ => withSelfhostCli fun exe => do
        let host ← cliDiffHost
        let files := #[("good.wiz", cliGood)]
        for args in [#["check", "--include", ".", "good.wiz"], #["check", "good.wiz", "--types"],
                     #["check", "good.wiz", "-v"]] do
          let spec : CliDiffSpec := { files := files, args := args }
          let (h, s) ← cliDiffBoth host exe spec
          checkEq 2 h.code
          checkEq 0 s.code
        skip "flags: the driver also has `--include` (an -I alias), `--types` and `-v`; the host has -I only and no verbose/type switch (its `wiz check` prints info already)" },
    { name := "run: an IO program prints the same output and exits 0", run := fun _ => do
        match ← cliRunOptions with
        | none => skip "no garbage collector, --gc-cflags"
        | some shOpts => withSelfhostCli fun exe => do
          let host ← cliDiffHost
          let tc ← cliDiffHostToolchain
          let spec : CliDiffSpec := { files := #[("prog.wiz", cliDiffHello)]
                                      args := #["run", "prog.wiz"]
                                      hostArgs := tc, shArgs := shOpts }
          let (h, s) ← cliDiffBoth host exe spec
          cliDiffSame spec h s
          checkEq 0 s.code
          checkEq "hello from the selfhost driver\n42\n" s.out },
    { name := "run: program arguments are the driver's (the host's `run` takes flags only)", run := fun _ => do
        match ← cliRunOptions with
        | none => skip "no garbage collector, --gc-cflags"
        | some shOpts => withSelfhostCli fun exe => do
          let host ← cliDiffHost
          let tc ← cliDiffHostToolchain
          let spec : CliDiffSpec := { files := #[("prog.wiz", cliHello)]
                                      args := #["run", "prog.wiz", "one", "two"]
                                      hostArgs := tc, shArgs := shOpts }
          let (h, s) ← cliDiffBoth host exe spec
          checkEq 2 h.code
          cliCheck h.err "unknown command: run prog.wiz one two" "the host's rejection"
          checkEq 0 s.code
          checkEq "hello from the selfhost driver\n42\n" s.out
          skip "`run`: the driver passes the words after FILE to the program (`run FILE ARG…`); the host's `run` has no program arguments and rejects them (exit 2)" },
    { name := "help and version: exit 0, one version line (the usage documents the subset)", run := fun _ => withSelfhostCli fun exe => do
        let host ← cliDiffHost
        let spec : CliDiffSpec := { args := #["--version"] }
        let (h, s) ← cliDiffBoth host exe spec
        cliDiffSame spec h s
        checkEq 0 s.code
        checkEq (h.out.replace "wiz-selfhost" "wiz") (s.out.replace "wiz-selfhost" "wiz")
        let spec2 : CliDiffSpec := { args := #["--help"] }
        let (h2, s2) ← cliDiffBoth host exe spec2
        checkEq 0 h2.code
        checkEq 0 s2.code
        for word in ["check", "build", "run"] do
          cliCheck h2.out word "host help"
          cliCheck s2.out word "driver help"
        skip "usage text: the driver documents the subset it has (no parse/doc/fmt/lsp, no --llvm; D2/D8)" },
    { name := "warnings: the host warns about a shadowed Prelude (the driver has none yet)", run := fun _ => withSelfhostCli fun exe => do
        let host ← cliDiffHost
        let files := #[("Prelude.wiz", "import Prelude\ndef shadow : Nat := 0\n"),
                       ("main.wiz", "import Prelude\ndef one : Nat := 1\n")]
        let spec : CliDiffSpec := { files := files, args := #["check", "-I", ".", "main.wiz"] }
        let (h, s) ← cliDiffBoth host exe spec
        checkEq 0 h.code
        checkEq 0 s.code
        cliCheck h.out "is ignored: module Prelude" "host warning"
        checkEq "" s.out
        skip "warnings: the host warns (on stdout) about a module root shadowing its own lib; the self-hosted loader canonicalises Prelude to the embedded prelude and has no warning channel yet (A14/D6)" },
    { name := "a missing file: both exit 1 (the host's message is an uncaught read)", run := fun _ => withSelfhostCli fun exe => do
        let host ← cliDiffHost
        let spec : CliDiffSpec := { args := #["check", "no.wiz"] }
        let (h, s) ← cliDiffBoth host exe spec
        checkEq 1 s.code
        checkEq 1 h.code
        checkEq "" s.out
        checkEq "no.wiz:1:1: error: no such file\n" s.err
        skip "message: the host lets IO.readFile throw (an uncaught exception on stderr); the driver checks access first and prints one positioned diagnostic (D6/D7)" }
  ]

builtin_initialize registerGroup cliDiffGroup

end Tests.Elab
