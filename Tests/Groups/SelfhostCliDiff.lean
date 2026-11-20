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
one, the cache flags, the flags the docs promise — and by the driver items of the
self-hosting parity audit, whose labels the cases cite: D2 subcommands, D3 flags, D4
build artifacts, D5 the elaboration cache, D6 diagnostics, D7 exit codes (and A14
modules, C5 the LLVM/IR backends, C9 `--lib`/`--no-main`, C12 the native operations, D8
LSP/doc).

## A difference is asserted, not skipped

A skip is for a case that could not run (no C compiler, no collector) and for nothing
else: it is not a pass, and an allow-list entry that excuses 14 of 30 cases hides the
group. A known parity difference is therefore an **expected difference**: the case
checks the exact symptom (the exit code, the message, the artifact) and records
`expected-difference: …` with `Tests.note`, then passes. If the driver catches up the
assertion stops holding and the case fails — the prompt to promote it — whereas a skip
would stay silent. This group has no `.github/skip-allowlist.json` entry; the two `run`
cases still skip on a host without the collector, as they must.

## What "normalised" means here

The two frontends are different elaborators, so their *wording* differs (`unknown
identifier 'nope'` against `unknown identifier nope`) and the self-hosted one carries a
stable `[code]` the Lean-hosted CLI does not print (`Msg.render`). A diagnostic line

    file:line:col: severity: message [code]

is compared as `file:line:col: severity: kind`, where `kind` is the code (or, for the
host, the same `ErrorCode` derived from its wording). `messages := true` also compares
the message text (the driver's `[code]` dropped, the tool name unified) for the cases
where both sides word it identically; the cases whose wording differs leave it off.
Driver lines that are not diagnostics (`unknown flag: …`, the version line) are compared
verbatim, with `wiz-selfhost` read as `wiz`. Two blocks are not compared by default:

* **the usage text** after a usage error (everything from the line that starts `usage`):
  the driver documents the subset it has (no `parse`/`doc`/`fmt`/`lsp`, no `--llvm`).
  The help case pins the driver's whole usage text and says which host commands it
  lacks, so this is a checked difference, not an unchecked block;
* **indented continuation lines** of a message (`type mismatch`'s `expected:` /
  `inferred:` lines), since the host's elaborator and the self-hosted one split a
  message differently. `continuations := true` compares them for a case where they
  match.

`columns := false` compares `file:line` only, for a diagnostic whose granularity is
still the command's start rather than the failing term (D6); the cases below are
`columns := true` for every error the self-hosted frontend now positions at the term.
A case whose artifact legitimately differs (D4: `build` writes C, not an executable)
asserts what it can and records it the same way.

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
  /-- Compare the message text too (the driver's `[code]` dropped, the tool name unified):
  only for the cases whose wording both frontends already share -/
  messages : Bool := false
  /-- Compare a message's indented continuation lines (`expected:` / `inferred:`) too -/
  continuations : Bool := false

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
   ("module ", "module-errors"),
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

/-- A diagnostic's message without the driver's trailing ` [code]` (the host prints no
code), so that a case can compare the wording both sides share. -/
def cliDiffText (msg : String) : String :=
  let parts := msg.splitOn " ["
  match parts.reverse with
  | last :: _ =>
    if parts.length > 1 && last.endsWith "]" then " [".intercalate parts.dropLast
    else msg
  | [] => msg

/-- One line, normalised: a diagnostic to `file:line: severity: kind` (or
`file:line:col: severity: kind`), plus its message text when `messages` is set; anything
else verbatim with the tool name unified. -/
def cliDiffLine (columns messages : Bool) (l : String) : String :=
  match l.splitOn ": " with
  | loc :: sev :: rest =>
    if rest.isEmpty || !(["error", "warning", "info"].contains sev) then cliDiffTool l
    else
      let msg := ": ".intercalate rest
      let what := if messages then s!"{cliDiffKind msg}: {cliDiffTool (cliDiffText msg)}"
        else cliDiffKind msg
      match loc.splitOn ":" with
      | [f, ln, col] =>
        if columns then s!"{f}:{ln}:{col}: {sev}: {what}"
        else s!"{f}:{ln}: {sev}: {what}"
      | _ => cliDiffTool l
  | _ => cliDiffTool l

/-- A stream, normalised (see the module docs). Indented continuation lines are dropped
unless `continuations` is set (the two elaborators split a message differently). -/
def cliDiffNormal (columns messages continuations : Bool) (s : String) : String :=
  let ls := cliDiffBeforeUsage (s.splitOn "\n")
  let ls := ls.filterMap fun l =>
    if l.isEmpty || (!continuations && l.startsWith "  ") then none
    else some (cliDiffLine columns messages l)
  "\n".intercalate ls

def cliDiffOneStream (spec : CliDiffSpec) (name ho so : String) : IO Unit := do
  let hn := cliDiffNormal spec.columns spec.messages spec.continuations ho
  let sn := cliDiffNormal spec.columns spec.messages spec.continuations so
  unless hn == sn do
    throw (IO.userError s!"{name} differs (args {" ".intercalate spec.args.toList}):\n-- wiz\n{hn}\n-- wiz-selfhost\n{sn}\n-- raw wiz\n{ho}\n-- raw wiz-selfhost\n{so}")

/-- Compare a run of each tool: exit code, standard output, standard error. -/
def cliDiffSame (spec : CliDiffSpec) (h s : CliDiffRun) : IO Unit := do
  unless h.code == s.code do
    throw (IO.userError s!"exit code differs (args {" ".intercalate spec.args.toList}): wiz {h.code}, wiz-selfhost {s.code}\n-- wiz stdout\n{h.out}\n-- wiz stderr\n{h.err}\n-- wiz-selfhost stdout\n{s.out}\n-- wiz-selfhost stderr\n{s.err}")
  cliDiffOneStream spec "stdout" h.out s.out
  cliDiffOneStream spec "stderr" h.err s.err

/-- A known parity difference, asserted rather than skipped: the case checked the exact
symptom (exit code, message, artifact) above and now records it. If the driver catches
up, one of those assertions fails first — that is the prompt to promote the case — where
a skip would stay silent. The case name is the `--timings` record's `case`. -/
def cliDiffKnown (symptom : String) : IO Unit :=
  Tests.note s!"expected-difference: {symptom}"

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

/-- The driver's usage text, verbatim (`selfhost/Cli.wiz` `usageText`): the help case
pins it, so an unintended wording change is a test failure and the expected
subcommand surface is checked line by line. -/
def cliDiffDriverHelp : String :=
  "usage: wiz-selfhost COMMAND FILE [OPTIONS]\n" ++
  "\n" ++
  "  wiz-selfhost check FILE         elaborate and type check FILE (diagnostics on\n" ++
  "                                  standard error; exit 1 if it has errors)\n" ++
  "  wiz-selfhost build FILE -o OUT  write the generated C to OUT\n" ++
  "                                  (--lib: OUT.c, OUT.h and the object OUT)\n" ++
  "  wiz-selfhost run FILE [ARG]...  compile `main` and run it (also `eval`)\n" ++
  "  wiz-selfhost version            print the version (also --version)\n" ++
  "  wiz-selfhost help               this text (also -h, --help)\n" ++
  "  wiz-selfhost lsp                a language server on stdin/stdout: initialize,\n" ++
  "                                  full-text didOpen/didChange/didClose,\n" ++
  "                                  publishDiagnostics, plainGoal/plainTermGoal (D8)\n" ++
  "\n" ++
  "options: -I DIR (a module root, repeatable; an `import M` is M.wiz there, then\n" ++
  "  in the working directory),\n" ++
  "  -o OUT (the C `run` compiles, kept), --cache DIR (default ~/.cache/wiz, as\n" ++
  "  the Lean-hosted `wiz`'s), --cache-ro DIR (a read-only layer, repeatable:\n" ++
  "  searched after --cache in order, never written), --no-cache (both lists),\n" ++
  "  --cache-prune DAYS (remove the write cache's keyed entries older than DAYS\n" ++
  "  days before the command; a layer is never pruned),\n" ++
  "  --cache-verify off|warn|strict (check an entry against its output manifest;\n" ++
  "  strict: only manifested entries), --target c (the only backend;\n" ++
  "  --llvm/--wasm/--split are the host's and are refused, C5),\n" ++
  "  -v (cache hits and misses), --types (each declaration's type),\n" ++
  "  --trust-native (27a: `def X : a = b := native_refl` is decided by running a and\n" ++
  "  b, not by the kernel; `#print axioms` lists the axiom it adds. There is no\n" ++
  "  --native-fuel: the self-hosted evaluator has no step counter),\n" ++
  "  --cc CMD, --rt DIR (the selfhost runtime, default selfhost), --cflags FLAGS,\n" ++
  "  --ldflags FLAGS, --trust-smt (the `smt` tactic is refused: no solver here, C15);\n" ++
  "  backend: --rc, --rc-owned, --gc, --unbox-structs, --lib, --no-main, --header\n" ++
  "\n" ++
  "without a command: input.wiz in the working directory to standard output\n\n"
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
        -- (both tools must exit 0 on a good file: equal non-zero codes are not a pass)
        checkEq 0 h.code
        checkEq 0 s.code
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
    { name := "check: a bad file has the same position, severity and kind (the column is the failing term)",
      run := fun _ => withSelfhostCli fun exe => do
        let host ← cliDiffHost
        -- unknown identifier, duplicate declaration and type mismatch: both report the
        -- term that failed (the identifier, the declared name, the mismatched term)
        let spec : CliDiffSpec := { files := #[("bad.wiz", cliBad)], args := #["check", "bad.wiz"] }
        let (h, s) ← cliDiffBoth host exe spec
        cliDiffSame spec h s
        checkEq 1 s.code
        checkEq "bad.wiz:3:18: error: unknown identifier nope [unknown-identifier]\n" s.err
        let dup := "import Prelude\ndef one : Nat := 1\ndef one : Nat := 2\n"
        let spec2 : CliDiffSpec := { files := #[("dup.wiz", dup)], args := #["check", "dup.wiz"] }
        let (h2, s2) ← cliDiffBoth host exe spec2
        cliDiffSame spec2 h2 s2
        checkEq 1 s2.code
        -- (the host's message is identical; both positions are the declared name)
        cliCheck s2.err "'one' has already been declared" "duplicate text"
        checkEq "dup.wiz:3:5: error: 'one' has already been declared [duplicate-declaration]\n" s2.err
        -- a type mismatch: the host's expected/inferred lines are indented and dropped
        let spec3 : CliDiffSpec := { files := #[("tm.wiz", "import Prelude\ndef bad : Nat := Bool.true\n")]
                                     args := #["check", "tm.wiz"] }
        let (h3, s3) ← cliDiffBoth host exe spec3
        cliDiffSame spec3 h3 s3
        checkEq 1 s3.code
        cliCheck s3.err "tm.wiz:2:18: error: type mismatch" "type mismatch" },
    { name := "messages: a duplicate declaration is word-for-word the same on both sides", run := fun _ => withSelfhostCli fun exe => do
        let host ← cliDiffHost
        let dup := "import Prelude\ndef one : Nat := 1\ndef one : Nat := 2\n"
        -- `messages := true`: the whole message after the kind, not just the `[code]`
        let spec : CliDiffSpec := { files := #[("dup.wiz", dup)], args := #["check", "dup.wiz"]
                                    messages := true }
        let (h, s) ← cliDiffBoth host exe spec
        cliDiffSame spec h s
        checkEq 1 s.code
        -- (the driver's raw line: the declared name's position and its `[code]`)
        checkEq "dup.wiz:3:5: error: 'one' has already been declared [duplicate-declaration]\n" s.err },
    { name := "smt: without --trust-smt the refusal is the host's, at the `smt` token (C15)", run := fun _ =>
        withSelfhostCli fun exe => do
        let host ← cliDiffHost
        -- `smt` (stage 28a) is a library tactic: the host parses it, elaborates it, and
        -- refuses it unless `--trust-smt`; the self-hosted frontend parses the same tree
        -- (Parse.wiz `surfaceCats`) and refuses it with the same message and exit code
        let src := "import Prelude\ndef t (a b : Nat) : Nat.add a b = Nat.add b a := by smt\n"
        let spec : CliDiffSpec := { files := #[("f.wiz", src)], args := #["check", "f.wiz"] }
        let (h, s) ← cliDiffBoth host exe spec
        cliDiffSame spec h s
        checkEq 1 s.code
        checkEq "" s.out
        checkEq ("f.wiz:2:53: error: SMT solving is not enabled: `smt` closes a goal on an " ++
          "SMT solver's word, which the kernel does not check; run with --trust-smt to allow it\n") s.err },
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
        cliDiffKnown "prelude: the self-hosted Prelude is one embedded module that includes the IO natives, and `import IO` is canonicalised to it; the host's `lib/Prelude.wiz` has no `IO`, so a file that omits `import IO` compiles only there (A14/C12)" },
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
    { name := "--llvm / --wasm: the host's aliases, refused as targets by the driver (C5)", run := fun _ => withSelfhostCli fun exe => do
        let host ← cliDiffHost
        let files := #[("good.wiz", cliGood)]
        for args in [#["check", "good.wiz", "--llvm"], #["--wasm", "check", "good.wiz"]] do
          let spec : CliDiffSpec := { files := files, args := args }
          let (h, s) ← cliDiffBoth host exe spec
          checkEq 0 h.code
          checkEq 1 s.code
          checkEq "" s.out
          let target := if args.contains "--llvm" then "llvm" else "wasm"
          cliCheck s.err s!"unsupported target {target}: the self-hosted backend emits C only (C5)" "the driver's rejection"
        cliDiffKnown "flags: `--llvm`/`--wasm` are target aliases in the host; the driver recognises them and refuses the target (exit 1), as `--target llvm|wasm` (C5)" },
    { name := "build --split N: the host splits the C into N units, the driver refuses it (C5)", run := fun _ => withSelfhostCli fun exe => do
        let host ← cliDiffHost
        let tc ← cliDiffHostToolchain
        let spec : CliDiffSpec := { files := #[("good.wiz", cliDiffHello)]
                                    args := #["build", "good.wiz", "-o", "out", "--split", "2"]
                                    hostArgs := tc }
        let (h, s) ← cliDiffBoth host exe spec
        checkEq 0 h.code
        check (← cliDiffExists h "out") "the host's split build wrote no artifact"
        checkEq 1 s.code
        cliCheck s.err "unsupported --split 2: the self-hosted backend emits one C unit (C5)" "the driver's rejection"
        -- (the leading form too: a value is a value, not a command)
        let spec2 : CliDiffSpec := { files := #[("good.wiz", cliGood)]
                                     args := #["--split", "2", "check", "good.wiz"] }
        let (h2, s2) ← cliDiffBoth host exe spec2
        checkEq 0 h2.code
        checkEq 1 s2.code
        cliDiffKnown "flags: `--split N` compiles N C units in parallel in the host; the self-hosted backend has one C unit, so the driver refuses the flag (exit 1) (C5)" },
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
        cliDiffKnown "backend: --target llvm/wasm selects LLVM/WebAssembly in the host (C5); the self-hosted backend emits C, so the driver refuses the name (exit 1) instead of silently building C" },
    { name := "--cache-verify: the modes are accepted, and strict is warm in both", run := fun _ => withSelfhostCli fun exe => do
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
        -- (the driver's own manifest makes a second strict run warm; `-v` shows it in
        -- `=selfhost-cli`, since the host has no verbose cache line)
        let spec : CliDiffSpec := { files := files
                                    args := #["--cache-verify=strict", "check", "cv.wiz", "--cache", "c"] }
        let h1 ← cliDiffInit spec.files
        let s1 ← cliDiffInit spec.files
        let _ ← cliDiffExec host h1 #[] spec.args
        let _ ← cliDiffExec exe s1 #[] spec.args
        let h2 ← cliDiffExec host h1 #[] spec.args
        let s2 ← cliDiffExec exe s1 #[] spec.args
        cliDiffSame spec h2 s2
        checkEq 0 s2.code
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
        cliDiffKnown "cache verification: both modes behave alike; the manifests' layouts differ (the host's per-module SHA-256/Merkle `.wizmf` under `manifest.d/`, the driver's per-entry digest sidecar) (D5)" },
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
        cliCheck s.err "main.wiz:3:18: error: unknown identifier one [unknown-identifier]" "driver cascade" },
    { name := "-I: an error inside a module (the host nests it under the import)", run := fun _ => withSelfhostCli fun exe => do
        let host ← cliDiffHost
        let files := #[("lib/M.wiz", cliBadModule),
                       ("main.wiz", "import Prelude\nimport M\ndef two : Nat := one\n")]
        let spec : CliDiffSpec := { files := files, args := #["check", "-I", "lib", "main.wiz"]
                                    continuations := true }
        let (h, s) ← cliDiffBoth host exe spec
        cliDiffSame spec h s
        checkEq 1 h.code
        checkEq 1 s.code
        -- both name the module at the import and its own line under it; the importer's
        -- later commands are still checked, at their failing term
        cliCheck h.err "module M has errors" "host nesting"
        cliCheck s.err "module M has errors" "driver nesting"
        let nested := "main.wiz:2:1: error: module M has errors:\n  M:3:18: error: unknown identifier"
        cliCheck h.err nested "the host's nested block"
        cliCheck s.err nested "the driver's nested block" },
    { name := "cache: --cache DIR is written by both, and a warm run agrees", run := fun _ => withSelfhostCli fun exe => do
        let host ← cliDiffHost
        let spec : CliDiffSpec := { files := #[("c.wiz", cliGood)]
                                    args := #["check", "c.wiz", "--cache", "c"] }
        let (h, s) ← cliDiffBoth host exe spec
        cliDiffSame spec h s
        checkEq 0 s.code
        check ((← cliDiffCacheEntries h "c") > 0) "the host wrote no cache entry"
        check ((← cliDiffCacheEntries s "c") > 0) "the driver wrote no cache entry"
        -- (D5) the driver's names are the host's four classes, one `.wizc` per module
        check ((← cliFilesEnding (s.dir / "c") ".wizc").size > 0) "the driver wrote no module entry"
        checkEq 0 (← cliFilesEnding (s.dir / "c") ".check").size
        checkEq 0 (← cliFilesEnding (s.dir / "c") ".c").size
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
    { name := "cache: --cache-ro DIR adds a read-only layer in both, and neither writes it", run := fun _ => withSelfhostCli fun exe => do
        let host ← cliDiffHost
        let files := #[("ro/.keep", ""), ("r.wiz", cliGood)]
        let spec : CliDiffSpec := { files := files
                                    args := #["check", "r.wiz", "--cache", "c", "--cache-ro", "ro"] }
        let (h, s) ← cliDiffBoth host exe spec
        cliDiffSame spec h s
        checkEq 0 s.code
        checkEq 0 h.code
        -- (an empty layer is not a cache source; the write cache gets the entry, and the
        -- read-only layer keeps only its own `.keep`)
        check ((← cliDiffEntries (h.dir / "ro")) == 1) "the host wrote its read-only layer"
        check ((← cliDiffEntries (s.dir / "ro")) == 1) "the driver wrote its read-only layer"
        -- `--no-cache` clears the write cache, and a later `--cache-ro` adds the layer back
        let spec2 : CliDiffSpec := { files := files
                                     args := #["check", "r.wiz", "--no-cache", "--cache-ro", "ro"] }
        let (h2, s2) ← cliDiffBoth host exe spec2
        cliDiffSame spec2 h2 s2
        checkEq 0 s2.code
        check ((← cliDiffEntries (h2.dir / "ro")) == 1) "the host wrote a layer under --no-cache"
        check ((← cliDiffEntries (s2.dir / "ro")) == 1) "the driver wrote a layer under --no-cache" },
    { name := "cache: --cache-prune DAYS checks its argument in both, and prunes before the run", run := fun _ => withSelfhostCli fun exe => do
        let host ← cliDiffHost
        let files := #[("p.wiz", cliGood)]
        -- (the host's `takeCachePrune` errors: the message alone, exit 1, in both)
        for days in ["0", "x"] do
          let spec : CliDiffSpec := { files := files, args := #["check", "p.wiz", "--cache-prune", days] }
          let (h, s) ← cliDiffBoth host exe spec
          cliDiffSame spec h s
          checkEq 1 s.code
          checkEq 1 h.code
        -- a prune before a run: both exit 0 and print the same summary (the four keyed
        -- extensions `.wizc`, `.wizm`, `.wizr`, `.wizs`; `c/.keep` makes the write cache
        -- exist, as a warm run would)
        let spec2 : CliDiffSpec :=
          { files := files.push ("c/.keep", "")
            args := #["check", "p.wiz", "--cache", "c", "--cache-prune", "7"] }
        let (h2, s2) ← cliDiffBoth host exe spec2
        cliDiffSame spec2 h2 s2
        checkEq 0 h2.code
        checkEq 0 s2.code
        checkEq ("cache prune: removed 0 files (0 .wizc, 0 .wizm, 0 .wizr, 0 .wizs), " ++
          "0 B older than 7 days in c\n") s2.err },
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
        cliDiffKnown "artifact: `build` writes an executable (via C), the self-hosted `build` the generated C (D4)" },
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
            cliDiffKnown "artifact: --lib's object/header/C match the host's shapes now; --no-main does not link without a `main` on this platform (the host's Wasm path), the driver writes the C (D4/C9)"
          else do
            cliDiffSame spec2 h3 s3
            checkEq 0 s3.code
            cliDiffKnown "artifact: --no-main links an executable without a `main` in the host; the driver writes the C for one (D4/C9)" },
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
        -- (a program with a `main`: the host reaches its C write, and throws there)
        let spec : CliDiffSpec := { files := #[("hello.wiz", cliHello)]
                                    args := #["build", "hello.wiz", "-o", "nodir/out"] }
        let (h, s) ← cliDiffBoth host exe spec
        checkEq 1 h.code
        checkEq 1 s.code
        unless !(← cliDiffExists h "nodir/out") do throw (IO.userError "the host wrote an artifact")
        unless !(← cliDiffExists s "nodir/out") do throw (IO.userError "the driver wrote an artifact")
        cliDiffKnown "message: a missing `-o` directory is an uncaught `IO.FS.writeFile` exception in the host (a machine-dependent trace on stderr); the driver writes one line (`error: cannot write …`). Both exit 1 and write nothing (D4/D7)" },
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
        cliDiffKnown "artifact: `--header` is the driver's header-only output (the one-shot `--header` mode, reused by `build`); the host has no such flag (`--lib` writes OUT.h itself), so it rejects it (D4)" },
    { name := "build --llvm: the host has it, the self-hosted backend is C only (C5)", run := fun _ => withSelfhostCli fun exe => do
        let host ← cliDiffHost
        let tc ← cliDiffHostToolchain
        let spec : CliDiffSpec := { files := #[("good.wiz", cliDiffHello)]
                                    args := #["build", "good.wiz", "-o", "out", "--llvm"]
                                    hostArgs := tc }
        let (h, s) ← cliDiffBoth host exe spec
        -- (the driver has no LLVM path at all: it recognises the flag and refuses the
        -- target, C5, rather than calling it an unknown flag)
        checkEq 1 s.code
        cliCheck s.err "unsupported target llvm: the self-hosted backend emits C only (C5)" "the driver's rejection"
        if h.code == 0 then do
          check (← cliDiffExists h "out") "the host's LLVM build wrote no artifact"
          cliDiffKnown "backend: the host builds through textual LLVM IR (`--llvm`); the self-hosted backend is C only (C5)"
        else do
          let why := " ".intercalate ((cliDiffNormal spec.columns spec.messages spec.continuations h.err).splitOn "\n")
          cliDiffKnown s!"backend: --llvm selects the host's LLVM path (exit {h.code} here: {why}); the self-hosted backend is C only (C5)" },
    { name := "extensions: --include, --types and -v are the driver's own (the host rejects them)", run := fun _ => withSelfhostCli fun exe => do
        let host ← cliDiffHost
        let files := #[("good.wiz", cliGood)]
        for args in [#["check", "--include", ".", "good.wiz"], #["check", "good.wiz", "--types"],
                     #["check", "good.wiz", "-v"]] do
          let spec : CliDiffSpec := { files := files, args := args }
          let (h, s) ← cliDiffBoth host exe spec
          checkEq 2 h.code
          checkEq 0 s.code
        cliDiffKnown "flags: the driver also has `--include` (an -I alias), `--types` and `-v`; the host has -I only and no verbose/type switch (its `wiz check` prints info already)" },
    { name := "subcommands: parse and fmt are the host's (the driver has no such command)", run := fun _ => withSelfhostCli fun exe => do
        let host ← cliDiffHost
        let files := #[("f.wiz", cliGood)]
        for args in [#["parse", "f.wiz"], #["fmt", "f.wiz"]] do
          let spec : CliDiffSpec := { files := files, args := args }
          let (h, s) ← cliDiffBoth host exe spec
          checkEq 0 h.code
          checkEq 2 s.code
          checkEq "" s.out
          cliCheck s.err s!"unknown command: {" ".intercalate args.toList}" "the driver's rejection"
        cliDiffKnown "subcommands: parse, doc, fmt, repl, test-driver, cache prune|verify|manifest and lsp are the host's; the driver has check/build/run/version/help (D2/D8)" },
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
          cliDiffKnown "`run`: the driver passes the words after FILE to the program (`run FILE ARG…`); the host's `run` has no program arguments and rejects them (exit 2)" },
    { name := "help and version: the version line is exact and both usage texts are pinned", run := fun _ => withSelfhostCli fun exe => do
        let host ← cliDiffHost
        let spec : CliDiffSpec := { args := #["--version"] }
        let (h, s) ← cliDiffBoth host exe spec
        cliDiffSame spec h s
        checkEq 0 s.code
        -- (the whole line, not just a prefix: `wiz VERSION` from one source)
        checkEq (h.out.replace "wiz-selfhost" "wiz") (s.out.replace "wiz-selfhost" "wiz")
        checkEq s!"wiz {Wiz.version}\n" (s.out.replace "wiz-selfhost" "wiz")
        let spec2 : CliDiffSpec := { args := #["--help"] }
        let (h2, s2) ← cliDiffBoth host exe spec2
        checkEq 0 h2.code
        checkEq 0 s2.code
        -- the driver's usage text verbatim, so a wording change is a test failure
        checkEq cliDiffDriverHelp s2.out
        -- and the exact command list it documents (D2): one line per subcommand
        let cmds := (s2.out.splitOn "\n").filter (fun l => l.startsWith "  wiz-selfhost ")
        checkEq ["  wiz-selfhost check FILE         elaborate and type check FILE (diagnostics on",
                 "  wiz-selfhost build FILE -o OUT  write the generated C to OUT",
                 "  wiz-selfhost run FILE [ARG]...  compile `main` and run it (also `eval`)",
                 "  wiz-selfhost version            print the version (also --version)",
                 "  wiz-selfhost help               this text (also -h, --help)",
                 "  wiz-selfhost lsp                a language server on stdin/stdout: initialize,"] cmds
        -- (the host's own list is the difference: these are the lines it has and the
        -- driver does not; each is asserted so implementing one fails the case)
        for word in ["parse", "repl", "test-driver", "doc", "fmt", "cache prune"] do
          cliCheck h2.out (s!"  wiz {word}") "host help"
          unless !((s2.out.splitOn (s!"  wiz-selfhost {word}")).length > 1) do
            throw (IO.userError s!"the driver now documents `{word}`: promote this case")
        cliDiffKnown "usage text: the driver lists check/build/run/version/help/lsp; the host lists those and parse, repl, test-driver, doc, fmt, cache prune/verify/manifest (D2/D8)" },
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
        cliDiffKnown "warnings: the host warns (on stdout) about a module root shadowing its own lib; the self-hosted loader canonicalises Prelude to the embedded prelude and has no warning channel yet (A14/D6)" },
    { name := "(C14) check --trust-native: native_refl is accepted in both, before or after the command", run := fun _ => withSelfhostCli fun exe => do
        let host ← cliDiffHost
        let files := #[("native.wiz", cliNativeRefl)]
        for args in [#["check", "native.wiz", "--trust-native"],
                     #["--trust-native", "check", "native.wiz"]] do
          let spec : CliDiffSpec := { files := files, args := args }
          let (h, s) ← cliDiffBoth host exe spec
          checkEq 0 h.code
          checkEq 0 s.code
          checkEq "" s.out
          checkEq "" s.err
          checkEq "" h.err
          cliCheck h.out "is accepted on the strength of native evaluation" "the host's warning"
        cliDiffKnown "warning: the host reports the acceptance as a warning naming the steps; the self-hosted frontend has no warning channel, and the `X.native✝` axiom is visible through `#print axioms` instead (D6/C14)" },
    { name := "(C14) check without --trust-native: native_refl is refused with the host's message in both", run := fun _ => withSelfhostCli fun exe => do
        let host ← cliDiffHost
        let spec : CliDiffSpec := { files := #[("native.wiz", cliNativeRefl)]
                                    args := #["check", "native.wiz"], columns := false }
        let (h, s) ← cliDiffBoth host exe spec
        cliDiffSame spec h s
        checkEq 1 h.code
        checkEq 1 s.code
        checkEq "" s.out
        checkEq "native.wiz:2:1: error: native evaluation is not enabled: `native_refl` decides an equation by running compiled code, which the kernel does not check; run with --trust-native to allow it\n" s.err },
    { name := "(C14) build --trust-native: both accept the flag and write an artifact (an executable there, the C here)", run := fun _ => withSelfhostCli fun exe => do
        let host ← cliDiffHost
        let tc ← cliDiffHostToolchain
        -- (the host's `build` needs a `main`; the driver writes the C without one)
        let spec : CliDiffSpec := { files := #[("nmain.wiz", cliNativeReflMain)]
                                    args := #["build", "nmain.wiz", "-o", "out", "--trust-native"]
                                    hostArgs := tc }
        let (h, s) ← cliDiffBoth host exe spec
        cliDiffSame spec h s
        checkEq 0 h.code
        checkEq 0 s.code
        check (← cliDiffExists h "out") "the host wrote no artifact"
        check (← cliDiffExists s "out") "the driver wrote no C"
        let sc ← cliDiffRead s "out"
        check (cliHas (sc.getD "") "/* x : ") "the driver's artifact is not the C for `x`"
        cliDiffKnown "artifact: `build` writes an executable (via C) in the host and the generated C here (D4)" },
    { name := "(C14) an unknown trust flag is the same usage error, before or after the command", run := fun _ => withSelfhostCli fun exe => do
        let host ← cliDiffHost
        let files := #[("native.wiz", cliNativeRefl)]
        -- (the host's `--trust-native` is a switch: its value form is left over as an
        -- unknown flag; a misspelling is one in both)
        for bad in ["--trust-native=1", "--trust-nativ"] do
          for args in [#["check", "native.wiz", bad], #[bad, "check", "native.wiz"]] do
            let spec : CliDiffSpec := { files := files, args := args }
            let (h, s) ← cliDiffBoth host exe spec
            cliDiffSame spec h s
            checkEq 2 h.code
            checkEq 2 s.code
            cliCheck s.err s!"unknown flag: {bad}" "the unknown flag's text" },
    { name := "(C14) --native-fuel: the host takes a step limit, the driver's evaluator has no counter", run := fun _ => withSelfhostCli fun exe => do
        let host ← cliDiffHost
        let spec : CliDiffSpec := { files := #[("native.wiz", cliNativeRefl)]
                                    args := #["check", "native.wiz", "--trust-native", "--native-fuel", "100"] }
        let (h, s) ← cliDiffBoth host exe spec
        checkEq 0 h.code
        checkEq 2 s.code
        cliCheck s.err "unknown flag: --native-fuel" "the driver's rejection"
        cliDiffKnown "native fuel: the self-hosted evaluator has no step counter, so `--native-fuel N` is refused as an unknown flag rather than accepted and ignored (C14)" },
    { name := "a missing file: one positioned diagnostic in both (exit 1)", run := fun _ => withSelfhostCli fun exe => do
        let host ← cliDiffHost
        let spec : CliDiffSpec := { args := #["check", "no.wiz"] }
        let (h, s) ← cliDiffBoth host exe spec
        cliDiffSame spec h s
        checkEq 1 s.code
        checkEq 1 h.code
        checkEq "" s.out
        checkEq "no.wiz:1:1: error: no such file\n" s.err
        checkEq "no.wiz:1:1: error: no such file\n" h.err }
  ]

builtin_initialize registerGroup cliDiffGroup

end Tests.Elab
