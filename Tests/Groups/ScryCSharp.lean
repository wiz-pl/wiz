import Wiz
import Tests.Harness

/-!
# Tests for scry's C# frontend (`Scry.CsCst`, `Scry.CsLower`)

The design is `scry/CSHARP.md`. C# is parsed by the vendored **tree-sitter-c-sharp**
(`scry/native/README.md`) through the shim; every fixture under `scry/corpus/csharp/`
has its checked-in `scry-cst` spill next to it (`FILE.cs` → `FILE.cst`, regenerated with
`scry-cst FILE.cs > FILE.cst`), so the tests need no native build, like `scry-c2wil`.

* **Spills**: each spill is a `c_sharp` store whose root spans its `.cs` text (a stale
  spill fails here first).
* **View goldens**: each `parse/*.cs` through `Scry.Cs.ofStore` against its `*.sexp`, a
  tree-sitter-style S-expression with field names: the grammar's tree as the lowering
  sees it (named nodes, field tokens, and the normalised fields of `Scry.CsCst`).
* **Lowering golden**: `lower/*.cs` against `*.wil` (every lowered function and the
  warnings), plus an execution check: a lowered C# method runs under `Wil.runFunction`
  and returns the value C# would.
* **End-to-end taint**: `taint/cwe78-process-unsafe.cs` (console input reaches
  `Process.Start` through string concatenation) fires the `command-injection` rule of
  `scry/corpus/csharp/csharp.scry`; its sanitised twin (`int.Parse` first) does not. Two
  more unsafe fixtures cover interpolation plus a `ProcessStartInfo` object, and an
  instance helper method (interprocedural parameter/return flow).

A golden mismatch prints the actual text. Setting `SCRY_CS_WRITE=1` writes the actual
text over the expected file **and still fails the case**, so a regenerated golden is
always reviewed in the diff and never passes silently.
-/

open Wiz

namespace Tests.ScryCSharp

/-- Every `lib/*.wiz`, `lib/D/*.wiz` (as `D.X`) and `scry/src/Scry/*.wiz` (as `Scry.X`). -/
def loader : IO (Name → Option String) := do
  let mut m : List (Name × String) := []
  for e in ← System.FilePath.readDir "lib" do
    if e.path.extension == some "wiz" then
      m := (e.path.fileStem.getD "", ← IO.FS.readFile e.path) :: m
    else if ← e.path.isDir then
      for f in ← System.FilePath.readDir e.path do
        if f.path.extension == some "wiz" then
          m := (e.fileName ++ "." ++ f.path.fileStem.getD "", ← IO.FS.readFile f.path) :: m
  for e in ← System.FilePath.readDir "scry/src/Scry" do
    if e.path.extension == some "wiz" then
      m := ("Scry." ++ e.path.fileStem.getD "", ← IO.FS.readFile e.path) :: m
  pure fun n => m.lookup n

/-- A Wiz string literal for `s`. -/
def wizStr (s : String) : String :=
  "\"" ++ s.foldl (fun acc c => acc ++ match c with
    | '"' => "\\\""
    | '\\' => "\\\\"
    | '\n' => "\\n"
    | '\t' => "\\t"
    | c => c.toString) "" ++ "\""

/-- Undo `#eval`'s quoting of a string result (`"…"` with `\"`, `\\`, `\n`, `\t`). -/
def unquote (s : String) : String := Id.run do
  let cs := s.toList
  let cs := if cs.head? == some '"' then cs.drop 1 else cs
  let cs := if cs.getLast? == some '"' then cs.dropLast else cs
  let mut out := ""
  let mut esc := false
  for c in cs do
    if esc then
      out := out.push (match c with
        | 'n' => '\n'
        | 't' => '\t'
        | c => c)
      esc := false
    else if c == '\\' then esc := true
    else out := out.push c
  pure out

/-- Run `body` (after the imports) and return the `#eval` message texts. -/
def runProbe (imports body : String) : IO (List String) := do
  let src := imports ++ body ++ "\n"
  let loader ← loader
  let s := runFrontend (R := ZeroOneMany) src { trustedModule := Tests.libModule, loader }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render src
  unless errs.isEmpty do
    throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
  pure (s.messages.toList.map (·.text))

def parseImports : String := "import Scry.CsCst\nimport Scry.CstStore\n"
def lowerImports : String := "import Scry.CsLower\n"
def taintImports : String :=
  "import Scry.CsLower\nimport Scry.Rules\nimport Scry.Models\nimport Scry.RuleTaint\nimport Scry.Interproc\n"

/-- A fixture's C# text and its checked-in spill (`dir/name.cs`, `dir/name.cst`). -/
def fixture (dir name : String) : IO (String × String) := do
  let src ← IO.FS.readFile s!"scry/corpus/csharp/{dir}/{name}.cs"
  let spill ← IO.FS.readFile s!"scry/corpus/csharp/{dir}/{name}.cst"
  pure (src, spill)

/-- The Wiz definitions `src` and `spill` of a fixture. -/
def fixtureDefs (src spill : String) : String :=
  s!"def src : String := {wizStr src}\n" ++ s!"def spill : String := {wizStr spill}\n"

/-- Every fixture, as `(dir, name)`. -/
def fixtures : List (String × String) :=
  [("parse", "hello"), ("parse", "members"), ("parse", "statements"), ("parse", "expressions"),
   ("lower", "basic"), ("taint", "cwe78-process-unsafe"), ("taint", "cwe78-process-safe"),
   ("taint", "cwe78-startinfo-unsafe"), ("taint", "cwe78-helper-unsafe")]

/-- Compare `actual` with the golden file `path` (see the module doc for `SCRY_CS_WRITE`). -/
def golden (path : String) (actual : String) : IO Unit := do
  let actual := String.ofList (actual.toList.reverse.dropWhile Char.isWhitespace).reverse ++ "\n"
  if (← IO.getEnv "SCRY_CS_WRITE").isSome then
    IO.FS.writeFile path actual
    throw (IO.userError s!"SCRY_CS_WRITE: wrote {path}; review the diff and rerun without it")
  let expected ← (try IO.FS.readFile path catch _ => pure "")
  unless expected == actual do
    throw (IO.userError s!"golden {path} differs; actual:\n{actual}")

def parseGolden (name : String) : IO Unit := do
  let (src, spill) ← fixture "parse" name
  match ← runProbe parseImports (fixtureDefs src spill ++
      s!"#eval Scry.Cs.renderSpill {wizStr (name ++ ".cs")} src spill\n") with
  | [m] => golden s!"scry/corpus/csharp/parse/{name}.sexp" (unquote m)
  | ms => throw (IO.userError s!"expected one #eval message, got {ms.length}: {ms}")

def lowerGolden (name : String) : IO Unit := do
  let (src, spill) ← fixture "lower" name
  match ← runProbe lowerImports (fixtureDefs src spill ++
      s!"#eval Scry.Cs.lowerRender {wizStr (name ++ ".cs")} src spill\n") with
  | [m] => golden s!"scry/corpus/csharp/lower/{name}.wil" (unquote m)
  | ms => throw (IO.userError s!"expected one #eval message, got {ms.length}: {ms}")

/-- A spill's freshness, read from its text (no Wiz evaluation): the `language` is
`c_sharp`, the `bytes` row is the `.cs` file's UTF-8 size, and the root's span starts at
0 with only whitespace after it. -/
def spillCheck (dir name : String) : IO String := do
  let (src, spill) ← fixture dir name
  let lines := (spill.splitOn "\n").toArray
  let after (h : String) : Option String := do
    let i ← lines.findIdx? (· == h)
    lines[i + 1]?
  let lang := (lines.find? (·.startsWith "language\t")).map (·.drop 9)
  let bytes := after "bytes\t1"
  let root := (lines.find? (·.startsWith "nodes\t")).bind fun h =>
    (lines.findIdx? (· == h)).bind fun i => lines[i + 1]?
  let (start, stop) := match root.map (·.splitOn "\t") with
    | some [_, _, _, _, _, a, b] => (a.toNat!, b.toNat!)
    | _ => (1, 0)
  let tailWs := (src.toList.drop stop).all (fun c => c == ' ' || c == '\n' || c == '\r')
  if lang == some "c_sharp" && bytes == some (toString src.utf8ByteSize) && start == 0 && tailWs then
    pure s!"{dir}/{name}: ok"
  else
    pure s!"{dir}/{name}: stale (language {lang}, bytes {bytes} of {src.utf8ByteSize}, root {start}..{stop})"

/-- The findings of the C# rule pack on a taint fixture, one `rule func arg` line each. -/
def taintFindings (name : String) : IO (List String) := do
  let (src, spill) ← fixture "taint" name
  let pack ← IO.FS.readFile "scry/corpus/csharp/csharp.scry"
  let body :=
    fixtureDefs src spill ++
    s!"def pack : Scry.RulePack := Scry.parseRulePack {wizStr pack}\n" ++
    s!"def prog : Wil.Program := Scry.Cs.programOf {wizStr (name ++ ".cs")} src spill\n" ++
    "def line (f : Scry.RuleFinding) : String := f.rule ++ \" \" ++ f.func ++ \" \" ++ f.name ++ \" arg \" ++ Nat.repr f.arg\n" ++
    "#eval List.length prog.funcs\n" ++
    "#eval String.intercalate \"|\" (List.map line (Scry.programFindings (Scry.analyze prog pack)))\n"
  match ← runProbe taintImports body with
  | [nf, fs] =>
    if nf == "0" then throw (IO.userError s!"{name}: the frontend produced no functions")
    let fs := unquote fs
    pure (if fs.isEmpty then [] else fs.splitOn "|")
  | ms => throw (IO.userError s!"expected two #eval messages, got {ms}")

def group : Group where
  name := "scry-csharp"
  exercise := "scry C# frontend (tree-sitter-c-sharp view, lowering, taint)"
  cases := [
    { name := "spills: every fixture's spill is tree-sitter-c-sharp and spans its text",
      run := fun _ => do
        let mut rs := []
        for (d, n) in fixtures do
          rs := rs ++ [← spillCheck d n]
        checkEq (fixtures.map fun (d, n) => s!"{d}/{n}: ok") rs },
    { name := "view: using, namespace, static class, Main, conditional, interpolation",
      run := fun _ => parseGolden "hello" },
    { name := "view: file-scoped namespace, generics, fields, properties, constructor, enum, struct, interface",
      run := fun _ => parseGolden "members" },
    { name := "view: for/foreach/while/do/if/switch/try-catch-finally/using/throw",
      run := fun _ => parseGolden "statements" },
    { name := "view: precedence, casts, is/as, new forms, lambdas, generic calls, ref/out, interpolation",
      run := fun _ => parseGolden "expressions" },
    { name := "lower: classes, fields, constructors, calls, strings, control flow, try/catch to Wil",
      run := fun _ => lowerGolden "basic" },
    { name := "lower: a lowered C# loop runs under Wil.runFunction (Sum(10) = 45, Fact(5) = 120)",
      run := fun _ => do
        let (src, spill) ← fixture "lower" "basic"
        let body :=
          fixtureDefs src spill ++
          "def prog : Wil.Program := Scry.Cs.programOf \"basic.cs\" src spill\n" ++
          "#eval Wil.Result.show (Wil.runFunction prog 10000 \"Demo.Calc.Sum\" [Wil.Val.ofNat 32 .true 10])\n" ++
          "#eval Wil.Result.show (Wil.runFunction prog 10000 \"Demo.Calc.Fact\" [Wil.Val.ofNat 32 .true 5])\n"
        let ms ← runProbe lowerImports body
        checkEq ["\"ok 45\"", "\"ok 120\""] ms },
    { name := "taint: CWE-78, console input concatenated into Process.Start fires command-injection",
      run := fun _ => do
        let fs ← taintFindings "cwe78-process-unsafe"
        checkEq ["command-injection Fixtures.Runner.Main System.Diagnostics.Process.Start arg 1"] fs },
    { name := "taint: CWE-78 sanitised twin (int.Parse before Process.Start) has no finding",
      run := fun _ => do
        let fs ← taintFindings "cwe78-process-safe"
        checkEq ([] : List String) fs },
    { name := "taint: CWE-78 through interpolation and a ProcessStartInfo object (constructor and receiver)",
      run := fun _ => do
        let fs ← taintFindings "cwe78-startinfo-unsafe"
        checkEq ["command-injection Fixtures.Pinger.Ping System.Diagnostics.ProcessStartInfo..ctor arg 1",
          "command-injection Fixtures.Pinger.Ping System.Diagnostics.Process.Start arg 0"] fs },
    { name := "taint: CWE-78 across an instance helper (parameter and return summary)",
      run := fun _ => do
        let fs ← taintFindings "cwe78-helper-unsafe"
        checkEq ["command-injection Fixtures.Shell.Run System.Diagnostics.Process.Start arg 1"] fs }
  ]

builtin_initialize registerGroup group

end Tests.ScryCSharp
