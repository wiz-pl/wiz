import Wiz
import Tests.Harness

/-!
# Tests for scry's C# frontend (`Scry.CsCst`, `Scry.CsLower`)

The design is `scry/CSHARP.md`. C# is parsed by **tree-sitter-c-sharp** (fetched by Nix,
`scry/native/README.md`) through the shim; every fixture under `scry/corpus/csharp/`
has its checked-in `scry-cst` spill next to it (`FILE.cs` → `FILE.cst`, regenerated with
`scry-cst FILE.cs > FILE.cst`), so the tests need no native build, like `scry-c2wil`.

* **Spills**: each spill is a `c_sharp` store whose root spans its `.cs` text (a stale
  spill fails here first).
* **View goldens**: each `parse/*.cs` through `Scry.Cs.ofStore` against its `*.sexp`, a
  tree-sitter-style S-expression with field names: the grammar's tree as the lowering
  sees it (named nodes, field tokens, and the normalised fields of `Scry.CsCst`).
* **Lowering golden**: `lower/*.cs` against `*.wil` (every lowered function and the
  warnings), plus an execution check: a lowered C# method runs under `Wil.runFunction`
  and returns the value C# would. `lower/modern` covers records, partial parts, switch
  expressions, LINQ, `with`, collection expressions and a constructor initialiser;
  `lower/toplevel` covers top-level statements (lowered as `<stem>.Main`);
  `lower/unsupported` is the warning golden for everything out of scope.
* **Silent skip**: `lower/{modern,toplevel,unsupported}` must each keep the warning that
  names every out-of-scope construct they contain. The case fails when one of them
  regresses from a warning to a silent skip (a construct that lowers to nothing without
  a diagnostic, so the analysis reports nothing about code it never read).
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

def csCmdImports : String :=
  "import Scry.CsCmd\nimport Scry.Wil\nimport Scry.Rules\nimport Scry.Interproc\nimport Json\n"

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
   ("parse", "modern"),
   ("lower", "basic"), ("lower", "modern"), ("lower", "toplevel"), ("lower", "unsupported"),
   ("taint", "cwe78-process-unsafe"), ("taint", "cwe78-process-safe"),
   ("taint", "cwe78-startinfo-unsafe"), ("taint", "cwe78-helper-unsafe"),
   ("taint", "cwe78-modern-unsafe"), ("taint", "cwe78-modern-safe")]

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

/-- The rendering of a lowered fixture (functions and warnings), read from the lowering
itself rather than from its golden. -/
def loweredText (name : String) : IO String := do
  let (src, spill) ← fixture "lower" name
  match ← runProbe lowerImports (fixtureDefs src spill ++
      s!"#eval Scry.Cs.lowerRender {wizStr (name ++ ".cs")} src spill\n") with
  | [m] => pure (unquote m)
  | ms => throw (IO.userError s!"expected one #eval message, got {ms.length}: {ms}")

/-- `(fixture, message substring)` pairs the lowering must still report. Every construct
of the first slice's out-of-scope list is here: the case fails when one of them regresses
from a warning to a **silent skip** (the analysis then says nothing about code it never
looked at), which is the failure mode this table exists to prevent. -/
def requiredWarnings : List (String × String) :=
  [("modern", "target-typed new() without a declared type"),
   ("modern", "local function Label not modelled"),
   ("modern", "is test not modelled"),
   ("modern", "switch expression arms are not compared"),
   ("modern", "with expression: the copy's members are not updated"),
   ("toplevel", "is test not modelled"),
   ("unsupported", "indexer_declaration member not modelled"),
   ("unsupported", "operator_declaration member not modelled"),
   ("unsupported", "destructor_declaration member not modelled"),
   ("unsupported", "delegate_declaration not modelled"),
   ("unsupported", "local function Local not modelled"),
   ("unsupported", "lambda body not lowered"),
   ("unsupported", "lock_statement not modelled"),
   ("unsupported", "goto_statement not modelled"),
   ("unsupported", "labeled_statement not modelled"),
   ("unsupported", "yield_statement not modelled"),
   ("unsupported", "preproc_if not modelled"),
   ("unsupported", "is test not modelled")]

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

/-! ## The `scry cs` fixture tree

`scry/corpus/csharp/repo/` is a small tree with two excluded directories and three
excluded file names. The group enumerates it with Lean's own `readDir` (the Wiz
interpreter cannot call `FS.listDir`), hands the listing to `Scry.Cs.walkOfPaths` (the
same exclusion rule the driver uses) and lowers the checked-in spills, so the report's
counts and coverage rows are the driver's own aggregation, not a second implementation.
`Broken.cs` has no spill: `scry-cst` refuses a tree with `ERROR` nodes, so the test builds
the `.err` result the native path produces. -/

partial def repoCs (dir : System.FilePath) (rel : String) : IO (List (String × String)) := do
  let mut out : List (String × String) := []
  for e in ← dir.readDir do
    let name := e.fileName
    let relC := if rel.isEmpty then name else rel ++ "/" ++ name
    if ← e.path.isDir then
      for c in ← repoCs e.path relC do
        out := c :: out
    else if name.endsWith ".cs" then
      out := (relC, e.path.toString) :: out
  pure out.reverse

def repoFiles : IO (List (String × String)) := do
  let fs ← repoCs ("scry/corpus/csharp/repo" : System.FilePath) ""
  pure (fs.toArray.qsort (fun a b => a.1 < b.1)).toList

/-- Wiz definitions for the whole tree: each `.cs` text, its spill when it has one, the
listing, and one `FileResult` per file. -/
def repoDefs (files : List (String × String)) : IO String := do
  let mut defs := ""
  let mut entries : List String := []
  let mut i := 0
  for (rel, full) in files do
    let text ← IO.FS.readFile full
    defs := defs ++ s!"def repoText{i} : String := {wizStr text}\n"
    let spillPath := (full.take (full.length - 3)).toString ++ ".cst"
    let spill? ← try some <$> IO.FS.readFile spillPath catch _ => pure none
    match spill? with
    | some spill =>
      defs := defs ++ s!"def repoSpill{i} : String := {wizStr spill}\n"
      entries := s!"  Scry.Cs.resultOfFront {wizStr rel} (Scry.Cs.frontend {wizStr rel} repoText{i} repoSpill{i})" :: entries
    | none =>
      entries := s!"  Scry.Cs.resultOfFront {wizStr rel} (.err \"deliberately invalid C#: the native parse fails\")" :: entries
    i := i + 1
  let paths := "[" ++ ", ".intercalate (files.map fun (r, _) => s!"({wizStr r}, {wizStr r})") ++ "]"
  pure (defs ++ s!"def repoPaths : List (String × String) := {paths}\n"
    ++ s!"def repoResults : List Scry.Cs.FileResult := [\n{",\n".intercalate entries.reverse}]\n")

/-- The tree's report, built by the same functions `scry cs` calls. -/
def repoBody (files : List (String × String)) : IO String := do
  let defs ← repoDefs files
  let pack ← IO.FS.readFile "scry/corpus/csharp/csharp.scry"
  pure (defs ++
    s!"def repoPack : Scry.RulePack := Scry.RulePack.withModels (Scry.parseRulePack {wizStr pack})\n" ++
    "def repoWalk : Scry.Cs.Walk := Scry.Cs.walkOfPaths repoPaths\n" ++
    "def repoKept : List Scry.Cs.FileResult := List.filter (fun r => List.any (fun p => String.eq p.1 r.path) repoWalk.files) repoResults\n" ++
    "def repoFuncs : List Wil.Func := List.concat (List.map (fun r => r.funcs) repoKept)\n" ++
    "def repoOrigins : Scry.OriginMap := Scry.Cs.originMapOf repoKept\n" ++
    "def repoProgram : Scry.ProgramResult := Scry.analyze (Wil.program repoFuncs) repoPack\n" ++
    "def repoFindings : List Scry.Cs.FindingRow := Scry.Cs.findingRows repoOrigins (Scry.programFindings repoProgram)\n" ++
    "def repoDiags : List Scry.Cs.CoverRow := Scry.Cs.coverageOfDiags (List.map (Scry.Cs.diagOfMem repoOrigins) repoProgram.warnings)\n" ++
    "def repoReport : Scry.Cs.Report := Scry.Cs.reportOf \"scry/corpus/csharp/repo\" \"directory\" repoWalk repoKept (.some \"scry/corpus/csharp/csharp.scry\") (List.length repoPack.rules) repoFindings repoDiags\n")

def oneMessage (what body : String) : IO String := do
  match ← runProbe csCmdImports body with
  | [m] => pure (unquote m)
  | ms => throw (IO.userError s!"{what}: expected one #eval message, got {ms.length}: {ms}")

def repoSummary : IO Unit := do
  let files ← repoFiles
  let body ← repoBody files
  golden "scry/corpus/csharp/repo/report.txt" (← oneMessage "repo summary" (body ++
    "#eval Scry.Cs.render repoReport\n"))

def repoJsonGolden : IO Unit := do
  let files ← repoFiles
  let body ← repoBody files
  golden "scry/corpus/csharp/repo/report.json" (← oneMessage "repo json" (body ++
    "#eval Json.render (Scry.Cs.jsonOf repoReport (Scry.Cs.statusOf (.report repoReport (.some .error))))\n"))

def repoCounts : IO Unit := do
  let files ← repoFiles
  let body ← repoBody files
  let m ← oneMessage "repo counts" (body ++
    "#eval \"before=\" ++ Nat.repr repoReport.before ++ \" found=\" ++ Nat.repr repoReport.found ++ \" excluded=\" ++ Nat.repr repoReport.excluded ++ \" parsed=\" ++ Nat.repr repoReport.parsed ++ \" lowered=\" ++ Nat.repr repoReport.lowered ++ \" failed=\" ++ Nat.repr repoReport.failed\n")
  checkEq "before=9 found=4 excluded=5 parsed=3 lowered=3 failed=1" m

def repoCoverage : IO Unit := do
  let files ← repoFiles
  let body ← repoBody files
  let m ← oneMessage "repo coverage" (body ++
    "#eval String.intercalate \"|\" (List.map (fun r => Scry.Severity.show r.level ++ \" \" ++ Nat.repr r.count ++ \" \" ++ r.construct) repoReport.coverage)\n")
  checkEq
    ("error 1 parse failure"
     ++ "|warning 3 unmodelled-external"
     ++ "|warning 1 lambda body not lowered: an opaque function value"
     ++ "|warning 1 query_expression not modelled: havoc"
     ++ "|note 1 excluded: *.Designer.cs"
     ++ "|note 1 excluded: *.g.cs"
     ++ "|note 1 excluded: bin/"
     ++ "|note 1 excluded: node_modules/"
     ++ "|note 1 excluded: obj/") m

def repoExitCodes : IO Unit := do
  let files ← repoFiles
  let body ← repoBody files
  let ms ← runProbe csCmdImports (body ++
    "def repoEmpty : Scry.Cs.Report := Scry.Cs.reportOf \"empty\" \"directory\" (Scry.Cs.walkOfPaths []) [] .none 0 [] []\n" ++
    "def repoFailed : Scry.Cs.Report := Scry.Cs.reportOf \"failed\" \"directory\" (Scry.Cs.walkOfPaths [(\"x.cs\",\"x.cs\")]) [Scry.Cs.resultOfFront \"x.cs\" (.err \"no parse\")] .none 0 [] []\n" ++
    "#eval Nat.repr (Scry.Cs.statusOf .usage)\n" ++
    "#eval Nat.repr (Scry.Cs.statusOf (.report repoEmpty (Option.none : Option Scry.Severity)))\n" ++
    "#eval Nat.repr (Scry.Cs.statusOf (.report repoFailed (Option.some .error)))\n" ++
    "#eval Nat.repr (Scry.Cs.statusOf (.report repoReport (Option.none : Option Scry.Severity)))\n" ++
    "#eval Nat.repr (Scry.Cs.statusOf (.report repoReport (Option.some .error)))\n" ++
    "#eval Nat.repr (Scry.Cs.statusOf (.report repoReport (Option.some .warning)))\n" ++
    "#eval match Scry.Cs.parseArgs [\"--bogus\"] with | .error _ => \"usage-error\" | .ok _ => \"accepted\"\n")
  checkEq ["2", "3", "3", "0", "1", "1", "usage-error"] (ms.map unquote)

def group : Group where
  name := "scry-csharp"
  exercise := "scry C# frontend (tree-sitter-c-sharp view, lowering, taint)"
  parallel := true
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
    { name := "view: record, switch expression, with, collection expression, query syntax",
      run := fun _ => parseGolden "modern" },
    { name := "lower: classes, fields, constructors, calls, strings, control flow, try/catch to Wil",
      run := fun _ => lowerGolden "basic" },
    { name := "lower: record and record struct, partial parts, switch expression, LINQ, with, collection, ctor init, async",
      run := fun _ => lowerGolden "modern" },
    { name := "lower: top-level statements become <stem>.Main (with the file's classes)",
      run := fun _ => lowerGolden "toplevel" },
    { name := "lower: out-of-scope constructs are reported by name, never skipped silently",
      run := fun _ => lowerGolden "unsupported" },
    { name := "silent skip: every out-of-scope construct keeps the warning that names it",
      run := fun _ => do
        let mut missing : List String := []
        for name in ["modern", "toplevel", "unsupported"] do
          let text ← loweredText name
          for (n, sub) in requiredWarnings do
            if n == name && !((text.splitOn sub).length > 1) then
              missing := s!"{name}: no warning contains \"{sub}\"" :: missing
        checkEq ([] : List String) missing.reverse },
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
        checkEq ["command-injection Fixtures.Shell.Run System.Diagnostics.Process.Start arg 1"] fs },
    { name := "taint: CWE-78 through a LINQ query, a switch expression, a record field and a with copy",
      run := fun _ => do
        let fs ← taintFindings "cwe78-modern-unsafe"
        checkEq ["command-injection Crux.Api.Endpoints.ReportEndpoints.Run System.Diagnostics.ProcessStartInfo.set_Arguments arg 1"] fs },
    { name := "taint: CWE-78 sanitised twin (int.Parse) over the same constructs has no finding",
      run := fun _ => do
        let fs ← taintFindings "cwe78-modern-safe"
        checkEq ([] : List String) fs },
    { name := "cs: the fixture tree's walk counts (before/after exclusions, parsed/lowered/failed)",
      run := fun _ => repoCounts },
    { name := "cs: the summary lists every skipped or warned construct with a count and an example",
      run := fun _ => repoCoverage },
    { name := "cs: the human report (counts, findings and coverage rows)",
      run := fun _ => repoSummary },
    { name := "cs: the JSON report (same counts, findings by rule and exit status)",
      run := fun _ => repoJsonGolden },
    { name := "cs: exit 0 clean, 1 gated, 2 usage, 3 nothing analysed",
      run := fun _ => repoExitCodes }
  ]

builtin_initialize registerGroup group

end Tests.ScryCSharp
