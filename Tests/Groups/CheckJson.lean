import Tests.Harness
import Lean.Data.Json

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

/-!
# `wiz check --json` and `wiz build --json` (format version 1)

The cases run this worktree's `wiz` as a child process, so they cover the contract a
tool sees: one JSON document on stdout, the human diagnostics on stderr, the same exit
status as the text mode, and a shape that `docs/schema/check-json-v1.json` documents.
-/

namespace Tests.CheckJson

open Lean (Json)

def get (j : Json) (k : String) : Json := (j.getObjVal? k).toOption.getD Json.null

def keys (j : Json) : List String :=
  match j with
  | .obj m => m.toList.map (·.1)
  | _ => []

def checkKeys (what : String) (expected : List String) (j : Json) : IO Unit := do
  let expected := expected.mergeSort (fun a b => decide (a ≤ b))
  let actual := (keys j).mergeSort (fun a b => decide (a ≤ b))
  unless actual == expected do
    throw (IO.userError s!"{what}: expected keys {expected}, got {actual}")

def str (j : Json) : String := (j.getStr?.toOption).getD ""
def nat (j : Json) : Nat := (j.getNat?.toOption).getD 0
def bool (j : Json) : Bool := (j.getBool?.toOption).getD false
def arr (j : Json) : Array Json := (j.getArr?.toOption).getD #[]

def codeOf (d : Json) : Option String := (get d "code").getStr?.toOption

def diags (j : Json) : Array Json := arr (get j "diagnostics")

def parseDoc (text : String) : IO Json :=
  match Json.parse text with
  | .ok j => pure j
  | .error e => throw (IO.userError s!"not JSON: {e}\n{text}")

structure Run where
  exit : UInt32
  stdout : String
  stderr : String

def wizPath : IO System.FilePath := do
  let p := ((← IO.appPath).parent.getD ".") / "wiz"
  unless ← p.pathExists do throw (IO.userError s!"no wiz beside the test driver: {p}")
  pure p

def runWiz (args : List String) : IO Run := do
  let wiz ← wizPath
  let out ← IO.Process.output { cmd := wiz.toString, args := args.toArray }
  pure { exit := out.exitCode, stdout := out.stdout, stderr := out.stderr }

/-- Run a JSON command and check the stream discipline: exactly one line on stdout, and
it is a JSON object. -/
def runJson (args : List String) : IO (Run × Json) := do
  let r ← runWiz args
  unless r.stdout.endsWith "\n" do
    throw (IO.userError s!"stdout does not end with a newline: {repr r.stdout}")
  let lines := r.stdout.trimAscii.toString.splitOn "\n"
  unless lines.length == 1 do
    throw (IO.userError s!"stdout is not one JSON document: {repr r.stdout}")
  pure (r, ← parseDoc r.stdout)

/-- A file in a fresh temporary directory (no case shares a path). -/
def tempFile (name text : String) : IO System.FilePath := do
  let dir ← IO.FS.createTempDir
  let p := dir / name
  IO.FS.writeFile p text
  pure p

/-- The character offset of the first `needle` (the frontend counts characters). -/
def charIndexOf (src needle : String) : Nat :=
  ((src.splitOn needle).headD "").toList.length

/-- The zero-based line and column of a character offset. -/
def lineColOf (src : String) (off : Nat) : Nat × Nat :=
  let pre := src.toList.take off
  (pre.count '\n', (pre.reverse.takeWhile (· != '\n')).length)

def docKeys : List String :=
  ["artifacts", "command", "diagnostics", "files", "ok", "tool", "version"]

def toolKeys : List String := ["commit", "name", "version"]
def diagKeys : List String :=
  ["code", "data", "fixes", "message", "notes", "related", "severity", "span"]
def spanKeys : List String := ["col", "end", "file", "line", "start"]
def fixKeys : List String := ["edits", "kind", "title"]
def editKeys : List String := ["newText", "span"]
def relatedKeys : List String := ["message", "span"]

/-- The golden shape: every level of the document has exactly the keys version 1
documents, and the schema documents exactly the same shape. A field added or removed in
the code or in the schema fails here until both are updated deliberately. -/
def checkShape (j : Json) : IO Unit := do
  checkKeys "document" docKeys j
  checkKeys "tool" toolKeys (get j "tool")
  for d in diags j do
    checkKeys "diagnostic" diagKeys d
    checkKeys "span" spanKeys (get d "span")
    for f in arr (get d "fixes") do
      checkKeys "fix" fixKeys f
      for e in arr (get f "edits") do
        checkKeys "edit" editKeys e
        checkKeys "edit span" spanKeys (get e "span")
  -- the schema's shape is the golden shape too
  let schema ← parseDoc (← IO.FS.readFile "docs/schema/check-json-v1.json")
  checkKeys "schema properties" docKeys (get schema "properties")
  let defs := get schema "$defs"
  checkKeys "schema diagnostic" diagKeys (get (get defs "diagnostic") "properties")
  checkKeys "schema span" spanKeys (get (get defs "span") "properties")
  checkKeys "schema fix" fixKeys (get (get defs "fix") "properties")
  checkKeys "schema edit" editKeys (get (get defs "edit") "properties")
  checkKeys "schema related" relatedKeys (get (get defs "related") "properties")

def fieldCheck (what : String) (j : Json) (expected : String) : IO Unit := do
  unless str (get j what) == expected do
    throw (IO.userError s!"{what}: expected {expected}, got {str (get j what)} in {j.compress}")

def severityCheck (d : Json) (expected : String) : IO Unit := fieldCheck "severity" d expected

def spanCheck (d : Json) (file : String) (src : String) (needle : String) (len : Nat) : IO Unit := do
  let sp := get d "span"
  let off := charIndexOf src needle
  let (line, col) := lineColOf src off
  unless str (get sp "file") == file do throw (IO.userError s!"span.file: {sp.compress}")
  unless nat (get sp "start") == off do
    throw (IO.userError s!"span.start: expected {off}, got {nat (get sp "start")} ({sp.compress})")
  unless nat (get sp "end") == off + len do
    throw (IO.userError s!"span.end: expected {off + len}, got {nat (get sp "end")} ({sp.compress})")
  unless nat (get sp "line") == line + 1 do
    throw (IO.userError s!"span.line: expected {line + 1}, got {nat (get sp "line")}")
  unless nat (get sp "col") == col + 1 do
    throw (IO.userError s!"span.col: expected {col + 1}, got {nat (get sp "col")}")

def group : Group where
  name := "wiz-json"
  exercise := "wiz check --json, format version 1"
  parallel := true
  cases := [
    { name := "clean: an empty diagnostics array, ok, exit 0", run := fun _ => do
        let src := "import Prelude\ndef two : Nat := 1 + 1\n"
        let p ← tempFile "clean.wiz" src
        let (r, j) ← runJson ["check", "--no-cache", "--json", p.toString]
        checkEq (0 : UInt32) r.exit
        checkEq "" r.stderr
        checkEq (1 : Nat) (nat (get j "version"))
        fieldCheck "command" j "check"
        fieldCheck "name" (get j "tool") "wiz"
        match get (get j "tool") "commit" with
        | .null | .str _ => pure ()
        | other => throw (IO.userError s!"tool.commit is neither a string nor null: {other.compress}")
        check (bool (get j "ok")) "ok is false"
        checkEq (#[] : Array Json) (diags j)
        checkEq [p.toString] ((arr (get j "files")).toList.map str)
        checkEq (#[] : Array String) (arr (get j "artifacts") |>.map str)
        checkShape j },
    { name := "error: code, message, span, and exit 1; stderr keeps the text", run := fun _ => do
        let src := "import Prelude\ndef bad : Nat := nope\n"
        let p ← tempFile "bad.wiz" src
        let (r, j) ← runJson ["check", "--no-cache", "--json", p.toString]
        checkEq (1 : UInt32) r.exit
        check (!r.stderr.isEmpty) "the human diagnostic is not on stderr"
        check ((r.stderr.splitOn "error: unknown identifier").length > 1) s!"stderr: {r.stderr}"
        check (!(bool (get j "ok"))) "ok is true with an error"
        let ds := diags j
        checkEq 1 ds.size
        let d := ds[0]!
        severityCheck d "error"
        checkEq (some "unknown-identifier") (codeOf d)
        check ((str (get d "message")).startsWith "unknown identifier") s!"message: {str (get d "message")}"
        spanCheck d p.toString src "nope" 4
        checkEq (#[] : Array Json) (arr (get d "related"))
        checkEq (#[] : Array Json) (arr (get d "notes"))
        checkShape j },
    { name := "warning only: exit 0, ok true, severity warning", run := fun _ => do
        let src := "import Word\ndef b : U8 := 300\n"
        let p ← tempFile "warn.wiz" src
        let (r, j) ← runJson ["check", "--no-cache", "--json", p.toString]
        checkEq (0 : UInt32) r.exit
        check ((r.stderr.splitOn "warning:").length > 1) s!"stderr: {r.stderr}"
        check (bool (get j "ok")) "ok is false for a warning"
        let ds := diags j
        checkEq 1 ds.size
        severityCheck ds[0]! "warning"
        checkEq (none : Option String) (codeOf ds[0]!)
        check (((str (get ds[0]! "message")).splitOn "does not fit").length > 1) s!"{(ds[0]!).compress}"
        spanCheck ds[0]! p.toString src "300" 3
        checkShape j },
    { name := "multiple files: files in argv order, diagnostics sorted by file", run := fun _ => do
        let srcZ := "import Prelude\ndef z : Nat := zz\n"
        let srcA := "import Prelude\ndef a : Nat := aa\n"
        let dir ← IO.FS.createTempDir
        let pz := dir / "z.wiz"
        let pa := dir / "a.wiz"
        IO.FS.writeFile pz srcZ
        IO.FS.writeFile pa srcA
        let (r, j) ← runJson ["check", "--no-cache", "--json", pz.toString, pa.toString]
        checkEq (1 : UInt32) r.exit
        checkEq [pz.toString, pa.toString] ((arr (get j "files")).toList.map str)
        let ds := diags j
        checkEq 2 ds.size
        checkEq pa.toString (str (get (get ds[0]! "span") "file"))
        checkEq pz.toString (str (get (get ds[1]! "span") "file"))
        checkEq (some "unknown-identifier") (codeOf ds[0]!)
        checkEq (some "unknown-identifier") (codeOf ds[1]!)
        checkShape j },
    { name := "astral characters: offsets and columns count Unicode scalar values", run := fun _ => do
        let src := "import Prelude\ndef emoji : String := \"😀\"\ndef bad : Nat := nope\n"
        let p ← tempFile "astral.wiz" src
        let (r, j) ← runJson ["check", "--no-cache", "--json", p.toString]
        checkEq (1 : UInt32) r.exit
        let d := (diags j)[0]!
        spanCheck d p.toString src "nope" 4
        -- 😀 is one character here: an LSP client's UTF-16 column would be one larger
        check (str (get (get d "span") "file") == p.toString) "span file"
        check (nat (get (get d "span") "start") > 0) "empty span"
        checkShape j },
    { name := "parse error: code parse-error and a point span", run := fun _ => do
        let src := "import Prelude\ndef := 1\n"
        let p ← tempFile "parse.wiz" src
        let (r, j) ← runJson ["check", "--no-cache", "--json", p.toString]
        checkEq (1 : UInt32) r.exit
        let d := (diags j)[0]!
        severityCheck d "error"
        checkEq (some "parse-error") (codeOf d)
        let sp := get d "span"
        checkEq (nat (get sp "start")) (nat (get sp "end"))
        checkEq (2 : Nat) (nat (get sp "line"))
        checkEq (5 : Nat) (nat (get sp "col"))
        checkShape j },
    { name := "an unreadable file: a diagnostic with a point span, not a crash", run := fun _ => do
        let dir ← IO.FS.createTempDir
        let p := dir / "missing.wiz"
        let (r, j) ← runJson ["check", "--no-cache", "--json", p.toString]
        checkEq (1 : UInt32) r.exit
        check (!r.stderr.isEmpty) "no human error on stderr"
        let d := (diags j)[0]!
        checkEq (none : Option String) (codeOf d)
        let sp := get d "span"
        checkEq p.toString (str (get sp "file"))
        checkEq (0 : Nat) (nat (get sp "start"))
        checkEq (0 : Nat) (nat (get sp "end"))
        checkEq (1 : Nat) (nat (get sp "line"))
        checkEq (1 : Nat) (nat (get sp "col"))
        checkShape j },
    { name := "--json-version 1 selects JSON without --json; another version is exit 2", run := fun _ => do
        let src := "import Prelude\ndef ok : Nat := 1\n"
        let p ← tempFile "version.wiz" src
        let (r, j) ← runJson ["check", "--no-cache", "--json-version", "1", p.toString]
        checkEq (0 : UInt32) r.exit
        checkEq (1 : Nat) (nat (get j "version"))
        let bad ← runWiz ["check", "--no-cache", "--json-version", "2", p.toString]
        checkEq (2 : UInt32) bad.exit
        checkEq "" bad.stdout
        check ((bad.stderr.splitOn "unsupported --json-version 2").length > 1) s!"stderr: {bad.stderr}" },
    { name := "fast build failure: the build document has the same shape", run := fun _ => do
        let src := "import Prelude\ndef bad : Nat := nope\n"
        let p ← tempFile "buildbad.wiz" src
        let (r, j) ← runJson ["build", "--no-cache", "--json", p.toString, "-o", (p.parent.getD "." / "out").toString]
        checkEq (1 : UInt32) r.exit
        fieldCheck "command" j "build"
        check (!(bool (get j "ok"))) "ok is true for a failed build"
        checkEq (#[] : Array String) (arr (get j "artifacts") |>.map str)
        checkEq 1 (diags j).size
        checkEq (some "unknown-identifier") (codeOf (diags j)[0]!)
        checkShape j },
    { name := "exit status is the text mode's (clean, warning, error)", run := fun _ => do
        for (name, src, expected) in [
            ("exitclean.wiz", "import Prelude\ndef ok : Nat := 1\n", (0 : UInt32)),
            ("exitwarn.wiz", "import Word\ndef b : U8 := 300\n", (0 : UInt32)),
            ("exiterr.wiz", "import Prelude\ndef bad : Nat := nope\n", (1 : UInt32))] do
          let p ← tempFile name src
          let text ← runWiz ["check", "--no-cache", p.toString]
          let (jrun, _) ← runJson ["check", "--no-cache", "--json", p.toString]
          checkEq expected text.exit
          checkEq text.exit jrun.exit },
    { name := "quick fixes and data: the same payload the LSP sends", run := fun _ => do
        let src := "import Prelude\ndef bad : Nat := Nat.addd 1 2\n"
        let p ← tempFile "fix.wiz" src
        let (_, j) ← runJson ["check", "--no-cache", "--json", p.toString]
        let d := (diags j)[0]!
        checkKeys "data" ["name", "suggestions"] (get d "data")
        let fixes := arr (get d "fixes")
        check (!fixes.isEmpty) s!"no quick fix: {d.compress}"
        let f := fixes[0]!
        check ((str (get f "title")).startsWith "Did you mean 'Nat.add'") s!"title: {get f "title"}"
        checkEq "quickfix" (str (get f "kind"))
        let e := (arr (get f "edits"))[0]!
        checkEq "Nat.add" (str (get e "newText"))
        checkShape j }
  ]

builtin_initialize registerGroup group

end Tests.CheckJson
