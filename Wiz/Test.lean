/-!
# The `-- test:` directive (stages 23f, 11ah)

A test file is a `.wiz` file whose first line says how to run it:

* `-- test: check` (the default): the messages of elaborating the file, as `wiz check`
  prints them (`path:line:col: severity: text`);
* `-- test: run`: what `main` prints, as `wiz run` prints it.

The expected output is beside the file in `F.expected`, or after the kind on the
directive line (`-- test: run Hello\n`, with `\n`, `\t`, `\r` and `\\` escapes). The
grail test runner reads the same directive from `Grail/Test.lean`; keeping the parser
here means `wiz test FILE` and `grail test` agree on what a test is.
-/

namespace Wiz

inductive TestKind where
  | check
  | run
  deriving BEq, Repr, Inhabited

/-- The kind named by a directive's first word. -/
def TestKind.ofWord (w : String) : Except String TestKind :=
  match w with
  | "check" => .ok .check
  | "run" => .ok .run
  | k => .error s!"unknown test kind {k} (check, run)"

/-- The kind of a file, from its first line (as `grail test` has always read it). -/
def TestKind.ofSource (src : String) : Except String TestKind :=
  let first := (src.splitOn "\n").headD ""
  if !first.startsWith "-- test:" then .ok .check else
  TestKind.ofWord ((first.drop 8).trimAscii.toString)

/-- What a failing test without a `-- test:` line is told (it was taken for a `check`,
which compares the messages of elaborating the file: a program's output never shows up). -/
def TestKind.defaultNote (src : String) : String :=
  if ((src.splitOn "\n").headD "").startsWith "-- test:" then "" else
  "\n      (no `-- test:` line, so this was a `check` test: the expected output is the " ++
  "messages of checking the file; for what `main` prints, make `-- test: run` the first line)"

def TestKind.name : TestKind → String
  | .check => "check" | .run => "run"

/-- A test file's first line: its kind, and (when it is on the same line) the expected
output. -/
structure Directive where
  kind : TestKind
  /-- the expected output written after the kind, already unescaped -/
  expected : Option String := none
  deriving Repr

/-- Expand `\n`, `\t`, `\r` and `\\` in an inline expected output; another escape keeps
its backslash. -/
def unescape (s : String) : String := Id.run do
  let mut out := ""
  let mut esc := false
  for c in s.toList do
    if esc then
      match c with
      | 'n' => out := out.push '\n'
      | 't' => out := out.push '\t'
      | 'r' => out := out.push '\r'
      | '\\' => out := out.push '\\'
      | c => out := out.push '\\'; out := out.push c
      esc := false
    else if c == '\\' then esc := true
    else out := out.push c
  if esc then out := out.push '\\'
  return out

/-- The directive of a file: the first line, and its inline expected output if there is
one. Files without a directive are `check` tests (as in `grail test`). -/
def directiveOf (src : String) : Except String Directive := do
  let first := (src.splitOn "\n").headD ""
  if !first.startsWith "-- test:" then return { kind := .check }
  let rest := (first.drop 8).trimAscii.toString
  if rest.isEmpty then return { kind := .check }
  let (word, tail) := match rest.splitOn " " with
    | w :: ts => (w, " ".intercalate ts)
    | [] => (rest, "")
  let kind ← TestKind.ofWord word
  return { kind, expected := if tail.isEmpty then none else some (unescape tail) }

/-- The first line where two texts differ, for the report. -/
def firstDifference (expected actual : String) : String := Id.run do
  let es := expected.splitOn "\n"
  let as := actual.splitOn "\n"
  for i in [0:max es.length as.length] do
    let e := es[i]?.getD "<end>"
    let a := as[i]?.getD "<end>"
    if e != a then return s!"line {i + 1}:\n      expected: {e}\n      actual:   {a}"
  pure "(the same)"

/-- The expected output of the test at `path`, and where it lives. -/
def expectedOfFile (path : System.FilePath) : IO (System.FilePath × Option String) := do
  let expFile := path.withExtension "expected"
  pure (expFile, ← if ← expFile.pathExists then some <$> IO.FS.readFile expFile else pure none)

/-- The expected output of a test, and where it lives. -/
def expectedOf (dir : System.FilePath) (file : String) : IO (System.FilePath × Option String) :=
  expectedOfFile (dir / file)

end Wiz
