import Wiz.Parser.Builtin

/-!
# The self-hosted toolchain's sources (stage 23e)

The self-hosted programs are one Wiz file each: the `selfhost/*.wiz` sources (their
imports dropped: they are concatenated), the parser tables generated from the Lean
parser's (`wizTables`), and a `main`. The tests (`Tests/Elab.lean`) and grail
(`Grail/Selfhost.lean`) both build them from here.
-/

namespace Wiz.Selfhost

/-- A Wiz string literal. -/
def wizLit (s : String) : String :=
  "\"" ++ String.join (s.toList.map fun c => if c == '"' then "\\\"" else if c == '\\' then "\\\\" else if c == '\n' then "\\n" else c.toString) ++ "\""

/-- A grammar descriptor as a Wiz `PD` (`selfhost/Parse.wiz`): sequences become binary. -/
partial def wizPD : ParserDescr → String
  | .atom t => s!"(PD.atom {wizLit t})"
  | .nonReserved t => s!"(PD.nonReserved {wizLit t})"
  | .ident => "PD.ident"
  | .num => "PD.num"
  | .str => "PD.str"
  | .cat c p => s!"(PD.cat {wizLit c} {p})"
  | .seq ps => ps.toList.foldr (fun p acc => if acc == "PD.empty" then wizPD p else s!"(PD.seq {wizPD p} {acc})") "PD.empty"
  | .many p => s!"(PD.many {wizPD p})"
  | .many1 p => s!"(PD.many1 {wizPD p})"
  | .optional p => s!"(PD.optional {wizPD p})"
  | .sepBy p sep t => s!"(PD.sepBy {wizPD p} {wizLit sep} {if t then ".true" else ".false"})"
  | .sepBy1 p sep t => s!"(PD.sepBy1 {wizPD p} {wizLit sep} {if t then ".true" else ".false"})"
  | .orelse p q => s!"(PD.orelse {wizPD p} {wizPD q})"
  | .node k p => s!"(PD.node {wizLit k} {wizPD p})"
  | .withPosition p => s!"(PD.withPosition {wizPD p})"
  | .withoutPosition p => s!"(PD.withoutPosition {wizPD p})"
  | .colGt => "PD.colGt"
  | .colGe => "PD.colGe"
  | .noWs => "PD.noWs"
  | .checkPrec p => s!"(PD.checkPrec {p})"

/-- A Wiz list literal. -/
def wizList (xs : List String) : String := xs.foldr (fun x acc => s!"(.cons {x} {acc})") ".nil"

/-- The parser tables as Wiz definitions: one per category, then `cats`. -/
def wizTables (t : ParserTables) : String := Id.run do
  let names := (t.cats.toList.map (·.1)).toArray.qsort (· < ·)
  let mut out := ""
  let mut i := 0
  for n in names do
    let cat := t.cats[n]!
    let ls := cat.leading.toList.map fun lp => s!"(Leading.mk {wizLit lp.kind} {lp.prec} {lp.priority} {wizPD lp.p})"
    let ts := cat.trailing.toList.map fun tp => s!"(Trailing.mk {wizLit tp.kind} {tp.prec} {tp.lhsPrec} {tp.priority} {wizPD tp.p})"
    out := out ++ s!"def cat{i} : Cat := Cat.mk {wizLit n} {wizList ls} {wizList ts}\n"
    i := i + 1
  out := out ++ s!"def cats : List Cat := {wizList ((List.range names.size).map (s!"cat{·}"))}\n"
  pure out

/-- A source without its `import` lines. -/
def strip (f : String) : String :=
  "\n".intercalate ((f.splitOn "\n").filter (!·.startsWith "import"))

/-- The tables and the token list, as Wiz. -/
def tablesSource : String :=
  let t := Builtin.tables
  wizTables t ++ s!"def tokens : List String := {wizList (t.tokens.toList.map wizLit)}\n"

def checkerFiles : List String :=
  ["selfhost/Lex.wiz", "selfhost/Parse.wiz", "selfhost/Kernel.wiz", "selfhost/Frontend.wiz"]

def compilerFiles : List String := checkerFiles ++ ["selfhost/Backend.wiz"]

/-- The self-hosted checker: reads `input.wiz` (and the modules it imports, with `-I`
roots) and prints what the frontend makes of them. -/
def checkerSource (srcs : List String) : String :=
  "import IO\nimport Std\n" ++ "\n".intercalate (srcs.map strip) ++ "\n" ++ tablesSource ++
    "def main : IO Unit := moduleMain cats tokens\n"

/-- The self-hosted compiler: reads `input.wiz` and prints C (the frontend's output as
comments). `--rc` (or `--rc-owned`, `--gc`) on its command line picks the backend's
mode (stage 21k; `genProgramArgs`). If the frontend reports an error (a line starting
with `error`), the errors go to standard error, no C is printed and the exit code is 1
(15g: before, the definition was just missing from the C, with the message in a comment).
A `link_c` file that doesn't exist is such an error too (stage 21t, `missingLinks`). -/
def compilerSource (srcs : List String) : String :=
  "import IO\nimport Std\nimport Sys\n" ++ "\n".intercalate (srcs.map strip) ++ "\n" ++ tablesSource ++
    "def commentLines : List String → List String\n  | .nil => .nil\n  | .cons l rest => .cons (String.append \"/* \" (String.append l \" */\")) (commentLines rest)\n" ++
    "def errLine (l : String) : Bool := match l with\n  | .mk cs => match cs with\n" ++
    "    | .cons a (.cons b (.cons c (.cons d (.cons e _)))) => Bool.and (Nat.beq (Char.code a) 101) (Bool.and (Nat.beq (Char.code b) 114)\n" ++
    "        (Bool.and (Nat.beq (Char.code c) 114) (Bool.and (Nat.beq (Char.code d) 111) (Nat.beq (Char.code e) 114))))\n    | _ => .false\n" ++
    "def errLines : List String → List String\n  | .nil => .nil\n  | .cons l rest => match errLine l with\n    | .true => .cons l (errLines rest)\n    | .false => errLines rest\n" ++
    "def ePrintAll : List String → IO Unit\n  | .nil => IO.pure ()\n  | .cons s ss => do\n    IO.ePrintln s;\n    ePrintAll ss\n" ++
    "def finish (args : List String) (text : String) (out : List String) (gs : Globals) (missing : List String) : IO Unit :=\n" ++
    "  match List.append (errLines (List.reverseOf out .nil)) missing with\n  | .nil => do\n    printAll (commentLines (List.reverseOf out .nil));\n" ++
    "    printDocs (genProgramArgs args text gs)\n  | .cons e es => do\n    ePrintAll (.cons e es);\n    Process.exit 1\n" ++
    "def main : IO Unit := do\n  args ← IO.args;\n  text ← IO.readFile \"input.wiz\";\n" ++
    "  tab ← moduleRootSources cats tokens (modRoots args) text;\n" ++
    "  match modCheckRun cats tokens tab (.cons \"Main\" .nil) with\n" ++
    "    | .mk run _ _ _ => IO.bind (missingLinks (List.reverseOf (Globals.ffi (Run.gs run)) .nil)) (fun missing => finish args text (Run.out run) (Run.gs run) missing)\n"

/-- The toolchain as its own input (for the bootstrap check): the compiler's source, with
`import Prelude` (the self-hosted frontend's prelude) instead of the Lean libraries. -/
def selfSource (srcs : List String) : String :=
  "import Prelude\n" ++ strip (compilerSource srcs)

end Wiz.Selfhost
