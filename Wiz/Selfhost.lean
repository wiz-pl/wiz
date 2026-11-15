import Wiz.Parser.Builtin
import Wiz.Version

/-!
# The self-hosted toolchain's sources (stage 23e)

The self-hosted programs are one Wiz file each: the `selfhost/*.wiz` sources (their
imports dropped: they are concatenated), the parser tables generated from the Lean
parser's (`wizTables`), and the driver (`selfhost/Cli.wiz`, stage 21 D2-D7: subcommands,
module roots, `-o`, a cache, positioned diagnostics, exit codes). The tests
(`Tests/Elab.lean`) and grail (`Grail/Selfhost.lean`) both build them from here.
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

/-- The driver (stage 21 D2-D7): the command line, as real Wiz source rather than
generated strings. It is the last of `compilerFiles`, so `compilerSource` can put it
after the parser tables (`cats`, `tokens`). -/
def driverFiles : List String := ["selfhost/Cli.wiz"]

def compilerFiles : List String := checkerFiles ++ ["selfhost/Backend.wiz"] ++ driverFiles

/-- The toolchain's identity, for the driver's cache key (source + toolchain): the
version (`Wiz.Version.version`, one source for every tool) and the sources themselves.
Any change to the selfhost sources makes the cache cold. -/
def toolchainId (srcs : List String) : String :=
  s!"{hash (Wiz.version ++ "\n".intercalate srcs)}"

/-- The self-hosted checker: reads `input.wiz` (and the modules it imports, with `-I`
roots) and prints what the frontend makes of them. -/
def checkerSource (srcs : List String) : String :=
  "import IO\nimport Std\n" ++ "\n".intercalate (srcs.map strip) ++ "\n" ++ tablesSource ++
    "def main : IO Unit := moduleMain cats tokens\n"

/-- The self-hosted compiler, with the driver (`selfhost/Cli.wiz`) last: `--rc` (or
`--rc-owned`, `--gc`) on its command line picks the backend's mode (stage 21k;
`genProgramArgs`). The driver's `main` is the command line; without a subcommand it is
the one-shot tool (reads `input.wiz` in the working directory and prints C, the
frontend's output as comments; the errors go to standard error and the exit code is 1,
15g). A `link_c` file that doesn't exist is such an error too (stage 21t,
`missingLinks`). -/
def compilerSource (srcs : List String) : String :=
  let lang := srcs.take (srcs.length - 1)
  let driver := srcs.drop lang.length
  "import IO\nimport Std\nimport Sys\n" ++ "\n".intercalate (lang.map strip) ++ "\n" ++ tablesSource ++
    "def wizVersion : String := " ++ wizLit Wiz.version ++ "\n" ++
    "def toolchainId : String := " ++ wizLit (toolchainId srcs) ++ "\n" ++
    "\n".intercalate (driver.map strip)

/-- The toolchain as its own input (for the bootstrap check): the compiler's source, with
`import Prelude` (the self-hosted frontend's prelude) instead of the Lean libraries. -/
def selfSource (srcs : List String) : String :=
  "import Prelude\n" ++ strip (compilerSource srcs)

end Wiz.Selfhost
