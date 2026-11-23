import Wiz.Parser.Builtin
import Wiz.Version

/-!
# The self-hosted toolchain's sources (stage 23e)

The self-hosted programs are one Wiz file each: the `selfhost/*.wiz` sources (their
imports dropped: they are concatenated) — including the parser tables
(`selfhost/Tables.wiz`, a checked-in file generated from the Lean parser's tables by
`scripts/GenSelfhostTables.lean`) and the driver (`selfhost/Cli.wiz`, stage 21 D2-D7:
subcommands, module roots, `-o`, a cache, positioned diagnostics, exit codes) — and a
`main` (`selfhost/Main.wiz`, `selfhost/Check.wiz`). The tests (`Tests/Elab.lean`) and
grail (`Grail/Selfhost.lean`) both build them from here.
-/

namespace Wiz.Selfhost

open ParserDescr

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

/-- (A13) The core tactic grammar, for the self-hosted frontend. The host reads tactics
from `syntax … : tactic` declarations in `lib/Prelude.wiz`; the self-hosted frontend has no
macro or `syntax` command, so the same shapes are built into the tables it is given. -/
def selfhostTacticRules : List LeadingParser :=
  [ { kind := "tactic.intro", prec := maxPrec, p := Builtin.seqs ["intro", ident] },
    { kind := "tactic.intros", prec := maxPrec, p := Builtin.seqs ["intros"] },
    { kind := "tactic.exact", prec := maxPrec, p := Builtin.seqs ["exact", cat "term" 0] },
    { kind := "tactic.apply", prec := maxPrec, p := Builtin.seqs ["apply", cat "term" 0] },
    { kind := "tactic.assumption", prec := maxPrec, p := Builtin.seqs ["assumption"] },
    { kind := "tactic.rfl", prec := maxPrec, p := Builtin.seqs ["rfl"] },
    { kind := "tactic.change", prec := maxPrec, p := Builtin.seqs ["change", cat "term" 0] },
    { kind := "tactic.unfold", prec := maxPrec, p := Builtin.seqs ["unfold", sepBy1 ident ","] },
    { kind := "tactic.constructor", prec := maxPrec, p := Builtin.seqs ["constructor"] },
    { kind := "tactic.rw", prec := maxPrec, p := Builtin.seqs ["rw", cat "term" 0] },
    { kind := "tactic.rwBack", prec := maxPrec, p := Builtin.seqs ["rw", "←", cat "term" 0] },
    { kind := "tactic.calc", prec := maxPrec,
      p := Builtin.seqs [nonReserved "calc", withPosition (many1 (Builtin.seqs [colGe, Builtin.calcStep]))] },
    { kind := "tactic.have", prec := maxPrec,
      p := Builtin.seqs ["have", ident, ":", cat "term" 0, optional (Builtin.seqs [":=", cat "term" 0])] },
    { kind := "tactic.suffices", prec := maxPrec, p := Builtin.seqs ["suffices", ident, ":", cat "term" 0] },
    { kind := "tactic.obtain", prec := maxPrec,
      p := Builtin.seqs ["obtain", "⟨", ident, ",", ident, "⟩", ":=", cat "term" 0] },
    { kind := "tactic.try", prec := maxPrec, p := Builtin.seqs ["try", cat "tactic" 0] },
    { kind := "tactic.first", prec := maxPrec,
      p := Builtin.seqs ["first", "|", cat "tactic" 0, "|", cat "tactic" 0] },
    { kind := "tactic.repeat", prec := maxPrec, p := Builtin.seqs ["repeat", cat "tactic" 0] },
    { kind := "tactic.paren", prec := maxPrec,
      p := Builtin.seqs ["(", sepBy (cat "tactic" 0) ";" true, ")"] } ]

def selfhostTables : ParserTables :=
  selfhostTacticRules.foldl (fun t lp => t.addLeading "tactic" lp) Builtin.tables

/-- The tables and the token list, as Wiz. -/
def tablesSource : String :=
  let t := selfhostTables
  wizTables t ++ s!"def tokens : List String := {wizList (t.tokens.toList.map wizLit)}\n"

/-- The header of `selfhost/Tables.wiz`: the generator, and what the file is. -/
def tablesFileHeader : String :=
  "-- Generated by `lake build genSelfhostTables` (`scripts/GenSelfhostTables.lean`); do not edit.\n" ++
  "-- The parser's grammar tables (`Wiz.Parser.Builtin.tables`), as Wiz data: one `catN`\n" ++
  "-- per category (sorted by name), then `cats` and `tokens`. The format is bootstrap\n" ++
  "-- ABI (`Cat`, `Leading`, `Trailing`, `PD.*` of `selfhost/Parse.wiz`): a seed parses\n" ++
  "-- this file with its own tables, so the constructors may not change without a seed\n" ++
  "-- bump (wiz-notes/post-lean-workflow.md §1.6, §5.1).\n"

/-- `selfhost/Tables.wiz`: the tables as a checked-in Wiz source file, which the
self-hosted programs read as one more module (the fixpoint's input set therefore holds
no generated Wiz text). `lake build genSelfhostTables` regenerates it and the `selfhost`
group fails when it is stale (`selfhost/Tables.wiz` vs `tablesFile`). (13v) The file is
wrapped in `namespace __root__` ... `end`, like the hand-written selfhost sources: batch
1 keeps the whole self-hosted tree global when the module path becomes the default
prefix, and a table file with a different shape would be a second kind of source. -/
def tablesFile : String := "namespace __root__\n" ++ tablesFileHeader ++ tablesSource ++ "end\n"

/-- The language: the modules the self-hosted frontend is made of, without an entry
point. Probes that build their own `main` use this list; the programs use
`checkerFiles`/`compilerFiles`. -/
def frontendFiles : List String :=
  ["selfhost/Lex.wiz", "selfhost/Parse.wiz", "selfhost/Kernel.wiz", "selfhost/CParse.wiz",
   "selfhost/CGlue.wiz", "selfhost/Frontend.wiz"]

/-- The generated tables (checked in: `selfhost/Tables.wiz`), read as a module like any
other; it defines `cats` and `tokens`. -/
def tableFiles : List String := ["selfhost/Tables.wiz"]

/-- The checker's entry point (`selfhost/Check.wiz`): `moduleMain cats tokens`. -/
def checkEntryFiles : List String := ["selfhost/Check.wiz"]

/-- The self-hosted checker's sources: the language, the tables and the entry point. -/
def checkerFiles : List String := frontendFiles ++ tableFiles ++ checkEntryFiles

/-- The driver (stage 21 D2-D7): the command line, as real Wiz source rather than
generated strings. It comes last but one in `compilerFiles` (before `Main.wiz`), so
`compilerSource` can put it after the parser tables (`cats`, `tokens`). -/
def driverFiles : List String := ["selfhost/Cli.wiz"]

/-- The compiler's entry point (`selfhost/Main.wiz`): `main` reads `IO.args` and calls
the driver's `dispatch`. Last, so everything it uses is before it. -/
def mainFiles : List String := ["selfhost/Main.wiz"]

def compilerFiles : List String :=
  frontendFiles ++ ["selfhost/Backend.wiz"] ++ tableFiles ++ driverFiles ++ mainFiles

/-- The toolchain's identity, for the driver's cache key (source + toolchain): the
version (`Wiz.Version.version`, one source for every tool) and the sources themselves.
Any change to the selfhost sources makes the cache cold. -/
def toolchainId (srcs : List String) : String :=
  s!"{hash (Wiz.version ++ "\n".intercalate srcs)}"

/-- The self-hosted checker: reads `input.wiz` (and the modules it imports, with `-I`
roots) and prints what the frontend makes of them. `srcs` is `checkerFiles`: the language,
the tables and `selfhost/Check.wiz`'s `main`. -/
def checkerSource (srcs : List String) : String :=
  "import IO\nimport Std\n" ++ "\n".intercalate (srcs.map strip)

/-- The self-hosted compiler, with the driver (`selfhost/Cli.wiz`) and then the entry
point (`selfhost/Main.wiz`) last: `--rc` (or `--rc-owned`, `--gc`) on its command line
picks the backend's mode (stage 21k; `genProgramArgs`). The driver's `main` is the
command line; without a subcommand it is the one-shot tool (reads `input.wiz` in the
working directory and prints C, the frontend's output as comments; the errors go to
standard error and the exit code is 1, 15g). A `link_c` file that doesn't exist is such
an error too (stage 21t, `missingLinks`).

`wizVersion` and `toolchainId` are the build's identity, not Wiz source: the release
string and a hash of these sources, which the driver keys its cache on. They are the one
thing the build has to pass in (the tables are `selfhost/Tables.wiz`). -/
def compilerSource (srcs : List String) : String :=
  "import IO\nimport Std\nimport Sys\n" ++
    "def wizVersion : String := " ++ wizLit Wiz.version ++ "\n" ++
    "def toolchainId : String := " ++ wizLit (toolchainId srcs) ++ "\n" ++
    "\n".intercalate (srcs.map strip)

/-- The toolchain as its own input (for the bootstrap check): the compiler's source, with
`import Prelude` (the self-hosted frontend's prelude) instead of the Lean libraries. -/
def selfSource (srcs : List String) : String :=
  "import Prelude\n" ++ strip (compilerSource srcs)

end Wiz.Selfhost
