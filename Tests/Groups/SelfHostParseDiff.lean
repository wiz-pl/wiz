import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

/-! A parser differential: the self-hosted parser (`selfhost/Lex.wiz` + `Parse.wiz`)
and the Lean parser are given the same tables (the ones the host frontend reaches after
loading `lib/Prelude.wiz`), and every `.wiz` under `lib/`, `examples/`, `selfhost/`,
`src/` and `scry/` is parsed by both. The first divergence per file is reported (a
different tree, or one side accepting where the other rejects), not just a count.

This is the layout check the FFI work exposed: the self-hosted parser must accept the
same files as the host, rather than the other way round. -/

namespace Tests.Elab

/-- Every `.wiz` under `dir`, recursively. -/
partial def corpusUnder (dir : System.FilePath) : IO (List System.FilePath) := do
  if !(← dir.pathExists) then return []
  let mut out := []
  for e in ← dir.readDir do
    if ← e.path.isDir then out := out ++ (← corpusUnder e.path)
    else if e.path.extension == some "wiz" then out := out ++ [e.path]
  return out

def corpusFiles : IO (List String) := do
  let mut fs : List String := []
  for d in ["lib", "examples", "selfhost", "src", "scry"] do
    fs := fs ++ ((← corpusUnder d).map (·.toString))
  return (fs.toArray.qsort (· < ·)).toList

/-- The host frontend's tables after `lib/Prelude.wiz`: its `syntax`, `notation` and
`infix` rules. Both sides of the differential use these tables. -/
def preludeTables : IO ParserTables := do
  let prelude ← IO.FS.readFile "lib/Prelude.wiz"
  let ioLib ← IO.FS.readFile "lib/IO.wiz"
  let stdLib ← IO.FS.readFile "lib/Std.wiz"
  let loader : Name → Option String := fun m =>
    if m == "Prelude" then some prelude else if m == "IO" then some ioLib
    else if m == "Std" then some stdLib else none
  return (runFrontend (R := ZeroOneMany) prelude { loader, trustedModule := Tests.libModule }).tables

/-- `s` after the prefix `p`, if it has it. -/
def afterPrefix (p s : String) : Option String :=
  if s.startsWith p then some (s.drop p.length).toString else none

/-- Escape a tree so that a command is one output line (the driver escapes the same
characters, so the two strings are directly comparable). -/
def escapeLines (s : String) : String :=
  ((s.replace "\\" "\\\\").replace "\n" "\\n").replace "\r" "\\r" |>.replace "\t" "\\t"
    |>.replace "\x00" "\\0"

/-- The position in a driver/host error message (`error <pos>: …`), for treating two
rejections at the same offset as agreement even when the lexer's words differ. -/
def errorPos (m : String) : Option Nat :=
  match afterPrefix "error " m with
  | some rest => (rest.takeWhile Char.isDigit).toNat?
  | none => none

/-- The Lean parser over a whole file with fixed tables: the trees, and the first error.
Unlike `parseFile`, it does not apply grammar-changing commands: the self-hosted driver
does not either, so the two sides see the same tables command by command. -/
partial def hostParseFixed (chars : Array Char) (tables : ParserTables) (pos : Nat) :
    List String × Option String :=
  let pos := skipWs chars pos
  if pos ≥ chars.size then ([], none)
  else match parseCommand chars tables pos with
    | .ok (cmd, stop) =>
      let (rest, err) := hostParseFixed chars tables stop
      (escapeLines (cmd.toSExpr (atoms := true)) :: rest, err)
    | .error e =>
      ([], some s!"error {e.pos}: expected {", ".intercalate e.expected.toList}")

/-- The self-hosted parser, as a program that reads the files named on its command line
and prints `C\t<tree>` per command or `E\t<error>`; `@@FILE\t<path>` starts a file. -/
def selfhostParser (t : ParserTables) : IO (Except String System.FilePath) := do
  let lexSrc ← IO.FS.readFile "selfhost/Lex.wiz"
  let parseSrc ← IO.FS.readFile "selfhost/Parse.wiz"
  let driver :=
    "def escChars : List Char -> List Char\n" ++
    "  | .nil => .nil\n" ++
    "  | .cons c rest => match Char.code c with\n" ++
    "    | 92 => .cons (Char.mk 92) (.cons (Char.mk 92) (escChars rest))\n" ++
    "    | 10 => .cons (Char.mk 92) (.cons (Char.mk 110) (escChars rest))\n" ++
    "    | 13 => .cons (Char.mk 92) (.cons (Char.mk 114) (escChars rest))\n" ++
    "    | 9 => .cons (Char.mk 92) (.cons (Char.mk 116) (escChars rest))\n" ++
    -- (a NUL, as in `"\\u{0}"`, would end the printed line in the C runtime)
    "    | 0 => .cons (Char.mk 92) (.cons (Char.mk 48) (escChars rest))\n" ++
    "    | _ => .cons c (escChars rest)\n" ++
    "def esc (s : String) : String := match s with\n  | .mk cs => .mk (escChars cs)\n" ++
    "def cmdLine (stx : Syntax) : String := String.append \"C\\t\" (esc (sexpr stx))\n" ++
    "partial def parseFixed (cats : List Cat) (tokens : List String) (input : Array Nat) (pos : Nat) : IO Unit :=\n" ++
    "  let pos := skipWs input pos;\n" ++
    "  match Nat.lt pos (Array.size input) with\n" ++
    "  | .false => IO.pure ()\n" ++
    "  | .true => match parseCommandAt cats tokens input pos with\n" ++
    "    | .err m => IO.println (String.append \"E\\t\" m)\n" ++
    "    | .ok stx stop => do\n" ++
    "      IO.println (cmdLine stx);\n" ++
    "      parseFixed cats tokens input stop\n" ++
    "partial def runFiles (cats : List Cat) (tokens : List String) : List String → IO Unit\n" ++
    "  | .nil => IO.pure ()\n" ++
    "  | .cons path rest => do\n" ++
    "    IO.println (String.append \"@@FILE\\t\" path);\n" ++
    "    text ← IO.readFile path;\n" ++
    "    parseFixed cats tokens (String.codes text) 0;\n" ++
    "    runFiles cats tokens rest\n" ++
    "def main : IO Unit := do\n" ++
    "  args ← IO.args;\n" ++
    "  runFiles cats tokens args\n"
  let prog := "import IO\nimport Std\n" ++ lexSrc ++ "\n" ++ parseSrc ++ "\n" ++
    Selfhost.wizTables t ++
    s!"def tokens : List String := {Selfhost.wizList (t.tokens.toList.map Selfhost.wizLit)}\n" ++ driver
  let stamp := toString (← (← IO.appPath).metadata).modified.sec
  let dir : System.FilePath := s!"/tmp/wiz-selfhost-{hash (prog ++ stamp)}"
  let exe := dir / "parser"
  if ← exe.pathExists then return .ok exe
  let start ← IO.monoMsNow
  IO.FS.createDirAll dir
  let prelude ← IO.FS.readFile "lib/Prelude.wiz"
  let ioLib ← IO.FS.readFile "lib/IO.wiz"
  let stdLib ← IO.FS.readFile "lib/Std.wiz"
  let loader : Name → Option String := fun m =>
    if m == "Prelude" then some prelude else if m == "IO" then some ioLib
    else if m == "Std" then some stdLib else none
  let s := runFrontend (R := ZeroOneMany) prog { loader, trustedModule := Tests.libModule }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render prog
  unless errs.isEmpty do return .error s!"unexpected errors:\n{"\n".intercalate errs.toList}"
  match Build.irProgram s "main" with
  | .error e => return .error e
  | .ok (decls, _) =>
    let tmp := dir / s!"parser-{← IO.monoNanosNow}"
    match ← Build.compileC (← toolchain) (C.program decls true (Build.extraC s)) tmp with
    | .error e => return .error e
    | .ok () =>
      IO.FS.rename tmp exe
      note s!"built parser {showMs ((← IO.monoMsNow) - start)}"
      return .ok exe

/-- The `@@FILE` sections of the driver's output. -/
partial def sections : List String → List (String × List String)
  | [] => []
  | line :: rest =>
    match afterPrefix "@@FILE\t" line with
    | some path =>
      let rec take (acc : List String) : List String → List String × List String
        | [] => (acc.reverse, [])
        | l :: ls =>
          if (afterPrefix "@@FILE\t" l).isSome then (acc.reverse, l :: ls)
          else take (l :: acc) ls
      let (body, rest) := take [] rest
      (path, body) :: sections rest
    | none => sections rest

/-- One side's commands and first error. -/
def parseSide (body : List String) : List String × Option String :=
  (body.filterMap fun l => afterPrefix "C\t" l,
   body.findSome? fun l => afterPrefix "E\t" l)

/-- The first divergence of two parse results, if any. -/
def firstDivergence (host : List String × Option String) (wiz : List String × Option String) :
    Option String :=
  match host.2, wiz.2 with
  | some h, some w =>
    -- both reject: agreement on the offset is acceptance agreement (the lexer's and
    -- the parser's wording for an unknown character need not be the same)
    match errorPos h, errorPos w with
    | some hp, some wp => if hp == wp then none else some s!"both reject, at {hp} and {wp}: Lean {h}; Wiz {w}"
    | _, _ => if h == w then none else some s!"both reject, differently: Lean {h}; Wiz {w}"
  | some h, none => some s!"Lean rejects: {h}; Wiz accepts"
  | none, some w => some s!"Wiz rejects: {w}; Lean accepts"
  | none, none =>
    let rec go (i : Nat) : List String → List String → Option String
      | [], [] => none
      | h :: _, [] => some s!"command {i}: Wiz has nothing for Lean's {h}"
      | [], w :: _ => some s!"command {i}: Wiz has {w}, Lean has nothing"
      | h :: hs, w :: ws =>
        if h == w then go (i + 1) hs ws
        else some s!"command {i}: Lean {h}\n  Wiz {w}"
    go 0 host.1 wiz.1

def parserDiffGroup : Group where
  name := "selfhost-parse-diff"
  shard := "selfhost-parse-diff"
  exercise := "Self-hosted parser parity"
  cases := [
    { name := "every corpus file parses as the Lean parser parses it (the first divergence per file)", run := fun _ => do
        let files ← corpusFiles
        check (!files.isEmpty) "no corpus files found"
        let tables ← preludeTables
        match ← selfhostParser tables with
        | .error e =>
          if (e.splitOn "gmp.h").length > 1 then skip "no toolchain" else throw (IO.userError e)
        | .ok exe =>
          let out ← IO.Process.output { cmd := exe.toString, args := files.toArray }
          unless out.exitCode == 0 do
            throw (IO.userError s!"the Wiz parser failed ({out.exitCode}): {out.stderr.take 2000}")
          let secs := sections (out.stdout.splitOn "\n")
          if secs.length != files.length then
            throw (IO.userError s!"{secs.length} sections for {files.length} files (a file could not be read?)")
          let mut bad : List String := []
          for (path, body) in secs do
            let text ← IO.FS.readFile path
            let host := hostParseFixed text.toList.toArray tables 0
            let wiz := parseSide (body.filter (· != ""))
            if let some d := firstDivergence host wiz then
              bad := bad ++ [s!"{path}: {d}"]
          unless bad.isEmpty do
            throw (IO.userError s!"parser divergences ({bad.length} files):\n{"\n".intercalate bad}") }
  ]

builtin_initialize registerGroup parserDiffGroup

end Tests.Elab
