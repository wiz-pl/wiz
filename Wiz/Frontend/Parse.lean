import Wiz.Parser.Interp
import Wiz.Parser.Builtin
import Wiz.Parser.SyntaxCmd

/-!
# Parsing a file

Files are parsed **one command at a time**, because a command such as `syntax` can
change the grammar used for the next one. Stage 3's frontend interleaves parsing with
elaboration in the same way. This module provides the pieces and a parse-only driver
for `wiz parse`.

**Error recovery:** after a parse error, skip from the start of the failed command to
the next line that starts in column 0
and carry on. One bad command then produces one error instead of ending the whole
file. The LSP needs this.
-/

namespace Wiz

structure Message where
  pos : Nat
  msg : String
  deriving Repr, Inhabited

def Message.render (input : String) (m : Message) : String :=
  let (l, c) := lineCol input m.pos
  s!"{l + 1}:{c + 1}: {m.msg}"

/-- (13o) Which rule reserved the keyword `v`: the first `term` or `command` rule (not a
built-in one) whose grammar mentions it. -/
def ParserTables.reservedBy? (tables : ParserTables) (v : String) : Option (Name × ParserDescr) := Id.run do
  if Builtin.tables.tokens.contains v then return none
  for c in ["command", "term"] do
    let some cat := tables.cats[(c : Name)]? | continue
    for p in cat.leading do
      if p.p.tokens.contains v then return some (p.kind, p.p)
    for p in cat.trailing do
      if p.p.tokens.contains v then return some (p.kind, .seq #[.cat c 0, p.p])
  return none

/-- (13o) A rule's grammar as the user reads it: its atoms, `…` for what is in between
(`exists …, …`, `feral … end`); optional parts are left out. -/
partial def ParserDescr.sketch (d : ParserDescr) : String :=
  let parts := go d
  parts.foldl (fun acc p => if acc.isEmpty then p
    else if p == "," || p == ")" || p == "]" || acc.endsWith "(" || acc.endsWith "[" then acc ++ p
    else if acc.endsWith "…" && p == "…" then acc
    else acc ++ " " ++ p) ""
where
  go : ParserDescr → List String
    | .atom t | .nonReserved t => [t.trimAscii.toString]
    | .seq ps => ps.toList.flatMap go
    | .optional _ => []
    | .many _ | .many1 _ | .sepBy .. | .sepBy1 .. => ["…"]
    | .node _ p | .withPosition p | .withoutPosition p => go p
    | .orelse p _ => go p
    | _ => ["…"]

/-- (13o) An identifier was expected where a word reserved by some notation stands (`def
exists := 1` after `import Logic`): say which notation, and (`site`, the declaring module
of a syntax kind) where it comes from. Done once, when the error is reported, not on
every failed alternative. -/
def ParseError.explainKeywords (tables : ParserTables) (site : Name → Option String := fun _ => none)
    (e : ParseError) : ParseError :=
  let pre := "identifier ('"
  let post := "' is a keyword)"
  -- (the message renders `shown`, not `expected`: both are explained)
  let explain (x : String) : String :=
    if x.startsWith pre && x.endsWith post then
      let v := ((x.drop pre.length).dropEnd post.length).toString
      match tables.reservedBy? v with
      | some (k, d) =>
        let from_ := match site k with
          | some "" => " of this file"
          | some m => s!" of module {m}"
          | none => ""
        s!"identifier ('{v}' is a keyword: the notation `{d.sketch}`{from_})"
      | none => x
    else x
  { e with expected := e.expected.map explain, shown := e.shown.map explain }

/-- Parse the command starting at (or after whitespace following) `pos`. -/
def parseCommand (chars : Array Char) (tables : ParserTables) (pos : Nat) :
    Except ParseError (Syntax × Nat) :=
  (runDescr (.withPosition (.cat "command" 0)) >>= fun r => pure r[0]!).run chars tables pos

/-- The start of the next line beginning in column 0 with a non-space character,
strictly after `pos`. -/
def recoverPos (chars : Array Char) (pos : Nat) : Nat := Id.run do
  let mut i := pos + 1
  while i < chars.size do
    if chars[i - 1]! == '\n' && !chars[i]!.isWhitespace then return i
    i := i + 1
  chars.size

/-- Grammar-changing commands. Everything else leaves the tables alone. -/
partial def updateTables (tables : ParserTables) (cmd : Syntax) : Except String ParserTables :=
  match cmd.kind with
  | "command.declareSyntaxCat" => match (cmd.getArg 1).getId? with
    | some c =>
      -- `(keywords := s)`: the category joins the keyword scope `s` (13j). The scope is set
      -- after the antiquotation parsers are added, so that they add no keyword to it.
      match ((cmd.getArg 2).getArg 3).getId?, tables.cats[c]? with
      | none, some { scope := some _, .. } => pure tables
      | none, _ => pure (Builtin.addMetaParsers (tables.declareCategory c) c)
      | some s, none => pure ((Builtin.addMetaParsers (tables.declareCategory c) c).setScope c s)
      | some s, some cat =>
        if cat.scope == some s then pure tables
        else throw s!"syntax category {c} is already declared, {match cat.scope with
          | some s' => s!"with the keyword scope {s'}"
          | none => "without a keyword scope"}"
    | none => throw "malformed declare_syntax_cat"
  | "command.syntax" => addSyntax tables cmd
  | "command.local" => updateTables tables (cmd.getArg 1)
  | _ => pure tables

structure ParsedFile where
  commands : Array Syntax := #[]
  messages : Array Message := #[]
  tables : ParserTables

/-- Parse a whole file, applying grammar-changing commands as they are seen. -/
partial def parseFile (input : String) (tables : ParserTables := Builtin.tables) : ParsedFile :=
  let chars := input.toList.toArray
  go chars 0 { tables }
where
  go (chars : Array Char) (pos : Nat) (acc : ParsedFile) : ParsedFile :=
    if skipWs chars pos ≥ chars.size then acc else
    match parseCommand chars acc.tables pos with
    | .ok (cmd, stop) =>
      match updateTables acc.tables cmd with
      | .ok tables => go chars stop { acc with commands := acc.commands.push cmd, tables }
      | .error msg =>
        go chars stop { acc with
          commands := acc.commands.push cmd
          messages := acc.messages.push { pos := cmd.info.start, msg } }
    | .error e =>
      let msg := ((e.explainKeywords acc.tables).render input).splitOn ": " |>.drop 1 |> ": ".intercalate
      go chars (recoverPos chars (skipWs chars pos)) { acc with messages := acc.messages.push { pos := e.pos, msg } }

end Wiz
