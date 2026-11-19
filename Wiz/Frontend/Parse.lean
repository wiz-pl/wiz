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

/-- Parse the command starting at (or after whitespace following) `pos`.

`import M` is a **header declaration**, not a rule of the extensible `command`
category: it is tried first, from `Builtin.importDescr`, so every top-level command
position parses it and no `syntax`/macro rule can produce it. -/
def parseCommand (chars : Array Char) (tables : ParserTables) (pos : Nat) :
    Except ParseError (Syntax × Nat) :=
  (runDescr (.withPosition (.orelse Builtin.importDescr (.cat "command" 0))) >>= fun r => pure r[0]!).run chars tables pos

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
  /-- The header's imports, in order (`pad`, so a caller can list them cheaply). -/
  imports : Array Name := #[]
  messages : Array Message := #[]
  tables : ParserTables

/-- The message for an `import` that a declaration already preceded. -/
def importOrderMessage : String :=
  "imports must precede declarations: an `import` may appear only at the top of the file, before every other command (comments are not commands)"

/-- Parse a whole file, applying grammar-changing commands as they are seen. The header
(comments and `import`s) comes first; an `import` after a non-import command is reported
and parsing carries on, so one mistake gives one message. -/
partial def parseFile (input : String) (tables : ParserTables := Builtin.tables) : ParsedFile :=
  let chars := input.toList.toArray
  go chars 0 { tables } true
where
  go (chars : Array Char) (pos : Nat) (acc : ParsedFile) (header : Bool) : ParsedFile :=
    if skipWs chars pos ≥ chars.size then acc else
    match parseCommand chars acc.tables pos with
    | .ok (cmd, stop) =>
      let isImport := cmd.isOfKind "command.import"
      let acc :=
        if isImport then
          { acc with commands := acc.commands.push cmd,
                     imports := acc.imports.push (((cmd.getArg 1).getId?).getD "_") }
        else { acc with commands := acc.commands.push cmd }
      let acc := if isImport && !header then
          { acc with messages := acc.messages.push { pos := cmd.info.start, msg := importOrderMessage } }
        else acc
      let header := header && isImport
      match updateTables acc.tables cmd with
      | .ok tables => go chars stop { acc with tables } header
      | .error msg =>
        go chars stop { acc with
          messages := acc.messages.push { pos := cmd.info.start, msg } } header
    | .error e =>
      let msg := ((e.explainKeywords acc.tables).render input).splitOn ": " |>.drop 1 |> ": ".intercalate
      go chars (recoverPos chars (skipWs chars pos)) { acc with messages := acc.messages.push { pos := e.pos, msg } } header

/-- The imports in a file's header, in order, without parsing past the first command that
is not an `import` (and without elaborating anything). This is the cheap dependency fact a
fixed header buys: `wiz parse --imports FILE`. -/
partial def parseImports (input : String) (tables : ParserTables := Builtin.tables) :
    Array Name × Array Message :=
  go (input.toList.toArray) 0 tables #[]
where
  go (chars : Array Char) (pos : Nat) (tables : ParserTables) (acc : Array Name) :
      Array Name × Array Message :=
    if skipWs chars pos ≥ chars.size then (acc, #[]) else
    match parseCommand chars tables pos with
    | .ok (cmd, stop) =>
      if cmd.isOfKind "command.import" then
        go chars stop tables (acc.push (((cmd.getArg 1).getId?).getD "_"))
      else (acc, #[])
    | .error e =>
      let msg := ((e.explainKeywords tables).render input).splitOn ": " |>.drop 1 |> ": ".intercalate
      (acc, #[{ pos := e.pos, msg }])

end Wiz
