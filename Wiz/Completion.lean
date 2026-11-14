import Wiz.Query
import Wiz.Actions

/-!
# Completion

What `textDocument/completion` offers at the cursor, by context:

* after `import`: module names (the libraries the server knows);
* `x.f…` where `x` is a value: the fields of its type (a structure, a Σ) and the functions
  of its type's namespace that take it first (`T.f x`, generalised field notation);
  where `x` is a namespace (a prefix of global names): the names in it;
* the keywords the **parser** expects at the cursor: the command around it is parsed with
  the input cut at the start of the word, and the tokens of the failure there are what
  may come next. That is the command keywords in column 0, tactic names inside `by`, the
  keywords of a keyword-scoped DSL (13j) inside it, `fun`/`match`/… where a term goes;
* where a term or an identifier may go: the locals in scope (with their types), then the
  globals (those whose type ends in the expected type's head first).

The document as typed usually doesn't elaborate at the cursor (`x.` or a half-written
word), so locals and the expected type come from elaborating a **patched** copy: the
word at the cursor replaced by a hole `_` (whose goal has the locals and the expected
type), or for `x.f…` by `x` alone (whose identifier has its type). The copy is cut at the
end of the command around the cursor (the next line starting in column 0), so only that
command is elaborated again: the earlier ones come from the query engine's memo.
-/

namespace Wiz.Completion

variable {R : Type} [QRig R] [DecidableEq R] [ToString R] [QuantitySyntax R]

/-- LSP `CompletionItemKind`s. -/
def kindFunction : Nat := 3
def kindConstructor : Nat := 4
def kindField : Nat := 5
def kindVariable : Nat := 6
def kindModule : Nat := 9
def kindKeyword : Nat := 14

structure Item where
  label : String
  kind : Nat
  detail : String := ""
  /-- sorted by this, then by label -/
  sortText : String := "5"
  /-- the text replacing `[start, cursor)` -/
  insert : String := label
  start : Nat
  /-- the global it stands for, whose doc comment the item shows -/
  global : Option Name := none
  deriving Repr, Inhabited, BEq

structure Result where
  items : Array Item
  /-- the list was cut (more would match a longer prefix) -/
  incomplete : Bool := false
  deriving Inhabited

def dropS (s : String) (k : Nat) : String := String.ofList (s.toList.drop k)

def isIdChar (c : Char) : Bool := isIdRest c || c == '.'

/-- Where the (possibly dotted) word ending at `off` starts. -/
def wordStart (chars : Array Char) (off : Nat) : Nat := Id.run do
  let mut i := min off chars.size
  while i > 0 && isIdChar chars[i - 1]! do i := i - 1
  pure i

/-- The start of the line containing `off`. -/
def lineStart (chars : Array Char) (off : Nat) : Nat := Id.run do
  let mut i := min off chars.size
  while i > 0 && chars[i - 1]! != '\n' do i := i - 1
  pure i

/-- The end of the command around `off`: the next line (after `off`'s) that starts in
column 0 with something other than a comment, or the end. -/
def commandEnd (chars : Array Char) (off : Nat) : Nat := Id.run do
  let mut i := off
  while i < chars.size do
    if chars[i]! == '\n' && i + 1 < chars.size then
      let c := chars[i + 1]!
      if !(c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '-' || c == '/') then return i + 1
    i := i + 1
  pure chars.size

/-- Names the infoview doesn't list (the elaborator's own). -/
def hidden (n : Name) : Bool :=
  (n.splitOn "✝").length > 1 || n.startsWith "_private." ||
  [".desc", ".casesOn", ".rec", ".ind", ".below", ".brecOn", ".noConfusion", ".sizeOf", ".elim", ".Tag"].any (n.endsWith ·)

/-- The head constant of a type, under its Π binders. -/
partial def resultHead : Term R → Option Name
  | .pi _ _ _ _ cod _ => resultHead cod
  | t => Actions.typeHead t

open Actions (typeHead fieldsOf)

/-- Does `n`'s first explicit argument have type `T …` (so that `x.f` means `T.f x`)? -/
def takesFirst (g : Globals R) (n T : Name) : Bool :=
  match g.find? n with
  | some d => match (Elab.piInfos d.type).find? (·.2.1 == .default) with
    | some (_, _, A) => typeHead A == some T
    | none => false
  | none => false

/-- A global as a completion item (replacing `[start, cursor)` by `insert`). -/
def globalItem (g : Globals R) (n : Name) (start : Nat) (insert : String) (expected : Option Name) : Item :=
  let (detail, sort, kind) := match g.find? n with
    | some d =>
      let matches_ := expected.isSome && resultHead d.type == expected
      (d.type.pretty [], if matches_ then "2" else "3", kindFunction)
    | none => ("", "3", kindFunction)
  { label := n, kind, detail, sortText := sort, insert, start, global := some n }

/-- What the language server needs from its document for completion. -/
structure Input (R : Type) where
  text : String
  off : Nat
  /-- the elaborated document -/
  state : CommandState R
  /-- elaborate a (patched) text, as the document is -/
  elabText : String → CommandState R
  /-- the modules `import` can name -/
  modules : Array String := #[]
  limit : Nat := 300

/-- The innermost hole (`.term _ _ true`) starting at `at_`. -/
def holeAt (s : CommandState R) (at_ : Nat) : Option (GoalView R) :=
  match Query.innermost s at_ (fun | .term r _ true => r.start == at_ | _ => false) (endIn := true) with
  | some (.term _ g _) => some g
  | _ => none

/-- The start of the command around `at_`: the last line starting in column 0 with a
non-space character, at or before `at_`. -/
def commandStart (chars : Array Char) (at_ : Nat) : Nat := Id.run do
  let mut i := min at_ chars.size
  while i > 0 do
    if chars[i - 1]! == '\n' && i < chars.size && !chars[i]!.isWhitespace && i ≤ at_ then return i
    i := i - 1
  pure 0

/-- What the parser expects at `at_` (its `expected` list: `'tok'` for tokens, the names
of categories and `identifier`): the command around `at_` parsed from its start with the
input cut at `at_`. Empty if parsing fails before `at_`. -/
def expectedAt (tables : ParserTables) (chars : Array Char) (at_ : Nat) : Array String :=
  let start := commandStart chars at_
  let input := chars.extract 0 at_
  let err := match runDescr (.withPosition (.cat "command" 0)) { input, tables } { pos := start } with
    | .ok _ st => st.err
    | .error st => st.err
  if err.pos ≥ at_ then err.expected.toList.eraseDups.toArray else #[]

/-- `w` of an expected token `'w'` spelled like an identifier. -/
def quotedWord? (e : String) : Option String :=
  let cs := e.toList
  if cs.length ≥ 3 && cs.head? == some '\'' && cs.getLast? == some '\'' then
    let w := String.ofList ((cs.drop 1).dropLast)
    if !w.isEmpty && isIdStart w.front && w.all isIdRest then some w else none
  else none

/-- Keep the items whose label starts with `pre`, sorted, at most `limit`. -/
def finish (items : Array Item) (pre : String) (limit : Nat) : Result :=
  let seen : Std.HashSet String := {}
  let (_, keep) := items.foldl (fun (seen, acc) i =>
    if seen.contains i.label || !(i.label.startsWith pre) || i.label == pre then (seen, acc)
    else (seen.insert i.label, acc.push i)) (seen, #[])
  let sorted := keep.qsort fun a b => a.sortText < b.sortText || (a.sortText == b.sortText && a.label < b.label)
  { items := sorted.extract 0 limit, incomplete := sorted.size > limit }

/-- The completions at `inp.off`. -/
def complete (inp : Input R) : Result := Id.run do
  let chars := inp.text.toList.toArray
  let off := min inp.off chars.size
  let ws := wordStart chars off
  let word := String.ofList (chars.extract ws off).toList
  let ls := lineStart chars ws
  let before := (String.ofList (chars.extract ls ws).toList)
  -- (the rest of the word, after the cursor, goes too)
  let we := Id.run do
    let mut i := off
    while i < chars.size && isIdRest chars[i]! do i := i + 1
    pure i
  let cut := commandEnd chars off
  let patched (p : String) : CommandState R :=
    inp.elabText (String.ofList (chars.extract 0 ws).toList ++ p ++ String.ofList (chars.extract we cut).toList)
  let g := inp.state.globals
  -- `import M`
  if (String.ofList (before.toList.dropWhile (·.isWhitespace))).startsWith "import " then
    let items := inp.modules.map fun m => { label := m, kind := kindModule, start := ws, sortText := "1" : Item }
    return finish items word inp.limit
  -- `q.f…`: in the namespace `q`, or a field of the value `q`
  if word.contains '.' then
    let q := String.ofList ((word.toList.reverse.dropWhile (· != '.')).drop 1).reverse
    let qstart := ws
    let fstart := ws + q.length + 1
    -- the names under `q` (one more component)
    let inNs := g.order.filter fun n => n.startsWith (q ++ ".") && !hidden n
    let mut items : Array Item := inNs.map fun n =>
      globalItem g n qstart n none
    -- `q` as a value: its type's namespace and fields
    let s := patched q
    match Query.innermost s (ws + q.length - 1) (fun | .ident r .. => r.stop == ws + q.length | _ => false) (endIn := true) with
    | some (.ident _ _ _ _ ty) =>
      for (f, fty) in Actions.fieldTypes g ty do
        items := items.push { label := q ++ "." ++ f, kind := kindField, detail := fty, start := qstart, sortText := "0", insert := q ++ "." ++ f,
                              global := (typeHead ty).map (· ++ "." ++ f) }
      if let some T := typeHead ty then
        for n in g.order do
          if n.startsWith (T ++ ".") && !hidden n && !(dropS n (T.length + 1)).contains '.' && takesFirst g n T then
            let f := dropS n (T.length + 1)
            let it := globalItem g n fstart f none
            items := items.push { it with label := q ++ "." ++ f, insert := q ++ "." ++ f, start := qstart, sortText := "1" }
    | _ => pure ()
    return finish items word inp.limit
  let mut items : Array Item := #[]
  -- the keywords the parser expects here (commands, tactics, a DSL's keywords, …), and
  -- whether a term or identifier may go here
  let exp := expectedAt inp.state.tables chars ws
  let wantsTerm := exp.isEmpty || exp.contains "term" || exp.contains "identifier"
  for e in exp do
    if let some w := quotedWord? e then
      items := items.push { label := w, kind := kindKeyword, start := ws, sortText := if wantsTerm then "4" else "1" }
  if !wantsTerm then return finish items word inp.limit
  -- a term: the hole's locals and expected type
  let s := patched "_"
  let mut expected : Option Name := none
  match holeAt s ws with
  | some gv =>
    -- (the innermost first)
    let mut ns : List Name := []
    let mut k := 0
    for (x, ty, _) in gv.hyps do
      if !(x.contains '✝') && x != "_" then
        items := items.push { label := x, kind := kindVariable, detail := ty.pretty ns, start := ws,
                              sortText := "0" ++ toString (100000 + (1000 - min k 999)) }
      ns := x :: ns
      k := k + 1
    expected := typeHead gv.target
  | none =>
    -- (the patch didn't elaborate there) the locals an unknown identifier saw
    if let some (.unknownIdent _ _ locals) := inp.state.infos.find? (fun | .unknownIdent r .. => r.start == ws | _ => false) then
      for x in locals do
        if !(x.contains '✝') then items := items.push { label := x, kind := kindVariable, start := ws, sortText := "0" }
  for n in g.order do
    if !hidden n && n.startsWith word then
      items := items.push (globalItem g n ws n expected)
  finish items word inp.limit

end Wiz.Completion
