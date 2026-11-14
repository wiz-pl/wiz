import Wiz.Query

/-!
# Semantic tokens

`textDocument/semanticTokens/full` marks the **keywords the file's own grammar makes**,
which a fixed syntax file can't know: the words of a declared syntax (`syntax`,
`notation`, the Prelude's tactics, a keyword-scoped DSL's `when … yes … no`) where the
info tree saw a node of that kind (`syntaxRef`), and the words the grammar reserves
everywhere (identifier-like tokens of `term` and `command` rules declared by the file or
its imports). Comments, strings and character literals are skipped. One token type,
`keyword`.
-/

namespace Wiz.Semantic

variable {R : Type} [QRig R] [DecidableEq R] [ToString R] [QuantitySyntax R]

/-- The identifier-like words of a parser (its atoms and non-reserved words). -/
partial def words : ParserDescr → List String
  | .atom t | .nonReserved t =>
    if t != "" && isIdStart t.front && t.all isIdRest then [t] else []
  | .seq ps => ps.toList.flatMap words
  | .many p | .many1 p | .optional p | .node _ p | .withPosition p | .withoutPosition p
  | .sepBy p _ _ | .sepBy1 p _ _ => words p
  | .orelse p q => words p ++ words q
  | _ => []

/-- The words of the rule of kind `k`. -/
def kindWords (t : ParserTables) (k : Name) : List String :=
  t.cats.fold (init := []) fun acc _ cat =>
    let ls := (cat.leading.filter (fun (p : LeadingParser) => p.kind == k)).toList.flatMap (words ·.p)
    let ts := (cat.trailing.filter (fun (p : TrailingParser) => p.kind == k)).toList.flatMap (words ·.p)
    acc ++ ls ++ ts

/-- The words of the text outside comments, strings and character literals: (start,
word). -/
def scan (chars : Array Char) : Array (Nat × String) := Id.run do
  let mut out : Array (Nat × String) := #[]
  let mut i := 0
  while i < chars.size do
    let c := chars[i]!
    let n := chars[i + 1]?
    if c == '-' && n == some '-' then
      while i < chars.size && chars[i]! != '\n' do i := i + 1
    else if c == '/' && n == some '-' then
      let mut depth := 0
      while i < chars.size do
        if chars[i]! == '/' && chars[i + 1]? == some '-' then depth := depth + 1; i := i + 2
        else if chars[i]! == '-' && chars[i + 1]? == some '/' then
          depth := depth - 1; i := i + 2
          if depth == 0 then break
        else i := i + 1
    else if c == '"' then
      i := i + 1
      while i < chars.size && chars[i]! != '"' do
        if chars[i]! == '\\' then i := i + 1
        i := i + 1
      i := i + 1
    else if isIdStart c && (i == 0 || !(isIdRest chars[i - 1]! || chars[i - 1]! == '.')) then
      let a := i
      while i < chars.size && (isIdRest chars[i]! || chars[i]! == '.') do i := i + 1
      out := out.push (a, String.ofList (chars.extract a i).toList)
    else i := i + 1
  out

/-- The keyword tokens of the document: (start, length), sorted. -/
def keywords (s : CommandState R) (text : String) : Array (Nat × Nat) := Id.run do
  let chars := text.toList.toArray
  let ws := scan chars
  -- the words reserved everywhere that the built-in grammar doesn't have (a syntax file
  -- knows those)
  let builtin : Std.HashSet String := Builtin.tables.tokens.foldl (·.insert ·) {}
  let reserved : Std.HashSet String := s.tables.tokens.foldl (fun acc t =>
    if !builtin.contains t && t != "" && isIdStart t.front && t.all isIdRest then acc.insert t else acc) {}
  let mut marks : Std.HashSet Nat := {}
  let mut out : Array (Nat × Nat) := #[]
  for (a, w) in ws do
    if reserved.contains w then marks := marks.insert a; out := out.push (a, w.length)
  -- the words of declared syntax, inside its nodes but not inside their child nodes
  let refs : Array (SourceInfo × Name) := s.infos.filterMap fun
    | .syntaxRef r (.kind k) => if r.synthetic then none else some (r, k)
    | _ => none
  let mut cache : Std.HashMap Name (List String) := {}
  for (r, k) in refs do
    let kw := match cache.get? k with
      | some kw => kw
      | none => kindWords s.tables k
    cache := cache.insert k kw
    if kw.isEmpty then continue
    let inner := refs.filter fun (r', _) => r.start ≤ r'.start && r'.stop ≤ r.stop && r'.stop - r'.start < r.stop - r.start
    for (a, w) in ws do
      if r.start ≤ a && a + w.length ≤ r.stop && kw.contains w && !marks.contains a &&
         !(inner.any fun (r', _) => r'.start ≤ a && a + w.length ≤ r'.stop) then
        marks := marks.insert a; out := out.push (a, w.length)
  out.qsort (·.1 < ·.1)

/-- The LSP encoding: per token, the line and start deltas, the length, the type (0,
`keyword`) and no modifiers. -/
def encode (text : String) (toks : Array (Nat × Nat)) : Array Nat := Id.run do
  let chars := text.toList.toArray
  let mut out : Array Nat := #[]
  let mut line := 0
  let mut col := 0
  let mut i := 0
  let mut pl := 0
  let mut pc := 0
  for (a, len) in toks do
    while i < a && i < chars.size do
      if chars[i]! == '\n' then line := line + 1; col := 0 else col := col + 1
      i := i + 1
    out := out ++ #[line - pl, if line == pl then col - pc else col, len, 0, 0]
    pl := line; pc := col
  out

end Wiz.Semantic
