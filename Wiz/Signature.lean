import Wiz.Query

/-!
# Signature help

While typing an application `f a b ‸`, `textDocument/signatureHelp` shows `f`'s
binders, `f (n : Nat) {A : Type} (xs : List A) : Nat`, with the explicit argument being
typed highlighted. The application is found in the text (the document rarely
elaborates mid-application): from the cursor back to the nearest unclosed bracket, or to
`:=`, `=>`, `,`, `|`, `;` at bracket depth 0, or the start of the command; the first
word there is the function, and the complete arguments after it count which explicit
binder is next. A global's binders come from its declaration; a local's from the type
the info tree recorded for it (at another use, or its binder).
-/

namespace Wiz.Signature

variable {R : Type} [QRig R] [DecidableEq R] [ToString R] [QuantitySyntax R]

structure Help where
  /-- `f (n : Nat) (m : Nat) : Nat` -/
  label : String
  /-- the explicit binders' ranges in `label` (character offsets) -/
  params : Array (Nat × Nat)
  active : Nat
  name : Name
  /-- (11s) the function's doc comment (Markdown), if it is a global with one -/
  doc : Option String := none
  deriving Repr, Inhabited

def opens (c : Char) : Bool := c == '(' || c == '[' || c == '⟨' || c == '{'
def closes (c : Char) : Bool := c == ')' || c == ']' || c == '⟩' || c == '}'

/-- The start of the application around `off`, and its top-level words up to `off`
(with their start offsets). -/
def application (chars : Array Char) (off : Nat) : Nat × Array (Nat × String) := Id.run do
  -- back to the start
  let mut i := min off chars.size
  let mut depth : Nat := 0
  let mut start := 0
  while i > 0 do
    let c := chars[i - 1]!
    if closes c then depth := depth + 1
    else if opens c then
      if depth == 0 then start := i; break
      depth := depth - 1
    else if depth == 0 then
      let c0 := if i ≥ 2 then chars[i - 2]! else ' '
      if (c == '=' && c0 == ':') || (c == '>' && c0 == '=') || c == ',' || c == '|' || c == ';' then
        start := i; break
      -- the start of the command (a line starting in column 0)
      if c == '\n' && i < chars.size && !chars[i]!.isWhitespace then start := i; break
    i := i - 1
  -- the words at depth 0
  let mut words : Array (Nat × String) := #[]
  let mut j := start
  let mut d : Nat := 0
  let mut cur := ""
  let mut curStart := start
  while j < off do
    let c := chars[j]!
    if d == 0 && c.isWhitespace then
      if !cur.isEmpty then words := words.push (curStart, cur); cur := ""
    else
      if cur.isEmpty then curStart := j
      cur := cur.push c
      if opens c then d := d + 1
      else if closes c && d > 0 then d := d - 1
    j := j + 1
  if !cur.isEmpty then words := words.push (curStart, cur ++ (if d > 0 then "…" else ""))
  (start, words)

/-- `label` and the explicit binders' ranges for `f : ty`. -/
def render (f : Name) (ty : Term R) : String × Array (Nat × Nat) := Id.run do
  let mut label := f
  let mut params : Array (Nat × Nat) := #[]
  let mut names : List Name := []
  let mut t := ty
  for _ in [0:256] do
    match t with
    | .pi x bi _ dom cod _ =>
      let x' := if x.isEmpty then "_" else x
      let part := match bi with
        | .default => s!"({x'} : {dom.pretty names})"
        | .implicit => s!"\{{x'} : {dom.pretty names}}"
        | .instImplicit => s!"[{dom.pretty names}]"
      let a := label.length + 1
      label := label ++ " " ++ part
      if bi == .default then params := params.push (a, label.length)
      names := x :: names
      t := cod
    | _ => break
  label := label ++ " : " ++ t.pretty names
  (label, params)

/-- The text up to `stop` with the brackets still open there closed (so that what is
before `stop` parses), and nothing after it. -/
def closedPrefix (chars : Array Char) (stop : Nat) : String := Id.run do
  let mut stack : List Char := []
  for c in chars.extract 0 stop do
    if c == '(' then stack := ')' :: stack
    else if c == '[' then stack := ']' :: stack
    else if c == '⟨' then stack := '⟩' :: stack
    else if c == '{' then stack := '}' :: stack
    else if closes c then stack := stack.drop 1
    else if c == '\n' then pure ()
  String.ofList (chars.extract 0 stop).toList ++ String.ofList stack ++ "\n"

/-- The signature help at `off`. A local function's type is read from the info tree of
`elabText` applied to the text cut after it (the document rarely elaborates there). -/
def helpAt (s : CommandState R) (text : String) (off : Nat)
    (elabText : String → CommandState R := fun _ => s) : Option Help := do
  let chars := text.toList.toArray
  let (_, words) := application chars off
  let (hstart, head) ← words[0]?
  guard (words.size ≥ 2 || (off > 0 && chars[off - 1]!.isWhitespace))
  guard (!head.isEmpty && head.all fun c => isIdRest c || c == '.')
  -- the argument being typed: after a space, a new one
  let typing := off > 0 && !chars[off - 1]!.isWhitespace
  let given := words.size - 1 - (if typing then 1 else 0)
  -- (named arguments `(x := e)` don't count)
  let given := given - ((words.extract 1 (1 + given)).filter fun (_, w) => w.startsWith "(" && (w.splitOn ":=").length > 1).size
  let localType (st : CommandState R) : Option (Term R) :=
    match Query.identAt st hstart with
    | some (.ident _ n true _ ty) => if n == head then some ty else none
    | _ => none
  let ty ← match s.globals.find? head with
    | some d => some d.type
    | none => (localType s).orElse fun _ => localType (elabText (closedPrefix chars (hstart + head.length)))
  let (label, params) := render head ty
  guard !params.isEmpty
  let doc := if s.globals.contains head then s.docOf? head else none
  pure { label, params, active := min given (params.size - 1), name := head, doc }

end Wiz.Signature
