import Wiz.Core.Pretty
import Wiz.Elab.Basic

/-!
# Tagged terms, for the infoview

`Term.prettyTagged` (`Core/Pretty.lean`) prints a term exactly as `Term.pretty` does, but as **tagged text**:
every printed subterm is wrapped in a tag naming it, so an infoview can highlight the
subterm under the mouse and ask about it (`wiz/subtermInfo`). A tag holds an index into
the array of subterms the printer returns; the language server turns those into refs of
the document's session table.

Each subterm remembers its context: the names and (where known) types of the variables in
scope, innermost first, so its type can be inferred later. A `fun` binder's type isn't in
the term, so under a `fun` it is unknown.
-/

namespace Wiz

variable {R : Type} [QuantitySyntax R] [BEq R]

/-! ## Goals -/

/-- The context of a goal's target: names and types, innermost first. -/
def GoalView.scope (g : GoalView R) : List Name × List (Option (Term R)) :=
  (g.hyps.toList.reverse.map (·.1), g.hyps.toList.reverse.map (some ·.2.1))

/-- A hypothesis and a goal, tagged. -/
structure TaggedGoal where
  hyps : Array (Name × TT × Option TT)
  target : TT
  userName : Option Name

def GoalView.tagged (g : GoalView R) (env : Option (Globals R) := none) : StateM (Array (Subterm R)) TaggedGoal := do
  let mut hyps := #[]
  let mut names : List Name := []
  let mut tys : List (Option (Term R)) := []
  for (x, ty, v) in g.hyps do
    let t ← ty.prettyTagged names tys env
    let v ← v.mapM (·.prettyTagged names tys env)
    hyps := hyps.push (x, t, v)
    names := x :: names
    tys := some ty :: tys
  pure { hyps, target := ← g.target.prettyTagged names tys env, userName := g.userName }

/-! ## Tactic widgets (11af)

A tactic can ask the infoview to show a widget (`TacticM.widget`): static HTML with a
plain-text title, attached to the tactic's range and to the goals open when it was
emitted. Wiz code controls the content, so it is **untrusted**: the protocol forbids
scripts, and `sanitizeWidgetHtml` removes the dangerous parts before the server sends a
widget. That is a safety net, not a sandbox: clients must still render widget HTML as
untrusted (for example in an iframe with a content security policy), and must treat the
title as text, never as HTML. -/

/-- ASCII lower case; other characters are unchanged. -/
def asciiLower (c : Char) : Char :=
  if 65 ≤ c.toNat && c.toNat ≤ 90 then Char.ofNat (c.toNat + 32) else c

/-- ASCII letter? -/
def isAsciiLetter (c : Char) : Bool :=
  (65 ≤ c.toNat && c.toNat ≤ 90) || (97 ≤ c.toNat && c.toNat ≤ 122)

/-- `p` occurs at the start of `s`, ignoring ASCII case. -/
partial def startsWithCI : List Char → List Char → Bool
  | [], _ => true
  | _ :: _, [] => false
  | p :: ps, c :: cs => asciiLower p == asciiLower c && startsWithCI ps cs

/-- `tag` ends at `<tag` followed by a tag boundary (not `<scripture`). -/
def tagBoundary (tag : String) (cs : List Char) : Bool :=
  match cs.drop ("<" ++ tag).toList.length with
  | [] => true
  | c :: _ => c == '>' || c == '/' || c.isWhitespace

/-- The rest after the first `ch` (or `[]`). -/
partial def skipPast (ch : Char) : List Char → List Char
  | [] => []
  | c :: cs => if c == ch then cs else skipPast ch cs

/-- The suffix starting at the first (case-insensitive) occurrence of `p`. -/
partial def dropUntilCI (p : List Char) : List Char → List Char
  | [] => []
  | cs@(_ :: rest) => if startsWithCI p cs then cs else dropUntilCI p rest

/-- Remove `<tag …> … </tag>` elements (their content too). -/
partial def stripElement (tag : String) : List Char → List Char
  | [] => []
  | c :: cs =>
    if startsWithCI ("<" ++ tag).toList (c :: cs) && tagBoundary tag (c :: cs) then
      let afterOpen := skipPast '>' (c :: cs)
      let afterClose := skipPast '>' (dropUntilCI ("</" ++ tag).toList afterOpen)
      stripElement tag afterClose
    else c :: stripElement tag cs

/-- Remove `<tag …>` elements that have no closing tag. -/
partial def stripVoid (tag : String) : List Char → List Char
  | [] => []
  | c :: cs =>
    if startsWithCI ("<" ++ tag).toList (c :: cs) && tagBoundary tag (c :: cs) then
      stripVoid tag (skipPast '>' (c :: cs))
    else c :: stripVoid tag cs

/-- The letters at the start of `cs`, and the rest. -/
partial def spanLetters : List Char → List Char × List Char
  | [] => ([], [])
  | c :: cs =>
    if isAsciiLetter c then
      let (a, b) := spanLetters cs
      (c :: a, b)
    else ([], c :: cs)

/-- The rest after an attribute value: quoted, or up to a space or `>`. -/
partial def skipAttrValue : List Char → List Char
  | [] => []
  | c :: cs =>
    if c == '"' then skipPast '"' cs
    else if c == '\'' then skipPast '\'' cs
    else if c.isWhitespace || c == '>' then c :: cs
    else skipAttrValue cs

/-- `cs` starts with an event-handler attribute (`onclick=…`, `onerror="…"`). Returns the
rest after its value. -/
def eventRest (cs : List Char) : Option (List Char) :=
  let (name, rest) := spanLetters cs
  match name with
  | a :: b :: _ =>
    if asciiLower a == 'o' && asciiLower b == 'n' && name.length > 2 then
      match rest.dropWhile (·.isWhitespace) with
      | '=' :: v => some (skipAttrValue v)
      | _ => none
    else none
  | _ => none

/-- Remove event-handler attributes from tags (not from text between them). -/
partial def stripEvents (inTag : Bool) : List Char → List Char
  | [] => []
  | c :: cs =>
    if c == '<' then c :: stripEvents true cs
    else if c == '>' then c :: stripEvents false cs
    else if inTag && (c.isWhitespace || c == '/') then
      match eventRest cs with
      | some rest => stripEvents true rest
      | none => c :: stripEvents true cs
    else c :: stripEvents inTag cs

/-- Remove every (case-insensitive) occurrence of `p`. -/
partial def stripCI (p : List Char) : List Char → List Char
  | [] => []
  | c :: cs =>
    if startsWithCI p (c :: cs) then stripCI p ((c :: cs).drop p.length)
    else c :: stripCI p cs

/-- (11af) Static HTML a widget may contain: scripts, styles, frames and other active
content are removed, as are event-handler attributes and `javascript:`-style URLs. The
result is safe to insert into a page that does not otherwise execute what it shows; it is
not a general sanitizer (a client should still sandbox widget HTML). -/
def sanitizeWidgetHtml (s : String) : String :=
  let cs := s.toList
  let cs := stripElement "script" cs
  let cs := stripElement "style" cs
  let cs := stripElement "iframe" cs
  let cs := stripElement "object" cs
  let cs := stripVoid "embed" cs
  let cs := stripVoid "meta" cs
  let cs := stripVoid "link" cs
  let cs := stripVoid "base" cs
  let cs := stripEvents false cs
  let cs := stripCI "javascript:".toList cs
  let cs := stripCI "vbscript:".toList cs
  let cs := stripCI "data:text/html".toList cs
  String.ofList cs

/-- Escape text for HTML (a widget's title). -/
def widgetEscape (s : String) : String :=
  s.foldl (fun acc c => acc ++ match c with
    | '&' => "&amp;" | '<' => "&lt;" | '>' => "&gt;" | '"' => "&quot;" | '\'' => "&#39;"
    | c => c.toString) ""

/-- A widget as an HTML block: its title escaped, its body sanitised. -/
def widgetHtml (title html : String) : String :=
  s!"<div class=\"wiz-widget\"><div class=\"wiz-widget-title\">{widgetEscape title}</div>" ++
    s!"{sanitizeWidgetHtml html}</div>"

end Wiz
