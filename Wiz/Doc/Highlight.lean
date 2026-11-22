import Lean.Data.Json
import Wiz.Parser.Token
import Wiz.Parser.Builtin

/-!
# Highlighting fenced code in doc comments

The static documentation (`wiz doc`) bakes the highlighting for a fenced code block into
the page: one `<span class="hl-…">` per selected token, with the token text escaped like
the rest of the Markdown. There is no JavaScript highlighter and no second lexer: for
`wiz` the scanner below is the parser's own `skipWs`/`readToken` pair over the module's
own token table (`CommandState.tables.tokens`), so a token boundary here cannot disagree
with the parser's.

The classes are the fixed eight of `docs-highlighting.md` §4.1. P0 emits only the four
that keep the page budget (`kw`, `com`, `str`, `num`); operators and identifiers stay
text (§3.3). A block whose language is not `wiz`, or whose body the scanner rejects, is
rendered escaped and plain: a highlighted block is either fully checked or plain (§5.3).
-/

namespace Wiz.Doc

open Lean (Json)

/-- Escape text for HTML text and attribute values. -/
def htmlEscape (s : String) : String :=
  s.foldl (fun acc c => acc ++ match c with
    | '&' => "&amp;" | '<' => "&lt;" | '>' => "&gt;" | '"' => "&quot;" | '\'' => "&#39;"
    | c => c.toString) ""

namespace Highlight

/-- The fixed class set (`docs-highlighting.md` §4.1). The HTML never carries any other
class name. -/
inductive Class where
  | kw | com | str | num | op | const | var | sort
  deriving Repr, BEq, Inhabited

/-- The canonical HTML class of a `Class`. -/
def className : Class → String
  | .kw => "hl-kw"
  | .com => "hl-com"
  | .str => "hl-str"
  | .num => "hl-num"
  | .op => "hl-op"
  | .const => "hl-const"
  | .var => "hl-var"
  | .sort => "hl-sort"

/-- One styled range of the source: character offsets, `[start, stop)`. -/
structure Span where
  start : Nat
  stop : Nat
  cls : Class
  deriving Repr, BEq, Inhabited

/-- A highlighted fenced block. -/
structure Block where
  /-- the fence's language as the registry spells it (`wiz`) -/
  language : String
  /-- the block's source, for the UTF-16 offsets in the JSON form -/
  source : String
  spans : Array Span
  deriving Repr, Inhabited

/-- The language word of a fence's info string: `wiz no-check` → `wiz` (the rest is a
directive, as the documentation examples use it). -/
def languageOf (info : String) : String :=
  String.ofList ((info.trimAscii.toString.toList).takeWhile (fun c => !c.isWhitespace))

/-- Is the fence language `wiz`? (The fence tag is case-insensitive.) -/
def isWiz (lang : String) : Bool := (languageOf lang).toLower == "wiz"

/-- The tokens of a block read with the built-in grammar (the fallback for a context
without a `CommandState`). -/
def builtinTokens : Array String := Wiz.Builtin.tables.tokens

/-- The class of a token. Reserved words are `atom`s that start like an identifier (or
with `_`, `#`, `@`); other atoms are notation and stay text in P0. Identifiers are left
unstyled: this is lexical, not semantic highlighting. -/
def classOfToken : Token → Option Class
  | .atom s =>
    match s.toList with
    | c :: _ => if c.isAlpha || c == '_' || c == '#' || c == '@' then some .kw else none
    | [] => none
  | .num _ => some .num
  | .str _ => some .str
  | .ident _ => none

/-- The characters `skipWs` treats as whitespace. -/
def isWs : Char → Bool
  | ' ' | '\t' | '\r' | '\n' => true
  | _ => false

/-- Scan a body with the parser's token reader. Every comment is recorded as one
`hl-com` span (the rules are `Token.commentEnd?`, the same ones `skipWs` uses); the
remaining spans are the tokens P0 styles. A lexical error stops the scan, so the rest of
the block is plain (the caller still escapes it). -/
partial def scan (tokens : Array String) (input : Array Char) (i : Nat)
    (acc : Array Span) : Array Span :=
  match input[i]? with
  | none => acc
  | some c =>
    if isWs c then scan tokens input (i + 1) acc
    else
      match commentEnd? input i with
      | some j =>
        -- (a comment always advances: `commentEnd?` returns a position after the opener)
        scan tokens input (max j (i + 1)) (acc.push { start := i, stop := j, cls := .com })
      | none =>
        match readToken tokens input i with
        | .ok ti =>
          let acc := match classOfToken ti.tok with
            | some cls => acc.push { start := ti.start, stop := ti.stop, cls }
            | none => acc
          scan tokens input (max ti.stop (i + 1)) acc
        | .error _ => acc

/-- The spans of a `wiz` body, or `none` for another language. -/
def blockOf (tokens : Array String) (lang : String) (body : String) : Option Block :=
  if isWiz lang then
    some { language := "wiz", source := body, spans := scan tokens body.toList.toArray 0 #[] }
  else none

/-- The escaped body with its spans wrapped. Text between and inside spans is escaped;
only the wrapper tags are added here. -/
def html (spans : Array Span) (src : String) : String :=
  let chars := src.toList.toArray
  let rec go (pos k : Nat) (acc : String) : String :=
    if k ≥ spans.size then
      acc ++ htmlEscape (String.ofList (chars.drop pos).toList)
    else
      let s := spans[k]!
      let start := min s.start chars.size
      let stop := min s.stop chars.size
      if stop ≤ pos then go pos (k + 1) acc
      else
        let before := htmlEscape (String.ofList ((chars.drop pos).take (start - pos)).toList)
        let text := htmlEscape (String.ofList ((chars.drop start).take (stop - start)).toList)
        go stop (k + 1) (acc ++ before ++ s!"<span class=\"{className s.cls}\">{text}</span>")
  if spans.isEmpty then htmlEscape src else go 0 0 ""

/-- A character offset as the UTF-16 offset the browser runtime uses. -/
def utf16Offset (chars : Array Char) (n : Nat) : Nat :=
  (chars.take (min n chars.size)).foldl
    (fun acc c => acc + if c.toNat > 0xFFFF then 2 else 1) 0

/-- `spans` as the `wizHighlight` data the hover runtime reads (`[start, end, class]`,
UTF-16 offsets). -/
def spansJson (chars : Array Char) (spans : Array Span) : Json :=
  Json.arr (spans.map fun s =>
    Json.arr #[Json.num (utf16Offset chars s.start),
      Json.num (utf16Offset chars s.stop), Json.str (className s.cls)])

end Highlight
end Wiz.Doc
