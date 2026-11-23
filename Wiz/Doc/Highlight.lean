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

-- ## The language registry (`docs-highlighting.md` §4)

/-- A package's string rule: open/close delimiters and the escape character. -/
structure StringRule where
  opener : String
  closer : String
  escape : String := "\\"
  multiline : Bool := false
  deriving Repr, Inhabited

/-- A declarative language spec (`docs-highlighting.md` §3.2): no grammar engine, no
callback. Every field is data the scanner below reads. -/
structure Spec where
  lineComment : List String := []
  /-- open, close, nested -/
  blockComment : Option (String × String × Bool) := none
  strings : List StringRule := []
  keywords : List String := []
  numberPrefix : List String := []
  operators : List String := []
  caseFold : Bool := false
  deriving Repr, Inhabited

/-- How a language is tokenised: the parser's own scanner, or a declarative spec. -/
inductive Lexer where
  | wiz
  | spec (s : Spec)
  deriving Repr, Inhabited

/-- A registered language: its canonical name, aliases, lexer and the subset of the
fixed eight classes its renderer emits. -/
structure Lang where
  name : String
  aliases : List String := []
  lexer : Lexer
  classes : List Class := [.kw, .com, .str, .num]
  /-- an external entry may replace a built-in of the same name (`wiz` never) -/
  override : Bool := false
  deriving Repr, Inhabited

/-- The languages `wiz doc` knows. Built-ins first; `--languages` files merge after. -/
structure Registry where
  langs : List Lang := []
  deriving Repr, Inhabited

/-- A class from its HTML name (`"kw"`, …, the exact eight). -/
def Class.ofName? : String → Option Class
  | "kw" => some .kw
  | "com" => some .com
  | "str" => some .str
  | "num" => some .num
  | "op" => some .op
  | "const" => some .const
  | "var" => some .var
  | "sort" => some .sort
  | _ => none

/-- `s` matches `input` at `i`. -/
def matchesAt (input : Array Char) (i : Nat) : List Char → Bool
  | [] => true
  | c :: cs => match input[i]? with
    | some x => x == c && matchesAt input (i + 1) cs
    | none => false

/-- Whether one of `ss` matches at `i`, and the match length. -/
def prefixAt (input : Array Char) (i : Nat) (ss : List String) : Option Nat :=
  ss.findSome? fun s => if matchesAt input i s.toList then some s.length else none

/-- The end of a line comment starting at `i` (the newline is not part of the span). -/
partial def lineCommentEnd (input : Array Char) (i : Nat) : Nat :=
  match input[i]? with
  | none => i
  | some '\n' => i
  | some _ => lineCommentEnd input (i + 1)

/-- The end of a block comment that starts after `open`, honouring nesting. -/
partial def blockCommentEnd (input : Array Char) (i : Nat) (opener closer : String)
    (nested : Bool) (depth : Nat) : Nat :=
  if depth == 0 then i
  else if matchesAt input i closer.toList then
    let j := i + closer.length
    if nested then blockCommentEnd input j opener closer nested (depth - 1) else j
  else if nested && matchesAt input i opener.toList then
    blockCommentEnd input (i + opener.length) opener closer nested (depth + 1)
  else match input[i]? with
    | none => i
    | some _ => blockCommentEnd input (i + 1) opener closer nested depth

/-- The end of a string that starts after `open`, and whether it closed. -/
partial def stringEnd (input : Array Char) (i : Nat) (r : StringRule) : Nat × Bool :=
  if matchesAt input i r.closer.toList then (i + r.closer.length, true)
  else if r.escape != "" && matchesAt input i r.escape.toList then
    stringEnd input (i + r.escape.length + 1) r
  else match input[i]? with
    | none => (i, false)
    | some '\n' => if r.multiline then stringEnd input (i + 1) r else (i, false)
    | some _ => stringEnd input (i + 1) r

/-- An identifier's end (the characters after the first). -/
partial def identEnd (input : Array Char) (i : Nat) : Nat :=
  match input[i]? with
  | some c => if c.isAlphanum || c == '_' || c == '$' then identEnd input (i + 1) else i
  | none => i

/-- A number's end: digits, letters (hex), `_` and `.`. -/
partial def numberEnd (input : Array Char) (i : Nat) : Nat :=
  match input[i]? with
  | some c => if c.isAlphanum || c == '_' || c == '.' then numberEnd input (i + 1) else i
  | none => i

/-- The longest operator from `ops` at `i`, if one matches. -/
def longestOp (input : Array Char) (i : Nat) (ops : List String) : Option Nat :=
  ops.foldl (fun best op =>
    if matchesAt input i op.toList then
      match best with
      | some n => if op.length > n then some op.length else best
      | none => some op.length
    else best) none

/-- Is `w` a keyword of `sp` (case-folded when the spec says so)? -/
def Spec.isKeyword (sp : Spec) (w : String) : Bool :=
  let w := if sp.caseFold then w.toLower else w
  sp.keywords.any fun k => (if sp.caseFold then k.toLower else k) == w

/-- The class of a span only if the language selected it (the fixed enum, a subset). -/
def keepClass (classes : List Class) (c : Class) : Option Class :=
  if classes.contains c then some c else none

-- Scan one declarative spec, in char offsets. Comments and strings are always consumed,
-- even when their class is not selected, so their contents are never re-tokenised.
mutual
partial def specScan (classes : List Class) (sp : Spec) (input : Array Char) (i : Nat)
    (acc : Array Span) : Array Span :=
  match input[i]? with
  | none => acc
  | some c =>
    if c.isWhitespace then specScan classes sp input (i + 1) acc
    else
      -- line comment
      match prefixAt input i sp.lineComment with
      | some _ =>
        let j := lineCommentEnd input i
        specScan classes sp input j
          (match keepClass classes .com with
            | some k => acc.push { start := i, stop := j, cls := k }
            | none => acc)
      | none =>
        match sp.blockComment with
        | some (op, cl, nested) =>
          if matchesAt input i op.toList then
            let j := blockCommentEnd input (i + op.length) op cl nested 1
            specScan classes sp input j
              (match keepClass classes .com with
                | some k => acc.push { start := i, stop := j, cls := k }
                | none => acc)
          else specScanBody classes sp input i c acc
        | none => specScanBody classes sp input i c acc

/-- The non-comment part of `specScan`: strings, numbers, identifiers, operators. -/
partial def specScanBody (classes : List Class) (sp : Spec) (input : Array Char) (i : Nat)
    (c : Char) (acc : Array Span) : Array Span :=
  -- string
  match sp.strings.find? (fun r => matchesAt input i r.opener.toList) with
  | some r =>
    let j := stringEnd input (i + r.opener.length) r
    specScan classes sp input j.1
      (match keepClass classes .str with
        | some k => acc.push { start := i, stop := j.1, cls := k }
        | none => acc)
  | none =>
    -- number (a digit, or a listed prefix followed by one)
    if c.isDigit || sp.numberPrefix.any (fun p =>
        matchesAt input i p.toList &&
        (match input[i + p.length]? with
          | some d => d.isDigit
          | none => false)) then
      let j := numberEnd input (i + 1)
      specScan classes sp input j
        (match keepClass classes .num with
          | some k => acc.push { start := i, stop := j, cls := k }
          | none => acc)
    else if c.isAlpha || c == '_' || c == '$' then
      let j := identEnd input (i + 1)
      let w := String.ofList ((input.extract i j).toList)
      specScan classes sp input j
        (if sp.isKeyword w then
          match keepClass classes .kw with
          | some k => acc.push { start := i, stop := j, cls := k }
          | none => acc
         else acc)
    else
      match longestOp input i sp.operators with
      | some n =>
        specScan classes sp input (i + n)
          (match keepClass classes .op with
            | some k => acc.push { start := i, stop := i + n, cls := k }
            | none => acc)
      | none => specScan classes sp input (i + 1) acc
end

/-- The built-in specs: the four non-Wiz languages the docs read most
(`docs-highlighting.md` §3.2). Identifiers stay unstyled; the classes are lexical. -/
def builtinSh : Lang :=
  { name := "sh", lexer := .spec {
      lineComment := ["#"]
      strings := [{ opener := "'", closer := "'" }, { opener := "\"", closer := "\"" }]
      keywords := ["if","then","else","elif","fi","for","do","done","case","esac",
        "while","until","function","in","export","local","return","set","unset"]
      operators := ["&&","||",";;","<<",">>","|","&",";","<",">","="]
    } }

def builtinJson : Lang :=
  { name := "json", lexer := .spec {
      strings := [{ opener := "\"", closer := "\"", escape := "\\" }]
      keywords := ["true","false","null"]
      numberPrefix := ["-"]
      operators := [":",",","[","]","{","}"]
    }, classes := [.kw, .str, .num, .op] }

def builtinWgsl : Lang :=
  { name := "wgsl", lexer := .spec {
      lineComment := ["//"]
      blockComment := some ("/*", "*/", true)
      strings := [{ opener := "\"", closer := "\"", escape := "\\" }]
      keywords := ["fn","let","var","const","struct","return","if","else","for","while",
        "loop","break","continue","true","false","switch","case","default","discard"]
      numberPrefix := ["0x","0b"]
      operators := ["->","==","!=","<=",">=","&&","||","<<",">>","+=","-=","*=","/=",
        "+","-","*","/","%","=","<",">","&","|","^","!","~",".",","]
    } }

def builtinLean : Lang :=
  { name := "lean", lexer := .spec {
      lineComment := ["--"]
      blockComment := some ("/-", "-/", true)
      strings := [{ opener := "\"", closer := "\"", escape := "\\" }]
      keywords := ["def","theorem","lemma","structure","inductive","class","instance",
        "where","match","with","fun","let","in","if","then","else","do","by","import",
        "open","namespace","end","mutual","section","variable","example","deriving","have",
        "show","from","at","set_option"]
      operators := ["→","←","↔","∀","∃","λ","≤","≥","≠","∧","∨","+","-","*","/","=","<",
        ">","++","::",":=","|>","<|"]
    } }

/-- The built-in registry: `wiz` uses the parser's own scanner, the rest their spec. -/
def Registry.builtins : Registry :=
  { langs := [
      { name := "wiz", lexer := .wiz },
      builtinSh, builtinJson, builtinWgsl, builtinLean
    ] }

/-- The language `name` (case-insensitive), by canonical name or alias. -/
def Registry.find? (r : Registry) (name : String) : Option Lang :=
  let n := name.toLower
  r.langs.find? fun l =>
    l.name.toLower == n || l.aliases.any fun a => a.toLower == n


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

/-- A block's spans in the registry: `wiz` uses the parser's own scanner and token
table; every other registered language uses its declarative spec. An unknown, untagged
or invalid language is `none` (the caller renders it plain: all or plain). -/
def blockOf (reg : Registry) (tokens : Array String) (lang : String) (body : String) :
    Option Block :=
  let word := languageOf lang
  match reg.find? word with
  | none => none
  | some l => match l.lexer with
    | .wiz =>
      some { language := l.name, source := body,
             spans := scan tokens body.toList.toArray 0 #[] }
    | .spec sp =>
      some { language := l.name, source := body,
             spans := specScan l.classes sp body.toList.toArray 0 #[] }

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
