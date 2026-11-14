import Wiz.Syntax.Basic

/-!
# Tokens

The parser is *scannerless*: no separate lexing pass. Tokens are read on demand from
any offset, because the set of reserved tokens can grow mid-file when a `syntax`
declaration adds new keywords or symbols.

The input is an `Array Char` and offsets are character indices.

Reading a token at offset `i`:

1. An identifier-start character reads an identifier. If the identifier is in the
   token table, it is a keyword. If a symbol token from the table matches a strictly
   *longer* prefix, the symbol wins.
2. A digit reads a number: decimal, or hexadecimal `0x3F` / binary `0b101`, which
   become the decimal `num` token they denote.
3. `"` reads a string literal.
4. Anything else is the **longest** token in the table that is a prefix of the input.
-/

namespace Wiz

inductive Token where
  | atom (val : String)
  | ident (val : Name)
  | num (digits : String)
  /-- decoded contents -/
  | str (val : String)
  deriving Repr, BEq, Inhabited

structure TokInfo where
  tok : Token
  start : Nat
  stop : Nat
  deriving Repr, Inhabited

/-- Letters that may start an identifier: ASCII letters, `_`, and Greek letters except
`λ`, `Π` and `Σ`, which are reserved for syntax. -/
def isIdStart (c : Char) : Bool :=
  c.isAlpha || c == '_' ||
  (('α' ≤ c && c ≤ 'ω') && c != 'λ') ||
  (('Α' ≤ c && c ≤ 'Ω') && c != 'Π' && c != 'Σ')

def isSubscript (c : Char) : Bool := '₀' ≤ c && c ≤ '₉'

def isIdRest (c : Char) : Bool :=
  isIdStart c || c.isDigit || c == '\'' || c == '!' || isSubscript c

/-- **Exercise 2.1.** Skip whitespace and comments starting at offset `i`, returning
the offset of the next significant character, or `input.size` at the end of input.

* Whitespace is `' '`, `'\t'`, `'\r'` and `'\n'`.
* `--` starts a comment running to the end of the line.
* `/-` starts a block comment ending at the matching `-/`. Block comments **nest**:
  `/- a /- b -/ c -/` is a single comment. An unterminated block comment runs to the
  end of the input. -/
partial def skipWs (input : Array Char) (i : Nat) : Nat :=
  --<sol
  match input[i]? with
  | some ' ' | some '\t' | some '\r' | some '\n' => skipWs input (i + 1)
  | some '-' => if input[i + 1]? == some '-' then skipWs input (lineEnd (i + 2)) else i
  | some '/' => if input[i + 1]? == some '-' then skipWs input (blockEnd (i + 2) 1) else i
  | _ => i
where
  lineEnd (j : Nat) : Nat :=
    match input[j]? with
    | none => j
    | some '\n' => j + 1
    | some _ => lineEnd (j + 1)
  blockEnd (j depth : Nat) : Nat :=
    match input[j]?, input[j + 1]? with
    | none, _ => j
    | some '-', some '/' => if depth == 1 then j + 2 else blockEnd (j + 2) (depth - 1)
    | some '/', some '-' => blockEnd (j + 2) (depth + 1)
    | _, _ => blockEnd (j + 1) depth
  --sol>

/-- **Exercise 2.2a.** Read an identifier starting at `i` (where `isIdStart` holds).
Identifiers may contain dots between components, like `Nat.add`. A `.` is part of the
identifier only if the character after it can start an identifier.
Returns the identifier and the offset just after it. -/
partial def readIdent (input : Array Char) (i : Nat) : String × Nat :=
  --<sol
  go i ""
where
  go (j : Nat) (acc : String) : String × Nat :=
    match input[j]? with
    | some c =>
      if isIdRest c then go (j + 1) (acc.push c)
      else if c == '.' && (input[j + 1]?.map isIdStart).getD false then go (j + 1) (acc.push c)
      else (acc, j)
    | none => (acc, j)
  --sol>

def hexVal? (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10) else none

/-- The escape sequence whose backslash is at `input[j]`: the character it stands for and
the offset after it, or why it is not one. `\n`, `\t`, `\r`, `\0`, `\\`, `\"`, `\'`,
`\xHH` (two hex digits) and `\u{H}` (one to six hex digits, a Unicode scalar value). The
self-hosted lexer (`selfhost/Lex.wiz`, `readStr`) reads the same escapes, with the same
messages. -/
def readEscape (input : Array Char) (j : Nat) : Except String (Char × Nat) :=
  match input[j + 1]? with
  | some 'n' => .ok ('\n', j + 2)
  | some 't' => .ok ('\t', j + 2)
  | some 'r' => .ok ('\r', j + 2)
  | some '0' => .ok (Char.ofNat 0, j + 2)
  | some '\\' => .ok ('\\', j + 2)
  | some '"' => .ok ('"', j + 2)
  | some '\'' => .ok ('\'', j + 2)
  | some 'x' => match (input[j + 2]?.bind hexVal?), (input[j + 3]?.bind hexVal?) with
    | some a, some b => .ok (Char.ofNat (a * 16 + b), j + 4)
    | _, _ => .error "the escape \\x needs two hexadecimal digits (as in \\x41)"
  | some 'u' =>
    let bad : Except String (Char × Nat) :=
      .error "the escape \\u is written \\u{H}, with one to six hexadecimal digits (as in \\u{3bb})"
    -- the digits from `input[k]`: `count` read so far, worth `n`
    let rec digits (k n count : Nat) (fuel : Nat) : Except String (Char × Nat) :=
      match fuel with
      | 0 => bad
      | f + 1 => match input[k]? with
      | none => bad
      | some c =>
        if c == '}' then
          if count == 0 then bad
          else if n > 0x10FFFF || (0xD800 ≤ n && n ≤ 0xDFFF) then
            .error "the escape \\u{H} is not a Unicode scalar value (at most 10FFFF, and not D800 to DFFF)"
          else .ok (Char.ofNat n, k + 1)
        else match hexVal? c with
          | some d => if count < 6 then digits (k + 1) (n * 16 + d) (count + 1) f else bad
          | none => bad
    if input[j + 2]? != some '{' then bad else digits (j + 3) 0 0 8
  | some c => .error s!"unknown escape sequence \\{c}"
  | none => .error "unterminated string literal"

/-- Where a string literal starting at `input[i]` goes wrong: the backslash of its first
bad escape, else its start (an unterminated literal). For error positions. -/
partial def strErrorPos (input : Array Char) (i : Nat) : Nat := go (i + 1)
where
  go (j : Nat) : Nat := match input[j]? with
    | none | some '"' => i
    | some '\\' => match readEscape input j with
      | .ok (_, k) => go k
      | .error _ => j
    | some _ => go (j + 1)

/-- **Exercise 2.2b.** Read a string literal; `input[i]` is the opening `"`.
Support the escapes `\n`, `\t`, `\\` and `\"` (the solution reads all of `readEscape`'s).
Returns the *decoded* string and the offset after the closing quote, or an error message
for an unterminated literal or an unknown escape. -/
partial def readStr (input : Array Char) (i : Nat) : Except String (String × Nat) :=
  --<sol
  go (i + 1) ""
where
  go (j : Nat) (acc : String) : Except String (String × Nat) :=
    match input[j]? with
    | none => .error "unterminated string literal"
    | some '"' => .ok (acc, j + 1)
    | some '\\' => match readEscape input j with
      | .ok (c, k) => go k (acc.push c)
      | .error e => .error e
    | some c => go (j + 1) (acc.push c)
  --sol>

/-- Does `tok` occur in `input` at offset `i`? -/
def matchesAt (input : Array Char) (i : Nat) (tok : String) : Bool := Id.run do
  let mut j := i
  for c in tok.toList do
    if input[j]? != some c then return false
    j := j + 1
  true

/-- **Exercise 2.3.** The longest token from `tokens` occurring at offset `i`. -/
def longestToken (tokens : Array String) (input : Array Char) (i : Nat) : Option String :=
  --<sol
  tokens.foldl (init := none) fun best tok =>
    if matchesAt input i tok && tok.length > (best.map (·.length)).getD 0 then some tok else best
  --sol>

/-- Read the token starting at offset `i`, which must not be whitespace. -/
def readToken (tokens : Array String) (input : Array Char) (i : Nat) :
    Except String TokInfo := do
  let some c := input[i]? | throw "unexpected end of input"
  let sym := longestToken tokens input i
  if isIdStart c then
    let (id, j) := readIdent input i
    match sym with
    -- a symbol token at least as long as the identifier wins (e.g. a keyword)
    | some t => if t.length ≥ j - i then return ⟨.atom t, i, i + t.length⟩
    | none => pure ()
    return ⟨.ident id, i, j⟩
  if c.isDigit then
    -- `0x3F`, `0b1010`: hexadecimal and binary numerals, read as the decimal `num`
    -- they denote (everything after the tokenizer sees decimal digits only)
    if c == '0' then
      let radix? : Option (Nat × (Char → Option Nat)) := match input[i + 1]? with
        | some 'x' | some 'X' => some (16, fun d =>
            if d.isDigit then some (d.toNat - '0'.toNat)
            else if 'a' ≤ d && d ≤ 'f' then some (d.toNat - 'a'.toNat + 10)
            else if 'A' ≤ d && d ≤ 'F' then some (d.toNat - 'A'.toNat + 10) else none)
        | some 'b' | some 'B' => some (2, fun d => if d == '0' || d == '1' then some (d.toNat - '0'.toNat) else none)
        | _ => none
      if let some (radix, digit) := radix? then
        if (input[i + 2]?.bind digit).isSome then
          let mut j := i + 2
          let mut n := 0
          while true do
            let some d := input[j]?.bind digit | break
            n := n * radix + d
            j := j + 1
          return ⟨.num (toString n), i, j⟩
    let mut j := i
    let mut digits := ""
    while (input[j]?.map Char.isDigit).getD false do
      digits := digits.push input[j]!
      j := j + 1
    return ⟨.num digits, i, j⟩
  if c == '"' then
    let (s, j) ← readStr input i
    return ⟨.str s, i, j⟩
  match sym with
  | some t => return ⟨.atom t, i, i + t.length⟩
  | none => throw s!"unexpected character '{c}'"

end Wiz
