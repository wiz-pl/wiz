import Std.Data.HashMap
import Wiz.Parser.Descr
import Wiz.Parser.Token

/-!
# The parser monad

A parser is a function `PCtx → PState → PResult α`. We write it by hand, not as
`StateT PState (Except _)`, because a *failing* parser still has to return its state:

* the **farthest error**, i.e. the furthest offset any alternative reached together
  with everything that was expected there, which is what produces a useful
  "expected ..." message after backtracking;
* the **memo table** (packrat caching of category parses), so work done inside a
  failed alternative isn't repeated by the next one.

Backtracking is unlimited: `orElse` restores the offset and tries the other branch.
-/

namespace Wiz

structure ParseError where
  pos : Nat := 0
  /-- everything that was expected at `pos`, as the alternatives failed there (the
  self-hosted parser, selfhost/Parse.wiz, reports the same list) -/
  expected : Array String := #[]
  /-- a token that could not be read there (a bad escape, an unexpected character): it
  is the message, rather than what was expected -/
  lexical : Option String := none
  /-- the same, for the message: a syntax category whose alternatives all failed at its
  first token is one entry ("term"), and what would only have continued a complete
  phrase is marked `secondary` -/
  shown : Array String := #[]
  deriving Repr, Inhabited

/-- The mark of an expectation that is shown only if there is no other one: what would
have continued a complete phrase (an infix operator, an application's argument). -/
def ParseError.secondary : String := "\x01"

/-- An expectation that says more than any summary of it: a keyword where an identifier
was expected, a character no token starts with. -/
def ParseError.telling (x : String) : Bool :=
  (x.splitOn "is a keyword").length > 1 || x.startsWith "unexpected character"

/-- `a`, `a or b`, `a, b or c`. -/
def orList : List String → String
  | [] => ""
  | [a] => a
  | [a, b] => s!"{a} or {b}"
  | a :: rest => s!"{a}, {orList rest}"

/-- What the input has at `pos`, for "unexpected …": the token (roughly: up to the next
space or bracket), or the end of the input. -/
def foundAt (input : String) (pos : Nat) : String :=
  let rest := (input.toList.drop pos).dropWhile (·.isWhitespace)
  match rest with
  | [] => "end of input"
  | c :: _ =>
    let stop (c : Char) := c.isWhitespace || "()[]{}⟨⟩,;".contains c
    let tok := if stop c then [c] else (rest.takeWhile (!stop ·)).take 20
    s!"'{String.ofList tok}'"

def ParseError.render (input : String) (e : ParseError) : String :=
  let (l, c) := lineCol input e.pos
  -- (the tokenizer's own complaint, `unexpected character '←'`, says what was found)
  let (unexp, exp) := e.shown.toList.partition (·.startsWith "unexpected ")
  let (second, first) := exp.partition (·.startsWith ParseError.secondary)
  let exp := if first.isEmpty then second.map (·.drop 1 |>.toString) else first
  let exp := exp.eraseDups
  let found := unexp.head?.getD s!"unexpected {foundAt input e.pos}"
  let exp := match e.lexical with
    | some m => m
    | none => if e.shown.isEmpty then "parse error"
      else if exp.isEmpty then found
      else s!"{found}; expected {orList exp}"
  s!"{l + 1}:{c + 1}: {exp}"

structure MemoKey where
  cat : Name
  prec : Nat
  pos : Nat
  saved : Option Nat
  deriving BEq, Hashable

structure PCtx where
  input : Array Char
  tables : ParserTables
  savedPos? : Option Nat := none
  /-- the precedence the innermost category is being parsed at -/
  prec : Nat := 0
  /-- the words that are not identifiers in the innermost category: the keywords of its
  scope (13j). A function of the category, so the memo key need not mention it. -/
  reserved : Array String := #[]

structure PState where
  pos : Nat := 0
  err : ParseError := {}
  memo : Std.HashMap MemoKey (Option (Syntax × Nat)) := {}
  /-- the token after each offset (where it starts, after whitespace), since alternatives
  look at the same tokens again and again -/
  toks : Std.HashMap Nat (Nat × Except String TokInfo) := {}

inductive PResult (α : Type) where
  | ok (a : α) (s : PState)
  | error (s : PState)

def P (α : Type) : Type := PCtx → PState → PResult α

instance : Monad P where
  pure a := fun _ s => .ok a s
  bind x f := fun c s => match x c s with
    | .ok a s => f a c s
    | .error s => .error s

namespace P

def ctx : P PCtx := fun c s => .ok c s
def state : P PState := fun _ s => .ok s s
def setPos (pos : Nat) : P Unit := fun _ s => .ok () { s with pos }
def withCtx (f : PCtx → PCtx) (p : P α) : P α := fun c s => p (f c) s

/-- Fail at `pos`, recording what was expected there if it is the farthest failure. -/
def failAt (pos : Nat) (expected : String) : P α := fun _ s =>
  let err :=
    if pos > s.err.pos then { pos, expected := #[expected], shown := #[expected] }
    else if pos == s.err.pos then
      if s.err.expected.contains expected && s.err.shown.contains expected then s.err else
      { s.err with expected := if s.err.expected.contains expected then s.err.expected else s.err.expected.push expected,
                   shown := if s.err.shown.contains expected then s.err.shown else s.err.shown.push expected }
    else s.err
  .error { s with err }

/-- Fail at `pos` because no token can be read there (`msg` says why). -/
def failLexAt (pos : Nat) (msg : String) : P α := fun _ s =>
  let err := if pos > s.err.pos then { pos, lexical := some msg }
    else if pos == s.err.pos then { s.err with lexical := some msg } else s.err
  .error { s with err }

/-- Replace what the farthest error expects at `pos` by `expected`, keeping what `before`
(the farthest error before some alternatives ran) expected there: the alternatives of a
syntax category that all failed at its first token are reported as the category
("expected term", not every token a term can start with). -/
def collapseErrAt (pos : Nat) (before : ParseError) (expected : String) : P Unit := fun _ s =>
  if s.err.pos != pos then .ok () s else
  let kept := if before.pos == pos then before.shown else #[]
  -- (but "'match' is a keyword here" and the tokenizer's "unexpected character" say
  -- more than "term")
  let kept := kept ++ s.err.shown.filter fun x => ParseError.telling x && !kept.contains x
  .ok () { s with err := { s.err with shown := if kept.contains expected then kept else kept.push expected } }

/-- Mark what was expected at `pos` since `before` (if the farthest error is there) as
secondary (`ParseError.secondary`): shown only when nothing else was expected there. -/
def markSecondaryAt (pos : Nat) (before : ParseError) : P Unit := fun _ s =>
  if s.err.pos != pos || before.pos > pos then .ok () s else
  let old := if before.pos == pos then before.shown else #[]
  let shown := s.err.shown.map fun x =>
    if old.contains x || x.startsWith ParseError.secondary || ParseError.telling x then x
    else ParseError.secondary ++ x
  .ok () { s with err := { s.err with shown } }

/-- Ordered choice with backtracking. (Only the position is kept for backtracking:
keeping `s` itself while `p` runs would share its memo table with `p`'s state, so that
every `memoStore` in `p` copied the whole table, quadratic in the input's length.) -/
def orElse (p q : P α) : P α := fun c s =>
  let pos := s.pos
  match p c s with
  | .ok a s' => .ok a s'
  | .error s' => q c { s' with pos }

instance : OrElse (P α) := ⟨fun p q => orElse p (q ())⟩

/-- Run `p`; on failure, backtrack and return `none`. -/
def try? (p : P α) : P (Option α) := orElse (some <$> p) (pure none)

def memoLookup (k : MemoKey) : P (Option (Option (Syntax × Nat))) := fun _ s =>
  .ok s.memo[k]? s

def memoStore (k : MemoKey) (v : Option (Syntax × Nat)) : P Unit := fun _ s =>
  .ok () { s with memo := s.memo.insert k v }

/-- Offset of the next significant character. -/
def nextPos : P Nat := do
  let c ← ctx
  let s ← state
  match s.toks[s.pos]? with
  | some (i, _) => pure i
  | none => pure (skipWs c.input s.pos)

/-- Look at the next token without consuming it. `none` at the end of input. -/
def peekToken : P (Option TokInfo) := fun c s =>
  let ((i, r), s) := match s.toks[s.pos]? with
    | some e => (e, s)
    | none =>
      let i := skipWs c.input s.pos
      let e := (i, readToken c.tables.tokens c.input i)
      (e, { s with toks := s.toks.insert s.pos e })
  if i ≥ c.input.size then .ok none s
  else match r with
    | .ok t => .ok (some t) s
    -- a bad escape is reported where it is, not at the literal's start
    | .error msg => failLexAt (if c.input[i]? == some '"' then strErrorPos c.input i else i) msg c s

/-- Consume the next token. -/
def nextToken (expected : String) : P TokInfo := do
  match ← peekToken with
  | some t => setPos t.stop; pure t
  | none => failAt (← nextPos) expected

end P

/-- Run a parser on a whole input. -/
def P.run (p : P α) (input : Array Char) (tables : ParserTables) (pos : Nat := 0) :
    Except ParseError (α × Nat) :=
  match p { input, tables } { pos } with
  | .ok a s => .ok (a, s.pos)
  | .error s => .error s.err

end Wiz
