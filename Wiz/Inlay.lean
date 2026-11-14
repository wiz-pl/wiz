import Wiz.Query

/-!
# Inlay hints

`textDocument/inlayHint` shows, after a binder the user wrote without a type, the type
the elaborator gave it: ` : Nat` after `x` in `fun x => …`, after `n` in `let n := …`.
The binders are the info tree's local identifiers (`recordBinder`) whose text is the
binder's own name, with `fun`/`λ` (past the other binders of the group) or `let` before
it, and `=>`, `↦`, `:=` or another binder after it, not `:`.
-/

namespace Wiz.Inlay

variable {R : Type} [QRig R] [DecidableEq R] [ToString R] [QuantitySyntax R]

structure Hint where
  /-- where the hint goes (after the binder) -/
  at_ : Nat
  label : String
  deriving Repr, Inhabited, BEq

/-- The word before `i` (skipping spaces), and where it starts. -/
def wordBefore (chars : Array Char) (i : Nat) : String × Nat := Id.run do
  let mut j := i
  while j > 0 && (chars[j - 1]! == ' ' || chars[j - 1]! == '\t') do j := j - 1
  let stop := j
  while j > 0 && (isIdRest chars[j - 1]! || chars[j - 1]! == '.') do j := j - 1
  (String.ofList (chars.extract j stop).toList, j)

/-- The first non-space characters after `i`. -/
def after (chars : Array Char) (i : Nat) : String := Id.run do
  let mut j := i
  while j < chars.size && (chars[j]! == ' ' || chars[j]! == '\t') do j := j + 1
  String.ofList (chars.extract j (j + 2)).toList

/-- Is the identifier at `[a, b)` a binder of `fun`/`λ` or `let`, without a type? -/
def unannotatedBinder (chars : Array Char) (a b : Nat) : Bool := Id.run do
  let nxt := after chars b
  if nxt.startsWith ":" && !nxt.startsWith ":=" then return false
  -- back over the other binders of the group to the keyword
  let mut i := a
  for _ in [0:32] do
    let (w, j) := wordBefore chars i
    if w == "fun" || w == "λ" then
      return nxt.startsWith "=>" || nxt.startsWith "↦" || (nxt.length > 0 && (isIdStart nxt.front || nxt.front == '_'))
    if w == "let" then return nxt.startsWith ":="
    if w.isEmpty || !(w.all fun c => isIdRest c) then
      -- `fun x y` written with `λ` directly before (no space): `λx`
      return (j > 0 && chars[j - 1]! == 'λ') && (nxt.startsWith "=>" || nxt.startsWith "↦")
    i := j
  false

/-- The hints in the range `[start, stop)` of `text`. -/
def hintsIn (s : CommandState R) (text : String) (start stop : Nat) : Array Hint := Id.run do
  let chars := text.toList.toArray
  let mut out : Array Hint := #[]
  let mut seen : Std.HashSet Nat := {}
  for i in s.infos do
    if let .ident r x true names ty := i then
      if r.synthetic || r.stop ≤ r.start || r.start < start || r.stop > stop || seen.contains r.stop then continue
      -- (the binder's own name as written)
      if String.ofList (chars.extract r.start r.stop).toList != x then continue
      if unannotatedBinder chars r.start r.stop then
        seen := seen.insert r.stop
        out := out.push { at_ := r.stop, label := s!" : {ty.pretty names}" }
  out

end Wiz.Inlay
