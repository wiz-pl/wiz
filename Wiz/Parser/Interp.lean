import Wiz.Parser.Monad

/-!
# Interpreting grammars

`runDescr` interprets one `ParserDescr`, and `categoryParser` is the Pratt loop for a
syntax category. They are mutually recursive because `cat` descriptors call back into
categories.

## Choosing between parsers

Within a category, *all* applicable leading parsers are tried from the same offset and
the one that consumes the **most input** wins. Ties go to the higher priority, then to
the parser **declared later**, so a user `syntax` declaration can override a built-in
one deterministically. Trailing parsers are chosen the same way.

Longest match makes grammars compose: `(x : A) → B` (a dependent arrow) and `(x : A)`
(a type ascription) both start with `(`. The arrow consumes more, so it wins.

Trying every alternative would be exponential on nested input, so category parses are
memoised by `(category, precedence, offset, saved position)`. This is packrat parsing.
-/

namespace Wiz

open P

/-- Column of an offset, 0-based. -/
def colOf (input : Array Char) (i : Nat) : Nat :=
  go i 0 i
where
  go (j col : Nat) : Nat → Nat
    | 0 => col
    | fuel + 1 => if j > 0 && input[j - 1]! != '\n' then go (j - 1) (col + 1) fuel else col

private def tokSyntax (t : TokInfo) : Syntax :=
  let info := { start := t.start, stop := t.stop }
  match t.tok with
  | .atom v => .atom info v
  | .ident n => .ident info n
  | .num d => .node info Syntax.numKind #[.atom info d]
  | .str s => .node info Syntax.strKind #[.atom info s]

/-- Pack the results of one iteration of `many`/`optional`: a single result stays as
is, otherwise wrap them in a `null` node. -/
def packItems (items : Array Syntax) : Syntax :=
  if h : items.size = 1 then items[0] else Syntax.mkNull items

/-- A successful alternative: what it built, where it stopped, and its rank. -/
structure Candidate where
  stx : Syntax
  stop : Nat
  prec : Nat
  priority : Nat
  index : Nat
  /-- the parser state after it ran (offset, errors; not the memo or token cache) -/
  state : PState

/-- **Exercise 2.5a.** Pick the winning candidate: the furthest `stop`, then the
highest `priority`, then the highest `index` (declared latest). -/
def Candidate.best (cs : Array Candidate) : Option Candidate :=
  --<sol
  cs.foldl (init := none) fun acc c => match acc with
    | none => some c
    | some b =>
      let better := c.stop > b.stop || (c.stop == b.stop &&
        (c.priority > b.priority || (c.priority == b.priority && c.index > b.index)))
      if better then some c else some b
  --sol>

/-- Run `p` from the current state as one alternative among several. On success it
returns the candidate *without* committing to its state; on failure it still keeps the
error and memo information. -/
def tryAlternative (p : P Syntax) (prec priority index : Nat) : P (Option Candidate) :=
  fun c s =>
    -- what to come back to, without the tables: keeping `s` itself while `p` runs would
    -- share them with `p`'s state, so that every insertion in `p` copied them
    let s₀ := { s with memo := {}, toks := {} }
    match p c s with
    | .ok stx s' =>
      -- the candidate doesn't keep the memo (`commit` replaces it anyway): sharing it would
      -- make the next `memoStore` copy the whole table
      let memo := s'.memo
      let toks := s'.toks
      let state := { s' with memo := {}, toks := {} }
      .ok (some { stx, stop := s'.pos, prec, priority, index, state })
        { s₀ with err := s'.err, memo, toks }
    | .error s' => .ok none { s₀ with err := s'.err, memo := s'.memo, toks := s'.toks }

/-- Commit to a candidate's state, keeping the accumulated errors and memo. -/
def commit (cand : Candidate) : P Unit := fun _ s =>
  .ok () { cand.state with err := s.err, memo := s.memo, toks := s.toks }

mutual

/-- **Exercise 2.4.** Interpret a descriptor, returning the syntax it produced.
Most cases are done; implement `many`, `many1`, `optional`, `sepBy` and `sepBy1`.

* `many p`: repeat `p` (with `try?`) until it fails **or stops making progress**, and
  return a single `null` node of the iterations, each one packed with `packItems`.
* `many1 p`: the same, but at least one iteration is required.
* `optional p`: a `null` node containing `p`'s items, or an empty one.
* `sepBy p sep allowTrailing`: `p (sep p)*` with the separator atoms included in the
  `null` node. With `allowTrailing`, a final `sep` is allowed. Empty input is fine.
* `sepBy1`: at least one `p`. -/
partial def runDescr : ParserDescr → P (Array Syntax)
  | .atom tok => do
    let i ← nextPos
    match ← peekToken with
    | some t@{ tok := .atom v, .. } =>
      if v == tok then setPos t.stop; pure #[tokSyntax t] else failAt i s!"'{tok}'"
    | _ => failAt i s!"'{tok}'"
  | .nonReserved tok => do
    let i ← nextPos
    match ← peekToken with
    | some t@{ tok := .ident v, .. } | some t@{ tok := .atom v, .. } =>
      if v == tok then setPos t.stop; pure #[.atom { start := t.start, stop := t.stop } tok]
      else failAt i s!"'{tok}'"
    | _ => failAt i s!"'{tok}'"
  | .ident => do
    let i ← nextPos
    match ← peekToken with
    | some t@{ tok := .ident v, .. } =>
      -- a keyword of the category's scope is not an identifier here (13j)
      if (← ctx).reserved.contains v then failAt i s!"identifier ('{v}' is a keyword here)" else
      setPos t.stop; pure #[tokSyntax t]
    | some t@{ tok := .atom "$", .. } =>
      -- an antiquotation where an identifier is expected (inside quotations)
      setPos t.stop
      match ← peekToken with
      | some t'@{ tok := .ident _, .. } =>
        if t'.start != t.stop then failAt i "identifier" else
        setPos t'.stop
        pure #[.node { start := t.start, stop := t'.stop } "antiquot" #[tokSyntax t, tokSyntax t']]
      | _ => failAt i "identifier"
    -- a word that a `term`/`command` rule reserved: say so (`ParseError.explainKeywords`
    -- names the rule when the error is reported, 13o)
    | some { tok := .atom v, .. } =>
      if v != "" && isIdStart v.front && v.all isIdRest then failAt i s!"identifier ('{v}' is a keyword)"
      else failAt i "identifier"
    | _ => failAt i "identifier"
  | .num => do
    let i ← nextPos
    match ← peekToken with
    | some t@{ tok := .num _, .. } => setPos t.stop; pure #[tokSyntax t]
    | _ => failAt i "numeral"
  | .str => do
    let i ← nextPos
    match ← peekToken with
    | some t@{ tok := .str _, .. } => setPos t.stop; pure #[tokSyntax t]
    | _ => failAt i "string literal"
  | .cat c prec => return #[← categoryParser c prec]
  | .seq ps => ps.foldlM (fun acc p => return acc ++ (← runDescr p)) #[]
  --<sol
  | .many p => return #[Syntax.mkNull (← manyLoop p #[])]
  | .many1 p => do
    let first ← runDescr p
    return #[Syntax.mkNull (← manyLoop p #[packItems first])]
  | .optional p => do
    let r ← try? (runDescr p)
    return #[Syntax.mkNull (r.getD #[])]
  | .sepBy p sep trailing => do
    match ← try? (runDescr p) with
    | none => return #[Syntax.mkNull #[]]
    | some first => return #[Syntax.mkNull (← sepLoop p sep trailing #[packItems first])]
  | .sepBy1 p sep trailing => do
    let first ← runDescr p
    return #[Syntax.mkNull (← sepLoop p sep trailing #[packItems first])]
  --|ex
  --| | .many p => sorry
  --| | .many1 p => sorry
  --| | .optional p => sorry
  --| | .sepBy p sep trailing => sorry
  --| | .sepBy1 p sep trailing => sorry
  --sol>
  | .orelse p q => runDescr p <|> runDescr q
  | .node k p => do
    let start ← nextPos
    let items ← runDescr p
    let stop := (← state).pos
    return #[.node { start := min start stop, stop } k items]
  | .withPosition p => do
    let i ← nextPos
    withCtx (fun c => { c with savedPos? := some i }) (runDescr p)
  | .withoutPosition p => withCtx (fun c => { c with savedPos? := none }) (runDescr p)
  | .colGt => do
    let c ← ctx
    let i ← nextPos
    match c.savedPos? with
    | some sp =>
      if colOf c.input i > colOf c.input sp then pure #[]
      else failAt i s!"token right of column {colOf c.input sp + 1}"
    | none => pure #[]
  | .colGe => do
    let c ← ctx
    let i ← nextPos
    match c.savedPos? with
    | some sp =>
      if colOf c.input i ≥ colOf c.input sp then pure #[]
      else failAt i s!"token at or right of column {colOf c.input sp + 1}"
    | none => pure #[]
  | .noWs => do
    let s ← state
    if (← nextPos) == s.pos then pure #[] else failAt s.pos "no space before this token"
  | .checkPrec p => do
    if (← ctx).prec ≤ p then pure #[] else failAt (← nextPos) s!"precedence at most {p}"

--<sol
/-- Iterations of `many` after the ones already in `acc`. -/
partial def manyLoop (p : ParserDescr) (acc : Array Syntax) : P (Array Syntax) := do
  let before := (← state).pos
  match ← try? (runDescr p) with
  | some items =>
    if (← state).pos == before then setPos before; pure acc
    else manyLoop p (acc.push (packItems items))
  | none => pure acc

/-- `(sep p)*`, then an optional trailing `sep`. -/
partial def sepLoop (p : ParserDescr) (sep : String) (trailing : Bool)
    (acc : Array Syntax) : P (Array Syntax) := do
  match ← try? (runDescr (.atom sep)) with
  | none => pure acc
  | some sepStx =>
    match ← try? (runDescr p) with
    | some items => sepLoop p sep trailing (acc ++ sepStx |>.push (packItems items))
    | none => if trailing then pure (acc ++ sepStx) else failAt (← nextPos) "separated item"

--|ex
--sol>
/-- **Exercise 2.5b.** The Pratt loop for category `c` at minimum precedence `rbp`.

1. Leading: try every leading parser of `c` with `prec ≥ rbp` (as `node kind p`,
   using `tryAlternative`). If none succeeds, fail with `"<c>"` expected. Otherwise
   `commit` to `Candidate.best`. The current left-hand side is now that node, and the
   current `lhsPrec` is that parser's `prec`.
2. Trailing, repeatedly: try every trailing parser with `prec ≥ rbp` and
   `lhsPrec ≤ current lhsPrec`. The result is a node of the trailing parser's kind whose
   children are the current left-hand side followed by the trailing parser's items.
   Ignore alternatives that consume nothing, or the loop would never end. Commit to
   the best one and continue; stop when none applies.

The memoisation around this is already written in `categoryParser`. -/
partial def categoryLoop (c : Name) (rbp : Nat) : P Syntax := do
  let tables := (← ctx).tables
  let some cat := tables.cats[c]? | failAt (← nextPos) s!"declared syntax category {c}"
  --<sol
  let errBefore := (← state).err
  let mut leading := #[]
  for lp in cat.leading, i in [0:cat.leading.size] do
    if lp.prec ≥ rbp then
      let run := withCtx (fun c => { c with prec := rbp }) (runDescr (.node lp.kind lp.p))
      if let some cand ← tryAlternative (run >>= fun r => pure r[0]!)
          lp.prec lp.priority i then
        leading := leading.push cand
  let some best := Candidate.best leading | do
    -- nothing got past the first token: say "expected term", not every token a term
    -- can start with
    let p ← nextPos
    collapseErrAt p errBefore c
    failAt p c
  commit best
  trailingLoop cat rbp best.stx best.prec
  --|ex
  --| sorry
  --sol>

--<sol
partial def trailingLoop (cat : Category) (rbp : Nat) (lhs : Syntax) (lhsPrec : Nat) :
    P Syntax := do
  let start := (← state).pos
  let errBefore := (← state).err
  let mut cands := #[]
  for tp in cat.trailing, i in [0:cat.trailing.size] do
    if tp.prec ≥ rbp && tp.lhsPrec ≤ lhsPrec then
      let p : P Syntax := do
        let items ← runDescr tp.p
        let stop := (← state).pos
        pure (.node { start := lhs.info.start, stop } tp.kind (#[lhs] ++ items))
      if let some cand ← tryAlternative p tp.prec tp.priority i then
        if cand.stop > start then cands := cands.push cand
  match Candidate.best cands with
  | none =>
    -- nothing continues the phrase here: what a continuation would have needed at the
    -- next token (an operator, an argument) is not what to report if the parse fails
    -- there ("expected ')'", not every infix operator)
    markSecondaryAt (← nextPos) errBefore
    pure lhs
  | some best =>
    commit best
    trailingLoop cat rbp best.stx best.prec

--|ex
--sol>
/-- Memoised category parser. -/
partial def categoryParser (c : Name) (rbp : Nat) : P Syntax := do
  -- the saved position only matters through its column (`colGt`/`colGe`), so key on that:
  -- nested layout blocks then share their memo entries
  let key : MemoKey := { cat := c, prec := rbp, pos := (← state).pos, saved := (← ctx).savedPos?.map (colOf (← ctx).input) }
  match ← memoLookup key with
  | some (some (stx, stop)) => setPos stop; pure stx
  | some none => failAt (← nextPos) c
  | none =>
    let reserved := (← ctx).tables.reservedIn c
    match ← try? (withCtx (fun x => { x with reserved }) (categoryLoop c rbp)) with
    | some stx => memoStore key (some (stx, (← state).pos)); pure stx
    | none => memoStore key none; failAt (← nextPos) c

end

/-- Parse one phrase of a category, then require the end of input. Mainly for tests. -/
def parseCategory (tables : ParserTables) (c : Name) (input : String) :
    Except String Syntax :=
  let chars := input.toList.toArray
  let p : P Syntax := do
    let stx ← categoryParser c 0
    let i ← nextPos
    if i < chars.size then failAt i "end of input" else pure stx
  match p.run chars tables with
  | .ok (stx, _) => .ok stx
  | .error e => .error (e.render input)

end Wiz
