import Wiz.Core.Term
import Wiz.Core.StructLayout
import Wiz.Rig

/-!
# Pretty printing core terms

Prints **surface syntax**, so `#check` output can be pasted back into a file.

`names` is the list of binder names in scope, innermost first (so `names[ix]` names
`var ix`). Shadowed binder names get primes so the output is unambiguous. Quantities
equal to the binder's default are omitted (see `QuantitySyntax`), and a Π whose
variable isn't used is printed as an arrow.

Precedences match the parser (`Wiz.Parser.Builtin`): arrows are 25, application is
`leadPrec` (1022) with arguments at `argPrec` (1023), and atoms are `maxPrec`.

There is one printer. It makes **tagged text** (`TT`): every printed subterm is wrapped
in a tag naming it, so an infoview can highlight the subterm under the mouse and ask
about it (`Infoview.lean`). `Term.pretty` is its text.

## Notation (11r)

Given the globals, the printer prints applications as notation, the way Lean's
delaborator and `app_unexpander`s do (`Globals.pp`, `Syntax/PPTable.lean`). At an
application whose head is a constant `c` with unexpanders:

1. its explicit arguments (the binder infos of `c`'s type) are **delaborated** to
   `Syntax`, bottom-up: variables and constants become identifiers, numerals numerals,
   `fun`s `fun`s, applications with unexpanders their notation; anything else is a
   **leaf** (`pp.leaf`) that the ordinary printer prints. Every node made from a subterm
   keeps a reference to it (in its `SourceInfo`), so the subterm stays tagged;
2. the unexpanders of `c` run, latest first, on `c x₁ … xₙ`; arguments beyond what a
   rule takes are applied to its result;
3. the result is **formatted** by walking the grammar of each node's kind (`PPFormat`,
   from the parser tables: built-in syntax too), parenthesising by precedence. A node
   that can't be formatted (a kind without a grammar, a shape that doesn't fit it) is
   printed from its subterm without notation, so notation never makes output wrong.
-/

namespace Wiz

variable {R : Type} [QuantitySyntax R] [BEq R]

def freshenName (names : List Name) (x : Name) : Name :=
  if x == "_" then x else go (names.length + 1) x
where
  -- `names.length + 1` primes always suffice, so the fuel never runs out
  go : Nat → Name → Name
    | 0, y => y
    | n + 1, y => if names.contains y then go n (y ++ "'") else y

/-- `Prop`, `Type`, `Type 2`, `Type u`, `Sort u`, `Type (max u v)`, ... -/
def showSort (l : Level) : String :=
  match l.toNat? with
  | some 0 => "Prop"
  | some 1 => "Type"
  | some (n + 1) => s!"Type {n}"
  | _ => match l with
    | .succ l' => s!"Type {Level.format.formatArg l'}"
    | _ => s!"Sort {Level.format.formatArg l}"

def atomicSort (l : Level) : Bool := l.toNat? == some 0 || l.toNat? == some 1

/-- Tagged text: a printed term whose subterms are marked (`tag id t`: `t` is the
subterm `id` of the printer's array). -/
inductive TT where
  | text (s : String)
  | append (xs : Array TT)
  | tag (id : Nat) (t : TT)
  deriving Inhabited, Repr

partial def TT.flatten : TT → String
  | .text s => s
  | .append xs => String.join (xs.toList.map TT.flatten)
  | .tag _ t => t.flatten

/-- The first and the last character of tagged text, if any. -/
partial def TT.firstChar? : TT → Option Char
  | .text s => s.toList.head?
  | .append xs => xs.toList.findSome? TT.firstChar?
  | .tag _ t => t.firstChar?

partial def TT.lastChar? : TT → Option Char
  | .text s => s.toList.getLast?
  | .append xs => xs.toList.reverse.findSome? TT.lastChar?
  | .tag _ t => t.lastChar?

/-- A printed subterm: what it is, and the variables in scope (innermost first; the type
of each lives in the context of the ones after it). -/
structure Subterm (R : Type) where
  kind : String
  name : Option Name := none
  names : List Name
  types : List (Option (Term R))
  term : Term R

instance {R : Type} : Inhabited (Subterm R) := ⟨{ kind := "", names := [], types := [], term := .var 0 }⟩

namespace Tagged

abbrev M (R : Type) := StateM (Array (Subterm R))

def txt (s : String) : TT := .text s
def cat (xs : List TT) : TT := .append xs.toArray
def paren (b : Bool) (t : TT) : TT := if b then cat [txt "(", t, txt ")"] else t

def isDefaultQ (bi : BinderInfo) : Term R → Bool
  | .qlit r => r == if bi == .implicit then QuantitySyntax.implicitDefault else QuantitySyntax.explicitDefault
  | _ => false

def kindOf : Term R → String
  | .var _ => "var" | .const .. => "const" | .sort _ => "sort" | .app .. => "app"
  | .lam .. => "lam" | .pi .. => "pi" | .letE .. | .split .. => "let" | .sigma .. => "sigma"
  | .pair .. => "pair" | .fst _ | .snd _ => "proj" | .eq .. | .eqTy .. | .refl .. | .reflTy _ => "eq"
  | .natLit _ | .qlit _ => "lit" | .mu .. | .nu .. | .con _ => "data"
  | _ => "other"

/-- Record `t` (printed as `body`, in `names`) as a subterm, and tag `body` with it. -/
def record (names : List Name) (tys : List (Option (Term R))) (t : Term R) (body : TT) : M R TT := do
  let id := (← get).size
  let name := match t with
    | .var ix => some (names[ix]?.getD s!"#{ix}")
    | .const n _ => some n
    | _ => none
  modify (·.push { kind := kindOf t, name, names, types := tys, term := t })
  pure (.tag id body)

def tuple : Term R → Array (Term R) → Array (Term R)
  | .pair a b, acc => tuple b (acc.push a)
  | t, acc => acc.push t

def spine : Term R → Array (Term R) → Term R × Array (Term R)
  | .app f a, acc => spine f (#[a] ++ acc)
  | t, acc => (t, acc)

def sep (xs : List TT) (s : String) : TT :=
  cat (xs.zipIdx.flatMap fun (x, i) => if i == 0 then [x] else [txt s, x])

/-! ### Delaboration to syntax, and formatting (11r) -/

/-- A subterm a syntax node was made from, with its context. -/
structure Ref (R : Type) where
  term : Term R
  names : List Name
  tys : List (Option (Term R))

instance : Inhabited (Ref R) := ⟨{ term := .var 0, names := [], tys := [] }⟩

abbrev DM (R : Type) := StateT (Array (Ref R)) (M R)

def leafKind : Name := "pp.leaf"

/-- A node made from the subterm `i` of the delaborator's array is marked in its
`SourceInfo` (no parsed syntax has `stop = 0` with `start > 0`). Positions don't survive
the interpreter (a procedural unexpander), so leaves carry their index as an atom. -/
def refInfo (i : Nat) : SourceInfo := { start := i + 1, stop := 0, synthetic := true }

def refOf? (s : Syntax) : Option Nat :=
  let i := s.info
  if i.synthetic && i.stop == 0 && i.start > 0 then some (i.start - 1) else none

def setInfo (s : Syntax) (i : SourceInfo) : Syntax := match s with
  | .atom _ v => .atom i v
  | .ident _ n => .ident i n
  | .node _ k as => .node i k as
  | .missing => .missing

def identStx (n : Name) : Syntax := .node {} "term.ident" #[.ident {} n]

def appStx (f : Syntax) (args : Array Syntax) : Syntax :=
  if args.isEmpty then f else .node {} "term.app" #[f, .node {} "null" args]

/-- The base name of a (possibly macro-scoped) identifier. -/
def stripScope (n : Name) : Name := (n.splitOn "✝").headD n

/-- Match an unexpander's pattern (`$x` binds anything). -/
partial def ppMatch (pat stx : Syntax) (acc : List (Name × Syntax)) : Option (List (Name × Syntax)) :=
  match pat with
  | .node _ "antiquot" as => match as[1]? with
    | some (Syntax.ident _ x) => some ((x, stx) :: acc)
    | _ => none
  | .node _ k as => match stx with
    | .node _ k' bs =>
      if k == k' && as.size == bs.size then (as.zip bs).foldlM (fun acc (a, b) => ppMatch a b acc) acc
      else none
    | _ => none
  | .atom _ v => match stx with
    | .atom _ v' => if v == v' then some acc else none
    | _ => none
  | .ident _ n => match stx with
    | .ident _ n' => if n == n' then some acc else none
    | _ => none
  | .missing => some acc

partial def ppInst (binds : List (Name × Syntax)) : Syntax → Syntax
  | s@(.node _ "antiquot" as) => match as[1]? with
    | some (Syntax.ident _ x) => (binds.lookup x).getD s
    | _ => s
  | .node i k as => .node i k (as.map (ppInst binds))
  | s => s

/-- The explicit arguments of an application of `c`. -/
def explicitArgs (g : Globals R) (c : Name) (args : Array (Term R)) : Array (Term R) :=
  let bis := match g.find? c with
    | some d => infos d.type
    | none => []
  ((args.toList.zipIdx.filter fun (_, i) => (bis[i]?.getD .default) == .default).map (·.1)).toArray
where
  infos : Term R → List BinderInfo
    | .pi _ bi _ _ cod _ => bi :: infos cod
    | _ => []

/-- `(fun x => b : T) a …` (what `match` elaborates to: a scrutinee bound by an annotated
`fun`) as `b[a/x] …`, when that is an application of a constant with unexpanders: so
`if c then t else e`, a `Bool.casesOn` under such a `fun`, prints as `if`. -/
def betaForNotation? (g : Globals R) (u : Term R) : Option (Term R) :=
  let (f, args) := spine u #[]
  let body? := match f with
    | .ann (.lam _ b) _ | .lam _ b => some b
    | _ => none
  match body?, args[0]? with
  | some b, some a =>
    let r := (args.extract 1 args.size).foldl .app (b.instantiateAt 0 a)
    match spine r #[] with
    | (.const c _, _) => if g.pp.unexpanders.contains c then some r else none
    | _ => none
  | _, _ => none

/-- The text of syntax, positions left out (to recognise a subtree again). -/
def stxKey (s : Syntax) : String := s.toSExpr (atoms := true)

/-- A procedural unexpander's output has no positions (the interpreter's `Syntax` has
none), so the subterm references of its input are lost. Put back every subtree of the
input that comes back unchanged (`[x, ys,*]` keeps `x` and the elements of `ys`). -/
partial def restoreRefs (input : Array Syntax) (out : Syntax) : Syntax :=
  let rec collect (m : Std.HashMap String Syntax) (s : Syntax) : Std.HashMap String Syntax :=
    let m := if (refOf? s).isSome then m.insert (stxKey s) s else m
    match s with
    | .node _ _ as => as.foldl collect m
    | _ => m
  let m := input.foldl collect {}
  let rec put (s : Syntax) : Syntax :=
    match s with
    | .node i k as => match m[stxKey s]? with
      | some orig => orig
      | none => .node i k (as.map put)
    | s => s
  if m.isEmpty then out else put out

/-- A piece of formatted syntax: a token (with its declared spelling, if known), a
separator, formatted text, or "no space here". -/
inductive Piece where
  | tok (s : String) (raw : Option String)
  | sep (s : String)
  | sub (t : TT)
  | noWs
  deriving Inhabited

/-- Characters of identifiers and keywords (Greek letters and subscripts too). -/
def identish (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '\'' || (c.val ≥ 0x370 && c.val < 0x400) ||
  (c.val ≥ 0x2080 && c.val < 0x209d)

def Piece.text : Piece → String
  | .tok s raw => raw.getD s
  | .sep s => s
  | .sub t => t.flatten
  | .noWs => ""

def Piece.first? : Piece → Option Char
  | .sub t => t.firstChar?
  | p => p.text.toList.head?

def Piece.last? : Piece → Option Char
  | .sub t => t.lastChar?
  | p => p.text.toList.getLast?

/-- Is a space needed between two pieces? Declared spacing wins (`" + "`); keywords are
separated; nothing goes inside brackets or before `,`/`;`; a symbol declared without
spaces (`"!"`, `"["`) gets none; two symbols are kept apart (`- -x`, not a comment). -/
def needSpace (a b : Piece) : Bool := Id.run do
  let some x := a.last? | return false
  let some y := b.first? | return false
  if let .tok _ (some r) := a then if r.toList.getLast?.any (·.isWhitespace) then return false
  if let .tok _ (some r) := b then if r.toList.head?.any (·.isWhitespace) then return false
  if b matches .sep _ then return false
  if a matches .sep _ || x == ',' || x == ';' then return true
  if "([{⟨".toList.contains x || ")]}⟩,;".toList.contains y then return false
  if !identish x && !identish y then return true
  if a matches .tok _ (some _) && !identish x then return false
  if b matches .tok _ (some _) && !identish y then return false
  return true

def joinPieces (ps : Array Piece) : TT := Id.run do
  let ps := ps.toList
  let n := (ps.filter fun p => !(p matches .noWs)).length
  let mut out : Array TT := #[]
  let mut prev : Option Piece := none
  let mut glue := false
  let mut k := 0
  for p in ps do
    if p matches .noWs then
      glue := true
      continue
    -- declared spacing at the very ends of a node is the parent's business
    let p := match p with
      | .tok s (some r) =>
        let r := if k == 0 then String.ofList (r.toList.dropWhile (·.isWhitespace)) else r
        let r := if k + 1 == n then String.ofList (r.toList.reverse.dropWhile (·.isWhitespace)).reverse else r
        Piece.tok s (some r)
      | p => p
    if let some q := prev then
      if !glue && needSpace q p then out := out.push (txt " ")
    out := out.push (match p with
      | .sub t => t
      | p => txt p.text)
    prev := some p
    glue := false
    k := k + 1
  return .append out

/-- How many syntax items a descriptor produces (`none`: it depends). -/
partial def itemCount : ParserDescr → Option Nat
  | .seq ps => ps.foldlM (fun n p => (n + ·) <$> itemCount p) 0
  | .withPosition p | .withoutPosition p => itemCount p
  | .orelse p q => do let a ← itemCount p; let b ← itemCount q; if a == b then some a else none
  | .colGt | .colGe | .noWs | .checkPrec _ => some 0
  | _ => some 1

/-- The precedence of the term that ends a descriptor, if it ends in one (`fun x => b`
ends in `term 0`: open to the right). -/
partial def lastCatPrec : ParserDescr → Option Nat
  | .cat "term" p => some p
  | .seq ps => (ps.toList.reverse.find? (itemCount · != some 0)).bind lastCatPrec
  | .withPosition p | .withoutPosition p | .many p | .many1 p | .optional p => lastCatPrec p
  | .sepBy p _ _ | .sepBy1 p _ _ => lastCatPrec p
  | .orelse p q => match lastCatPrec p, lastCatPrec q with
    | some a, some b => some (min a b)
    | a, b => a <|> b
  | _ => none

def effPrec (f : PPFormat) : Nat := match lastCatPrec f.p with
  | some q => min f.prec q
  | none => f.prec

def rawOf (f : PPFormat) (tok : String) : Option String :=
  f.raw.find? fun r => String.ofList ((r.toList.dropWhile (·.isWhitespace)).reverse.dropWhile (·.isWhitespace)).reverse == tok

/-- (13p) `S.mk Δ a₁ … aₙ` read back as a structure update `{ s with fᵢ := aᵢ, … }`: some
fields are the projections of one term `s` at their own components (`StructLayout`) and
the others are not. `let x := e; S.mk …` (how `{ e with … }` elaborates when `e` is not a
variable) is `{ e with … }` when `x` is only the subject; a field updated with an update
of its own old value is a path (`{ s with a.b := v }`). -/
partial def structUpdateView? (g : Globals R) (t : Term R) : Option (Term R × List (List Name × Term R)) := do
  match t with
  | .letE _ _ _ val body =>
    let (s, fs) ← structUpdateView? g body
    guard (s == .var 0 && fs.all fun (_, v) => !v.hasVar 0)
    pure (val, fs.map fun (p, v) => (p, v.instantiateAt 0 val))
  | _ =>
    let (.const mk _, args) := Term.spine t | none
    guard (mk.endsWith ".mk")
    let L ← structLayoutWith? (fun _ => false) g (mk.dropEnd 3).toString
    let n := L.fields.length
    guard (n > 0 && args.length == L.nParams + n)
    let fieldArgs := args.drop L.nParams
    let rec unsnd : Nat → Term R → Option (Term R)
      | 0, u => some u
      | j + 1, .snd u => unsnd j u
      | _, _ => none
    -- the term whose projection field `i`'s argument is, if it is one
    let subjectOf (i : Nat) (a : Term R) : Option (Term R) := do
      let k ← L.fieldComp? i
      if k + 1 == L.comps.length then unsnd k a
      else match a with
        | .fst u => unsnd k u
        | _ => none
    let subjs := fieldArgs.zipIdx.map fun (a, i) => subjectOf i a
    let s ← subjs.findSome? id
    let kept := subjs.map (· == some s)
    guard (kept.any id && kept.any (!·))
    let updates := (L.fields.zip (fieldArgs.zip kept)).filterMap fun (f, a, k) => if k then none else some (f, a)
    pure (s, updates.flatMap fun (f, a) =>
      let own := (L.fields.idxOf? f).bind L.fieldComp? |>.map (L.compTerm · s)
      match structUpdateView? g a with
      | some (s', fs') => if own == some s' then fs'.map fun (p, v) => (f :: p, v) else [([f], a)]
      | none => [([f], a)])

mutual

/-- Print `t` at precedence `prec`. With `env`, applications print as notation (except at
the root when `noUnexp`: printing a node whose notation couldn't be formatted). -/
partial def go (env : Option (Globals R)) (names : List Name) (tys : List (Option (Term R))) (prec : Nat)
    (t : Term R) (noUnexp : Bool := false) : M R TT := do
  let body ← printNode env names tys prec t noUnexp
  record names tys t body

partial def printNode (env : Option (Globals R)) (names : List Name) (tys : List (Option (Term R))) (prec : Nat)
    (t : Term R) (noUnexp : Bool) : M R TT := do
  let sub (p : Nat) (u : Term R) : M R TT := go env names tys p u
  let app (f : TT) (args : List (Term R)) : M R TT := do
    let as ← args.mapM (sub 1023)
    pure (paren (prec > 1022) (cat (f :: as.flatMap fun a => [txt " ", a])))
  let qtyPrefix (bi : BinderInfo) (q : Term R) : M R TT := match q with
    | .qlit r =>
      let dflt := if bi == .implicit then QuantitySyntax.implicitDefault else QuantitySyntax.explicitDefault
      pure (txt (if r == dflt then "" else QuantitySyntax.display r ++ " "))
    | q => do pure (cat [txt "%", ← sub 1024 q, txt " "])
  -- notation (11r)
  if let some g := env then
    if !noUnexp && g.pp.active && (t matches .app .. || t matches .const ..) then
      let (r, _) ← (do
        match ← unexpand g names tys t with
        | some s => fmt g s "term" prec
        | none => pure none : DM R (Option TT)).run #[]
      if let some tt := r then return tt
    -- (13p) a structure update
    if !noUnexp && g.pp.useNotation then
      if let some (s, fs) := structUpdateView? g t then
        let fields ← fs.mapM fun (p, v) => do pure (cat [txt (".".intercalate p ++ " := "), ← sub 0 v])
        return cat [txt "{ ", ← sub 0 s, txt " with ", sep fields ", ", txt " }"]
  match t with
  | .var ix => pure (txt (names[ix]?.getD s!"#{ix}"))
  | .const n _ => pure (txt (Globals.privateBase n))
  | .mvar m => pure (txt s!"?m{m}")
  | .qty => pure (txt "Qty")
  | .size => pure (txt "Size")
  | .sizeLt s => pure (paren (prec > 1022) (cat [txt "Size< ", ← sub 1024 s]))
  | .szInf => pure (txt "∞")
  | .szSuc s => pure (cat [txt "↑", ← sub 1024 s])
  | .sfix _ _ _ _ P f s i x => app (txt "sfix") [P, f, s, i, x]
  | .cocon x => app (txt "cocon") [x]
  | .scase _ q _ _ _ P m s i x =>
    -- (K1) the quantity, unless it is the ordinary ω case
    app (txt "scase") ((if isDefaultQ .default q then [] else [q]) ++ [P, m, s, i, x])
  | .scofix _ _ _ A f s i a => app (txt "scofix") [A, f, s, i, a]
  | .qlit r => pure (txt (QuantitySyntax.display r))
  | .sort l => pure (paren (prec > 1022 && !atomicSort l) (txt (showSort l)))
  | .pi x bi q dom cod _ =>
    if bi == .default && isDefaultQ .default q && !cod.hasVar 0 then
      pure (paren (prec > 25) (cat [← sub 26 dom, txt " → ", ← go env ("_" :: names) (some dom :: tys) 25 cod]))
    else
      let x' := freshenName names (if x == "_" then "x" else x)
      let (o, c) := match bi with
        | .implicit => ("{", "}")
        | .instImplicit => ("[", "]")
        | .default => ("(", ")")
      pure (paren (prec > 25) (cat [txt o, ← qtyPrefix bi q, txt s!"{x'} : ", ← sub 0 dom, txt s!"{c} → ",
        ← go env (x' :: names) (some dom :: tys) 25 cod]))
  | .lam .. =>
    let (xs, names', tys', body) := lams names tys t #[]
    pure (paren (prec > 0) (cat [txt s!"fun {" ".intercalate xs.toList} => ", ← go env names' tys' 0 body]))
  | .app .. =>
    let (f, args) := spine t #[]
    let as ← args.toList.mapM (sub 1023)
    let hd ← sub 1024 f
    pure (paren (prec > 1022) (cat (hd :: as.flatMap fun a => [txt " ", a])))
  | .letE x q ty val body =>
    let x' := freshenName names x
    pure (paren (prec > 0) (cat [txt "let ", ← qtyPrefix .default q, txt s!"{x'} : ", ← sub 0 ty, txt " := ",
      ← sub 0 val, txt "; ", ← go env (x' :: names) (some ty :: tys) 0 body]))
  | .ann tm ty => pure (cat [txt "(", ← sub 0 tm, txt " : ", ← sub 0 ty, txt ")"])
  | .sigma x q a b _ =>
    if isDefaultQ .default q && !b.hasVar 0 then
      pure (paren (prec > 35) (cat [← sub 36 a, txt " × ", ← go env ("_" :: names) (some a :: tys) 35 b]))
    else
      let x' := freshenName names x
      pure (paren (prec > 35) (cat [txt "(", ← qtyPrefix .default q, txt s!"{x'} : ", ← sub 0 a, txt ") × ",
        ← go env (x' :: names) (some a :: tys) 35 b]))
  | .pair .. =>
    let parts ← (tuple t #[]).toList.mapM (sub 0)
    pure (cat [txt "(", sep parts ", ", txt ")"])
  | .fst u => pure (cat [← sub 1024 u, txt ".1"])
  | .snd u => pure (cat [← sub 1024 u, txt ".2"])
  | .split q s _ _ x y b =>
    let x' := freshenName names x
    let y' := freshenName (x' :: names) y
    pure (paren (prec > 0) (cat [txt "let ", ← qtyPrefix .default q, txt s!"({x'}, {y'}) := ", ← sub 0 s, txt "; ",
      ← go env (y' :: x' :: names) (none :: none :: tys) 0 b]))
  | .unit l => pure (txt (match l.toNat? with
    | some 0 => "True"
    | some 1 => "Unit"
    | _ => s!"Unit.\{{l}}"))
  | .tt => pure (txt "()")
  | .empty l => pure (txt (match l.toNat? with
    | some 0 => "False"
    | some 1 => "Empty"
    | _ => s!"Empty.\{{l}}"))
  | .absurd _ u => pure (paren (prec > 1022) (cat [txt "absurd ", ← sub 1023 u]))
  | .letUnit u b => pure (paren (prec > 0) (cat [txt "let () := ", ← sub 0 u, txt "; ", ← sub 0 b]))
  | .eq _ a b | .eqTy a b => pure (paren (prec > 50) (cat [← sub 51 a, txt " = ", ← sub 51 b]))
  | .refl _ a | .reflTy a => pure (paren (prec > 1022) (cat [txt "refl ", ← sub 1023 a]))
  | .cast _ _ e u => pure (paren (prec > 1022) (cat [txt "cast ", ← sub 1023 e, txt " ", ← sub 1023 u]))
  | .enum ls => pure (txt s!"Enum [{", ".intercalate ls}]")
  | .tag ls i => pure (txt s!"'{ls[i]?.getD s!"#{i}"}")
  | .ecase _ _ u bs =>
    let bs ← bs.mapM (sub 0)
    pure (paren (prec > 1022) (cat [txt "ecase ", ← sub 1023 u, txt " [", sep bs ", ", txt "]"]))
  | .desc _ I => pure (paren (prec > 1022) (cat [txt "Desc ", ← sub 1023 I]))
  | .dret i => app (txt "Desc.ret") [i]
  | .darg q S D => app (txt "Desc.arg") [q, S, D]
  | .drec q j D => app (txt "Desc.rec") [q, j, D]
  | .dhrec q H j D => app (txt "Desc.hrec") [q, H, j, D]
  | .delim _ P a b c h D => app (txt "Desc.elim") [P, a, b, c, h, D]
  | .mu _ _ _ _ s (some (n, _, as)) | .nu _ _ _ _ s (some (n, _, as)) =>
    let head ← if s matches .szInf then pure (txt n) else pure (cat [txt s!"{n}^", ← sub 1024 s])
    if as.isEmpty then pure head else app head as
  | .mu _ _ D i s none =>
    app (← if s matches .szInf then pure (txt "μ") else pure (cat [txt "μ^", ← sub 1024 s])) [D, i]
  | .con (.pair (.tag ls i) rest) | .con (.pair (.up (.tag ls i)) rest) =>
    -- `.c f₁ … fₙ`: the payload ends with the index equation and `()`
    let fields := (tuple rest #[]).toList
    let fields := fields.take (fields.length - 2)
    -- (a `mutual` block's tag `A.c` is written `.c`, `ctorShort`)
    let c := txt s!".{ctorShort (ls[i]?.getD s!"#{i}")}"
    if fields.isEmpty then pure c else app c fields
  | .con x => app (txt "con") [x]
  | .ind _ _ _ _ P m i x => app (txt "ind") [P, m, i, x]
  | .nu _ _ D i s none =>
    app (← if s matches .szInf then pure (txt "ν") else pure (cat [txt "ν^", ← sub 1024 s])) [D, i]
  | .out x => app (txt "out") [x]
  | .coit _ _ _ S st i s => app (txt "coit") [S, st, i, s]
  | .natLit n => pure (txt (toString n))
  -- Q4: the elaborator lifts small fields; `up`/`down` are invisible
  | .ulift _ _ A => app (txt "ULift") [A]
  | .up a | .down a => printNode env names tys prec a noUnexp
  -- (P2) the proof marker is invisible too
  | .prf _ a => printNode env names tys prec a noUnexp
  | .natOp op args => app (txt s!"<{op}>") args.toList
  | .transp _ _ P p _ e =>
    pure (paren (prec > 1022) (cat [txt "transp ", ← sub 1023 P, txt " ", ← sub 1023 p, txt " ", ← sub 1023 e]))

/-- The binders of nested `fun`s, named apart. -/
partial def lams (names : List Name) (tys : List (Option (Term R))) :
    Term R → Array Name → Array Name × List Name × List (Option (Term R)) × Term R
  | .lam x b, acc =>
    let x' := freshenName names (if x == "_" && b.hasVar 0 then "x" else x)
    lams (x' :: names) (none :: tys) b (acc.push x')
  | t, acc => (acc, names, tys, t)

/-- A subterm as syntax, for unexpanders to match (see the module docstring). -/
partial def delab (g : Globals R) (names : List Name) (tys : List (Option (Term R))) (u : Term R) :
    DM R Syntax := do
  let ref (s : Syntax) : DM R Syntax := do
    let i := (← get).size
    modify (·.push { term := u, names, tys })
    pure (setInfo s (refInfo i))
  let leaf : DM R Syntax := do
    let i := (← get).size
    modify (·.push { term := u, names, tys })
    pure (.node {} leafKind #[.atom {} (toString i)])
  match u with
  | .up a | .down a => delab g names tys a
  | .var ix => ref (identStx (names[ix]?.getD s!"#{ix}"))
  | .natLit n => ref (.node {} "term.num" #[.node {} "num" #[.atom {} (toString n)]])
  | .lam x b =>
    let x' := freshenName names (if x == "_" && b.hasVar 0 then "x" else x)
    let body ← delab g (x' :: names) (none :: tys) b
    let binder : Syntax := if x' == "_" then .node {} "term.hole" #[.atom {} "_"] else .ident {} x'
    ref (.node {} "term.fun" #[.atom {} "fun", .node {} "null" #[binder], .atom {} "=>", body])
  | .const .. | .app .. =>
    match ← unexpand g names tys u with
    | some s => ref s
    | none => match u with
      | .const n _ => ref (identStx (Globals.privateBase n))
      | _ => leaf
  | _ => leaf

/-- The notation for an application of a constant with unexpanders, if one applies. -/
partial def unexpand (g : Globals R) (names : List Name) (tys : List (Option (Term R))) (u : Term R) :
    DM R (Option Syntax) := do
  let u := (betaForNotation? g u).getD u
  let (f, args) := spine u #[]
  let .const c _ := f | return none
  -- a numeral at a type other than `Nat` (7e): `OfNat.ofNat A n inst` with a literal `n`
  -- prints as the numeral `n` (its type and instance are implicit; H14 S2)
  if c == "OfNat.ofNat" && args.size == 3 then
    if let .natLit n := args[1]! then
      return some (.node {} "term.num" #[.node {} "num" #[.atom {} (toString n)]])
  let some entries := g.pp.unexpanders[c]? | return none
  if entries.isEmpty then return none
  let argStx ← (explicitArgs g c args).mapM (delab g names tys)
  let head := identStx (Globals.privateBase c)
  for e in entries do
    match e.how with
    | .rule pat tmpl =>
      if e.arity ≤ argStx.size then
        if let some bs := ppMatch pat (appStx head (argStx.extract 0 e.arity)) [] then
          return some (appStx (ppInst bs tmpl) (argStx.extract e.arity argStx.size))
    | .fn fn =>
      for k in (List.range (argStx.size + 1)).reverse do
        if let some out := g.pp.run fn (appStx head (argStx.extract 0 k)) then
          return some (appStx (restoreRefs (argStx.extract 0 k) out) (argStx.extract k argStx.size))
  return none

/-- Format syntax of category `c` at precedence `prec`; a node made from a subterm is
tagged with it, and printed from it (without notation) if it can't be formatted. -/
partial def fmt (g : Globals R) (s : Syntax) (c : Name) (prec : Nat) : DM R (Option TT) := do
  let refs ← get
  let r? := (refOf? s).bind (refs[·]?)
  let body ← fmtNode g s c prec
  match r? with
  | none => pure body
  | some r => match body with
    | some tt => pure (some (← (record r.names r.tys r.term tt : M R TT)))
    | none =>
      if c != "term" then pure none
      else pure (some (← (go (some g) r.names r.tys prec r.term (noUnexp := true) : M R TT)))

partial def fmtNode (g : Globals R) (s : Syntax) (c : Name) (prec : Nat) : DM R (Option TT) := do
  match s with
  | .node _ "pp.leaf" #[.atom _ i] =>
    let some r := (← get)[i.toNat?.getD 0]? | return none
    pure (some (← (go (some g) r.names r.tys prec r.term : M R TT)))
  | .ident _ n => pure (some (txt (stripScope n)))
  | .node _ k args =>
    let some f := g.pp.formats[k]? | return none
    let parenIf (t : TT) : TT := paren (c == "term" && prec > effPrec f) t
    if f.leading then
      let some (ps, j) ← walk g f args 0 f.p | return none
      if j != args.size then return none
      pure (some (parenIf (joinPieces ps)))
    else
      let some lhs := args[0]? | return none
      let some l ← fmt g lhs f.cat f.lhsPrec | return none
      let some (ps, j) ← walk g f args 1 f.p | return none
      if j != args.size then return none
      pure (some (parenIf (joinPieces (#[Piece.sub l] ++ ps))))
  | _ => pure none

/-- Walk a descriptor over the children `args` from `i`: the pieces, and the next child. -/
partial def walk (g : Globals R) (f : PPFormat) (args : Array Syntax) (i : Nat) (d : ParserDescr) :
    DM R (Option (Array Piece × Nat)) := do
  match d with
  | .atom tok | .nonReserved tok => match args[i]? with
    | some (.atom _ v) => if v == tok then pure (some (#[.tok tok (rawOf f tok)], i + 1)) else pure none
    | _ => pure none
  | .ident => match args[i]? with
    | some (.ident _ n) => pure (some (#[.sub (txt (stripScope n))], i + 1))
    | _ => pure none
  | .num => match args[i]? with
    | some (.node _ "num" #[.atom _ v]) => pure (some (#[.sub (txt v)], i + 1))
    | _ => pure none
  | .str => match args[i]? with
    | some (.node _ "str" #[.atom _ v]) => pure (some (#[.sub (txt v.quote)], i + 1))
    | _ => pure none
  | .cat c p => match args[i]? with
    | some a => match ← fmt g a c p with
      | some t => pure (some (#[.sub t], i + 1))
      | none => pure none
    | none => pure none
  | .seq ps =>
    let mut acc := #[]
    let mut j := i
    for p in ps do
      let some (xs, j') ← walk g f args j p | return none
      acc := acc ++ xs
      j := j'
    pure (some (acc, j))
  | .withPosition p | .withoutPosition p => walk g f args i p
  | .colGt | .colGe | .checkPrec _ => pure (some (#[], i))
  | .noWs => pure (some (#[.noWs], i))
  | .orelse p q => match ← walk g f args i p with
    | some r => pure (some r)
    | none => walk g f args i q
  | .node k p => match args[i]? with
    | some (.node _ k' as) =>
      if k != k' then return none
      let some (xs, j) ← walk g f as 0 p | return none
      if j != as.size then return none
      pure (some (xs, i + 1))
    | _ => pure none
  | .many p | .many1 p => match args[i]? with
    | some (.node _ "null" es) =>
      if d matches .many1 _ && es.isEmpty then return none
      let mut acc := #[]
      for e in es do
        let some xs ← iter g f p e | return none
        acc := acc ++ xs
      pure (some (acc, i + 1))
    | _ => pure none
  | .optional p => match args[i]? with
    | some (.node _ "null" es) =>
      if es.isEmpty then return some (#[], i + 1)
      let some (xs, j) ← walk g f es 0 p | return none
      if j != es.size then return none
      pure (some (xs, i + 1))
    | _ => pure none
  | .sepBy p sep _ | .sepBy1 p sep _ => match args[i]? with
    | some (.node _ "null" es) =>
      if d matches .sepBy1 .. && es.isEmpty then return none
      let mut acc := #[]
      for (e, k) in es.toList.zipIdx do
        if k % 2 == 1 then
          unless e matches .atom .. do return none
          acc := acc.push (.sep sep)
        else
          let some xs ← iter g f p e | return none
          acc := acc ++ xs
      pure (some (acc, i + 1))
    | _ => pure none

/-- One iteration of `many`/`sepBy`: a single item stays as it is, several are a `null`
node (`packItems`). -/
partial def iter (g : Globals R) (f : PPFormat) (p : ParserDescr) (e : Syntax) : DM R (Option (Array Piece)) := do
  let whole (xs : Array Syntax) : DM R (Option (Array Piece)) := do
    match ← walk g f xs 0 p with
    | some (ps, j) => pure (if j == xs.size then some ps else none)
    | none => pure none
  match itemCount p with
  | some 1 => whole #[e]
  | some _ => match e with
    | .node _ "null" xs => whole xs
    | _ => pure none
  | none => match ← whole #[e] with
    | some ps => pure (some ps)
    | none => match e with
      | .node _ "null" xs => whole xs
      | _ => pure none

end

end Tagged

/-- Print `t` (with `names` and their types in scope, innermost first) as tagged text,
appending its subterms to the state. Flattened, it is `t.pretty names g`. With the
globals `g`, applications print as notation (`Globals.pp`). -/
def Term.prettyTagged (names : List Name) (tys : List (Option (Term R))) (t : Term R)
    (g : Option (Globals R) := none) : StateM (Array (Subterm R)) TT :=
  Tagged.go g names tys 0 t

/-- `t` at precedence `prec`, without notation: the output parses back (`Reflect.lean`). -/
def Term.prettyPrec (names : List Name) (prec : Nat) (t : Term R) : String :=
  ((Tagged.go none names [] prec t).run' #[]).flatten

/-- `t` as text; with the globals `g`, applications print as notation. -/
def Term.pretty (names : List Name := []) (t : Term R) (g : Option (Globals R) := none) : String :=
  ((Tagged.go g names [] 0 t).run' #[]).flatten

/-- `t` as text, with the notation of `g` (`Term.pretty`). -/
def Term.ppIn (g : Globals R) (names : List Name) (t : Term R) : String := t.pretty names (some g)

instance : ToString (Term R) := ⟨fun t => t.pretty []⟩

/-- (24e) A goal's target as text after the goal's `⊢`: in parentheses when it shows a
`⊢` of its own (a notation, such as separation logic's entailment), so that
`⊢ (l ↦ 1 ⊢ l ↦ 2)` doesn't read as two turnstiles of one goal. -/
def goalTarget (s : String) : String :=
  if (s.splitOn "⊢").length > 1 then s!"({s})" else s

/-- A printed term for a message, at most about `max` characters: a longer one keeps
its beginning and its end, and says how much was left out. (A normal form can be huge:
an equation between two long lists computes to a Σ of a hundred `True`s.) -/
def elideLong (s : String) (max : Nat := 1500) : String :=
  let n := s.length
  if n ≤ max then s else
  let head := String.ofList (s.toList.take (max * 2 / 3))
  let tail := String.ofList (s.toList.drop (n - max / 3))
  s!"{head} … ({n - head.length - tail.length} characters left out) … {tail}"

end Wiz
