import Wiz.Elab.Basic

/-!
# The structured view (`wiz-info/1`)

The projection a lint rule or a tactic may read instead of a kernel term. Every fact
here is a name, a number, a boolean, a span or a fixed spelling; a term the view does
not name is an **opaque handle** (a fresh `h<n>`, meaningful only inside one document).

Two records:

* `BinderFact` is the traversal's own record of one binder (the same walk `W101` uses):
  its name, whether its scope mentions it, its depth, what kind of binder it is, the
  binder info of a `Π`, and the **head constant and arity** of its type. The type term
  itself is not kept; `handle` identifies it opaquely.
* `InfoRow` is one node of the elaboration info tree (`Wiz/Elab/Basic.lean`'s `Info`),
  projected to a whitelist of variants. The variants that carry only messages or quick
  fix data (`warning`, `trace`, `fix`) are not exposed.

`Wiz/Lint.lean` renders these as the `binder-info` and `info` lines of the
`wiz-lint/2` view (`docs/lint-abi.md`); the same binder row is the answer to the
`Tac.getBinderFacts` request. The schema and what is deliberately not exposed are in
`wiz-notes/structured-view.md`.
-/

namespace Wiz
namespace Elab
namespace View

/-- A field of a tab-separated row never contains a tab or a newline. -/
def viewText (s : String) : String :=
  String.ofList (s.toList.map fun c => if c == '\t' || c == '\n' || c == '\r' then ' ' else c)

/-- A name a lint never reports: `_`, a name the elaborator generated (`x✝`), or a
user-written name that starts with `_`. -/
def hiddenName (n : Name) : Bool :=
  n == "_" || n.startsWith "_" || n.toList.contains '✝'

/-- The head constant of an application spine, and the number of arguments applied to
it. `none` when the head is not a constant (a variable, a sort, a description former,
a metavariable, …): the view then names no head and the term is only a handle. -/
def headArity? (t : Term R) : Option (Name × Nat) :=
  let (head, args) := t.spine
  match head with
  | .const n _ => some (n, args.length)
  | _ => none

/-- The binder-info spelling a row uses. -/
def binderInfoKey : BinderInfo → String
  | .default => "default"
  | .implicit => "implicit"
  | .instImplicit => "instImplicit"

/-- One binder of a declaration, as the view names it. `handle` is `some k` when the
binder has a type term (a `Π`, `let` or `Σ` binder); it identifies that occurrence
opaquely, so a rule can tell rows apart without reading the term. `lam`, `split` and
`ecase` binders have no type in the term, so they carry no handle. -/
structure BinderFact where
  name : Name
  used : Bool
  depth : Nat
  /-- `pi`, `lam`, `let`, `sigma`, `split` or `ecase` -/
  kind : String := "pi"
  bi : BinderInfo := .default
  head : Option Name := none
  arity : Nat := 0
  handle : Option Nat := none
  deriving Repr, Inhabited

/-- One binder row of the view (`binder-info` in `wiz-lint/2`). -/
structure BinderRow where
  decl : String := ""
  depth : Nat := 0
  name : String := ""
  used : Bool := false
  kind : String := "pi"
  bi : String := "default"
  head : String := ""
  arity : Nat := 0
  handle : String := ""
  deriving Repr, Inhabited

/-- An opaque handle's spelling. -/
def handleKey : Option Nat → String
  | some n => s!"h{n}"
  | none => ""

/-- Project a traversal fact to its row. -/
def BinderFact.row (decl : Name) (f : BinderFact) : BinderRow :=
  { decl := toString decl
    depth := f.depth
    name := toString f.name
    used := f.used
    kind := f.kind
    bi := binderInfoKey f.bi
    head := (f.head.map toString).getD ""
    arity := f.arity
    handle := handleKey f.handle }

/-- Render one `binder-info` line (the fields are already view-safe). -/
def BinderRow.render (b : BinderRow) : String :=
  "\t".intercalate ["binder-info", viewText b.decl, toString b.depth, viewText b.name,
    toString b.used, b.kind, b.bi, viewText b.head, toString b.arity, b.handle]

/-- One projected `Info` node (`info` in `wiz-lint/2`). `node` is the variant's stable
spelling; `flag` is a small node-specific word (`local`/`global`, `hole`/`term`,
`annotated`/`inferred`, `block`/`single`, `kind`/`cat`, `rule`/`fn`, …); `head`/`arity`
describe the node's principal type; `handle` identifies that type opaquely; `data` is
the node-specific text (a hole's name, an expansion's handler, an instance's head, …). -/
structure InfoRow where
  decl : String := ""
  node : String := ""
  start : Nat := 0
  stop : Nat := 0
  name : String := ""
  flag : String := ""
  head : String := ""
  arity : Nat := 0
  handle : String := ""
  data : String := ""
  deriving Repr, Inhabited

/-- Render one `info` line. -/
def InfoRow.render (i : InfoRow) : String :=
  "\t".intercalate ["info", viewText i.decl, i.node, toString i.start, toString i.stop,
    viewText i.name, i.flag, viewText i.head, toString i.arity, i.handle, viewText i.data]

/-- The head and arity of a term, as a row spells them. -/
def typeHead (t : Term R) : String × Nat :=
  match headArity? t with
  | some (n, a) => (toString n, a)
  | none => ("", 0)

/-- The common fields of one projected `Info` node. -/
def infoRow (decl node : String) (info : SourceInfo) : InfoRow :=
  { decl, node, start := info.start, stop := info.stop }

/-- Project one `Info` node. `handle` is the next opaque handle number; a node whose
principal type is exposed by head/arity consumes one, so the returned counter is `k + 1`.
Nodes that are only messages or quick-fix data (`warning`, `trace`, `fix`) are not
exposed. -/
def infoNode? (decl : String) (handle : Nat) (i : Info R) : Option (InfoRow × Nat) :=
  match i with
  | .ident info name isLocal _ ty =>
    let (head, arity) := typeHead ty
    let row := infoRow decl "ident" info
    some ({ row with name := toString name,
            flag := if isLocal then "local" else "global", head := head, arity := arity,
            handle := handleKey (some handle) }, handle + 1)
  | .term info goal isHole =>
    let (head, arity) := typeHead goal.target
    let row := infoRow decl "term" info
    some ({ row with name := (goal.userName.map toString).getD "",
            flag := if isHole then "hole" else "term", head := head, arity := arity,
            handle := handleKey (some handle),
            data := toString goal.hyps.size }, handle + 1)
  | .tactic info block before after =>
    let row := infoRow decl "tactic" info
    some ({ row with flag := if block then "block" else "single",
            data := s!"{before.size}->{after.size}" }, handle)
  | .matchCases info m =>
    let row := infoRow decl "match" info
    some ({ row with name := toString m.type,
            flag := if m.catchAll then "catchAll" else "covered",
            arity := m.columns, data := toString m.covered.length }, handle)
  | .decl info name _ ty annotated _ =>
    let (head, arity) := typeHead ty
    let row := infoRow decl "decl" info
    some ({ row with name := toString name,
            flag := if annotated then "annotated" else "inferred", head := head, arity := arity,
            handle := handleKey (some handle) }, handle + 1)
  | .unknownIdent info name locals =>
    let row := infoRow decl "unknownIdent" info
    some ({ row with name := toString name,
            flag := "unknown", arity := locals.length }, handle)
  | .syntaxRef info ref =>
    let row := infoRow decl "syntaxRef" info
    some ({ row with
            name := match ref with | .kind k => toString k | .cat c => toString c,
            flag := match ref with | .kind _ => "kind" | .cat _ => "cat" }, handle)
  | .expansion info kind handler _ =>
    let row := infoRow decl "expansion" info
    some ({ row with name := toString kind,
            flag := match handler with | .rule .. => "rule" | .fn .. => "fn",
            data := match handler with
              | .rule _ m => m
              | .fn what f => s!"{what} {f}" }, handle)
  | .importMod info m =>
    let row := infoRow decl "import" info
    some ({ row with name := toString m }, handle)
  | .inst info _ ty inst =>
    let (head, arity) := typeHead ty
    let instHead := match headArity? inst with
      | some (n, a) => s!"{n}/{a}"
      | none => "opaque"
    let row := infoRow decl "inst" info
    some ({ row with flag := "instance", head := head, arity := arity,
            handle := handleKey (some handle), data := instHead }, handle + 1)
  | .warning .. | .trace .. | .fix .. => none

/-! ## The binder walk

The walk is the one `W101`/`W102` use: it records every `Π`/`λ`/`let`/`Σ`/`split`/
`ecase` binder and every shadowing local, handles the binder constructors explicitly,
and visits every other constructor's children generically. -/

/-- The state of one traversal: the binder stack, which binder ids were used, the facts,
the names whose inner binder shadowed an outer local and was used, and the next opaque
handle number. -/
structure Scan where
  next : Nat := 0
  stack : Array (Name × Nat) := #[]
  used : Std.HashMap Nat Bool := {}
  facts : Array BinderFact := #[]
  shadows : Array Name := #[]
  handle : Nat := 0

/-- A binder's written quantity is erased (0)? A symbolic quantity is left alone. -/
def erasedQuantity [BEq R] [Zero R] (q : Term R) : Bool :=
  match q with
  | .qlit r => r == (Zero.zero : R)
  | _ => false

/-- Walk a term, recording every `pi`/`lam`/`letE`/`sigma`/`split`/`ecase` binder and
every shadowing local. The traversal handles the binder constructors explicitly and uses
the generic child traversal for every other constructor, so a new constructor's children
are still visited. `startHandle` continues the opaque handle numbering when a earlier
scan (a declaration's domain, say) has already used handles. -/
partial def scanTerm [BEq R] [Zero R] (initial : Array Name) (t : Term R)
    (recordPi : Bool := true) (startHandle : Nat := 0) : Scan :=
  let stack := initial.mapIdx (fun i n => (n, i))
  (go t).run { next := initial.size, stack, handle := startHandle } |>.2
where
  lookup (stack : Array (Name × Nat)) (ix : Nat) : Option (Name × Nat) :=
    if ix < stack.size then stack[stack.size - 1 - ix]? else none

  mark (s : Scan) (ix : Nat) : Scan :=
    match lookup s.stack ix with
    | some (_, id) => { s with used := s.used.insert id true }
    | none => s

  /-- Push a binder, scan its body, and record the fact (and a shadow) unless `record` is
  false. The `pi` binders of an annotation inside a value are generated by the
  elaborator from the `lam` binder it annotates; recording both would report one source
  binder twice. `ty?` is the binder's type where the term has one; `handle` is allocated
  from the pre-body counter so a body's binders never take the same handle. -/
  binder (name : Name) (record : Bool) (kind : String) (bi : BinderInfo)
      (ty? : Option (Term R)) (body : StateM Scan Unit) : StateM Scan Unit := do
    let s ← get
    let id := s.next
    let h := s.handle
    let (head, arity) := match ty? with
      | some t => match headArity? t with
        | some (n, a) => (some n, a)
        | none => (none, 0)
      | none => (none, 0)
    let shadowed := !hiddenName name && s.stack.any (fun (n, _) => n == name)
    modify fun s =>
      { s with next := id + 1, handle := if ty?.isSome then h + 1 else h,
        stack := s.stack.push (name, id) }
    body
    let s ← get
    let used := s.used.getD id false
    modify fun s =>
      { s with
        stack := s.stack.pop
        facts := if record then s.facts.push
          { name, used, depth := s.stack.size, kind, bi, head, arity,
            handle := if ty?.isSome then some h else none } else s.facts
        shadows := if record && shadowed && used && !hiddenName name then s.shadows.push name else s.shadows }

  go : Term R → StateM Scan Unit
    | .var ix => modify fun s => mark s ix
    | .pi x bi q dom cod _ => do
        go q; go dom; binder x (recordPi && !erasedQuantity q) "pi" bi (some dom) (go cod)
    | .lam x body => binder x true "lam" .default none (go body)
    | .letE x q ty val body => do
        go q; go ty; go val; binder x (!erasedQuantity q) "let" .default (some ty) (go body)
    | .sigma x q a b _ => do
        go q; go a; binder x (!erasedQuantity q) "sigma" .default (some a) (go b)
    | .split q s z m x y b => do
        go q; go s
        binder z true "split" .default none (go m)
        binder x true "split" .default none (binder y true "split" .default none (go b))
    | .ecase z motive scrut branches => do
        go scrut
        binder z true "ecase" .default none (go motive)
        for b in branches do go b
    | t => t.forChildren (fun _ => pure ()) (fun _ c => go c)

/-- Walk the declaration's leading `pi` telescope and the matching leading `lam` chain
together. A parameter is used when **either** the rest of its type or the body of its
value mentions it, so a dependent return type is not a false positive. The names in the
elaborated telescope and the value's `lam` are the same (the elaborator writes one from
the other); once they differ the type's `pi` is an arrow (an anonymous binder) and the
value is scanned on its own. The last component is the next opaque handle number. -/
partial def telescope [BEq R] [Zero R] (ty : Term R) (val : Option (Term R)) (i : Nat)
    (names : List Name) (startHandle : Nat := 0) :
    Array BinderFact × Array Name × Term R × Option (Term R) × List Name × Nat :=
  match ty, val with
  | .pi x bi q dom cod _, some (.lam y body) =>
    let domScan := scanTerm #[] dom (startHandle := startHandle)
    if x != y then
      (domScan.facts, domScan.shadows, ty, val, names, domScan.handle) else
    let used := cod.hasVar 0 || body.hasVar 0
    let h := domScan.handle
    let (head, arity) := match headArity? dom with
      | some (n, a) => (some n, a)
      | none => (none, 0)
    let erased := erasedQuantity q
    let (facts', shadows, ty', val', names', next) :=
      telescope cod (some body) (i + 1) (names ++ [x])
        (if erased then h else h + 1)
    let facts : Array BinderFact :=
      if erased then #[] else
      #[{ name := x, used, depth := i, kind := "pi", bi, head, arity, handle := some h }]
    (domScan.facts ++ facts ++ facts', domScan.shadows ++ shadows, ty', val', names', next)
  | _, _ => (#[], #[], ty, val, names, startHandle)

/-- The binders of a declaration, without counting a declaration parameter twice (once
from the `pi` in its type and once from the `lam` in its value). -/
def declFacts [BEq R] [Zero R] (d : Decl R) : Array BinderFact × Array Name :=
  let (teleFacts, teleShadows, tyRest, valRest, names, h) := telescope d.type d.value 0 [] 0
  let tyScan := scanTerm #[] tyRest (startHandle := h)
  let valScan := match valRest with
    | some v => scanTerm names.toArray v (recordPi := false)
        (startHandle := tyScan.handle)
    | none => ({ facts := (#[] : Array BinderFact), shadows := (#[] : Array Name),
                 handle := tyScan.handle } : Scan)
  (teleFacts ++ tyScan.facts ++ valScan.facts,
   teleShadows ++ tyScan.shadows ++ valScan.shadows)

end View
end Elab
end Wiz
