import Wiz.Elab.Command
import Wiz.Module
import Wiz.Lint.Basic

/-!
# Lint: warnings about a program the elaborator accepted

The lint pass is **post-elaboration**: it reads the declarations a command added and
records findings as ordinary `Msg`s (`severity` and `code := the rule id`). It never
changes a declaration, a message the elaborator produced, or whether a program is
accepted.

The pass is off by default (`CommandState.lintEnabled`). `wiz lint` turns it on; `wiz
check`, `wiz build` and the language server leave it off, so the normal build pays
nothing and no existing message changes.

A rule is the same record a core rule and a package rule use: a stable `W` code, a
category, a default severity, a scope, the capabilities it needs, and whether a per-site
marker may suppress it. Core registers the five rules of `wiz-notes/linting.md` §3.5;
a package registers its `W500`–`W999` rules with `lint-set`/`lint` (`docs/lint-abi.md`).
The package ABI is a pure `String → String` runner over the stable `CommandView`; the
registry checks the code block, the declared capabilities, and the runner's trust/partial
closure before a set runs.

## Suppression

The only mechanism in P0 is the per-site marker:

    out := out ++ [d]        -- lint: allow W201 (the list has at most 4 entries here)

It applies on the finding's line or the line above it. A marker must give a reason and
must name a registered code; a typo is an error, not a silent suppression. A rule that
is not suppressible (a safety rule, P1) cannot be named by a marker.
-/

namespace Wiz
namespace Lint

/-- One finding: its primary span, severity, rule code, message and stable anchor. -/
structure Finding where
  info : SourceInfo
  severity : Severity
  code : String
  text : String
  anchor : String := ""
  deriving Repr, Inhabited

/-- The input a rule may read. `chars` is the file text (for suppression); `decls` are
the declarations this command added (empty for a module-scope rule's later run). -/
structure RuleInput (R : Type) where
  module : String
  path : String
  cmd : Syntax
  chars : Array Char
  added : Array Name
  decls : Array (Name × Decl R)
  globals : Globals R
  docs : Std.HashMap Name DeclDoc
  sites : Std.HashMap Name (SourceInfo × String)
  imports : Array (Name × SourceInfo)
  publicRoots : List String
  effectful : Std.HashSet Name
  loader : Name → Option String
  /-- the messages the command produced (the `messages` capability) -/
  messages : Array Msg := #[]

/-- A lint rule. The id is stable forever; a retired rule is `off` with a tombstone row
in `docs/error-codes.md`, never reused. -/
structure Rule (R : Type) where
  id : String
  name : String
  category : Category
  defaultSeverity : Severity
  scope : Scope
  requires : List Capability
  suppressible : Bool := true
  run : RuleInput R → Array Finding

/-! ## Common helpers -/

/-- A name a lint never reports: `_`, a name the elaborator generated (`x✝`), or a
user-written name that starts with `_`. -/
def hiddenName (n : Name) : Bool :=
  n == "_" || n.startsWith "_" || n.toList.contains '✝'

/-- Is the declaration's path under one of the configured public roots? An empty root
means every path. -/
def underPublicRoot (path : String) (roots : List String) : Bool :=
  roots.any fun root =>
    root == "" || path == root || path.startsWith root ||
    (path.splitOn ("/" ++ root ++ "/")).length > 1

/-- The head constant of an application spine, if it is a constant. -/
def headConst? (t : Term R) : Option Name :=
  match t.spine with
  | (.const n _, _) => some n
  | _ => none

/-- The line (0-based) of an offset in the source text. -/
def lineOf (chars : Array Char) (pos : Nat) : Nat :=
  (chars.extract 0 (min pos chars.size)).foldl (fun n c => if c == '\n' then n + 1 else n) 0

/-! ## The binder visitor (`W101`, `W102`) -/

/-- A binder with the result of its scope: `used` counts a `var` occurrence anywhere in
the scope (a type or proof use counts, so the rule cannot contradict QTT). -/
structure BinderFact where
  name : Name
  used : Bool
  depth : Nat
  deriving Repr, Inhabited

/-- The state of one traversal: the binder stack, which binder ids were used, the facts,
and the names whose inner binder shadowed an outer local and was used. -/
structure Scan where
  next : Nat := 0
  stack : Array (Name × Nat) := #[]
  used : Std.HashMap Nat Bool := {}
  facts : Array BinderFact := #[]
  shadows : Array Name := #[]

/-- A binder's written quantity is erased (0)? A symbolic quantity is left alone. -/
def erasedQuantity [BEq R] [Zero R] (q : Term R) : Bool :=
  match q with
  | .qlit r => r == (Zero.zero : R)
  | _ => false

/-- Walk a term, recording every `pi`/`lam`/`letE`/`sigma`/`split` binder and every
shadowing local. The traversal handles the binder constructors explicitly and uses the
generic child traversal for every other constructor, so a new constructor's children are
still visited. -/
partial def scanTerm [BEq R] [Zero R] (initial : Array Name) (t : Term R) (recordPi : Bool := true) : Scan :=
  let stack := initial.mapIdx (fun i n => (n, i))
  (go t).run { next := initial.size, stack } |>.2
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
  binder twice. -/
  binder (name : Name) (record : Bool) (body : StateM Scan Unit) : StateM Scan Unit := do
    let s ← get
    let id := s.next
    let shadowed := !hiddenName name && s.stack.any (fun (n, _) => n == name)
    modify fun s => { s with next := id + 1, stack := s.stack.push (name, id) }
    body
    let s ← get
    let used := s.used.getD id false
    modify fun s =>
      { s with
        stack := s.stack.pop
        facts := if record then s.facts.push { name, used, depth := s.stack.size } else s.facts
        shadows := if record && shadowed && used && !hiddenName name then s.shadows.push name else s.shadows }

  go : Term R → StateM Scan Unit
    | .var ix => modify fun s => mark s ix
    | .pi x _ q dom cod _ => do
        go q; go dom; binder x (recordPi && !erasedQuantity q) (go cod)
    | .lam x body => binder x true (go body)
    | .letE x q ty val body => do
        go q; go ty; go val; binder x (!erasedQuantity q) (go body)
    | .sigma x q a b _ => do
        go q; go a; binder x (!erasedQuantity q) (go b)
    | .split q s z m x y b => do
        go q; go s
        binder z true (go m)
        binder x true (binder y true (go b))
    | .ecase z motive scrut branches => do
        go scrut
        binder z true (go motive)
        for b in branches do go b
    | t => t.forChildren (fun _ => pure ()) (fun _ c => go c)

/-- Walk the declaration's leading `pi` telescope and the matching leading `lam` chain
together. A parameter is used when **either** the rest of its type or the body of its
value mentions it, so a dependent return type is not a false positive. The names in the
elaborated telescope and the value's `lam` are the same (the elaborator writes one from
the other); once they differ the type's `pi` is an arrow (an anonymous binder) and the
value is scanned on its own. -/
partial def telescope [BEq R] [Zero R] (ty : Term R) (val : Option (Term R)) (i : Nat)
    (names : List Name) :
    Array BinderFact × Array Name × Term R × Option (Term R) × List Name :=
  match ty, val with
  | .pi x _ q dom cod _, some (.lam y body) =>
    let domScan := scanTerm #[] dom
    if x != y then (domScan.facts, domScan.shadows, ty, val, names) else
    let used := cod.hasVar 0 || body.hasVar 0
    let facts : Array BinderFact :=
      if erasedQuantity q then #[] else #[{ name := x, used, depth := i }]
    let (facts', shadows, ty', val', names') := telescope cod (some body) (i + 1) (names ++ [x])
    (domScan.facts ++ facts ++ facts', domScan.shadows ++ shadows, ty', val', names')
  | _, _ => (#[], #[], ty, val, names)

/-- The binders of a declaration, without counting a declaration parameter twice (once
from the `pi` in its type and once from the `lam` in its value). -/
def declFacts [BEq R] [Zero R] (d : Decl R) : Array BinderFact × Array Name :=
  let (teleFacts, teleShadows, tyRest, valRest, names) := telescope d.type d.value 0 []
  let tyScan := scanTerm #[] tyRest
  let valScan := match valRest with
    | some v => scanTerm names.toArray v (recordPi := false)
    | none => ({ facts := (#[] : Array BinderFact), shadows := (#[] : Array Name) } : Scan)
  (teleFacts ++ tyScan.facts ++ valScan.facts,
   teleShadows ++ tyScan.shadows ++ valScan.shadows)

/-- `W101`: a `pi`/`lam`/`letE` binder with no occurrence in its scope. -/
def w101 [BEq R] [Zero R] : Rule R :=
  { id := "W101", name := "unused-binding", category := .correctness,
    defaultSeverity := .warning, scope := .declaration,
    requires := [.decl, .spans],
    run := fun input => Id.run do
      let mut out : Array Finding := #[]
      for (n, d) in input.decls do
        let (facts, _) := declFacts d
        for f in facts do
          if !f.used && !hiddenName f.name then
            let info := (input.sites.get? n).map (·.1) |>.getD default
            out := out.push
              { info, severity := .warning, code := "W101",
                text := s!"unused binding '{f.name}'",
                anchor := s!"{n}#{f.depth}" }
      out }

/-- `W102`: an inner local binder with the same name as an outer local, where the inner
binder is used. A hint: idiomatic shadowing is common. -/
def w102 [BEq R] [Zero R] : Rule R :=
  { id := "W102", name := "shadowed-local", category := .correctness,
    defaultSeverity := .hint, scope := .declaration,
    requires := [.decl, .spans],
    run := fun input => Id.run do
      let mut out : Array Finding := #[]
      for (n, d) in input.decls do
        let (_, shadows) := declFacts d
        for x in shadows do
          let info := (input.sites.get? n).map (·.1) |>.getD default
          out := out.push
            { info, severity := .hint, code := "W102",
              text := s!"local binding '{x}' shadows an outer local",
              anchor := s!"{n}#{x}" }
      out }

/-! ## `W103`: a discarded `Result`/`Option` -/

/-- The type heads whose failure/value is silently discarded by `let _ := …`. -/
def discardedType? (ty : Term R) : Option String :=
  match headConst? ty with
  | some "Result" => some "Result"
  | some "ResultQ" => some "ResultQ"
  | some "Option" => some "Option"
  | _ => none

/-- Find `let _ := e` where `e`'s elaborated type is a `Result`/`Option`. A `do e` is
`Monad.bind e (fun _ => …)`, so it is not a `let` and is not reported: the failure
propagates. -/
partial def discardedTerms (t : Term R) : Array (String × Name) :=
  let here := match t with
    | .letE x _ ty _ _ => match discardedType? ty with
      -- `_` and `_x` are the wildcard lets; the parser does not accept a bare `_` here,
      -- so the convention in a Wiz source is a leading underscore.
      | some tyName => if x.startsWith "_" then #[(tyName, x)] else #[]
      | none => #[]
    | _ => #[]
  let rest := match t with
    | .pi _ _ q a b _ => discardedTerms q ++ discardedTerms a ++ discardedTerms b
    | .lam _ b => discardedTerms b
    | .letE _ q ty val body => discardedTerms q ++ discardedTerms ty ++ discardedTerms val ++ discardedTerms body
    | .sigma _ q a b _ => discardedTerms q ++ discardedTerms a ++ discardedTerms b
    | .split q s _ m _ _ b => discardedTerms q ++ discardedTerms s ++ discardedTerms m ++ discardedTerms b
    | .ecase _ m s bs => discardedTerms m ++ discardedTerms s ++ (bs.foldl (· ++ discardedTerms ·) #[])   -- complexity: ok (one array per case alternative)
    | t => (t.forChildren (m := StateM (Array (String × Name))) (fun _ => pure ())
        (fun _ c => modify (· ++ discardedTerms c)) |>.run #[]).2
  here ++ rest

/-- `W103`: a discarded `Result`/`Option` value. -/
def w103 : Rule R :=
  { id := "W103", name := "discarded-result", category := .correctness,
    defaultSeverity := .warning, scope := .declaration,
    requires := [.decl, .spans],
    run := fun input => Id.run do
      let mut out : Array Finding := #[]
      for (n, d) in input.decls do
        let terms := discardedTerms d.type ++ (d.value.map discardedTerms |>.getD #[])
        for (tyName, _) in terms do
          let info := (input.sites.get? n).map (·.1) |>.getD default
          out := out.push
            { info, severity := .warning, code := "W103",
              text := s!"a {tyName} is discarded: its failure is not handled",
              anchor := s!"{n}#discarded" }
      out }

/-! ## `W301`: a public declaration without a doc comment -/

def documentedKind : String → Bool
  | "def" | "partial def" | "abbrev" | "structure" | "class" | "inductive"
  | "coinductive" | "axiom" | "opaque" | "theorem" => true
  | _ => false

/-- `W301`: a top-level public declaration in a public root has no doc comment.
Constructors, fields, instances and auxiliary names are exempt (their `kind` is not in
`documentedKind`). -/
def w301 : Rule R :=
  { id := "W301", name := "missing-doc", category := .api,
    defaultSeverity := .warning, scope := .declaration,
    requires := [.decl, .spans],
    run := fun input => Id.run do
      let mut out : Array Finding := #[]
      unless underPublicRoot input.path input.publicRoots do return #[]
      for n in input.added do
        let some d := input.docs.get? n | continue
        if !documentedKind d.kind || hiddenName n || input.globals.privates.contains n then continue
        if d.kind.startsWith "private" then continue
        let hasDoc := match d.doc with
          | some s => !s.trimAscii.isEmpty
          | none => false
        unless hasDoc do
          let info := (input.sites.get? n).map (·.1) |>.getD default
          out := out.push
            { info, severity := .warning, code := "W301",
              text := s!"public declaration '{n}' has no doc comment",
              anchor := s!"{n}#decl" }
      out }

/-! ## `W302`: an unused import -/

/-- The modules reachable from `m` (including `m`), read from the same loader the
frontend used. -/
partial def importClosure (loader : Name → Option String) (m : Name) : List Name :=
  let rec go (seen : List Name) (m : Name) : List Name :=
    if seen.contains m then [] else
    match loader m with
    | none => [m]
    | some src => m :: (Module.importsOf src).flatMap (go (m :: seen))
  go [] m

/-- The constants a declaration's type and value mention. -/
partial def constsOf (t : Term R) : List Name :=
  let here := match t with
    | .const n _ => [n]
    | _ => []
  here ++ (t.forChildren (m := StateM (List Name)) (fun _ => pure ())
    (fun _ c => modify (· ++ constsOf c)) |>.run []).2

/-- `W302`: a direct import no declaration in the target uses, and that contributes no
effect. Conservative: a module that registers an instance, syntax, notation, a builtin,
an attribute, an export or FFI/link code is never reported, nor is a module that is the
only path to a used declaration. -/
def w302 : Rule R :=
  { id := "W302", name := "unused-import", category := .api,
    defaultSeverity := .warning, scope := .module,
    requires := [.imports, .globals],
    run := fun input => Id.run do
      if input.imports.isEmpty then return #[]
      let mut used : Std.HashSet Name := {}
      for n in input.globals.order do
        match input.sites.get? n with
        | some (_, m) => if m == input.module then
          match input.globals.find? n with
          | some d =>
            for c in constsOf d.type ++ (d.value.map constsOf |>.getD []) do
              match input.globals.declModule[c]? with
              | some cm => used := used.insert cm
              | none => pure ()
          | none => pure ()
        | none => pure ()
      let usedModules := used.fold (init := []) fun acc m => m :: acc
      let mut out : Array Finding := #[]
      for (m, info) in input.imports do
        if input.effectful.contains m then continue
        let closure := importClosure input.loader m
        -- A used declaration also reachable through another direct import does not make
        -- this one necessary (the target imports `Prelude` directly as well, say).
        let others := (input.imports.filter (·.1 != m)).toList.flatMap fun (o, _) =>
          importClosure input.loader o
        let needed := closure.any fun n => usedModules.contains n && !others.contains n
        if needed then continue
        out := out.push
          { info, severity := .warning, code := "W302",
            text := s!"unused import '{m}'", anchor := s!"import:{m}" }
      out }

/-- The core registry. The order is the order findings are emitted. -/
def registry (R : Type) [BEq R] [Zero R] : Array (Rule R) := #[w101, w102, w103, w301, w302]

def selected (rules : Array (Rule R)) (ids : List String) : Array (Rule R) :=
  if ids.isEmpty then rules else rules.filter fun r => ids.contains r.id

/-! ## The package ABI: a stable view, a pure runner, a checked set

A package lint set is a Wiz module with a `lint-set` header and one `lint` command per
rule. The rule's runner is a **pure, total function** `String → String`: the host builds
the stable `Lint.Command` view (only the fields the rule declared), calls the runner in
the interpreter, and reads findings back. The runner cannot do IO (the input is a
string, and a trust source in its closure is a registration error), and it cannot read a
capability the set did not declare because the view does not contain it.

`docs/lint-abi.md` is the wire format. The registry checks, before a set runs:

* the code is in the package block `W500`–`W999` and is unique in the enabled closure;
* every rule's `requires` is declared by the set, and is a stable capability;
* the runner's closure has no trust source (`Globals.axiomsOf`: an axiom, a foreign
  function, `implemented_by`, an untrusted `builtin`, a native representation) and no
  `partial` definition.
-/

/-- A span in the stable view: `{ start, stop }` offsets in the target file. -/
structure SpanView where
  start : Nat := 0
  stop : Nat := 0
  deriving Repr, Inhabited, BEq

/-- One declaration of the command (the `decl` capability). -/
structure DeclView where
  name : String := ""
  kind : String := ""
  isPublic : Bool := false
  hasDoc : Bool := false
  deriving Repr, Inhabited, BEq

/-- One binder of the command's declarations (the `facts` capability): whether it is
used in its scope, and its depth in the binder stack. -/
structure BinderView where
  name : String := ""
  used : Bool := false
  depth : Nat := 0
  deriving Repr, Inhabited, BEq

/-- One direct import (the `imports` capability). -/
structure ImportView where
  name : String := ""
  start : Nat := 0
  stop : Nat := 0
  deriving Repr, Inhabited, BEq

/-- One message the command produced (the `messages` capability). -/
structure MessageView where
  severity : String := ""
  code : String := ""
  start : Nat := 0
  stop : Nat := 0
  text : String := ""
  deriving Repr, Inhabited, BEq

/-- The stable `Lint.Command` view: what a package rule sees, and nothing else. The
view's `capabilities` header names exactly the sections present, so a rule can tell an
absent capability from an empty one. -/
structure CommandView where
  capabilities : List Capability := []
  module : String := ""
  path : String := ""
  kind : String := ""
  name : String := ""
  span : Option SpanView := none
  decls : Array DeclView := #[]
  binders : Array BinderView := #[]
  imports : Array ImportView := #[]
  globals : Array String := #[]
  messages : Array MessageView := #[]
  deriving Repr, Inhabited

/-- A view field never contains a tab or a newline (the format's separators). -/
def viewText (s : String) : String :=
  String.ofList (s.toList.map fun c => if c == '\t' || c == '\n' || c == '\r' then ' ' else c)

/-- Render the view as the stable line format (`docs/lint-abi.md`). One header line, then
one line per fact, fields separated by a tab. -/
def CommandView.render (v : CommandView) : String :=
  let line (xs : List String) : String := "\t".intercalate xs
  let caps := line ["caps", ",".intercalate (v.capabilities.map Capability.key)]
  let head := [line ["view", "wiz-lint/1"], caps,
    line ["module", viewText v.module], line ["path", viewText v.path],
    line ["command", viewText v.kind, viewText v.name]]
  let span := match v.span with
    | some s => [line ["span", toString s.start, toString s.stop]]
    | none => []
  let decls := v.decls.toList.map fun d =>
    line ["decl", viewText d.name, viewText d.kind, toString d.isPublic, toString d.hasDoc]
  let binders := v.binders.toList.map fun b =>
    line ["binder", viewText b.name, toString b.used, toString b.depth]
  let imports := v.imports.toList.map fun i =>
    line ["import", viewText i.name, toString i.start, toString i.stop]
  let globals := v.globals.toList.map fun g => line ["global", viewText g]
  let messages := v.messages.toList.map fun m =>
    line ["message", viewText m.severity, viewText m.code, toString m.start, toString m.stop,
      viewText m.text]
  "\n".intercalate (head ++ span ++ decls ++ binders ++ imports ++ globals ++ messages) ++ "\n"

/-- Build the view a rule declared. A section the rule did not ask for is absent (not
empty): the view's `caps` line says which sections it may read. -/
def viewOf [BEq R] [Zero R] (input : RuleInput R) (req : List Capability) : CommandView :=
  let one := if input.decls.size == 1 then input.decls[0]! else ("_", default)
  let kind := ((input.docs.get? one.1).map (·.kind)).getD ""
  { capabilities := req
    module := input.module
    path := input.path
    kind
    name := if one.1 == "_" then "" else toString one.1
    span := (if req.contains .spans then some { start := input.cmd.info.start, stop := input.cmd.info.stop } else none)
    decls := (if req.contains .decl then input.decls.map fun (n, _) =>
      { name := toString n
        kind := ((input.docs.get? n).map (·.kind)).getD ""
        isPublic := !input.globals.privates.contains n && underPublicRoot input.path input.publicRoots
        hasDoc := match input.docs.get? n with
          | some d => d.doc.any fun s => !s.trimAscii.isEmpty
          | none => false } else #[])
    binders := (if req.contains .facts then input.decls.flatMap fun (_, d) =>
      (declFacts d).1.map fun b => { name := toString b.name, used := b.used, depth := b.depth }
      else #[])
    imports := (if req.contains .imports then input.imports.map fun (n, i) =>
      { name := toString n, start := i.start, stop := i.stop } else #[])
    globals := (if req.contains .globals then input.globals.order.map toString else #[])
    messages := (if req.contains .messages then input.messages.map fun m =>
      { severity := match m.severity with | .error => "error" | .warning => "warning" | .info => "info"
        code := m.code, start := m.info.start, stop := m.info.stop, text := m.text } else #[]) }

/-- A Wiz `String` as the interpreter represents it (`String.mk (List Char)`). -/
def stringRVal (s : String) : RVal :=
  -- `String.mk (List Char)`, with each `Char.mk n` as `⟨n⟩` (the form `wiz_nat_show`
  -- builds and `RVal.stringValue?` reads)
  .obj 0 #[s.toList.foldr (fun c t => .obj 1 #[.obj 0 #[.nat c.toNat], t]) (.obj 0 #[])]

/-- Call a package rule's `String → String` runner in the interpreter. `none` when the
runner does not return a string (a malformed set, reported as a failed rule). -/
def callRunner (code : Code) (runner : Name) (arg : String) : Option String :=
  let f := run code [] (.global runner)
  stringValue? (applyN code f [stringRVal arg])

/-- Read a runner's findings: `start<TAB>stop<TAB>anchor<TAB>text` per line. The code and
severity are the rule's metadata, never the runner's choice, so a set cannot spoof
another rule's code. -/
def parseFindings (rule : LintRuleDecl) (out : String) : Array Finding := Id.run do
  let mut fs : Array Finding := #[]
  for line in out.splitOn "\n" do
    if line.trimAscii.isEmpty then continue
    match line.splitOn "\t" with
    | start :: stop :: anchor :: rest =>
      let text := "\t".intercalate rest
      fs := fs.push
        { info := { start := (String.toNat? start).getD 0, stop := (String.toNat? stop).getD 0 }
          severity := rule.defaultSeverity, code := rule.code, text, anchor }
    | _ => pure ()
  fs

/-- Every declaration reachable from `roots` through types, values, implementations and
witnesses (the closure `partial` and trust checks walk). -/
partial def reachable (g : Globals R) (todo : List Name) (seen : Std.HashSet Name) :
    Std.HashSet Name × List Name := Id.run do
  let mut seen := seen
  let mut order : List Name := []
  let mut todo := todo
  while !todo.isEmpty do
    let n := todo.head!
    todo := todo.tail
    if seen.contains n then continue
    seen := seen.insert n
    order := n :: order
    match g.find? n with
    | none => pure ()
    | some d =>
      for t in [d.type] ++ d.value.toList ++ d.impl.toList ++ d.witness.toList do
        todo := constsOf t ++ todo
  pure (seen, order.reverse)

/-- Is the declaration from the toolchain's own library (reviewed), rather than the
package's lint module? The library's `partial` helpers (the termination checker cannot
see through every string walk) are trusted; a package-defined `partial` is not. -/
def trustedDecl (s : CommandState R) (n : Name) : Bool :=
  s.trustedModule ((s.globals.declModule[n]?).getD "")

/-- A **package-defined** `partial` definition reached from the runner: the lint driver
must terminate, so such a set is refused. A `partial` in the trusted library is allowed
(it is reviewed code, and the runner still runs under the interpreter). -/
def partialIn (s : CommandState R) (roots : List Name) : Option Name :=
  let (_, names) := reachable s.globals roots {}
  names.find? fun n => match s.globals.find? n with
    | some d => d.witness.isSome && !trustedDecl s n
    | none => false

/-- A trust source the rule's closure reaches outside the toolchain's library. A
`builtin`/`native` registration from lib is reviewed; the same thing from the package's
own module is what the registry refuses. -/
def untrustedAxiom [QRig R] [DecidableEq R] [ToString R] [QuantitySyntax R]
    (s : CommandState R) (runner : Name) : Option String :=
  (s.globals.axiomsOf runner).find? fun line =>
    let name := match line.splitOn " := " with
      | _ :: rhs :: _ => rhs.trimAscii.toString
      | _ => line
    !trustedDecl s name

/-- Check a package lint module's declaration: the header, the code block, the
capabilities, and the runner's closure. A failure is a registration error, never a rule
that quietly does nothing. -/
def checkSet [QRig R] [BEq R] [DecidableEq R] [ToString R] [QuantitySyntax R] [Zero R]
    (s : CommandState R) (decl : LintSetDecl)
    (coreCodes : List String) : Except String LintPackageSet := do
  if decl.name.isEmpty then throw "a package lint set needs a name (`lint-set`)"
  if decl.abi.isEmpty then throw s!"lint set {decl.name}: the ABI range is missing"
  unless decl.abi == "wiz-lint/1" do
    throw s!"lint set {decl.name}: unsupported lint ABI '{decl.abi}' (this toolchain reads wiz-lint/1)"
  if decl.capabilities.isEmpty then
    throw s!"lint set {decl.name}: the capability set is empty (declare `[decl, spans, …]`)"
  for c in decl.capabilities do
    unless packageCapability c do
      throw s!"lint set {decl.name}: the capability '{c.key}' is not part of the package lint ABI"
  if decl.rules.isEmpty then throw s!"lint set {decl.name}: no rules"
  let mut rules : Array LintRuleDecl := #[]
  for r in decl.rules do
    -- the package block is W500–W999, and the code is a `W` + three digits
    let n? := if r.code.startsWith "W" then String.toNat? (r.code.drop 1).toString else none
    match n? with
    | some n => if n < 500 || n > 999 then
        throw s!"lint set {decl.name}: rule {r.code} is outside the package block W500–W999"
    | none => throw s!"lint set {decl.name}: '{r.code}' is not a lint code (W + three digits)"
    if coreCodes.contains r.code then
      throw s!"lint set {decl.name}: rule {r.code} collides with a core rule"
    if rules.any (·.code == r.code) then
      throw s!"lint set {decl.name}: rule {r.code} is registered twice"
    for c in r.requires do
      unless decl.capabilities.contains c do
        throw s!"lint set {decl.name}: rule {r.code} needs '{c.key}', which the set does not declare"
      unless packageCapability c do
        throw s!"lint set {decl.name}: rule {r.code} asks for the unstable capability '{c.key}'"
    if s.globals.find? r.runner |>.isNone then
      throw s!"lint set {decl.name}: rule {r.code} names the runner '{r.runner}', which is not declared"
    match untrustedAxiom s r.runner with
    | some a => throw s!"lint set {decl.name}: rule {r.code} reaches the trust source '{a}'"
    | none => pure ()
    match partialIn s [r.runner] with
    | some p => throw s!"lint set {decl.name}: rule {r.code} reaches the partial definition '{p}'"
    | none => pure ()
    rules := rules.push r
  let code ← match compileReachable s.globals s.builtins (rules.toList.map (·.runner))
      (externImpls := false) with
    | Except.ok code => pure code
    | Except.error e => throw s!"lint set {decl.name}: cannot compile its runners: {e}"
  pure { name := decl.name, abi := decl.abi, capabilities := decl.capabilities, rules, code }

/-- Load and check one elaborated package lint module. -/
def loadPackageSet [QRig R] [BEq R] [DecidableEq R] [ToString R] [QuantitySyntax R] [Zero R]
    (s : CommandState R) : Except String LintPackageSet :=
  checkSet s s.lintSetDecl ((registry R).toList.map (·.id))

/-- Load several sets, refusing a duplicate code across them (the registry key is
`(kind, name)`, so a code can have one provider in the enabled closure). -/
def loadPackageSets [QRig R] [BEq R] [DecidableEq R] [ToString R] [QuantitySyntax R] [Zero R]
    (states : Array (CommandState R)) : Except String (Array LintPackageSet) := do
  let mut out : Array LintPackageSet := #[]
  for s in states do
    let set ← loadPackageSet s
    for r in set.rules do
      for other in out do
        if other.rules.any (·.code == r.code) then
          throw s!"lint code {r.code} is registered by both '{other.name}' and '{set.name}'"
    out := out.push set
  pure out

/-- The package sets enabled for this run (a set runs only when the consumer names it). -/
def enabledSets (s : CommandState R) : Array LintPackageSet :=
  s.lintPackageSets.filter fun set => s.lintSets.contains set.name

/-- Run the enabled package rules of one scope over the stable view. -/
def runPackageRules [BEq R] [Zero R] (s : CommandState R) (input : RuleInput R)
    (scope : Scope) : Array Finding := Id.run do
  let mut out : Array Finding := #[]
  for set in enabledSets s do
    for r in set.rules do
      if r.scope != scope then continue
      if !s.lintRules.isEmpty && !s.lintRules.contains r.code then continue
      let view := viewOf input r.requires
      match callRunner set.code r.runner view.render with
      | some text => out := out ++ parseFindings r text
      | none =>
        out := out.push
          { info := input.cmd.info, severity := .error, code := "lint-set-failed"
            text := s!"package lint set {set.name}: rule {r.code} did not return a String" }
  out

/-! ## The registry and the driver -/

/-- A finding as the ordinary message the rest of the toolchain already knows. -/
def Finding.toMsg (f : Finding) : Msg :=
  { info := f.info, severity := (match f.severity with
      | .error => .error | .warning => .warning | _ => .info), text := f.text, code := f.code }

def makeInput (s : CommandState R) (cmd : Syntax) (chars : Array Char)
    (added : Array Name) : RuleInput R :=
  { module := s.module, path := s.lintPath, cmd, chars, added,
    decls := added.filterMap fun n => (s.globals.find? n).map fun d => (n, d),
    globals := s.globals, docs := s.declDocs, sites := s.declSites,
    imports := s.lintImports, publicRoots := s.lintPublicRoots,
    effectful := s.lintEffectful, loader := s.loader, messages := s.messages }

/-- Run the declaration-scope rules after one command. -/
def runCommand [BEq R] [Zero R] (s : CommandState R) (cmd : Syntax) (chars : Array Char)
    (added : Array Name) : Array Finding :=
  let input := makeInput s cmd chars added
  let rules := selected (registry R) s.lintRules |>.filter (·.scope == .declaration)
  rules.flatMap (fun r => r.run input) ++ runPackageRules s input .declaration

/-- Run the module-scope rules once the target is elaborated. -/
def runModule [BEq R] [Zero R] (s : CommandState R) (chars : Array Char) : Array Finding :=
  let input := makeInput s Syntax.missing chars #[]
  let rules := selected (registry R) s.lintRules |>.filter (·.scope == .module)
  rules.flatMap (fun r => r.run input) ++ runPackageRules s input .module

/-- Did importing `inner` add an effect (an instance, syntax, notation, a builtin, an
attribute, FFI/link code, …)? A module that does is never reported as an unused import,
because a name never appears in the target even though the effect is needed. -/
def effectfulImport (outer inner : CommandState R) : Bool :=
  inner.builtins.length > outer.builtins.length ||
  inner.instances.size > outer.instances.size ||
  inner.classes.length > outer.classes.length ||
  inner.foreignTypes.length > outer.foreignTypes.length ||
  inner.cCode.size > outer.cCode.size ||
  inner.cFuncs.length > outer.cFuncs.length ||
  inner.cStructs.length > outer.cStructs.length ||
  inner.linkC.size > outer.linkC.size ||
  inner.linkLibs.size > outer.linkLibs.size ||
  inner.globals.assumed.length > outer.globals.assumed.length ||
  inner.macros.length > outer.macros.length ||
  inner.cmdMacros.length > outer.cmdMacros.length ||
  inner.procMacros.length > outer.procMacros.length ||
  inner.tactics.length > outer.tactics.length ||
  inner.simpLemmas.length > outer.simpLemmas.length ||
  inner.derivers.length > outer.derivers.length ||
  inner.ppUser.length > outer.ppUser.length ||
  inner.tables.tokens.size > outer.tables.tokens.size ||
  inner.tables.cats.size > outer.tables.cats.size ||
  inner.rawAtoms.size > outer.rawAtoms.size

/-! ## Per-site suppression -/

structure Suppression where
  /-- the 0-based line the marker is on -/
  line : Nat
  /-- the codes it names -/
  codes : List String
  /-- the marker's position, for a diagnostic about the marker -/
  info : SourceInfo

/-- Split a marker line at its marker. Returns the codes and the reason text. -/
def parseMarker (text : String) : Option (List String × String) := do
  let rest ← match text.splitOn "-- lint: allow" with
    | _ :: rest :: _ => pure rest
    | _ => none
  let rest := rest.trimAscii.toString
  let (codesPart, reason) := match rest.splitOn "(" with
    | c :: r => (c, String.intercalate "(" r)
    | [] => ("", "")
  let codes := (codesPart.splitOn ",").map (·.trimAscii.toString) |>.filter (· != "")
  let reason := match reason.splitOn ")" with
    | r :: _ => r.trimAscii.toString
    | [] => ""
  pure (codes, reason)

/-- The markers of a file, from its text. Only the documented line-comment form is
recognised; a marker inside a string is not a marker. -/
def suppressions (text : String) : Array Suppression := Id.run do
  let mut out : Array Suppression := #[]
  let mut line := 0
  let mut start := 0
  let chars := text.toList.toArray
  for i in List.range (chars.size + 1) do
    if i == chars.size || chars[i]! == '\n' then
      let text := String.ofList (chars.extract start i).toList
      if let some (codes, _) := parseMarker text then
        out := out.push { line, codes, info := { start, stop := i } }
      line := line + 1
      start := i + 1
  out

/-- Apply the per-site markers: remove a finding named by a marker on its line or the
line above, and report a marker that names an unknown or non-suppressible code, or gives
no reason. -/
def applySuppressions [BEq R] [Zero R] (s : CommandState R) (chars : Array Char) : CommandState R := Id.run do
  let text := String.ofList chars.toList
  let marks := suppressions text
  let core := registry R
  let pkg := (enabledSets s).toList.flatMap (·.rules.toList)
  -- a code's suppressibility, or `none` when no rule registers it
  let known (c : String) : Option Bool :=
    match core.find? (·.id == c) with
    | some r => some r.suppressible
    | none => (pkg.find? (·.code == c)).map (·.suppressible)
  let mut problems : Array Msg := #[]
  for mk in marks do
    let lineText := String.ofList (chars.extract mk.info.start (min mk.info.stop chars.size)).toList
    let reason := match parseMarker lineText with
      | some (_, r) => r
      | none => ""
    for c in mk.codes do
      if c.isEmpty then
        problems := problems.push { info := mk.info, severity := .error, text := "a lint suppression needs a code" }
      else if (known c).isNone then
        problems := problems.push { info := mk.info, severity := .error, text := s!"a lint suppression names an unknown code '{c}'" }
      else if (known c) == some false then
        problems := problems.push { info := mk.info, severity := .error, text := s!"lint rule {c} is not suppressible" }
      if reason.isEmpty then
        problems := problems.push { info := mk.info, severity := .error, text := s!"a lint suppression of {c} needs a reason" }
  let suppressed (m : Msg) : Bool :=
    if !m.code.startsWith "W" then false else
    let l := lineOf chars m.info.start
    marks.any fun mk =>
      (mk.line == l || mk.line + 1 == l) && mk.codes.contains m.code
  return { s with messages := s.messages.filter (!suppressed ·) ++ problems }

/-- Finish a lint run: the module-scope findings, then suppression. This is the only
place the lint driver touches the state, and it only appends/removes messages with a
`W` code (and reports a malformed marker). -/
def finish [BEq R] [Zero R] (s : CommandState R) (chars : Array Char) : CommandState R :=
  let findings := runModule s chars
  let s := { s with messages := s.messages ++ findings.map Finding.toMsg }
  applySuppressions s chars

end Lint
end Wiz
