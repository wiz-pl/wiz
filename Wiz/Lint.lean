import Wiz.Elab.Command
import Wiz.Module

/-!
# Lint: warnings about a program the elaborator accepted

The lint pass is **post-elaboration**: it reads the declarations a command added and
records findings as ordinary `Msg`s (`severity` and `code := the rule id`). It never
changes a declaration, a message the elaborator produced, or whether a program is
accepted.

The pass is off by default (`CommandState.lintEnabled`). `wiz lint` turns it on; `wiz
check`, `wiz build` and the language server leave it off, so the normal build pays
nothing and no existing message changes.

A rule is the same record a package rule will be: a stable `W` code, a category, a
default severity, a scope, the capabilities it needs, and whether a per-site marker may
suppress it. P0 registers the five rules of `wiz-notes/linting.md` §3.5; the package
loader and the capability ABI are P1.

## Suppression

The only mechanism in P0 is the per-site marker:

    out := out ++ [d]        -- lint: allow W201 (the list has at most 4 entries here)

It applies on the finding's line or the line above it. A marker must give a reason and
must name a registered code; a typo is an error, not a silent suppression. A rule that
is not suppressible (a safety rule, P1) cannot be named by a marker.
-/

namespace Wiz
namespace Lint

/-- The stable category of a rule. The `W` block allocates codes by category
(`docs/error-codes.md`): `W1xx` correctness, `W2xx` performance, `W3xx` API/style,
`W4xx` maintainability, `W5xx` package sets. -/
inductive Category where
  | correctness
  | performance
  | api
  | maintainability
  | ecosystem
  deriving BEq, Repr, Inhabited

/-- The default severity of a rule. `off` means the rule is registered but does not
run unless a repository enables it. `hint` maps to the messages' `info` severity. -/
inductive Severity where
  | off
  | hint
  | warning
  | error
  deriving BEq, Repr, Inhabited

/-- What a rule sees: a command's declarations, or the whole module for a module-scope
rule. A source range is the primary span; the anchor is stable across a reindent (`f#2`
is the second parameter of `f`). -/
inductive Scope where
  | declaration
  | module
  | workspace
  deriving BEq, Repr, Inhabited

/-- The capability a rule declares. P0 rules need `decl` and `spans` only; the others
are named here so the registry shape does not assume "core only". -/
inductive Capability where
  | decl
  | spans
  | imports
  | globals
  | messages
  | info
  | tactics
  | kernelTerm
  | sourceText
  deriving BEq, Repr, Inhabited

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
    | .ecase _ m s bs => discardedTerms m ++ discardedTerms s ++ (bs.foldl (· ++ discardedTerms ·) #[])
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

/-! ## The registry and the driver -/

/-- The core registry. The order is the order findings are emitted. -/
def registry (R : Type) [BEq R] [Zero R] : Array (Rule R) := #[w101, w102, w103, w301, w302]

def selected (rules : Array (Rule R)) (ids : List String) : Array (Rule R) :=
  if ids.isEmpty then rules else rules.filter fun r => ids.contains r.id

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
    effectful := s.lintEffectful, loader := s.loader }

/-- Run the declaration-scope rules after one command. -/
def runCommand [BEq R] [Zero R] (s : CommandState R) (cmd : Syntax) (chars : Array Char)
    (added : Array Name) : Array Finding :=
  let rules := selected (registry R) s.lintRules |>.filter (·.scope == .declaration)
  rules.flatMap fun r => r.run (makeInput s cmd chars added)

/-- Run the module-scope rules once the target is elaborated. -/
def runModule [BEq R] [Zero R] (s : CommandState R) (chars : Array Char) : Array Finding :=
  let rules := selected (registry R) s.lintRules |>.filter (·.scope == .module)
  rules.flatMap fun r => r.run (makeInput s Syntax.missing chars #[])

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
  let known := registry R
  let mut problems : Array Msg := #[]
  for mk in marks do
    let lineText := String.ofList (chars.extract mk.info.start (min mk.info.stop chars.size)).toList
    let reason := match parseMarker lineText with
      | some (_, r) => r
      | none => ""
    for c in mk.codes do
      if c.isEmpty then
        problems := problems.push { info := mk.info, severity := .error, text := "a lint suppression needs a code" }
      else if !known.any (·.id == c) then
        problems := problems.push { info := mk.info, severity := .error, text := s!"a lint suppression names an unknown code '{c}'" }
      else if ((known.find? (·.id == c)).map (·.suppressible)).getD true == false then
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
