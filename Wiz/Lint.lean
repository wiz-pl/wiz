import Wiz.Elab.Command
import Wiz.Frontend.Parse
import Lean.Data.Json

/-!
# `ward`: warnings about a file that the elaborator accepts

`wiz lint` (stage 11ad) reports **style** and **hygiene** problems without failing the
elaboration: errors are still errors, but a warning is a warning, and the exit status is
0 unless `--deny` is given.

The checks here are deliberately cheap and conservative: each one is either purely
textual (tabs, trailing whitespace, CRLF, long lines, `sorry`) or reads facts the
elaborator already records (the declaration table, the declaration sites and the info
tree), so `lint` adds no elaboration work of its own.

| rule | what it reports |
|------|-----------------|
| `style.tabs` | a tab in indentation or alignment |
| `style.trailing-whitespace` | spaces or tabs at the end of a line |
| `style.crlf` | CRLF line endings (once per file) |
| `style.line-length` | a line longer than `--max-line` (`0` turns it off) |
| `sorry` | the identifier `sorry`/`admit`, which Wiz does not check |
| `axiom` | an `axiom` declared in this file |
| `shadowed-binder` | a binder whose name is an enclosing binder's or a visible global's (parameters, `let`, `fun`/`∀`) |
| `unused-import` | an imported module nothing in this file uses |
| `duplicate-import` | the same module imported twice |

The `unused-import` check is only as good as the info tree: an import counts as used
when a name from that module is mentioned (also in a command argument, a quotation, or a
string literal that is a global's exact name), an instance from it is found, or syntax it
declared is used. Imports are transitive in Wiz, so an import is also needed when it is
the only path to a used module, and an import that is itself used or effectful (one with
`builtin`, `syntax`, `notation`, `macro_rules`, `infix…`/`prefix`/`postfix` or
`attribute [`) stays explicit. Nothing is reported for a file with elaboration errors: a
failed command may hide the use.

Deferred (they need the elaborator to say more than the info tree does today):
`redundant := rfl` (would need the kernel's answer for a definition accepted by
computation), unused private declarations, unused local `let` variables, and anything
inside a `match` alternative: the branch context holds the earlier alternatives'
pattern variables and the constructor's field names, so `| .b n => …` cannot tell the
field `n` from a shadowed `n` without the alternative's own scope. See
`wiz-notes/ward.md`.
-/

namespace Wiz.Lint

/-- The lint's options (`wiz lint --max-line N --no-style`). -/
structure Options where
  /-- report a line longer than this (`0`: never) -/
  maxLine : Nat := 120
  /-- the purely textual `style.*` rules -/
  style : Bool := true
  deriving Repr, Inhabited, BEq

/-- One finding. `info` is its source range (`start = stop` is a position). -/
structure Diag where
  info : SourceInfo
  severity : Severity
  /-- the rule's stable name, e.g. `unused-import` -/
  rule : String
  message : String
  deriving Repr, Inhabited, BEq

def severityName : Severity → String
  | .error => "error"
  | .warning => "warning"
  | .info => "info"

/-- `PATH:LINE:COL: warning: MESSAGE [RULE]` (1-based, as `wiz check`). -/
def Diag.render (path text : String) (d : Diag) : String :=
  let (l, c) := lineCol text d.info.start
  s!"{path}:{l + 1}:{c + 1}: {severityName d.severity}: {d.message} [{d.rule}]"

/-- A diagnostic as JSON (1-based `line`/`column`, end exclusive). -/
def Diag.toJson (text : String) (d : Diag) : Lean.Json :=
  let (l, c) := lineCol text d.info.start
  let (l₂, c₂) := lineCol text (max d.info.stop d.info.start)
  Lean.Json.mkObj [
    ("rule", Lean.Json.str d.rule),
    ("severity", Lean.Json.str (severityName d.severity)),
    ("message", Lean.Json.str d.message),
    ("line", Lean.Json.num (Lean.JsonNumber.fromNat (l + 1))),
    ("column", Lean.Json.num (Lean.JsonNumber.fromNat (c + 1))),
    ("endLine", Lean.Json.num (Lean.JsonNumber.fromNat (l₂ + 1))),
    ("endColumn", Lean.Json.num (Lean.JsonNumber.fromNat (c₂ + 1)))]

/-! ## Style, from the text -/

/-- The `style.*` findings: tabs, trailing whitespace, CRLF (reported once) and long
lines. At most one finding of each rule per line, at its first position. -/
def styleDiags (opts : Options) (text : String) : Array Diag := Id.run do
  let chars := text.toList.toArray
  let mut out : Array Diag := #[]
  let mut crlf := false
  let mut lineStart := 0
  let mut i := 0
  while i ≤ chars.size do
    let eol := if i == chars.size then true else chars[i]! == '\n'
    if eol then
      let mut stop := i
      -- CRLF: the `\r` before the `\n` (once per file)
      if i > lineStart && chars[i - 1]! == '\r' then
        stop := i - 1
        unless crlf do
          crlf := true
          out := out.push { info := { start := i - 1, stop := i }, severity := .warning,
                            rule := "style.crlf", message := "CRLF line ending: write LF" }
      -- trailing whitespace, and the trailing run (a tab there is reported as a tab)
      let mut t := stop
      while t > lineStart && (chars[t - 1]! == ' ' || chars[t - 1]! == '\t') do t := t - 1
      let trailingTabs := (List.range (stop - t)).all fun k => chars[t + k]! == '\t'
      if t < stop && !trailingTabs then
        out := out.push { info := { start := t, stop }, severity := .warning,
                          rule := "style.trailing-whitespace", message := "trailing whitespace" }
      -- a tab anywhere on the line (indentation, alignment)
      let mut j := lineStart
      while j < stop && chars[j]! != '\t' do j := j + 1
      if j < stop then
        out := out.push { info := { start := j, stop := j + 1 }, severity := .warning,
                          rule := "style.tabs", message := "tab: use spaces" }
      if opts.maxLine > 0 && stop - lineStart > opts.maxLine then
        out := out.push { info := { start := lineStart + opts.maxLine, stop }, severity := .warning,
                          rule := "style.line-length",
                          message := s!"line is {stop - lineStart} characters (max {opts.maxLine})" }
      lineStart := i + 1
    i := i + 1
  out

/-- The identifiers `sorry` and `admit` in `text`, outside comments and strings. Wiz has
neither: a file that says `sorry` does not elaborate, and nothing is proved. -/
def sorryDiags (text : String) : Array Diag := Id.run do
  let chars := text.toList.toArray
  let mut out : Array Diag := #[]
  let mut i := 0
  let mut block := 0
  while i < chars.size do
    let c := chars[i]!
    if block > 0 then
      if c == '/' && i + 1 < chars.size && chars[i + 1]! == '-' then
        block := block + 1
        i := i + 2
      else if c == '-' && i + 1 < chars.size && chars[i + 1]! == '/' then
        block := block - 1
        i := i + 2
      else i := i + 1
    else if c == '-' && i + 1 < chars.size && chars[i + 1]! == '-' then
      while i < chars.size && chars[i]! != '\n' do i := i + 1
    else if c == '/' && i + 1 < chars.size && chars[i + 1]! == '-' then
      block := 1
      i := i + 2
    else if c == '"' then
      i := i + 1
      while i < chars.size && chars[i]! != '"' do
        if chars[i]! == '\\' then i := i + 2 else i := i + 1
      i := i + 1
    else if isIdStart c then
      let start := i
      while i < chars.size && isIdRest chars[i]! do i := i + 1
      let w := String.ofList (chars.extract start i).toList
      if w == "sorry" || w == "admit" then
        out := out.push { info := { start, stop := i }, severity := .warning, rule := "sorry",
                          message := s!"'{w}' is not checked: Wiz has no sorry (write the proof, or declare an axiom)" }
    else i := i + 1
  out

/-! ## `axiom` declarations -/

/-- The axioms declared in this file (not in its imports), by their declaration site. -/
def axiomDiags {R : Type} (s : CommandState R) : Array Diag :=
  (s.declDocs.toList.filterMap fun (n, d) => do
    guard (d.kind == "axiom" || d.kind.endsWith " axiom")
    let (site, m) ← s.declSites.get? n
    guard (m == "")
    pure ({ info := { start := d.start, stop := site.stop }, severity := .warning, rule := "axiom",
            message := s!"'{n}' is an axiom: its type is trusted, not checked" } : Diag)).toArray

/-! ## Shadowed binders

The elaborator records every binder it is given (`recordBinder`) in the info tree, with
the local context *before* the binder. So a binder's info entry says whether its name is
already in scope, and whether it is a global's. Finding the binder entries is the work:
a `SourceInfo` is a binder's when the syntax at it binds a name, which is what
`binderSites` collects (binders, `fun`/`∀` names, `let` names, and pattern variables).
A pattern variable is a variable only if it does not name a constructor, which
`patView` decides against the globals. -/

/-- The sites of the names `stx` binds: `(x : A)`, `{x}`, `[C]` binders anywhere,
`fun`/`∀` bare names, `let` names `x`, `let (a, b) := …`. A `match` alternative is
skipped whole: the elaborator's branch context also holds the earlier alternatives'
pattern variables (the case tree binds them in one context), so a name bound there would
look like a shadow that the source does not have. A site with no info in the tree (a
macro's output) is skipped by the caller. -/
partial def binderSites (stx : Syntax) : Array SourceInfo :=
  let here : Array SourceInfo :=
    if stx.isOfKind "binder.explicit" || stx.isOfKind "binder.implicit" || stx.isOfKind "binder.inst" then
      (Wiz.Elab.binderViews stx).map (·.info)
    else if stx.isOfKind "term.fun" || stx.isOfKind "term.forall" then
      ((stx.getArg 1).args.filterMap fun b => if b matches .ident .. then some b.info else none)
    else if stx.isOfKind "term.let" then #[(stx.getArg 2).info]
    else if stx.isOfKind "term.letPair" then #[(stx.getArg 3).info, (stx.getArg 5).info]
    else if stx.isOfKind "term.letTuple" then
      #[(stx.getArg 3).info, (stx.getArg 5).info] ++ (stx.getArg 7).args.map (·.info)
    else #[]
  if stx.isOfKind "match.alt" then #[] else
  here ++ stx.args.foldl (fun acc a => acc ++ binderSites a) #[]

/-- The info tree's binder entries: `(start, stop) → (name, local names in scope)`. -/
def binderEntries {R : Type} (s : CommandState R) :
    Std.HashMap (Nat × Nat) (Name × List Name) :=
  s.infos.foldl (fun m i => match i with
    | .ident r n true names _ => m.insert (r.start, r.stop) (n, names)
    | _ => m) {}

/-- A binder that is named like an enclosing binder, or like a global visible where it
is bound. A declaration's own command is not a visible global there (`def f (f : Nat)`
is the name being declared, not a shadow), and neither is a later declaration. -/
def shadowDiags {R : Type} (s : CommandState R) (text : String) : Array Diag := Id.run do
  let entries := binderEntries s
  let mut out : Array Diag := #[]
  let mut seen : Std.HashSet (Nat × Nat) := {}
  for cmd in (parseFile text).commands do
    for site in binderSites cmd do
      if site.stop == 0 || seen.contains (site.start, site.stop) then continue
      seen := seen.insert (site.start, site.stop)
      let some (n, names) := entries.get? (site.start, site.stop) | continue
      if n == "_" || n == "inst✝" then continue
      if names.contains n then
        out := out.push { info := site, severity := .warning, rule := "shadowed-binder",
                          message := s!"binder '{n}' shadows an enclosing binder '{n}'" }
      else if let some (ds, m) := s.declSites.get? n then
        -- a global from another module is visible; this file's only after its command
        let visible := m != "" || ds.stop ≤ site.start
        let self := ds.start ≤ site.start && site.stop ≤ ds.stop
        if visible && !self then
          let origin := if m == "" then "this file" else s!"module {m}"
          out := out.push { info := site, severity := .warning, rule := "shadowed-binder",
                            message := s!"binder '{n}' shadows the global '{n}' ({origin})" }
  pure out

/-! ## Imports -/

/-- Does the module's own source change its importers without being named? `builtin`
registrations, notation, macros and attributes all do; a plain declaration does not. -/
def effectfulImport (src : String) : Bool :=
  src.splitOn "\n" |>.any fun line =>
    let t := line.trimAscii.toString
    ["builtin", "syntax", "notation", "macro_rules", "declare_syntax_cat", "attribute",
     "infix", "prefix", "postfix"].any (t.startsWith ·)

/-- The constants a term mentions. -/
partial def constsIn {R : Type} (t : Term R) : List Name :=
  (match t with | .const n _ => [n] | _ => []) ++
  ((Term.forChildren (m := StateM (List Name)) (fun _ => pure ())
    (fun _ c => modify (fun acc => acc ++ constsIn c)) t).run []).2

/-- Every identifier the syntax mentions: terms, command arguments (`attribute [deriver
C]`, `deriving C`, `#print axioms f`, `builtin k := n`) and quotations, none of which the
info tree has (only terms push identifiers). -/
partial def identsIn (stx : Syntax) : Array Name :=
  (match stx with | .ident _ n => #[n] | _ => #[]) ++
  stx.args.foldl (fun acc a => acc ++ identsIn a) #[]

/-- The string literals the syntax mentions: a tactic that builds a term by name
(`Expr.mkApp (.const "Bits.wland_bit")`) needs the module that declares it, and no
identifier says so. -/
partial def stringsIn (stx : Syntax) : Array String :=
  (match stx.getStr? with | some v => #[v] | none => #[]) ++
  stx.args.foldl (fun acc a => acc ++ stringsIn a) #[]

/-- The modules this file uses: what the info tree names (identifiers, instances found by
search, syntax references, expansion handlers) and every identifier the syntax mentions
(command arguments and quotations included; over-marking a module can only hide a warning,
which is the safe direction). -/
def usedModules {R : Type} (s : CommandState R) (text : String) : Std.HashSet String := Id.run do
  let mut used : Std.HashSet String := {}
  let siteOf : Name → Option String := fun n => (s.declSites.get? n).map (·.2)
  let syntaxMod : SyntaxRef → Option String := fun ref =>
    match ref with
    | .kind k => (s.kindSites.get? k).map (·.2)
    | .cat c => (s.catSites.get? c).map (·.2)
  for i in s.infos do
    match i with
    | .ident _ n false _ _ =>
      if let some m := siteOf n then
        if m != "" then used := used.insert m
    | .inst _ _ _ inst =>
      for n in constsIn inst do
        if let some m := siteOf n then
          if m != "" then used := used.insert m
    | .syntaxRef _ ref =>
      if let some m := syntaxMod ref then
        if m != "" then used := used.insert m
    | .expansion _ _ (.rule _ m) _ => if m != "" then used := used.insert m
    | .expansion _ _ (.fn _ f) _ =>
      if let some m := siteOf f then
        if m != "" then used := used.insert m
    | _ => ()
  for cmd in (parseFile text).commands do
    for n in identsIn cmd do
      if let some m := siteOf n then
        if m != "" then used := used.insert m
    for v in stringsIn cmd do
      if let some m := siteOf v then
        if m != "" then used := used.insert m
  pure used

/-- The modules `m` imports directly, from its source (the imports of an import are
transitive in Wiz: they come into the importer's scope, names and effects alike). -/
def importsOf {R : Type} (s : CommandState R) (m : String) : Array String :=
  match s.loader m with
  | none => #[]
  | some src => (parseFile src).commands.filterMap fun c =>
      if c.isOfKind "command.import" then (c.getArg 1).getId? else none

/-- The dependency table of the modules reachable from `todo`: each module's direct
imports, its source parsed once. -/
partial def loadDeps {R : Type} (s : CommandState R) (deps : Std.HashMap String (Array String))
    (todo : List String) : Std.HashMap String (Array String) :=
  match todo with
  | [] => deps
  | m :: rest =>
    if deps.contains m then loadDeps s deps rest
    else
      let ds := importsOf s m
      loadDeps s (deps.insert m ds) (ds.toList ++ rest)

/-- Every module `todo` reaches, in `seen` (which is returned). -/
partial def reach (deps : Std.HashMap String (Array String)) (seen : Std.HashSet String)
    (todo : List String) : Std.HashSet String :=
  match todo with
  | [] => seen
  | m :: rest =>
    if seen.contains m then reach deps seen rest
    else reach deps (seen.insert m) ((deps.getD m #[]).toList ++ rest)

/-- Imports that nothing in the file needs. An import is needed when some module it
brings (itself or, transitively, one of its imports: Wiz imports are transitive) is used
by name, or has effects on its importers (`effectfulImport`); it is reported when the
*other* imports bring all of those already, so `import A` + `import B` with `B` importing
`A` reports the redundant `A`. Nothing is reported for a file with elaboration errors (a
failed command may be the use), and the same module imported twice also gets a
`duplicate-import`. -/
def importDiags {R : Type} (s : CommandState R) (text : String) : Array Diag := Id.run do
  let cmds := (parseFile text).commands
  let imports : Array (Name × SourceInfo) := cmds.filterMap fun c =>
    if c.isOfKind "command.import" then
      match (c.getArg 1).getId? with
      | some n => some (n, (c.getArg 1).info)
      | none => none
    else none
  let mut out : Array Diag := #[]
  let mut seen : Std.HashSet Name := {}
  for (n, info) in imports do
    if seen.contains n then
      out := out.push { info, severity := .warning, rule := "duplicate-import",
                        message := s!"module {n} is imported twice" }
    seen := seen.insert n
  if s.messages.any (·.severity == .error) then return out
  let direct := imports.map fun (n, _) => s!"{n}"
  let deps := loadDeps s {} direct.toList
  let used := usedModules s text
  -- what the imports must bring: used modules, and modules with effects on importers
  let mut needed : Std.HashSet String := {}
  for m in direct do
    for r in (reach deps {} [m]).toList do
      if used.contains r then needed := needed.insert r
      else if let some src := s.loader r then
        if effectfulImport src then needed := needed.insert r
  let mut reported : Std.HashSet Name := {}
  for (n, info) in imports, idx in [0:imports.size] do
    -- a duplicate is the duplicate's finding; report the first occurrence only
    if reported.contains n then continue
    -- an import that is itself used, or that has effects on its importers, is kept:
    -- `import Prelude` stays explicit even though another import would bring it
    let m := s!"{n}"
    if used.contains m then continue
    if let some src := s.loader m then
      if effectfulImport src then continue
    let others := direct.zipIdx.foldl (fun acc (m, j) =>
      if j == idx then acc else reach deps acc [m]) {}
    if needed.toList.all (others.contains ·) then
      reported := reported.insert n
      out := out.push { info, severity := .warning, rule := "unused-import",
                        message := s!"module {n} is imported but nothing needs it (no name or syntax from it, no module it brings, is used)" }
  pure out

/-! ## The whole lint -/

/-- Every finding for `text` and its elaborated state `s`, sorted by position. The
elaborator's own messages are included (errors count as errors, as in `wiz check`). -/
def run {R : Type} (opts : Options) (text : String) (s : CommandState R) : Array Diag :=
  let elaborator := s.messages.map fun msg =>
    { info := msg.info, severity := msg.severity,
      rule := if msg.code.isEmpty then "elaborator" else msg.code, message := msg.text : Diag }
  let found :=
    (if opts.style then styleDiags opts text else #[]) ++
    sorryDiags text ++
    axiomDiags s ++
    shadowDiags s text ++
    importDiags s text
  (elaborator ++ found).qsort fun a b =>
    a.info.start < b.info.start || (a.info.start == b.info.start && a.rule < b.rule)

end Wiz.Lint
