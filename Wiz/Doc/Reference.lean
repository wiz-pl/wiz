import Wiz.Doc.Site

/-!
# The reference manual (stage 11s)

`wiz doc --reference DIR` writes a reference manual of the documented modules: one
section per module with every public declaration, its kind, its full signature (the
elaborated type, so implicit arguments are in it), its doc comment (Markdown, rendered
with the same renderer as the doc pages and with links between declarations), and the
instances of each class (or for each type). A **notation table** at the top lists every
infix, prefix and postfix operator the grammar declared, with its precedence,
associativity and what it expands to. The table is read from the parser tables and the
macro rules the modules registered, so it cannot disagree with the parser.

The manual is generated, not hand-written: `wiz doc --reference DIR --check` writes
nothing and fails when `DIR/index.md` differs from what the modules now say. The docs job
runs it on every push, and the group `doc` checks the committed manual
(`docs/reference/index.md`) against the library.

`--reference` also writes `reference.html` into the site, so a module page can link a
declaration to its entry here.
-/

namespace Wiz.Doc
namespace Reference

/-- One row of the notation table. -/
structure Op where
  /-- the operator as written, without the spaces of the declaration -/
  op : String
  /-- `infixl`, `infixr`, `infix`, `prefix` or `postfix` -/
  fixity : String
  prec : Nat
  /-- `left`, `right` or `none` (`—` for a prefix or postfix operator) -/
  assoc : String
  /-- what the macro rule makes of it, as source-like text -/
  expands : String
  /-- the module that declared it -/
  module : String
  kind : Name
  deriving Inhabited

/-- One entry of the manual: a declaration and its constructors or fields. -/
abbrev Section := Module × Array Entry

/-- The manual's data, made once from the elaborated modules. -/
structure Data where
  title : String
  sections : Array Section
  ops : Array Op
  /-- every documented name (a backticked name in a doc comment that is one is a link) -/
  names : Std.HashSet String
  /-- instances by class, and by the types an instance is for (as the doc pages group
  them), from every documented module (not only the ones a class's own module imports) -/
  byClass : Std.HashMap Name (Array Name)
  byType : Std.HashMap Name (Array Name)
  /-- the elaborated type of every instance -/
  instanceSig : Std.HashMap Name String
  moduleCount : Nat
  declCount : Nat
  /-- declarations and their constructors or fields: one signature each -/
  sigCount : Nat

/-! ## The notation table

The parser tables are the grammar the modules were parsed with. An operator rule has a
recognisable shape: a leading rule `op term` (prefix), a trailing rule `term op term`
(infix) or `term op` (postfix). The two operand precedences say how it associates,
exactly as `notationRule` wrote them: `(p, p+1)` is left, `(p+1, p)` right, `(p+1, p+1)`
neither. The macro rule of the same kind says what the operator means. -/

/-- Source-like text for a syntax tree (a macro rule's template). It is the declaration's
own spelling, not a parse: enough to read what the operator expands to. -/
partial def syntaxText : Syntax → String
  | .missing => "_"
  | .atom _ s => s
  | .ident _ n => n
  | .node _ "null" as => " ".intercalate (as.toList.map syntaxText)
  | .node _ "antiquot" as => match as.toList with
    | [_, x] => "$" ++ syntaxText x
    | _ => " ".intercalate (as.toList.map syntaxText)
  | .node _ "num" as => match as.toList with | [.atom _ v] => v | _ => " ".intercalate (as.toList.map syntaxText)
  | .node _ "str" as => match as.toList with | [.atom _ v] => v.quote | _ => " ".intercalate (as.toList.map syntaxText)
  | .node _ "term.paren" as => match as.toList with | [a] => "(" ++ syntaxText a ++ ")" | _ => " ".intercalate (as.toList.map syntaxText)
  | .node _ "term.app" as => match as.toList with
    | f :: .node _ "null" _ :: args => " ".intercalate (syntaxText f :: args.map syntaxText)
    | _ => " ".intercalate (as.toList.map syntaxText)
  | .node _ _ as => " ".intercalate (as.toList.map syntaxText)

def opText (s : String) : String := s.trimAscii.toString

/-- The associativity of an infix rule from its precedence and its operands'
(`notationRule`'s `(p, p+1)` etc.). -/
def assocOf (prec : Nat) (l r : Nat) : String :=
  if l == prec && r == prec + 1 then "left"
  else if l == prec + 1 && r == prec then "right"
  else "none"

/-- An operator-shaped rule: operator, fixity, precedence, associativity. A leading rule
spells `op term`; a trailing one keeps its left operand out of the descriptor (`lhsPrec`
has it), so an infix rule is `op term` and the other precedence is `lhsPrec`. -/
def shapeOf (leading : Bool) (lhsPrec : Nat) (p : ParserDescr) (prec : Nat) :
    Option (String × String × Nat × String) :=
  if leading then
    match p with
    | .seq ps => match ps.toList with
      | [.atom op, .cat _ _] => some (opText op, "prefix", prec, "—")
      | _ => none
    | _ => none
  else
    match p with
    | .seq ps => match ps.toList with
      | [.atom op, .cat _ r] =>
        let a := assocOf prec lhsPrec r
        some (opText op, (if a == "left" then "infixl" else if a == "right" then "infixr" else "infix"),
          prec, a)
      | _ => none
    | .atom op => some (opText op, "postfix", prec, "—")
    | _ => none

/-- An operator is a symbol, not a word (`do` is notation too, but not an operator). -/
def symbolOp (op : String) : Bool :=
  op.toList.any fun c => !(c.isAlphanum || c == '_' || c.isWhitespace)

/-- The macro rule of `kind`, from the module that declared it. -/
def macroOf? (states : Array St) (kind : Name) : Option MacroRule :=
  states.toList.findSome? fun st => st.macros.find? (·.kind == kind)

/-- Every operator the documented modules' grammar declares, one row per syntax kind.
The states are the modules' (an imported module's notation is in each importer's state,
so the rows are deduplicated by kind). Sorted by precedence, tightest first. -/
def collectOps (states : Array St) : Array Op := Id.run do
  let mut ops : Array Op := #[]
  let mut seen : Std.HashSet Name := {}
  for st in states do
    let cat := st.tables.cats.getD "term" {}
    for t in cat.trailing do
      if seen.contains t.kind then continue
      match shapeOf false t.lhsPrec t.p t.prec with
      | some (op, fixity, prec, assoc) =>
        seen := seen.insert t.kind
        let (expands, module) := match macroOf? states t.kind with
          | some r => (syntaxText r.template, r.module)
          | none => ("", "")
        if !module.isEmpty && symbolOp op then
          ops := ops.push { op, fixity, prec, assoc, expands, module, kind := t.kind }
      | none => pure ()
    for l in cat.leading do
      if seen.contains l.kind then continue
      match shapeOf true 0 l.p l.prec with
      | some (op, fixity, prec, assoc) =>
        seen := seen.insert l.kind
        let (expands, module) := match macroOf? states l.kind with
          | some r => (syntaxText r.template, r.module)
          | none => ("", "")
        if !module.isEmpty && symbolOp op then
          ops := ops.push { op, fixity, prec, assoc, expands, module, kind := l.kind }
      | none => pure ()
  pure <| ops.qsort fun a b =>
    a.prec > b.prec || (a.prec == b.prec && (a.op < b.op || (a.op == b.op && a.kind < b.kind)))

/-- Make the manual's data from the modules' pages. -/
def collect (title : String) (sections : Array Section) (states : Array St) : Data := Id.run do
  let mut names : Std.HashSet String := {}
  let mut declCount := 0
  let mut sigCount := 0
  let mut byClass : Std.HashMap Name (Array Name) := {}
  let mut byType : Std.HashMap Name (Array Name) := {}
  let mut sigs : Std.HashMap Name String := {}
  let mut instSeen : Std.HashSet Name := {}
  for st in states do
    for i in st.instances do
      if i.name.startsWith "_private." || instSeen.contains i.name then continue
      instSeen := instSeen.insert i.name
      if let some d := st.globals.find? i.name then
        sigs := sigs.insert i.name (Term.pretty [] d.type (some st.globals))
        byClass := byClass.insert i.cls ((byClass.getD i.cls #[]).push i.name)
        for t in (instanceTypes d.type).eraseDups do
          byType := byType.insert t ((byType.getD t #[]).push i.name)
  for (_, es) in sections do
    for e in es do
      names := names.insert e.name
      declCount := declCount + 1
      sigCount := sigCount + 1
      for k in e.children do
        names := names.insert k.name
        sigCount := sigCount + 1
  pure ⟨title, sections, collectOps states, names, byClass, byType, sigs, sections.size,
    declCount, sigCount⟩

/-- The instances of a class declaration, or the instances for a type one, from every
documented module. -/
def Data.instancesFor (d : Data) (e : Entry) : Array Name :=
  ((d.byClass.getD e.name #[]) ++ (d.byType.getD e.name #[])).toList.eraseDups.toArray

def Data.instanceSigOf (d : Data) (n : Name) : String := d.instanceSig.getD n ""

/-! ## Markdown -/

/-- A link target for a documented name, inside the manual. -/
def Data.href? (d : Data) (n : String) : Option String :=
  if d.names.contains n then some s!"#{n}" else none

/-- A doc comment as HTML (the doc pages' renderer; backticked names link inside the
manual). -/
def Data.docHtml (d : Data) (doc : Option String) : String :=
  match doc with
  | some s => s!"<div class=\"doc\">{render (fun c => d.href? c) s}</div>"
  | none => ""

/-- A doc comment as inline HTML (for a constructor's or field's line). -/
def Data.docInline (d : Data) (doc : Option String) : String :=
  match doc with
  | some s =>
    let p := ((s.splitOn "\n\n").headD "").replace "\n" " "
    s!" — {inline (fun c => d.href? c) p}"
  | none => ""

def mdEscape (s : String) : String := (s.replace "|" "\\|").replace "\n" " "

/-- A table cell: inert text (the table's own syntax), in a code span where it is code. -/
def mdCode (s : String) : String := s!"`{mdEscape s}`"

/-- The notation table. -/
def notationMarkdown (d : Data) : String :=
  if d.ops.isEmpty then "No operator notation is declared.\n" else
  let rows := d.ops.toList.map fun o =>
    let exp := if o.expands.isEmpty then "" else mdCode o.expands
    s!"| {mdCode o.op} | {o.fixity} | {o.prec} | {o.assoc} | {exp} | {mdEscape o.module} |"
  "| operator | fixity | precedence | associativity | expands to | module |\n" ++
  "| --- | --- | ---: | --- | --- | --- |\n" ++ String.join (rows.map (· ++ "\n"))

/-- The declarations of a module, as the module section's own table of contents. -/
def sectionToc (es : Array Entry) : String :=
  let items := es.toList.map fun e => s!"- [{e.name}](#{e.name})"
  String.join (items.map (· ++ "\n"))

/-- A constructor or field: its anchor, name, signature and doc. -/
def childMarkdown (d : Data) (k : Entry) : String :=
  let short := match k.name.splitOn "." |>.getLast? with
    | some s => s
    | none => k.name
  s!"- <a id=\"{htmlEscape k.name}\"></a>{mdCode short} : {mdCode k.sigText}{d.docInline k.doc}\n"

/-- The instances of a class (or for a type), with their signatures and links. -/
def instancesMarkdown (d : Data) (e : Entry) : String :=
  let is := d.instancesFor e
  if is.isEmpty then "" else
  let what := if e.kind == "class" then "Instances of this class" else "Instances for this type"
  let rows := is.toList.map fun i =>
    let name := match d.href? i with
      | some h => s!"[{mdCode i}]({h})"
      | none => mdCode i
    s!"- {name} : {mdCode (d.instanceSigOf i)}\n"
  s!"\n**{what} ({is.size})**\n\n" ++ String.join rows

/-- One declaration: heading with a stable, declaration-based anchor, kind and source,
its signature, its doc, its constructors or fields and its instances. -/
def entryMarkdown (d : Data) (m : Module) (e : Entry) : String :=
  let kids := if e.children.isEmpty then "" else
    let what := if e.children.all (·.kind == "field") then "Fields" else
      if e.children.all (·.kind == "constructor") then "Constructors" else "Constructors and fields"
    s!"\n**{what}**\n\n" ++ String.join (e.children.toList.map fun k => childMarkdown d k)
  s!"<a id=\"{htmlEscape e.name}\"></a>\n" ++
  s!"### {mdCode e.name}\n\n" ++
  s!"{e.kind} · `{mdEscape m.rel}:{e.line}`\n\n" ++
  -- (a signature is a type, not a Wiz file: a plain block, which the docs-examples
  -- check does not try to `wiz check`)
  s!"```text\n{e.sigText}\n```\n" ++
  d.docHtml e.doc ++ "\n" ++ kids ++ instancesMarkdown d e ++ "\n"

/-- The manual as one Markdown file: header, contents, notation table, then a section per
module and a subsection per declaration. -/
def markdown (d : Data) : String :=
  let toc := d.sections.toList.map fun (m, es) =>
    let summary := match moduleDocOf m.src with
      | some s => s!" — {mdEscape (docSummary (some s))}"
      | none => ""
    s!"- [{m.name}](#module-{m.name}) ({es.size} declaration{if es.size == 1 then "" else "s"}){summary}"
  let sections := d.sections.toList.map fun (m, es) =>
    let doc := match moduleDocOf m.src with
      | some s => s!"<a id=\"module-{htmlEscape m.name}\"></a>\n" ++ s!"<div class=\"doc\">{render (fun c => d.href? c) s}</div>\n"
      | none => s!"<a id=\"module-{htmlEscape m.name}\"></a>\n"
    s!"\n## {m.name}\n\n" ++ doc ++ "\n" ++
    (if es.isEmpty then "No public declarations.\n" else
      "**In this module:**\n\n" ++ sectionToc es ++ "\n") ++
    String.join (es.toList.map fun e => "\n" ++ entryMarkdown d m e)
  s!"<!-- Generated by `wiz doc --lib --reference docs/reference`; do not edit by hand. -->\n" ++
  s!"# {d.title}\n\n" ++
  s!"Generated from the elaborated modules: {d.moduleCount} module{if d.moduleCount == 1 then "" else "s"}, " ++
  s!"{d.declCount} declaration{if d.declCount == 1 then "" else "s"}, " ++
  s!"{d.sigCount} signature{if d.sigCount == 1 then "" else "s"}, " ++
  s!"{d.ops.size} operator notation{if d.ops.size == 1 then "" else "s"}. " ++
  "The table of contents links every section and declaration; a name in a doc comment " ++
  "links to its entry. Regenerate with `wiz doc --lib --reference docs/reference`.\n\n" ++
  "## Contents\n\n" ++
  "- [Notation and precedence](#notation)\n" ++
  String.join (toc.map (· ++ "\n")) ++ "\n" ++
  "## Notation and precedence\n\n<a id=\"notation\"></a>\n\n" ++
  notationMarkdown d ++ "\n" ++
  String.join sections


/-! ## HTML

The same manual as a page of the site, so that a module page can link a declaration to
its entry. The signatures keep the pages' cross-links (to every module's page), and the
doc comments are the same Markdown. -/

def refChildHtml (c : Ctx) (k : Entry) : String :=
  let short := match k.name.splitOn "." |>.getLast? with
    | some s => s
    | none => k.name
  s!"<li class=\"{htmlEscape k.kind}\" id=\"{htmlEscape k.name}\">{sigBlock c k short}{docHtml c k.doc}</li>"

def refInstancesHtml (_c : Ctx) (d : Data) (e : Entry) : String :=
  let is := d.instancesFor e
  if is.isEmpty then "" else
  let what := if e.kind == "class" then "Instances of this class" else "Instances for this type"
  let items := is.toList.map fun i =>
    let name := match d.href? i with
      | some h => s!"<a href=\"{htmlEscape h}\"><code>{htmlEscape i}</code></a>"
      | none => s!"<code>{htmlEscape i}</code>"
    s!"<li>{name} : <code>{htmlEscape (d.instanceSigOf i)}</code></li>"
  s!"<details class=\"instances\"><summary>{what} ({is.size})</summary><ul>{String.join items}</ul></details>"

def refEntryHtml (c : Ctx) (o : Options) (m : Module) (d : Data) (e : Entry) : String :=
  let kids := if e.children.isEmpty then "" else
    let what := if e.children.all (·.kind == "field") then "Fields" else
      if e.children.all (·.kind == "constructor") then "Constructors" else "Constructors and fields"
    s!"<div class=\"children\"><div class=\"children-title\">{what}</div><ul>" ++
    String.join (e.children.toList.map fun k => refChildHtml c k) ++ "</ul></div>"
  s!"<div class=\"decl ref\" id=\"{htmlEscape e.name}\">" ++
  s!"<div class=\"decl-head\"><span class=\"kind\">{htmlEscape e.kind}</span> " ++
  s!"<a class=\"anchor\" href=\"#{htmlEscape e.name}\">{htmlEscape e.name}</a>{sourceLink o m e.line}</div>" ++
  sigBlock c e "" ++ docHtml c e.doc ++ kids ++ refInstancesHtml c d e ++ "</div>\n"

def refNotationHtml (d : Data) : String :=
  if d.ops.isEmpty then "<p class=\"nothing\">No operator notation is declared.</p>" else
  let rows := d.ops.toList.map fun o =>
    let exp := if o.expands.isEmpty then "" else s!"<code>{htmlEscape o.expands}</code>"
    let mod := if o.module.isEmpty then "" else
      s!"<a href=\"#module-{htmlEscape o.module}\">{htmlEscape o.module}</a>"
    s!"<tr><td class=\"op\"><code>{htmlEscape o.op}</code></td><td>{o.fixity}</td>" ++
    s!"<td class=\"num\">{o.prec}</td><td>{o.assoc}</td><td>{exp}</td><td>{mod}</td></tr>"
  s!"<table class=\"api-table notation\"><thead><tr><th>operator</th><th>fixity</th>" ++
  s!"<th>precedence</th><th>associativity</th><th>expands to</th><th>module</th></tr></thead>" ++
  s!"<tbody>{String.join rows}</tbody></table>"

def refSectionHtml (o : Options) (d : Data) (mods : List String) (m : Module) (es : Array Entry)
    (st : St) : String :=
  let c : Ctx := { st, modules := mods, current := "" }
  let count := es.foldl (fun n e => n + 1 + e.children.size) 0
  s!"<section class=\"ref-module\" id=\"module-{htmlEscape m.name}\">" ++
  s!"<h2><a href=\"{htmlEscape (pageOf m.name)}\">{htmlEscape m.name}</a> " ++
  s!"<span class=\"count\">{count} signature{if count == 1 then "" else "s"}</span></h2>" ++
  docHtml c (moduleDocOf m.src) ++
  (if es.isEmpty then "<p class=\"nothing\">No public declarations.</p>" else
    String.join (es.toList.map fun e => refEntryHtml c o m d e)) ++
  "</section>\n"

/-- The reference page of the site. -/
def html (o : Options) (d : Data) (states : Array St) (mods : List String) : String :=
  let sections := d.sections.toList.zipIdx.map fun ((m, es), i) =>
    let st := match states[i]? with | some st => st | none => ({} : St)
    refSectionHtml o d mods m es st
  let mp := if d.moduleCount == 1 then "" else "s"
  let dp := if d.declCount == 1 then "" else "s"
  let sp := if d.sigCount == 1 then "" else "s"
  head o s!"Reference — {o.title}" false ++ nav mods "" ++
  s!"<main class=\"reference\"><h1>Reference manual</h1>" ++
  s!"<p class=\"lede\">{d.moduleCount} module{mp}, {d.declCount} declaration{dp}, " ++
  s!"{d.sigCount} signature{sp}, {d.ops.size} operator notation{if d.ops.size == 1 then "" else "s"}. " ++
  s!"Every declaration with its full signature (implicit arguments included), its doc " ++
  s!"comment and the instances of its class, plus the notation table. " ++
  s!"<a href=\"index.html\">Back to the modules</a>; every module page links here.</p>" ++
  s!"<h2 id=\"notation\">Notation and precedence</h2>" ++ refNotationHtml d ++
  String.join sections ++ "</main>\n</body></html>\n"

end Reference
end Wiz.Doc
