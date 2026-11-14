import Wiz.LSP
import Wiz.Doc.Markdown
import Wiz.Parser.DocComment

/-!
# scroll: the documentation generator (stage 11s)

`wiz doc` makes a static site from a set of modules: one page per module, every
declaration with its kind, its signature (the infoview's tagged printer,
`Term.prettyTagged`), its doc comment (Markdown), a link to its source, the instances of
each class and for each type, cross-links on every constant of a signature, a search
index (`search.js`) and a grouped index page (the language, each library prefix and
`Library`) with stable group anchors and breadcrumbs. See `wiz-notes/scroll.md` and
`docs/stages/11-tooling.md`, 11s.

Each page is complete HTML (readable without JS). It also carries its data as JSON: per
declaration its signature as tagged text (the infoview protocol's format) and the table
of its subterms in the shape of a `wiz/subtermInfo` answer (kind, name, text, type,
definition), precomputed since there is no server. `scroll.js` hands that to the web
infoview's Wasm module (`web/Web.wiz`, whose doc page model is `lib/Tagged.wiz`, shared
with the infoview), which renders the signatures as interactive tagged text.
-/

namespace Wiz.Doc

open Lean (Json)

abbrev St := CommandState ZeroOneMany

/-- A module to document. -/
structure Module where
  name : String
  /-- its source, and its path relative to its module root (for source links) -/
  src : String
  rel : String

structure Options where
  out : System.FilePath
  /-- source links: this, then the path relative to the root, then `#L<line>` -/
  sourceUrl : Option String := none
  title : String := "Wiz documentation"
  /-- the Wasm module and its JS (`web/build.sh`'s output) -/
  web : Option System.FilePath := none
  /-- the site's own files (scroll.css, scroll.js, tagged.js): `web/` of the checkout,
  or share/wiz/web -/
  assets : Option System.FilePath := none

/-- A page's file name. -/
def pageOf (m : String) : String := s!"{m}.html"

/-- The section of the index a module is listed under: the language's `Prelude` and `Std`
alone, the first component of a dotted name (`Hdl`, `Scry`, …), and `Library` for the
rest. -/
def groupOf (m : String) : String :=
  match m.splitOn "." with
  | [one] => if one == "Prelude" || one == "Std" then one else "Library"
  | g :: _ => g
  | [] => "Library"

/-- The index's group order: `Prelude`, `Std`, the libraries (by name), `Library`. -/
def groupRank (g : String) : Nat × String :=
  if g == "Prelude" then (0, "") else if g == "Std" then (1, "") else
  if g == "Library" then (3, "") else (2, g)

/-- A group's stable anchor on the index page. -/
def groupAnchor (g : String) : String := s!"group-{g}"

/-- The modules grouped for the index and the navigation, each group's modules sorted. -/
def groupModules (ms : List String) : List (String × List String) :=
  let groups := (ms.map groupOf).eraseDups.mergeSort (fun a b =>
    let ra := groupRank a
    let rb := groupRank b
    ra.1 < rb.1 || (ra.1 == rb.1 && ra.2 ≤ rb.2))
  groups.map fun g => (g, (ms.filter (groupOf · == g)).mergeSort (· ≤ ·))

/-- The first paragraph of a module doc that is not a heading, as plain text. -/
def summaryText (doc : Option String) : String :=
  match doc with
  | some d =>
    let p := ((d.splitOn "\n\n").find? fun (p : String) => !p.startsWith "#").getD ""
    (p.replace "\n" " ").take 160 |>.toString
  | none => ""

/-- What the elaborator makes for its own use, and private names: not documented. -/
def hidden (n : Name) (d? : Option DeclDoc) : Bool :=
  n.startsWith "_private." || LSP.auxiliaryDecl n || (d?.map (·.kind == "auxiliary")).getD false

/-- One declaration's page data and HTML. -/
structure Entry where
  name : Name
  kind : String
  doc : Option String
  line : Nat
  /-- the DOM id of its signature (`sig-N`), and the signature as JSON (`sig`, `subs`) -/
  sigId : String
  data : Json
  /-- the fallback signature (links, no tags) -/
  sigHtml : String
  children : Array Entry := #[]
  instances : Array Name := #[]

/-- The context the pages are made in: where every documented name is. -/
structure Ctx where
  st : St
  /-- documented modules (names are linked only to these) -/
  modules : List String
  /-- the module being documented -/
  current : String

/-- Where a constant is documented: `M.html#n`, if it is. -/
def Ctx.href? (c : Ctx) (n : Name) : Option String := do
  let (_, m) ← c.st.declSites.get? n
  unless c.modules.contains m do none
  if hidden n (c.st.declDocs.get? n) || c.st.globals.privates.contains n then none
  pure (if m == c.current then s!"#{n}" else s!"{pageOf m}#{n}")

/-- Tagged text as HTML for readers without JS: text, and a link on every documented
constant. -/
partial def fallbackHtml (c : Ctx) (subs : Array (Subterm ZeroOneMany)) : TT → String
  | .text s => htmlEscape s
  | .append xs => String.join (xs.toList.map (fallbackHtml c subs))
  | .tag id t =>
    let inner := fallbackHtml c subs t
    match subs[id]? with
    | some { kind := "const", name := some n, .. } => match c.href? n with
      | some h => s!"<a href=\"{htmlEscape h}\">{inner}</a>"
      | none => inner
    | _ => inner

/-- A subterm as a `wiz/subtermInfo` answer, precomputed: the type as text, the
definition as a link. -/
def subJson (c : Ctx) (sub : Subterm ZeroOneMany) : Json :=
  let ty := match LSP.subtermType c.st.globals sub with
    | some t => Json.str (t.pretty sub.names (some c.st.globals))
    | none => Json.null
  let defn := match sub.kind, sub.name with
    | "const", some n => match c.href? n, c.st.declSites.get? n with
      | some h, some (_, m) => Json.mkObj [("href", h), ("uri", (if m.isEmpty then c.current else m) ++ "." ++ n)]
      | _, _ => Json.null
    | _, _ => Json.null
  Json.mkObj [("kind", sub.kind), ("name", match sub.name with | some n => Json.str n | none => Json.null),
    ("text", sub.term.pretty sub.names (some c.st.globals)), ("type", ty), ("definition", defn)]

/-- The name as shown: with its universe parameters. -/
def shownName (d : Decl ZeroOneMany) : String :=
  if d.levelParams.isEmpty then d.name else s!"{d.name}.\{{" ".intercalate d.levelParams}}"

/-- The kind of a declaration, as shown. -/
def kindOf (st : St) (n : Name) : String :=
  if st.instances.any (·.name == n) then "instance" else
  if st.classes.any (·.name == n) then "class" else
  match st.declDocs.get? n with
  | some d => d.kind
  | none => "def"

/-- The constants at the heads of an instance's class arguments (`Add Nat`: `Nat`). -/
def instanceTypes (t : Term ZeroOneMany) : List Name :=
  let rec body : Term ZeroOneMany → Term ZeroOneMany
    | .pi _ _ _ _ b _ => body b
    | t => t
  let rec spine : Term ZeroOneMany → Term ZeroOneMany × List (Term ZeroOneMany)
    | .app f a => let (h, as) := spine f; (h, as ++ [a])
    | t => (t, [])
  let (_, args) := spine (body t)
  args.filterMap fun a => match (spine a).1 with
    | .const n _ => some n
    | .mu _ _ _ _ _ (some (n, _, _)) | .nu _ _ _ _ _ (some (n, _, _)) => some n
    | _ => none

/-- Make the entry of declaration `n`; `counter` numbers the signatures. -/
def entry (c : Ctx) (src : String) (n : Name) (counter : Nat) : Option Entry := do
  let d ← c.st.globals.find? n
  let (site, _) ← c.st.declSites.get? n
  let (tt, subs) := (d.type.prettyTagged [] [] (some c.st.globals)).run #[]
  let sigId := s!"sig-{counter}"
  let data := Json.mkObj [("id", sigId), ("name", n), ("sig", LSP.ttJson subs 0 tt),
    ("subs", Json.arr (subs.map (subJson c)))]
  let dd := c.st.declDocs.get? n
  let start := match dd with
    | some d => if d.start > 0 then d.start else site.start
    | none => site.start
  pure { name := n, kind := kindOf c.st n, doc := dd.bind (·.doc), line := (lineCol src start).1 + 1,
         sigId, data, sigHtml := fallbackHtml c subs tt }

/-- The documented declarations of the module (in source order), with their
constructors and fields. -/
def entries (c : Ctx) (src : String) : Array Entry := Id.run do
  let st := c.st
  let mine := st.globals.order.filter fun n => match st.declSites.get? n with
    | some (_, m) => m == c.current
    | none => false
  let mut out : Array Entry := #[]
  let mut k := 0
  -- the instances of each class and for each type
  let mut forClass : Std.HashMap Name (Array Name) := {}
  let mut forType : Std.HashMap Name (Array Name) := {}
  for i in st.instances do
    if i.name.startsWith "_private." then continue
    forClass := forClass.insert i.cls ((forClass.getD i.cls #[]).push i.name)
    if let some d := st.globals.find? i.name then
      for t in (instanceTypes d.type).eraseDups do
        forType := forType.insert t ((forType.getD t #[]).push i.name)
  for n in mine do
    let dd := st.declDocs.get? n
    if hidden n dd || st.globals.privates.contains n then continue
    -- (constructors and fields are shown with their type)
    if (dd.bind (·.parent)).isSome then continue
    let some e := entry c src n k | continue
    k := k + 1
    let mut kids : Array Entry := #[]
    for m in mine do
      if (st.declDocs.get? m).bind (·.parent) == some n then
        if let some ke := entry c src m k then
          kids := kids.push ke
          k := k + 1
    let insts := (forClass.getD n #[]) ++ (forType.getD n #[])
    out := out.push { e with children := kids, instances := insts.toList.eraseDups.toArray }
  out

/-! ## HTML -/

/-- Code in backticks in a doc comment links to the declaration it names. -/
def docLink (c : Ctx) (code : String) : Option String :=
  c.href? code

def docHtml (c : Ctx) (doc : Option String) : String :=
  match doc with
  | some d => s!"<div class=\"doc\">{render (docLink c) d}</div>"
  | none => ""

def sourceLink (o : Options) (m : Module) (line : Nat) : String :=
  match o.sourceUrl with
  | some u => s!"<a class=\"src\" href=\"{htmlEscape u}{htmlEscape m.rel}#L{line}\">source</a>"
  | none => s!"<span class=\"src\">{htmlEscape m.rel}:{line}</span>"

def instancesHtml (c : Ctx) (is : Array Name) : String :=
  if is.isEmpty then "" else
  let links := is.toList.map fun i => match c.href? i with
    | some h => s!"<a href=\"{htmlEscape h}\"><code>{htmlEscape i}</code></a>"
    | none => s!"<code>{htmlEscape i}</code>"
  s!"<details class=\"instances\"><summary>Instances ({is.size})</summary><ul>{String.join (links.map (s!"<li>{·}</li>"))}</ul></details>"

def sigBlock (c : Ctx) (e : Entry) (short : String) : String :=
  let d? := c.st.globals.find? e.name
  let shown := match d? with
    | some d => if short.isEmpty then shownName d else short
    | none => e.name
  s!"<pre class=\"sig\"><code><span class=\"decl-name\">{htmlEscape shown}</span> : <span class=\"sig-type\" id=\"{e.sigId}\">{e.sigHtml}</span></code></pre>"

def entryHtml (c : Ctx) (o : Options) (m : Module) (e : Entry) : String :=
  let kids := if e.children.isEmpty then "" else
    let items := e.children.toList.map fun k =>
      let short := match k.name.splitOn "." |>.getLast? with
        | some s => s
        | none => k.name
      s!"<li class=\"{htmlEscape k.kind}\" id=\"{htmlEscape k.name}\">{sigBlock c k short}{docHtml c k.doc}</li>"
    let what := if e.children.all (·.kind == "field") then "Fields" else
      if e.children.all (·.kind == "constructor") then "Constructors" else "Constructors and fields"
    s!"<div class=\"children\"><div class=\"children-title\">{what}</div><ul>{String.join items}</ul></div>"
  s!"<div class=\"decl\" id=\"{htmlEscape e.name}\" data-kind=\"{htmlEscape e.kind}\">" ++
  s!"<div class=\"decl-head\"><span class=\"kind\">{htmlEscape e.kind}</span> <a class=\"anchor\" href=\"#{htmlEscape e.name}\">{htmlEscape e.name}</a>{sourceLink o m e.line}</div>" ++
  sigBlock c e "" ++ docHtml c e.doc ++ kids ++ instancesHtml c e.instances ++ "</div>\n"

/-- JSON inside `<script>`: `</` can't end the element. -/
def scriptJson (j : Json) : String := (j.compress.replace "</" "<\\/")

def head (o : Options) (title : String) (wasm : Bool) : String :=
  s!"<!doctype html>\n<html lang=\"en\"><head><meta charset=\"utf-8\">" ++
  s!"<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">" ++
  s!"<title>{htmlEscape title}</title><link rel=\"stylesheet\" href=\"scroll.css\">" ++
  -- the search (a classic script: it works from file:// too), and with the Wasm module
  -- the interactive signatures (a module script: needs http)
  "<script src=\"search.js\" defer></script><script src=\"scroll-search.js\" defer></script>" ++
  (if wasm then "<script type=\"module\" src=\"scroll.js\"></script>" else "") ++
  s!"</head><body>\n<header><a class=\"site\" href=\"index.html\">{htmlEscape o.title}</a>" ++
  "<input id=\"search\" type=\"search\" placeholder=\"Search modules and declarations\" autocomplete=\"off\" aria-label=\"Search modules and declarations\">" ++
  "<div id=\"results\" hidden></div></header>\n"

def nav (mods : List String) (current : String) : String :=
  let groups := groupModules mods
  let body := groups.map fun (g, ms) =>
    let items := ms.map fun m =>
      let cls := if m == current then " class=\"current\"" else ""
      s!"<li><a{cls} href=\"{htmlEscape (pageOf m)}\">{htmlEscape m}</a></li>"
    s!"<div class=\"nav-group\"><a href=\"index.html#{htmlEscape (groupAnchor g)}\">{htmlEscape g}</a></div>" ++
    s!"<ul>{String.join items}</ul>"
  s!"<nav><div class=\"nav-title\">Modules</div>{String.join body}</nav>\n"

/-- Where a module sits: the site, its group on the index, then the module. -/
def crumbs (o : Options) (m : String) : String :=
  let g := groupOf m
  s!"<div class=\"crumbs\" role=\"navigation\" aria-label=\"Breadcrumb\">" ++
  s!"<a href=\"index.html\">{htmlEscape o.title}</a><span class=\"sep\">/</span>" ++
  s!"<a href=\"index.html#{htmlEscape (groupAnchor g)}\">{htmlEscape g}</a><span class=\"sep\">/</span>" ++
  s!"<span aria-current=\"page\">{htmlEscape m}</span></div>\n"

def modulePage (c : Ctx) (o : Options) (m : Module) (es : Array Entry) (wasm : Bool) : String :=
  let data := Json.mkObj [("module", m.name), ("decls", Json.arr (es.flatMap fun e => #[e.data] ++ e.children.map (·.data)))]
  let toc := es.toList.map fun e => s!"<li><a href=\"#{htmlEscape e.name}\">{htmlEscape e.name}</a></li>"
  head o s!"{m.name} — {o.title}" wasm ++ nav c.modules m.name ++
  s!"<main>{crumbs o m.name}<h1>{htmlEscape m.name}</h1>" ++ s!"<div class=\"module-src\">{sourceLink o m 1}</div>" ++
  docHtml c (moduleDocOf m.src) ++
  (if es.isEmpty then "<p class=\"nothing\">No public declarations.</p>" else "") ++
  String.join (es.toList.map (entryHtml c o m)) ++
  s!"</main><aside class=\"toc\"><div class=\"nav-title\">On this page</div><ul>{String.join toc}</ul></aside>" ++
  "<div id=\"info\" hidden></div>" ++
  s!"<script type=\"application/json\" id=\"wiz-doc-data\">{scriptJson data}</script>\n</body></html>\n"

def indexPage (o : Options) (mods : List (String × Option String × Nat)) (wasm : Bool) : String :=
  let names := mods.map (·.1)
  let groups := groupModules names
  let totalDecls := mods.foldl (fun acc (_, _, n) => acc + n) 0
  let summaryOf (m : String) : String :=
    match mods.find? (·.1 == m) with
    | some (_, some d, _) =>
      -- (the first paragraph that is not a heading)
      inline (fun _ => none) ((((d.splitOn "\n\n").find? fun (p : String) => !p.startsWith "#").getD "").replace "\n" " ")
    | _ => ""
  let countOf (m : String) : Nat :=
    match mods.find? (·.1 == m) with
    | some (_, _, n) => n
    | none => 0
  let toc := groups.map fun (g, ms) =>
    s!"<a href=\"#{htmlEscape (groupAnchor g)}\">{htmlEscape g} <span class=\"count\">{ms.length}</span></a>"
  let sections := groups.map fun (g, ms) =>
    let items := ms.map fun m =>
      let n := countOf m
      let plural := if n == 1 then "" else "s"
      s!"<li><a class=\"module\" href=\"{htmlEscape (pageOf m)}\">{htmlEscape m}</a>" ++
      s!"<span class=\"decl-count\">{n} declaration{plural}</span>" ++
      s!"<div class=\"summary\">{summaryOf m}</div></li>"
    s!"<section class=\"group\" id=\"{htmlEscape (groupAnchor g)}\">" ++
    s!"<h2><a href=\"#{htmlEscape (groupAnchor g)}\">{htmlEscape g}</a>" ++
    s!" <span class=\"count\">{ms.length} module{(if ms.length == 1 then "" else "s")}</span></h2>" ++
    s!"<ul class=\"modules\">{String.join items}</ul></section>"
  let plural := if names.length == 1 then "" else "s"
  head o o.title wasm ++ nav names "" ++
  s!"<main class=\"index\"><h1>{htmlEscape o.title}</h1>" ++
  s!"<p class=\"lede\">{names.length} module{plural}, {totalDecls} declarations. " ++
  s!"Search by name from the box above, or browse a group.</p>" ++
  s!"<div class=\"group-nav\">{String.join toc}</div>" ++
  String.join sections ++ "</main>\n</body></html>\n"

/-- The search index: every documented module and declaration (name, module, kind, the
first line of its doc), as a script (so that it loads from `file://` too). A module row's
`kind` is `module`, and `scroll-search.js` links it to its page rather than an anchor. -/
def searchJs (rows : Array Json) : String :=
  s!"window.wizSearchIndex = {(Json.arr rows).compress};\n"

/-- Copy a file if it exists; whether it did. -/
def copyIf (src dst : System.FilePath) : IO Bool := do
  if ← src.pathExists then
    IO.FS.writeBinFile dst (← IO.FS.readBinFile src); pure true
  else pure false

/-- Make the site. `elabMod m` elaborates `import m` (with the module roots that find every
module of `mods`). Returns the number of pages made. -/
def run (elabMod : String → IO St) (mods : Array Module) (o : Options) : IO Nat := do
  IO.FS.createDirAll o.out
  let names := mods.toList.map (·.name)
  -- the Wasm module and the site's scripts
  let mut wasm := false
  if let some w := o.web then
    if ← (w / "wiz-infoview.mjs").pathExists then
      for f in ["wiz-infoview.mjs", "wiz-infoview.wasm"] do
        discard <| copyIf (w / f) (o.out / f)
      wasm := true
  if let some a := o.assets then
    for f in ["scroll.css", "scroll.js", "tagged.js", "scroll-search.js"] do
      discard <| copyIf (a / f) (o.out / f)
  let mut rows : Array Json := #[]
  let mut summaries : Array (String × Option String × Nat) := #[]
  for m in mods do
    let st ← elabMod m.name
    for msg in st.messages do
      if msg.severity == .error then IO.eprintln s!"{m.name}: {msg.text}"
    let c : Ctx := { st, modules := names, current := m.name }
    let es := entries c m.src
    IO.FS.writeFile (o.out / pageOf m.name) (modulePage c o m es wasm)
    IO.FS.writeFile (o.out / s!"{m.name}.json")
      (Json.mkObj [("module", m.name), ("decls", Json.arr (es.flatMap fun e => #[e.data] ++ e.children.map (·.data)))]).compress
    let doc := moduleDocOf m.src
    let decls := es.foldl (fun acc e => acc + 1 + e.children.size) 0
    summaries := summaries.push (m.name, doc, decls)
    -- (the module itself is searchable: its page, its summary)
    rows := rows.push (Json.mkObj [("n", m.name), ("m", m.name), ("k", "module"), ("d", summaryText doc)])
    for e in es do
      for x in #[e] ++ e.children do
        let first := match x.doc with
          | some d => (d.splitOn "\n\n").headD "" |>.replace "\n" " "
          | none => ""
        rows := rows.push (Json.mkObj [("n", x.name), ("m", m.name), ("k", x.kind), ("d", (first.take 160).toString)])
  IO.FS.writeFile (o.out / "search.js") (searchJs rows)
  IO.FS.writeFile (o.out / "index.html") (indexPage o summaries.toList wasm)
  pure mods.size

end Wiz.Doc
