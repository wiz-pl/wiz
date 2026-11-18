import Wiz.LSP
import Wiz.Doc.Markdown
import Wiz.Parser.DocComment

/-!
# scroll: the documentation generator (stage 11s)

`wiz doc` makes a static site from a set of modules: one page per module, every
declaration with its kind, its signature (the infoview's tagged printer,
`Term.prettyTagged`), its doc comment (Markdown), a link to its source, the instances of
each class and for each type, cross-links on every constant of a signature, an API
index (`api.html`, `api.json`) of every module and declaration, a search index
(`search.js`, over names, doc comments and signatures) and a landing page. See
`wiz-notes/scroll.md` and `docs/stages/11-tooling.md`, 11s.

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
  /-- where the site's own files are (scroll.css, scroll.js, tagged.js, and with
  `--serve` lsp-client.js, goals.js, doc-live.js, doc-live.css): searched in order,
  `web/` of a checkout or share/wiz/web of a release -/
  assets : List System.FilePath := []
  /-- (11s) `--serve`: the pages carry the live documentation client, which asks a
  `wiz lsp --ws` for a declaration's type and doc in a panel -/
  serve : Bool := false
  /-- the port of the language server (`--lsp PORT`); `none`: the client stays inert -/
  lsp : Option Nat := none
  /-- write the reference manual (`Reference.markdown`) to this directory (`--reference`) -/
  reference : Option System.FilePath := none
  /-- with `--reference`: write nothing, and report the files that differ (`--check`) -/
  check : Bool := false
  /-- the manual's own title (`--title`, else "Wiz standard library reference") -/
  referenceTitle : String := "Wiz standard library reference"

/-- What `run` made: the site's pages, the reference files that are not up to date (with
`--check`), and the reference files it wrote. -/
structure RunResult where
  pages : Nat
  /-- the reference manual files that differ from what the modules say (paths) -/
  stale : Array String := #[]
  /-- the committed manual that was written (empty when `--check` wrote nothing) -/
  written : Array String := #[]
  deriving Inhabited

/-- A page's file name. -/
def pageOf (m : String) : String := s!"{m}.html"

/-- What the elaborator makes for its own use, and private names: not documented. -/
def hidden (n : Name) (d? : Option DeclDoc) : Bool :=
  n.startsWith "_private." || LSP.auxiliaryDecl n || (d?.map (·.kind == "auxiliary")).getD false

/-- One declaration's page data and HTML. -/
structure Entry where
  name : Name
  kind : String
  doc : Option String
  line : Nat
  /-- where the declaration's name is: 0-based line and column, for the live client -/
  line0 : Nat
  col : Nat
  /-- the DOM id of its signature (`sig-N`), and the signature as JSON (`sig`, `subs`) -/
  sigId : String
  data : Json
  /-- the fallback signature (links, no tags) -/
  sigHtml : String
  /-- the signature as tagged text and its subterms, so that it can be rendered again in
  another context (the API index: every signature links to its module's page) -/
  tt : TT
  subs : Array (Subterm ZeroOneMany)
  /-- the signature as plain text, for the search index -/
  sigText : String
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
    | .mu _ _ _ _ _ (some (n, _, _)) _ | .nu _ _ _ _ _ (some (n, _, _)) => some n
    | _ => none

/-- The character offset of the declaration's name in the command at `site`: the last
component of the name as written (`Shape.area` → `area`, `Point.x` → `x`), or the
command's start when it is not there (a constructor, whose name is generated). -/
def identOffset (src : String) (site : SourceInfo) (n : Name) : Nat :=
  let stop := if site.stop > site.start then site.stop else site.start
  let text := String.ofList ((src.toList.drop site.start).take (stop - site.start))
  let name := s!"{n}"
  let last := ((name.splitOn ".").getLast?).getD name
  if last.isEmpty then site.start else
  let before := (text.splitOn last).headD ""
  if before.length < text.length then site.start + before.length else site.start

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
  let (line0, _) := lineCol src start
  let col := (lineCol src (identOffset src site n)).2
  pure { name := n, kind := kindOf c.st n, doc := dd.bind (·.doc), line := line0 + 1, line0, col,
         sigId, data, sigHtml := fallbackHtml c subs tt, tt, subs, sigText := tt.flatten }

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
      let md := st.declDocs.get? m
      -- (a private constructor or field is not documented either)
      if (md.bind (·.parent)) == some n && !hidden m md &&
          !st.globals.privates.contains m then
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

/-- (11s) With `--serve`, where the declaration's name is in its module's source: the
live client asks the language server about that position. Empty otherwise, so a plain
`wiz doc` page is exactly the static one. -/
def declAttrs (o : Options) (e : Entry) : String :=
  if o.serve then s!" data-doc-line=\"{e.line0}\" data-doc-col=\"{e.col}\"" else ""

def entryHtml (c : Ctx) (o : Options) (m : Module) (e : Entry) : String :=
  let kids := if e.children.isEmpty then "" else
    let items := e.children.toList.map fun k =>
      let short := match k.name.splitOn "." |>.getLast? with
        | some s => s
        | none => k.name
      s!"<li class=\"{htmlEscape k.kind}\" id=\"{htmlEscape k.name}\"{declAttrs o k}>{sigBlock c k short}{docHtml c k.doc}</li>"
    let what := if e.children.all (·.kind == "field") then "Fields" else
      if e.children.all (·.kind == "constructor") then "Constructors" else "Constructors and fields"
    s!"<div class=\"children\"><div class=\"children-title\">{what}</div><ul>{String.join items}</ul></div>"
  s!"<div class=\"decl\" id=\"{htmlEscape e.name}\" data-kind=\"{htmlEscape e.kind}\"{declAttrs o e}>" ++
  s!"<div class=\"decl-head\"><span class=\"kind\">{htmlEscape e.kind}</span> <a class=\"anchor\" href=\"#{htmlEscape e.name}\">{htmlEscape e.name}</a>" ++
  s!"<a class=\"ref\" href=\"reference.html#{htmlEscape e.name}\">reference</a>{sourceLink o m e.line}</div>" ++
  sigBlock c e "" ++ docHtml c e.doc ++ kids ++ instancesHtml c e.instances ++ "</div>\n"

/-- The first paragraph of a doc comment that is not a heading, as plain text. -/
def docSummary (doc : Option String) : String :=
  match doc with
  | some d =>
    let p := ((d.splitOn "\n\n").find? fun (p : String) => !p.startsWith "#").getD ""
    (p.replace "\n" " ").trimAscii.toString
  | none => ""

/-- A doc comment as one line of plain text, for the search index. -/
def docText (doc : Option String) : String :=
  match doc with
  | some d => (d.replace "\n" " ").trimAscii.toString
  | none => ""

/-- Where a declaration is documented: always its module's page, even from `api.html`. -/
def apiHref (m : Module) (e : Entry) : String := s!"{pageOf m.name}#{e.name}"

/-- One declaration in the API index: kind, name, signature (with cross-links) and the
first paragraph of its doc. -/
def apiRow (c : Ctx) (m : Module) (e : Entry) (child : Bool) : String :=
  let cls := if child then "api-decl child" else "api-decl"
  s!"<tr class=\"{cls}\" id=\"api-{htmlEscape e.name}\">" ++
  s!"<td class=\"kind\">{htmlEscape e.kind}</td>" ++
  s!"<td class=\"name\"><a href=\"{htmlEscape (apiHref m e)}\"><code>{htmlEscape e.name}</code></a></td>" ++
  s!"<td class=\"api-sig\"><code>{fallbackHtml c e.subs e.tt}</code></td>" ++
  s!"<td class=\"summary\">{inline (docLink c) ((docSummary e.doc).take 200 |>.toString)}</td></tr>"

/-- A module's section of the API index: every declaration and its constructors or
fields, with links back to the module page. -/
def apiSection (c : Ctx) (m : Module) (es : Array Entry) : String :=
  let count := es.foldl (fun n e => n + 1 + e.children.size) 0
  let rows := es.toList.map fun e =>
    apiRow c m e false ++ String.join (e.children.toList.map fun k => apiRow c m k true)
  let plural := if count == 1 then "" else "s"
  s!"<section class=\"api-module\" id=\"module-{htmlEscape m.name}\">" ++
  s!"<h2><a href=\"{htmlEscape (pageOf m.name)}\">{htmlEscape m.name}</a>" ++
  s!" <span class=\"count\">{count} declaration{plural}</span></h2>" ++
  s!"<table class=\"api-table\"><thead><tr><th>kind</th><th>name</th><th>signature</th><th>docs</th></tr></thead>" ++
  s!"<tbody>{String.join rows}</tbody></table></section>\n"

/-- The API index's rows as JSON (`api.json`): the machine-readable form of `api.html`. -/
def apiRows (m : Module) (es : Array Entry) : Array Json :=
  es.flatMap fun e => (#[e] ++ e.children).map fun x =>
    Json.mkObj [("name", x.name), ("module", m.name), ("kind", x.kind),
      ("sig", x.sigText), ("doc", docText x.doc), ("href", apiHref m x)]

/-- JSON inside `<script>`: `</` can't end the element. -/
def scriptJson (j : Json) : String := (j.compress.replace "</" "<\\/")

def head (o : Options) (title : String) (wasm : Bool) (live : Bool := false) : String :=
  s!"<!doctype html>\n<html lang=\"en\"><head><meta charset=\"utf-8\">" ++
  s!"<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">" ++
  s!"<title>{htmlEscape title}</title><link rel=\"stylesheet\" href=\"scroll.css\">" ++
  (if live then "<link rel=\"stylesheet\" href=\"doc-live.css\">" else "") ++
  -- the search (a classic script: it works from file:// too), and with the Wasm module
  -- the interactive signatures (a module script: needs http)
  "<script src=\"search.js\" defer></script><script src=\"scroll-search.js\" defer></script>" ++
  (if wasm then "<script type=\"module\" src=\"scroll.js\"></script>" else "") ++
  s!"</head><body>\n<header><a class=\"site\" href=\"index.html\">{htmlEscape o.title}</a>" ++
  "<a class=\"api-link\" href=\"api.html\">API index</a>" ++
  "<a class=\"api-link\" href=\"reference.html\">Reference</a>" ++
  "<input id=\"search\" type=\"search\" placeholder=\"Search declarations, docs and signatures\" autocomplete=\"off\" aria-label=\"Search declarations, docs and signatures\">" ++
  "<div id=\"results\" hidden></div></header>\n"

def nav (mods : List String) (current : String) : String :=
  let items := mods.map fun m =>
    let cls := if m == current then " class=\"current\"" else ""
    s!"<li><a{cls} href=\"{htmlEscape (pageOf m)}\">{htmlEscape m}</a></li>"
  s!"<nav><div class=\"nav-title\">Modules</div><ul>{String.join items}</ul></nav>\n"

def modulePage (c : Ctx) (o : Options) (m : Module) (es : Array Entry) (wasm : Bool) : String :=
  let data := Json.mkObj [("module", m.name), ("decls", Json.arr (es.flatMap fun e => #[e.data] ++ e.children.map (·.data)))]
  let toc := es.toList.map fun e => s!"<li><a href=\"#{htmlEscape e.name}\">{htmlEscape e.name}</a></li>"
  -- (11s) the live client: where it asks, and the source it opens in the server
  let live := o.serve
  let serveData := Json.mkObj [("module", m.name), ("src", s!"sources/{m.name}.wiz"),
    ("lsp", match o.lsp with | some p => Json.str s!"ws://127.0.0.1:{p}" | none => Json.null)]
  head o s!"{m.name} — {o.title}" wasm live ++ nav c.modules m.name ++
  s!"<main><h1>{htmlEscape m.name}</h1>" ++
  s!"<div class=\"module-src\"><a class=\"ref\" href=\"reference.html#module-{htmlEscape m.name}\">reference</a> " ++
  s!"{sourceLink o m 1}</div>" ++
  docHtml c (moduleDocOf m.src) ++
  (if es.isEmpty then "<p class=\"nothing\">No public declarations.</p>" else "") ++
  String.join (es.toList.map (entryHtml c o m)) ++
  s!"</main><aside class=\"toc\"><div class=\"nav-title\">On this page</div><ul>{String.join toc}</ul></aside>" ++
  "<div id=\"info\" hidden></div>" ++
  s!"<script type=\"application/json\" id=\"wiz-doc-data\">{scriptJson data}</script>\n" ++
  (if live then
    s!"<script type=\"application/json\" id=\"wiz-doc-serve\">{scriptJson serveData}</script>\n" ++
    "<script type=\"module\" src=\"doc-live.js\"></script>\n"
   else "") ++
  "</body></html>\n"

def indexPage (o : Options) (mods : List (String × Option String)) : String :=
  let items := mods.map fun (m, doc) =>
    -- (the first paragraph that is not a heading)
    let summary := match doc with
      | some d => inline (fun _ => none) ((((d.splitOn "\n\n").find? fun (p : String) => !p.startsWith "#").getD "").replace "\n" " ")
      | none => ""
    s!"<li><a href=\"{htmlEscape (pageOf m)}\">{htmlEscape m}</a><div class=\"summary\">{summary}</div></li>"
  head o o.title false ++ nav (mods.map (·.1)) "" ++
  s!"<main><h1>{htmlEscape o.title}</h1>" ++
  s!"<p class=\"lede\">{mods.length} module{(if mods.length == 1 then "" else "s")}. " ++
  s!"Browse the <a href=\"api.html\">API index</a> for every declaration and signature, " ++
  s!"the <a href=\"reference.html\">reference manual</a> for full signatures, doc comments " ++
  s!"and the notation table, " ++
  s!"or search names, doc comments and signatures from the box above.</p>" ++
  s!"<ul class=\"modules\">{String.join items}</ul></main>\n</body></html>\n"

/-- The API/library index: every documented module with all its declarations, their
kinds, signatures (with the same cross-links as the pages) and doc summaries. It is
generated from the same data as `A.B.json` and written with them (`api.json`). -/
def apiPage (o : Options) (mods : List String) (sections : Array String)
    (moduleCount declCount : Nat) : String :=
  let mp := if moduleCount == 1 then "" else "s"
  let dp := if declCount == 1 then "" else "s"
  head o s!"API index — {o.title}" false ++ nav mods "" ++
  s!"<main class=\"api\"><h1>API index</h1>" ++
  s!"<p class=\"lede\">{moduleCount} module{mp}, {declCount} declaration{dp}. " ++
  s!"Every name links to its signature on its module page; the search box above also " ++
  s!"matches doc comments and signatures. <a href=\"index.html\">Back to the modules</a>; " ++
  s!"the same index is <a href=\"api.json\">api.json</a>.</p>" ++
  String.join sections.toList ++ "</main>\n</body></html>\n"

/-- The search index: every documented module and declaration, with its name, module,
kind, doc summary, signature text and target, as a script (so that it loads from
`file://` too). `scroll-search.js` matches names first, then doc comments and
signatures. -/
def searchJs (rows : Array Json) : String :=
  s!"window.wizSearchIndex = {(Json.arr rows).compress};\n"

/-- Copy `f` from the first of `dirs` that has it; whether one did. -/
def copyFirst (dirs : List System.FilePath) (f : String) (out : System.FilePath) : IO Bool := do
  for d in dirs do
    if ← (d / f).pathExists then
      IO.FS.writeBinFile (out / f) (← IO.FS.readBinFile (d / f))
      return true
  pure false

end Wiz.Doc
