import Wiz.Doc.Registry
import Wiz.Doc.Site
import Wiz.Doc.Reference

/-!
# Building the documentation site (stage 11s)

`run` is `wiz doc`: it makes the pages (`Site`), the reference page of the site and, with
`--reference`, the committed reference manual (`Reference`). It needs both, so it lives
here rather than in `Site` (which `Reference` reads). `elabMod m` elaborates `import m`
with the module roots that find every module of `mods`; the result counts the pages and
names the reference files that differ (`--check`).

Each module's page is made by `pieceOf`: elaborate it, then render its page, its JSON and
its rows of the API and search indexes. That work is independent per module, so `--jobs N`
runs a sliding window of `N` of them at once (`mapWindow`). Every output is assembled in
the modules' own order (the order `run` was given them), whichever finishes first, so the
files are byte-for-byte the same as `--jobs 1`; only the `-v` log follows completion order
(each line names its module, so a line is readable on its own).

`-v` writes the progress log to stderr and leaves stdout and the pages alone: the phase
boundaries, each module's elaboration and rendering time and its cache hits, the
declarations (every 25th with `-v`, every one with `-vv`), the write phase, and a final
summary with the wall time and (on Linux) the peak RSS.
-/

namespace Wiz.Doc

open Lean (Json)

/-- One module's finished work: everything its page and the shared indexes need, made
before anything is written. Holding this for every module is what lets `--jobs` write in
the modules' order. -/
structure Piece where
  module : Module
  st : St
  entries : Array Entry
  page : String
  /-- the page's data (`<module>.json`) -/
  json : String
  /-- the module's section of `api.html`, and its rows of `api.json` -/
  apiSection : String
  apiRows : Array Json
  /-- its rows of the search index -/
  rows : Array Json
  /-- the module's doc comment, for the landing page -/
  summary : Option String
  decls : Nat
  errors : Array String
  elabMs : Nat
  renderMs : Nat
  /-- cache hits reported by the elaborator (one per replayed command) -/
  hits : Nat

/-- The verbose log (`-v`, `-vv`): a line on stderr, never on stdout. -/
def say (o : Options) (s : String) : IO Unit :=
  if o.verbose > 0 then IO.eprintln s!"doc: {s}" else pure ()

def secs (ms : Nat) : String :=
  if ms < 1000 then s!"{ms}ms" else s!"{(ms / 100) / 10}.{((ms / 100) % 10)}s"

/-- Peak resident set size in KiB, from `/proc/self/status` (Linux); `none` elsewhere.
Cheap: one small read, once, at the end. -/
def peakRssKB : IO (Option Nat) := do
  try
    let text ← IO.FS.readFile "/proc/self/status"
    for line in text.splitOn "\n" do
      if line.startsWith "VmHWM:" then
        let digits := (line.drop 6).trimAscii.toString.toList.takeWhile (·.isDigit)
        if let some n := String.ofList digits |>.toNat? then return some n
    return none
  catch _ => return none

/-- Make one module's page and its rows of the shared indexes. -/
def pieceOf (o : Options) (mods : Array Module) (names : List String) (wasm : Bool)
    (elabMod : String → IO (St × Nat)) (i : Nat) (m : Module) : IO Piece := do
  let t0 ← IO.monoMsNow
  say o s!"[{i + 1}/{mods.size}] {m.name}: elaborate"
  let (st, hits) ← elabMod m.name
  let tElab ← IO.monoMsNow
  let errors := st.messages.filter (·.severity == .error) |>.map (·.text)
  for e in errors do IO.eprintln s!"{m.name}: {e}"
  let c : Ctx := { st, modules := names, current := m.name, highlight := o.highlight, registry := o.registry }
  let es := entries c m.src
  let decls := es.foldl (fun n e => n + 1 + e.children.size) 0
  if o.verbose > 1 then
    for e in es do
      for x in #[e] ++ e.children do
        IO.eprintln s!"doc: [{i + 1}/{mods.size}] {m.name} decl: {x.name} ({x.kind})"
  else if o.verbose > 0 then
    let mut k := 0
    for e in es do
      for x in #[e] ++ e.children do
        k := k + 1
        if k % 25 == 0 then
          IO.eprintln s!"doc: [{i + 1}/{mods.size}] {m.name} decl {k}/{decls}: {x.name} ({x.kind})"
  let page := modulePage c o m es wasm
  let json := (Json.mkObj [("module", m.name),
    ("decls", Json.arr (es.flatMap fun e => #[e.data] ++ e.children.map (·.data)))]).compress
  -- (the API index: all modules, every declaration, the same cross-links)
  let ac : Ctx := { st, modules := names, current := "" }
  let apiSection := apiSection ac m es
  let apiRows := apiRows m es
  -- (the search: the module itself, then its declarations)
  let doc := moduleDocOf m.src
  let mut rows : Array Json := #[Json.mkObj [("n", m.name), ("m", m.name), ("k", "module"),
    ("d", (docText doc).take 500 |>.toString), ("s", ""), ("u", pageOf m.name)]]
  for e in es do
    for x in #[e] ++ e.children do
      rows := rows.push (Json.mkObj [("n", x.name), ("m", m.name), ("k", x.kind),
        ("d", (docText x.doc).take 500 |>.toString),
        ("s", (x.sigText.take 500).toString), ("u", apiHref m x)])
  let tEnd ← IO.monoMsNow
  let elabMs := tElab - t0
  let renderMs := tEnd - tElab
  if o.verbose > 0 then
    IO.eprintln s!"doc: [{i + 1}/{mods.size}] {m.name}: done {secs (tEnd - t0)} \
      (elaborate {secs elabMs}, render {secs renderMs}), {decls} declaration(s), \
      {hits} cache hit(s)"
  pure { module := m, st, entries := es, page, json, apiSection, apiRows, rows,
         summary := doc, decls, errors, elabMs, renderMs, hits }

/-- `f` over `xs`, at most `jobs` at once and with the results in `xs`' order. A sliding
window (not chunks): when one finishes, the next starts, so a slow module does not idle
the other slots. The first failure is returned after the tasks in flight are joined. -/
partial def mapWindow (jobs : Nat) (xs : Array α) (f : α → IO β) : IO (Array β) := do
  let k := max 1 jobs
  let mut pending : List (Task (Except IO.Error β)) := []
  let mut next := 0
  let mut out : Array β := #[]
  let mut failure : Option IO.Error := none
  while next < xs.size || !pending.isEmpty do
    let mut filling := true
    while filling && pending.length < k do
      match xs[next]? with
      | some x =>
        pending := pending ++ [← IO.asTask (prio := .dedicated) (f x)]
        next := next + 1
      | none => filling := false
    match pending with
    | t :: rest =>
      pending := rest
      match t.get with
      | .ok b => out := out.push b
      | .error e => if failure.isNone then failure := some e
    | [] => pure ()
  match failure with
  | some e => throw e
  | none => pure out

def run (elabMod : String → IO (St × Nat)) (mods : Array Module) (o : Options) : IO RunResult := do
  let tAll ← IO.monoMsNow
  -- the language registry: built-ins, then `--languages` files, then the host hook
  let registry ← Wiz.Doc.Registry.loadFiles ((← Wiz.Doc.Registry.envFiles) ++ o.languages)
  let o : Options := { o with registry := registry }
  IO.FS.createDirAll o.out
  let names := mods.toList.map (·.name)
  -- the Wasm module and the site's scripts
  let mut wasm := false
  if let some w := o.web then
    if ← (w / "wiz-infoview.mjs").pathExists then
      for f in ["wiz-infoview.mjs", "wiz-infoview.wasm"] do
        discard <| copyFirst [w] f o.out
      wasm := true
  for f in ["scroll.css", "highlight.css", "scroll.js", "scroll-search.js"] do
    discard <| copyFirst o.assets f o.out
  -- The pages' runtimes: the search's and, with --serve, the live panel's. They are
  -- optional, like the Wasm module: a page without them stays static (the search box
  -- says the runtime is missing).
  for f in ["wiz-docs-ui.mjs", "wiz-doc-live-ui.mjs"] do
    discard <| copyFirst o.assets f o.out
  -- the mount contract the two runtimes share (`framework/mount.js` and its imports)
  IO.FS.createDirAll (o.out / "framework")
  for f in ["mount.js", "driver.js", "runtime.js"] do
    discard <| copyFirst (o.assets.map (fun d => d / "framework")) f (o.out / "framework")
  -- (11s) the live client: only with --serve, so a plain site is unchanged
  if o.serve then
    for f in ["lsp-client.js", "doc-live.js", "doc-live.css"] do
      unless ← copyFirst o.assets f o.out do
        throw (IO.userError s!"wiz doc: --serve: {f} is not in the web assets: give --web DIR \
          (a release's share/wiz/web) or run in a checkout")
  let tWork ← IO.monoMsNow
  let pieces ← mapWindow o.jobs mods.zipIdx fun (m, i) => pieceOf o mods names wasm elabMod i m
  let tRendered ← IO.monoMsNow
  -- (the site's shared pages are assembled in the modules' own order: identical output
  -- for every `--jobs`)
  let mut rows : Array Json := #[]
  let mut summaries : Array (String × Option String) := #[]
  let mut apiSections : Array String := #[]
  let mut apiDecls : Array Json := #[]
  let mut sections : Array Reference.Section := #[]
  let mut states : Array St := #[]
  let mut declCount := 0
  let mut elabSum := 0
  let mut renderSum := 0
  let mut hitSum := 0
  for p in pieces do
    rows := rows.append p.rows
    sections := sections.push (p.module, p.entries)
    states := states.push p.st
    summaries := summaries.push (p.module.name, p.summary)
    apiSections := apiSections.push p.apiSection
    apiDecls := apiDecls ++ p.apiRows
    declCount := declCount + p.decls
    elabSum := elabSum + p.elabMs
    renderSum := renderSum + p.renderMs
    hitSum := hitSum + p.hits
  let tAssembled ← IO.monoMsNow
  say o s!"phase elaboration: {secs elabSum} over {pieces.size} module(s) \
    ({secs (tRendered - tWork)} wall, {o.jobs} job(s), {hitSum} cache hit(s))"
  say o s!"phase rendering: {secs renderSum} (accumulated)"
  say o s!"phase writing: {pieces.size} page(s) + {pieces.size} module JSON file(s) \
    + index, api, search, reference"
  -- (one page and one `<module>.json` per module, in the modules' order)
  for p in pieces do
    let pageFile := o.out / pageOf p.module.name
    let jsonFile := o.out / s!"{p.module.name}.json"
    IO.FS.writeFile pageFile p.page
    IO.FS.writeFile jsonFile p.json
  IO.FS.writeFile (o.out / "search.js") (searchJs rows)
  -- (the landing and API pages have no signatures to render: no Wasm module script)
  IO.FS.writeFile (o.out / "index.html") (indexPage o summaries.toList)
  IO.FS.writeFile (o.out / "api.html") (apiPage o names apiSections mods.size declCount)
  let apiModules := summaries.map fun (m, doc) =>
    Json.mkObj [("name", m), ("href", pageOf m), ("doc", docText doc)]
  let apiFile := o.out / "api.json"
  IO.FS.writeFile apiFile
    (Json.mkObj [("title", o.title), ("modules", Json.arr apiModules), ("decls", Json.arr apiDecls)]).compress
  -- (the reference manual: the page of the site, and the committed Markdown when asked)
  let data := Reference.collect o.referenceTitle sections states
  IO.FS.writeFile (o.out / "reference.html") (Reference.html o data states names)
  let mut written : Array String := #[]
  let mut stale : Array String := #[]
  if let some dir := o.reference then
    if !o.check then IO.FS.createDirAll dir
    let file := dir / "index.md"
    let text := Reference.markdown data
    if o.check then
      if ← file.pathExists then
        let old ← IO.FS.readFile file
        if old != text then stale := stale.push file.toString
      else stale := stale.push file.toString
    else
      IO.FS.writeFile file text
      written := written.push file.toString
  let tEnd ← IO.monoMsNow
  say o s!"phase writing: {secs (tEnd - tAssembled)}"
  let rss ← peakRssKB
  say o s!"summary: {pieces.size} module(s), {declCount} declaration(s), \
    {2 * pieces.size + 5 + (if o.reference.isSome && !o.check then 1 else 0)} file(s) written, \
    {secs (tEnd - tAll)} wall ({secs elabSum} elaborating, {secs renderSum} rendering, \
    {o.jobs} job(s)), peak RSS {match rss with | some kb => s!"{kb / 1024} MiB" | none => "?"}"
  pure { pages := mods.size, stale, written }

end Wiz.Doc
