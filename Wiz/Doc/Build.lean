import Wiz.Doc.Site
import Wiz.Doc.Reference

/-!
# Building the documentation site (stage 11s)

`run` is `wiz doc`: it makes the pages (`Site`), the reference page of the site and, with
`--reference`, the committed reference manual (`Reference`). It needs both, so it lives
here rather than in `Site` (which `Reference` reads). `elabMod m` elaborates `import m`
with the module roots that find every module of `mods`; the result counts the pages and
names the reference files that differ (`--check`).
-/

namespace Wiz.Doc

def run (elabMod : String → IO St) (mods : Array Module) (o : Options) : IO RunResult := do
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
  let mut summaries : Array (String × Option String) := #[]
  let mut apiSections : Array String := #[]
  let mut apiDecls : Array Json := #[]
  let mut sections : Array Reference.Section := #[]
  let mut states : Array St := #[]
  let mut declCount := 0
  for m in mods do
    let st ← elabMod m.name
    for msg in st.messages do
      if msg.severity == .error then IO.eprintln s!"{m.name}: {msg.text}"
    let c : Ctx := { st, modules := names, current := m.name }
    let es := entries c m.src
    IO.FS.writeFile (o.out / pageOf m.name) (modulePage c o m es wasm)
    IO.FS.writeFile (o.out / s!"{m.name}.json")
      (Json.mkObj [("module", m.name), ("decls", Json.arr (es.flatMap fun e => #[e.data] ++ e.children.map (·.data)))]).compress
    sections := sections.push (m, es)
    states := states.push st
    let doc := moduleDocOf m.src
    summaries := summaries.push (m.name, doc)
    -- (the API index: all modules, every declaration, the same cross-links)
    let ac : Ctx := { st, modules := names, current := "" }
    apiSections := apiSections.push (apiSection ac m es)
    apiDecls := apiDecls ++ apiRows m es
    declCount := declCount + es.foldl (fun n e => n + 1 + e.children.size) 0
    -- (the search: the module itself, then its declarations)
    rows := rows.push (Json.mkObj [("n", m.name), ("m", m.name), ("k", "module"),
      ("d", (docText doc).take 500 |>.toString), ("s", ""), ("u", pageOf m.name)])
    for e in es do
      for x in #[e] ++ e.children do
        rows := rows.push (Json.mkObj [("n", x.name), ("m", m.name), ("k", x.kind),
          ("d", (docText x.doc).take 500 |>.toString),
          ("s", (x.sigText.take 500).toString), ("u", apiHref m x)])
  IO.FS.writeFile (o.out / "search.js") (searchJs rows)
  -- (the landing and API pages have no signatures to render: no Wasm module script)
  IO.FS.writeFile (o.out / "index.html") (indexPage o summaries.toList)
  IO.FS.writeFile (o.out / "api.html") (apiPage o names apiSections mods.size declCount)
  let apiModules := summaries.map fun (m, doc) =>
    Json.mkObj [("name", m), ("href", pageOf m), ("doc", docText doc)]
  IO.FS.writeFile (o.out / "api.json")
    (Json.mkObj [("title", o.title), ("modules", Json.arr apiModules), ("decls", Json.arr apiDecls)]).compress
  -- (the reference manual: the page of the site, and the committed Markdown when asked)
  let data := Reference.collect o.title sections states
  IO.FS.writeFile (o.out / "reference.html") (Reference.html o data states names)
  let mut stale : Array String := #[]
  let mut written : Array String := #[]
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
  pure { pages := mods.size, stale, written }


end Wiz.Doc
