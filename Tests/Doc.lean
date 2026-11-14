import Tests.Harness
import Tests.Grail
import Wiz.Doc.Site

/-! # 11s: doc comments and `wiz doc` (scroll) -/

namespace Tests.Doc
open Wiz
open Tests.Grail (mkTree)

/-- A small library with doc comments: a structure with documented fields, an inductive
type (a constructor doc before `|` and one after it), a class, an instance, a `mutual`
block, a private definition and Markdown. -/
def basicSrc : String := "/-! # Shapes

Basic **shapes**, for the `doc` tests. -/
import Prelude

/-- A point in the *plane*, with `Nat` coordinates. -/
structure Point where
  /-- the horizontal coordinate -/
  x : Nat
  /-- the vertical one -/
  y : Nat

/-- Shapes. -/
inductive Shape where
  /-- a dot at a point -/
  | dot (p : Point)
  | /-- a box from one corner to the other -/ box (a : Point) (b : Point)

/-- Things with an area.

* one item
* two items -/
class Area (A : Type) where
  area : A → Nat

/-- The area of a shape:
```
Shape.area (.dot p) = 0
``` -/
def Shape.area : Shape → Nat
  | .dot _ => 0
  | .box _ _ => 1

instance : Area Shape := Area.mk Shape.area

-- not a doc comment
def undocumented (n : Nat) : Nat := n

mutual
/-- even -/
def isEven : Nat → Bool
  | .zero => .true
  | .succ n => isOdd n
/-- odd -/
def isOdd : Nat → Bool
  | .zero => .false
  | .succ n => isEven n
end

/-- not shown -/
private def secret : Nat := 0
"

def useSrc : String := "import Shapes.Basic
/-- Twice the area, see `Shape.area`. -/
def twice (s : Shape) : Nat := Nat.add (Area.area s) (Area.area s)
"

def pkgFiles : List (String × String) :=
  [("grail.wiz", "import Grail\ndef package : Package := Package.new \"shapes\" |> Package.lib \"shapes\" \"src\"\n"),
   ("src/Shapes/Basic.wiz", basicSrc), ("src/Shapes/Use.wiz", useSrc)]

def elabBasic (cache : Option System.FilePath := none) : IO (CommandState ZeroOneMany) := do
  let prelude ← IO.FS.readFile "lib/Prelude.wiz"
  let loader : Name → Option String := fun m => if m == "Prelude" then some prelude else none
  let init : CommandState ZeroOneMany := { loader, trustedModule := Tests.libModule }
  match cache with
  | none => pure (runFrontend basicSrc init)
  | some dir => pure (← Cache.elaborateCached (some dir) [] basicSrc init 0).1

def docOf (s : CommandState ZeroOneMany) (n : Name) : String :=
  match s.declDocs.get? n with
  | some d => s!"{d.kind}|{d.doc.getD "-"}|{d.parent.getD "-"}"
  | none => "none"

/-- The files of a directory, recursively. -/
partial def filesUnder (d : System.FilePath) : IO (Array System.FilePath) := do
  let mut out := #[]
  for e in ← d.readDir do
    if ← e.path.isDir then out := out ++ (← filesUnder e.path) else out := out.push e.path
  pure out

/-- Every `href="P#A"` (relative, to a page of the site) of the site's pages: whether
`P` exists and has an element with id `A`. The broken ones. -/
def brokenLinks (out : System.FilePath) : IO (Array String) := do
  let mut broken := #[]
  for f in ← filesUnder out do
    unless f.extension == some "html" do continue
    let html ← IO.FS.readFile f
    for part in (html.splitOn "href=\"").drop 1 do
      let target := (part.splitOn "\"").headD ""
      if target.startsWith "http" || target.endsWith ".css" then continue
      let (page, anchor) := match target.splitOn "#" with
        | [p] => (p, "")
        | p :: a :: _ => (p, a)
        | [] => ("", "")
      let file := if page.isEmpty then f else out / page
      unless ← file.pathExists do broken := broken.push s!"{f.fileName.getD ""}: {target}"; continue
      unless anchor.isEmpty do
        let t ← IO.FS.readFile file
        let unesc := anchor.replace "&#39;" "'"
        unless (t.splitOn s!"id=\"{anchor}\"").length > 1 || (t.splitOn s!"id=\"{unesc}\"").length > 1 do
          broken := broken.push s!"{f.fileName.getD ""}: {target}"
  pure broken

def runOut (cmd : String) (args : List String) (cwd : Option System.FilePath := none) : IO String := do
  let o ← IO.Process.output { cmd, args := args.toArray, cwd }
  unless o.exitCode == 0 do throw (IO.userError s!"{cmd} {args}: exit {o.exitCode}\n{o.stdout}\n{o.stderr}")
  pure o.stdout

def wiz : IO String := do pure (← IO.FS.realPath ".lake/build/bin/wiz").toString

/-- `wiz doc` on the package's source directory, plain (no Wasm). -/
def makeSite (dir : System.FilePath) : IO System.FilePath := do
  let out := dir / "site"
  discard <| runOut (← wiz) ["doc", (dir / "src").toString, "-o", out.toString,
    "--source-url", "https://example.org/blob/abc/src/", "--web", (dir / "no-web").toString]
  pure out

def has (text frag : String) : Bool := (text.splitOn frag).length > 1
def checkHas (text frag : String) : IO Unit := check (has text frag) s!"missing {frag}"

/-- The core library modules whose every public declaration must have a doc comment. -/
def coreModules : List String := ["Prelude", "Std", "Vec", "Word"]

/-- The declarations on a module page (`wiz doc`'s HTML) without a doc comment of their
own (constructors and fields are not counted). -/
def undocumented (html : String) : Array String := Id.run do
  let mut out := #[]
  for part in (html.splitOn "<div class=\"decl\" id=\"").drop 1 do
    let n := (part.splitOn "\"").headD ""
    -- (the declaration's own part: before its constructors, fields and instances)
    let own := (((part.splitOn "<div class=\"children\">").headD "").splitOn "<details class=\"instances\">").headD ""
    unless has own "<div class=\"doc\">" do out := out.push n
  out

def libDocCase : Case :=
  { name := "the core library is documented: a module doc and a doc comment on every public declaration (Prelude, Std, Vec, Word)", run := fun _ => do
      let dir ← IO.FS.createTempDir
      let out := dir / "site"
      discard <| runOut (← wiz) (["doc"] ++ coreModules.map (s!"lib/{·}.wiz") ++
        ["-o", out.toString, "--web", (dir / "no-web").toString])
      let index ← IO.FS.readFile (out / "index.html")
      let mut missing : Array String := #[]
      for m in coreModules do
        let src ← IO.FS.readFile s!"lib/{m}.wiz"
        check (has src "/-!") s!"lib/{m}.wiz has no module doc"
        checkHas index s!"href=\"{m}.html\""
        let html ← IO.FS.readFile (out / s!"{m}.html")
        check (has html "<div class=\"decl\"") s!"{m}: no declarations on its page"
        missing := missing ++ (undocumented html).map (s!"{m}: {·}")
      check missing.isEmpty s!"declarations without a doc comment: {missing}" }

def docGroup : Group where
  name := "doc"
  parallel := true
  exercise := "Stage 11s (docs/stages/11-tooling.md)"
  cases := [
    { name := "doc comments are stored on declarations: commands, constructors, fields, mutual, private", run := fun _ => do
        let s ← elabBasic
        let errs := s.messages.filter (·.severity == .error)
        check errs.isEmpty s!"{errs.toList.map (·.text)}"
        checkEq "structure|A point in the *plane*, with `Nat` coordinates.|-" (docOf s "Point")
        checkEq "field|the horizontal coordinate|Point" (docOf s "Point.x")
        checkEq "field|the vertical one|Point" (docOf s "Point.y")
        checkEq "constructor|-|Point" (docOf s "Point.mk")
        checkEq "inductive|Shapes.|-" (docOf s "Shape")
        checkEq "constructor|a dot at a point|Shape" (docOf s "Shape.dot")
        checkEq "constructor|a box from one corner to the other|Shape" (docOf s "Shape.box")
        checkEq "class|Things with an area.\n\n* one item\n* two items|-" (docOf s "Area")
        checkEq "def|-|-" (docOf s "undocumented")
        checkEq "def|even|-" (docOf s "isEven")
        checkEq "def|odd|-" (docOf s "isOdd")
        check (has (docOf s "Shape.area") "Shape.area (.dot p) = 0") (docOf s "Shape.area")
        -- (in the main file a private name is not renamed: `Globals.privates`)
        checkEq "private def|not shown|-" (docOf s "secret")
        checkEq (some "# Shapes\n\nBasic **shapes**, for the `doc` tests.") (moduleDocOf basicSrc) },
    { name := "the cache replays doc comments", run := fun _ => do
        let dir ← IO.FS.createTempDir
        let a ← elabBasic (some dir)
        let b ← elabBasic (some dir)
        for n in ["Point", "Point.x", "Shape.box", "Area", "isOdd", "Shape.area"] do
          checkEq (docOf a n) (docOf b n)
        checkEq "constructor|a box from one corner to the other|Shape" (docOf b "Shape.box") },
    { name := "Markdown: paragraphs, emphasis, code, lists, fences, links; HTML escaped", run := fun _ => do
        let r := Doc.render (fun c => if c == "f" then some "M.html#f" else none)
        checkEq "<p>a <em>b</em> <strong>c</strong> <a href=\"M.html#f\"><code>f</code></a> <code>g</code></p>\n" (r "a *b* **c** `f` `g`")
        checkEq "<ul><li>x</li><li>y z</li></ul>\n" (r "* x\n* y\n  z")
        checkEq "<pre><code>a &lt; b\n</code></pre>\n".length (r "```\na < b\n\n```").length
        checkEq "<p>&lt;script&gt; <a href=\"https://e.org\">l</a> j</p>\n" (r "<script> [l](https://e.org) [j](javascript:x)") },
    { name := "wiz doc: a page per module, kinds, docs as HTML, source links, instances, index", run := fun _ => do
        let dir ← mkTree pkgFiles
        let out ← makeSite dir
        let basic ← IO.FS.readFile (out / "Shapes.Basic.html")
        let use ← IO.FS.readFile (out / "Shapes.Use.html")
        let index ← IO.FS.readFile (out / "index.html")
        for frag in ["id=\"Point\"", "id=\"Point.x\"", "id=\"Shape.dot\"", "id=\"Shape.box\"", "id=\"Area\"", "id=\"Shape.area\"",
            "id=\"isEven\"", "id=\"undocumented\"",
            "<span class=\"kind\">structure</span>", "<span class=\"kind\">inductive</span>", "<span class=\"kind\">class</span>",
            "<p>A point in the <em>plane</em>, with <code>Nat</code> coordinates.</p>", "<p>a dot at a point</p>",
            "<ul><li>one item</li><li>two items</li></ul>", "<h4>Shapes</h4>",
            "href=\"https://example.org/blob/abc/src/Shapes/Basic.wiz#L7\"", "Instances (1)"] do
          checkHas basic frag
        check (!has basic "not shown" && !has basic "secret") "a private declaration is documented"
        check (!has basic "Shape.rec" && !has basic "Shape.desc") "an auxiliary declaration is documented"
        -- (the signature's constants link to their pages; the doc's code too)
        checkHas use "href=\"Shapes.Basic.html#Shape\""
        checkHas use "<a href=\"Shapes.Basic.html#Shape.area\"><code>Shape.area</code></a>"
        checkHas index "href=\"Shapes.Basic.html\""
        checkHas index "Basic <strong>shapes</strong>, for the <code>doc</code> tests." },
    { name := "wiz doc: every cross-link resolves; every declaration is in the search index", run := fun _ => do
        let dir ← mkTree pkgFiles
        let out ← makeSite dir
        let broken ← brokenLinks out
        check broken.isEmpty s!"broken links: {broken}"
        let idx ← IO.FS.readFile (out / "search.js")
        let some json := (idx.splitOn "window.wizSearchIndex = ")[1]? | throw (IO.userError "no index")
        let .ok (.arr rows) := Lean.Json.parse ((json.trimAscii.dropEnd 1).toString) | throw (IO.userError "index is not JSON")
        let names := rows.filterMap fun r => (r.getObjValAs? String "n").toOption
        for n in ["Point", "Point.x", "Point.y", "Shape", "Shape.dot", "Shape.box", "Area", "Area.area", "Shape.area", "undocumented",
            "isEven", "isOdd", "twice"] do
          check (names.contains n) s!"{n} is not in the index"
        -- and every declaration on a page is in it
        for page in ["Shapes.Basic.html", "Shapes.Use.html"] do
          let html ← IO.FS.readFile (out / page)
          for part in (html.splitOn "<div class=\"decl\" id=\"").drop 1 do
            let n := (part.splitOn "\"").headD ""
            check (names.contains n) s!"{n} ({page}) is not in the index" },
    { name := "wiz doc: the pages are complete without JS (no module script without the Wasm); the data is there for it", run := fun _ => do
        let dir ← mkTree pkgFiles
        let out ← makeSite dir
        let basic ← IO.FS.readFile (out / "Shapes.Basic.html")
        check (!has basic "type=\"module\"") "a module script without the Wasm module"
        -- the signature as text, with links, in the page itself
        checkHas basic "<span class=\"decl-name\">Shape.area</span> : <span class=\"sig-type\" id=\"sig-"
        checkHas basic "<a href=\"#Shape\">Shape</a> → <a href=\"#Nat\">Nat</a>" <|>
          checkHas basic "<a href=\"#Shape\">Shape</a> → Nat"
        -- the JSON the Wasm module reads: tagged text and the subterm table
        checkHas basic "<script type=\"application/json\" id=\"wiz-doc-data\">"
        let data ← IO.FS.readFile (out / "Shapes.Basic.json")
        checkHas data "\"tag\":[{\"kind\":\"const\",\"name\":\"Shape\""
        checkHas data "\"definition\":{\"href\":\"#Shape\"" },
    { name := "grail doc: the package's lib targets", run := fun _ => do
        let dir ← mkTree pkgFiles
        let grail ← IO.FS.realPath ".lake/build/bin/grail"
        let o ← runOut grail.toString ["doc", "--web", (dir / "no-web").toString] (cwd := some dir)
        checkHas o "2 modules"
        let basic ← IO.FS.readFile (dir / ".grail" / "doc" / "Shapes.Basic.html")
        checkHas basic "<a class=\"site\" href=\"index.html\">shapes</a>"
        checkHas basic "id=\"Shape.box\"" },
    { name := "the doc page model (lib/Tagged.wiz, the Wasm module's) renders a page's JSON: hover, click, keys", run := fun _ => do
        let dir ← mkTree pkgFiles
        let out ← makeSite dir
        -- the declaration `twice`, as scroll.js hands it over
        let data ← IO.FS.readFile (out / "Shapes.Use.json")
        let .ok j := Lean.Json.parse data | throw (IO.userError "page data is not JSON")
        let some (.arr decls) := (j.getObjVal? "decls").toOption | throw (IO.userError "no decls")
        let some d := decls[0]? | throw (IO.userError "no decl")
        IO.FS.writeFile (dir / "decl.json") d.compress
        -- tag 0 is the whole type, 1 `(s : Shape)`'s `Shape`
        let prog := s!"import IO\nimport Tagged\n" ++
          "def display : List DocAct → IO Unit\n  | .nil => IO.pure ()\n  | .cons a rest => do\n" ++
          "    (match a with\n      | .html id h => IO.println (String.append id (String.append \": \" h))\n" ++
          "      | .info h => IO.println (String.append \"info: \" h)\n      | .go u => IO.println (String.append \"go: \" u));\n    display rest\n" ++
          "def ev (s : DocSt) (e : String) : IO DocSt :=\n  let r := DocPage.step s e;\n  do\n    display r.2;\n    IO.pure r.1\n" ++
          s!"def main : IO Unit := do\n  j ← IO.readFile {(dir / "decl.json").toString.quote};\n" ++
          "  s1 ← ev DocSt.empty (String.append \"decl\\n\" j);\n  s2 ← ev s1 \"hover\\nsig-0 1\";\n" ++
          "  s3 ← ev s2 \"click\\nsig-0 1\";\n  s4 ← ev s3 \"click\\nsig-0 0\";\n  s5 ← ev s4 \"key\\nArrowRight\";\n  s6 ← ev s5 \"leave\\n\";\n  IO.pure ()\n"
        IO.FS.writeFile (dir / "page.wiz") prog
        let tc ← toolchain
        let o ← IO.Process.output { cmd := ← wiz, args := (tc.toFlags ++ ["run", (dir / "page.wiz").toString]).toArray }
        if o.exitCode != 0 then
          if ["gmp.h", "No such file"].any (has o.stderr ·) then skip "no toolchain" else
          throw (IO.userError s!"wiz run: {o.stdout}\n{o.stderr}")
        let lines := o.stdout.splitOn "\n"
        -- rendered as tagged text, every subterm a span
        check ((lines.headD "").startsWith "sig-0: <span class=\"tt k-pi\" data-ref=\"") (lines.headD "")
        checkHas o.stdout "<span class=\"tt k-const\" data-ref="
        -- hovering `Shape`: what it is, where it is documented
        checkHas o.stdout "info: <span class=\"kind\">const</span> <code>Shape : Type</code><div class=\"def\">defined at <a href=\"Shapes.Basic.html#Shape\">"
        -- clicking a constant goes to its definition; clicking the arrow selects it
        checkHas o.stdout "go: Shapes.Basic.html#Shape"
        checkHas o.stdout "tt k-pi sel"
        -- the arrow key moves the selection to the next tag
        checkHas o.stdout "data-idx=\"1\" title=\"Shape\""
        check (lines.any (fun l => has l "sel\" data-ref" && has l "data-idx=\"1\"")) o.stdout },
    libDocCase
  ]

def groups : List Group := [docGroup]

end Tests.Doc
