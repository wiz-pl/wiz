import Tests.Harness
import Tests.Grail
import Wiz.Doc.Site
import Wiz.Socket

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

/-- A package for the reference manual: an implicit argument, a class with two
instances, an infix operator of its own, markup in a doc comment, and a module without
any doc comments. -/
def refSrc : String := "/-! # Reference fixture

A module with **markup** and `Sized`, for the `reference` tests. -/
import Prelude

/-- The identity, at an implicit type. -/
def ident {A : Type} (a : A) : A := a

/-- Things with a size. -/
class Sized (A : Type) where
  /-- how big it is -/
  size : A → Nat

/-- A pair of numbers. -/
structure Pair where
  /-- the first -/
  left : Nat
  /-- the second -/
  right : Nat

instance : Sized Pair := Sized.mk (fun _ => 2)
instance : Sized Nat := Sized.mk (fun n => n)

/-- A made-up operator, to show the notation table. -/
infixl:33 \" +? \" => HAdd.hAdd
"

def refEmpty : String := "import Prelude

def quiet : Nat := 1
"

def refPkgFiles : List (String × String) :=
  [("grail.wiz", "import Grail\ndef package : Package := Package.new \"ref\" |> Package.lib \"ref\" \"src\"\n"),
   ("src/Ref/A.wiz", refSrc), ("src/Ref/Empty.wiz", refEmpty)]

/-- A module with one declaration of every command kind that declares a name: a `def`
(plain and by equations), a `partial def`, an `axiom`, an `extern`, a `foreign_type`, a
`glue`, a `c_struct`, a `structure` (with a field and a dotted method), a `class` and its
instance, an `inductive`, a `coinductive` and a `sealed inductive`, plus a `theorem`,
`lemma` and `abbrev` written as *user* commands (`syntax … : command`, the language's
extension point). It also has a private definition and commands that declare nothing
(`#check`, `attribute`, `notation`, `syntax`, `export`), which must make no entry. -/
def kindsSrc : String := "/-! # Kinds

One declaration of each command kind, for the `doc` tests. -/
import Prelude

/-- A user command: `theorem n : T := e` is `def n : T := e`. -/
syntax (name := theorem) \"theorem\" ident \":\" term \":=\" term : command

def theoremMacro : CommandMacro := fun stx =>
  let n := Syntax.getArg stx 1;
  let t := Syntax.getArg stx 3;
  let e := Syntax.getArg stx 5;
  MacroM.pure (.cons `(command| def $n : $t := $e) .nil)

attribute [macro command.theorem] theoremMacro

/-- A user command: a `lemma` is a theorem. -/
syntax (name := lemma) \"lemma\" ident \":\" term \":=\" term : command

def lemmaMacro : CommandMacro := fun stx =>
  let n := Syntax.getArg stx 1;
  let t := Syntax.getArg stx 3;
  let e := Syntax.getArg stx 5;
  MacroM.pure (.cons `(command| def $n : $t := $e) .nil)

attribute [macro command.lemma] lemmaMacro

/-- A user command: an `abbrev` is a definition too (Wiz has no reducibility hints). -/
syntax (name := abbrev) \"abbrev\" ident \":\" term \":=\" term : command

def abbrevMacro : CommandMacro := fun stx =>
  let n := Syntax.getArg stx 1;
  let t := Syntax.getArg stx 3;
  let e := Syntax.getArg stx 5;
  MacroM.pure (.cons `(command| def $n : $t := $e) .nil)

attribute [macro command.abbrev] abbrevMacro

/-- a definition -/
def aDef (n : Nat) : Nat := n

/-- a definition by equations -/
def aEqns : Nat → Nat
  | .zero => 0
  | .succ n => n

/-- the body of this one must not appear in its signature -/
def withBody (n : Nat) : Nat := Nat.succ (Nat.succ n)

/-- a partial definition -/
partial def aPartial (n : Nat) : Nat := aPartial n

/-- an axiom -/
axiom anAxiom : Nat

/-- an external constant -/
extern \"kinds_extern\" anExtern : Nat

/-- a foreign type -/
foreign_type aHandle

/-- a glued function -/
glue aGlue (n : Nat) : Nat := \"return n + 1;\"

/-- a C struct -/
c_struct \"struct kinds_pair\" AKindsPair where
  /-- the first -/
  a : Nat
  /-- the second -/
  b : Nat

/-- a structure -/
structure AStructure where
  /-- the x -/
  x : Nat
  /-- the y -/
  y : Nat

/-- a method of the structure: its name is fully qualified -/
def AStructure.area : AStructure → Nat
  | .mk _ _ => 0

/-- a class -/
class AClass (A : Type) where
  /-- how big -/
  size : A → Nat

/-- a named instance -/
instance anInstance : AClass Nat := AClass.mk (fun n => n)

/-- an inductive type -/
inductive AnInductive where
  /-- a constructor -/
  | aCtor
  /-- another -/
  | bCtor (n : Nat)

/-- a coinductive type -/
coinductive ACoinductive where
  /-- the observation -/
  head : Nat

/-- a sealed inductive -/
sealed inductive ASealed where
  /-- the only constructor -/
  | seal

/-- a theorem (a user command): its statement is its type -/
theorem aTheorem : Nat → Nat := fun n => Nat.succ n

/-- a lemma (a user command: shown as `theorem`) -/
lemma aLemma : Nat := 1

/-- an abbreviation (a user command) -/
abbrev anAbbrev : Nat := 2

-- not a doc comment
def undocumentedKind : Nat := 0

/-- private: not documented -/
private def aSecret : Nat := 0

-- (commands that declare nothing: no entry)
#check aDef
attribute [inline] withBody
notation:max \"kindsBang\" n => aDef n
syntax (name := kindsSyntax) \"kinds_syntax\" : command
export \"kinds_export\" withBody
"

def kindsPkgFiles : List (String × String) :=
  [("grail.wiz", "import Grail\ndef package : Package := Package.new \"kinds\" |> Package.lib \"kinds\" \"src\"\n"),
   ("src/Kinds/All.wiz", kindsSrc)]

def elabBasic (cache : Option System.FilePath := none) : IO (CommandState ZeroOneMany) := do
  let prelude ← IO.FS.readFile "lib/Prelude.wiz"
  let loader : Name → Option String := fun m => if m == "Prelude" then some prelude else none
  let init : CommandState ZeroOneMany := { loader, trustedModule := Tests.libModule }
  match cache with
  | none => pure (runFrontend basicSrc init)
  | some dir => pure (← Cache.elaborateCached (some dir) [] basicSrc init 0).1

def elabKinds : IO (CommandState ZeroOneMany) := do
  let prelude ← IO.FS.readFile "lib/Prelude.wiz"
  let loader : Name → Option String := fun m => if m == "Prelude" then some prelude else none
  pure (runFrontend kindsSrc { loader, trustedModule := Tests.libModule })

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

/-- The rows of `search.js`, if it is the generated index. -/
def searchRows? (js : String) : Option (Array Lean.Json) := do
  let some json := (js.splitOn "window.wizSearchIndex = ")[1]? | none
  let .ok (.arr rows) := Lean.Json.parse ((json.trimAscii.dropEnd 1).toString) | none
  pure rows

/-- A string field of an index row (`""` if missing). -/
def field (j : Lean.Json) (k : String) : String := (j.getObjValAs? String k).toOption.getD ""

def runOut (cmd : String) (args : List String) (cwd : Option System.FilePath := none) : IO String := do
  let o ← IO.Process.output { cmd, args := args.toArray, cwd }
  unless o.exitCode == 0 do throw (IO.userError s!"{cmd} {args}: exit {o.exitCode}\n{o.stdout}\n{o.stderr}")
  pure o.stdout

def wiz : IO String := do pure (← IO.FS.realPath ".lake/build/bin/wiz").toString

/-- A free TCP port on the loopback interface (bound and released: the server test's). -/
def freePort : IO UInt16 := do
  let (fd, p) ← Wiz.Socket.tcpListen Wiz.Socket.loopback 0
  Wiz.Socket.closeFd fd
  pure p

/-- One HTTP/1.0 GET through already-connected handles; the whole response (the
documentation server answers with `Connection: close`). -/
def httpReq (r w : IO.FS.Handle) (path : String) : IO String := do
  let rs := IO.FS.Stream.ofHandle r
  let ws := IO.FS.Stream.ofHandle w
  ws.putStr s!"GET {path} HTTP/1.0\r\nHost: 127.0.0.1\r\n\r\n"
  ws.flush
  rs.readToEnd

/-- One HTTP/1.0 GET to a local server. -/
def httpGet (port : UInt16) (path : String) : IO String := do
  let (r, w) ← Wiz.Socket.tcpConnect Wiz.Socket.loopback port
  httpReq r w path

/-- Connect to `port`, retrying while the server starts (about 10 s in all). -/
def connectSoon (port : UInt16) : IO (Option (IO.FS.Handle × IO.FS.Handle)) := do
  let rec go : Nat → IO (Option (IO.FS.Handle × IO.FS.Handle))
    | 0 => pure none
    | n + 1 => do
      match ← (try some <$> Wiz.Socket.tcpConnect Wiz.Socket.loopback port catch _ => pure none) with
      | some c => pure (some c)
      | none => IO.sleep 25; go n
  go 400

/-- `wiz doc` on the package's source directory, plain (no Wasm). -/
def makeSite (dir : System.FilePath) : IO System.FilePath := do
  let out := dir / "site"
  discard <| runOut (← wiz) ["doc", (dir / "src").toString, "-o", out.toString,
    "--source-url", "https://example.org/blob/abc/src/", "--web", (dir / "no-web").toString]
  pure out

def has (text frag : String) : Bool := (text.splitOn frag).length > 1
def checkHas (text frag : String) : IO Unit := check (has text frag) s!"missing {frag}"

/-- The `data-kind` of the declaration `id` on a module page (`""` if it has no entry). -/
def kindOn (html id : String) : String :=
  match (html.splitOn s!"<div class=\"decl\" id=\"{id}\" data-kind=\"")[1]? with
  | some rest => (rest.splitOn "\"").headD ""
  | none => ""

/-- A declaration's heading and signature on a module page (up to the end of its
signature block): the part that must not show its body. -/
def declHead (html id : String) : String :=
  match (html.splitOn s!"<div class=\"decl\" id=\"{id}\" data-kind=\"")[1]? with
  | some rest => (rest.splitOn "</code></pre>").headD ""
  | none => ""

/-- The kind (the `class` attribute) of the child entry `id` (a constructor or field) on a
module page: `field`, `constructor`, … (`""` if there is no such child). -/
def childKindOn (html id : String) : String := Id.run do
  let mut out := ""
  for part in (html.splitOn "<li class=\"").drop 1 do
    match part.splitOn "\"" with
    | cls :: _ :: i :: _ => if i == id && out.isEmpty then out := cls
    | _ => pure ()
  return out

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
    { name := "doc comments are stored for every command kind that declares a name", run := fun _ => do
        let s ← elabKinds
        let errs := s.messages.filter (·.severity == .error)
        check errs.isEmpty s!"{errs.toList.map (·.text)}"
        for p in [("aDef", "def"), ("aEqns", "def"), ("withBody", "def"),
            ("aPartial", "partial def"), ("anAxiom", "axiom"), ("anExtern", "extern"),
            ("aHandle", "foreign type"), ("aGlue", "glue"), ("AKindsPair", "c struct"),
            ("AStructure", "structure"), ("AStructure.area", "def"), ("AClass", "class"),
            ("anInstance", "instance"), ("AnInductive", "inductive"),
            ("ACoinductive", "coinductive"), ("ASealed", "sealed inductive"),
            ("aTheorem", "theorem"), ("aLemma", "theorem"), ("anAbbrev", "abbrev"),
            ("undocumentedKind", "def")] do
          checkEq p.2 ((docOf s p.1).splitOn "|" |>.headD "")
        -- (constructors and fields: their kind and parent)
        checkEq "field|the x|AStructure" (docOf s "AStructure.x")
        checkEq "field|the first|AKindsPair" (docOf s "AKindsPair.a")
        checkEq "constructor|-|AStructure" (docOf s "AStructure.mk")
        checkEq "constructor|a constructor|AnInductive" (docOf s "AnInductive.aCtor")
        checkEq "field|the observation|ACoinductive" (docOf s "ACoinductive.head")
        checkEq "constructor|the only constructor|ASealed" (docOf s "ASealed.seal")
        checkEq "field|how big|AClass" (docOf s "AClass.size") },
    { name := "wiz doc: every command kind that declares a name is an entry with its kind and signature", run := fun _ => do
        let dir ← mkTree kindsPkgFiles
        let out ← makeSite dir
        let html ← IO.FS.readFile (out / "Kinds.All.html")
        for p in [("aDef", "def"), ("aEqns", "def"), ("withBody", "def"),
            ("aPartial", "partial def"), ("anAxiom", "axiom"), ("anExtern", "extern"),
            ("aHandle", "foreign type"), ("aGlue", "glue"), ("AKindsPair", "c struct"),
            ("AStructure", "structure"), ("AStructure.area", "def"), ("AClass", "class"),
            ("anInstance", "instance"), ("AnInductive", "inductive"),
            ("ACoinductive", "coinductive"), ("ASealed", "sealed inductive"),
            ("aTheorem", "theorem"), ("aLemma", "theorem"), ("anAbbrev", "abbrev"),
            ("undocumentedKind", "def")] do
          checkEq p.2 (kindOn html p.1)
        for p in [("AStructure.x", "field"), ("AStructure.mk", "constructor"),
            ("AKindsPair.a", "field"), ("AKindsPair.mk", "constructor"),
            ("AClass.size", "field"), ("AnInductive.aCtor", "constructor"),
            ("ACoinductive.head", "field"), ("ASealed.seal", "constructor")] do
          checkEq p.2 (childKindOn html p.1)
        -- the signature is the type or the statement, not the body
        check (has (declHead html "withBody") "Nat") (declHead html "withBody")
        check (!has (declHead html "withBody") "succ") "withBody's body is in its signature"
        check (!has (declHead html "aTheorem") "succ") "aTheorem's proof is in its signature"
        check (has (declHead html "anInstance") "AClass") (declHead html "anInstance")
        check (has (declHead html "anAxiom") "Nat") (declHead html "anAxiom")
        check (has (declHead html "aPartial") "Nat → Nat") (declHead html "aPartial")
        -- a dotted name keeps its fully qualified anchor
        checkHas html "id=\"AStructure.area\""
        -- private, auxiliary and non-declaring commands make no entry
        check (!has html "aSecret") "a private declaration is documented"
        check (!has html "AnInductive.rec") "an auxiliary declaration is documented"
        for k in ["auxiliary", "check", "eval", "syntax", "notation", "attribute", "export",
            "deriving"] do
          check (!has html s!"data-kind=\"{k}\"") s!"a {k} command has an entry"
        -- the API index, api.json and the search index carry the same kinds
        let api ← IO.FS.readFile (out / "api.html")
        for k in ["theorem", "c struct", "partial def", "foreign type", "sealed inductive"] do
          checkHas api s!"class=\"kind\">{k}</td>"
        checkHas api "href=\"Kinds.All.html#aTheorem\""
        let text ← IO.FS.readFile (out / "api.json")
        let .ok j := Lean.Json.parse text | throw (IO.userError "api.json is not JSON")
        let some (.arr decls) := (j.getObjVal? "decls").toOption
          | throw (IO.userError "api.json has no decls")
        for p in [("aTheorem", "theorem"), ("aPartial", "partial def"),
            ("AKindsPair", "c struct"), ("anExtern", "extern"), ("aHandle", "foreign type")] do
          let some d := decls.find? (fun d => field d "name" == p.1)
            | throw (IO.userError s!"{p.1} is not in api.json")
          checkEq p.2 (field d "kind")
        let idx ← IO.FS.readFile (out / "search.js")
        let some rows := searchRows? idx | throw (IO.userError "search.js is not the index")
        for p in [("aTheorem", "theorem"), ("aGlue", "glue"), ("anInstance", "instance")] do
          let some r := rows.find? (fun r => field r "n" == p.1)
            | throw (IO.userError s!"{p.1} is not in the search index")
          checkEq p.2 (field r "k")
        -- the same input makes the same page and index (deterministic order and anchors)
        let out2 := dir / "site2"
        discard <| runOut (← wiz) ["doc", (dir / "src").toString, "-o", out2.toString,
          "--source-url", "https://example.org/blob/abc/src/", "--web", (dir / "no-web").toString]
        checkEq (← IO.FS.readFile (out / "Kinds.All.html")) (← IO.FS.readFile (out2 / "Kinds.All.html"))
        checkEq (← IO.FS.readFile (out / "api.json")) (← IO.FS.readFile (out2 / "api.json")) },
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
        let api ← IO.FS.readFile (out / "api.html")
        checkHas api "href=\"Shapes.Basic.html#Shape\""
        checkHas api "href=\"Shapes.Use.html#twice\""
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
    { name := "wiz doc: the API index and api.json list every module and declaration; search covers docs and signatures", run := fun _ => do
        let dir ← mkTree pkgFiles
        let out ← makeSite dir
        let api ← IO.FS.readFile (out / "api.html")
        for frag in ["<h1>API index</h1>", "id=\"module-Shapes.Basic\"", "id=\"module-Shapes.Use\"",
            "href=\"Shapes.Basic.html#Shape\"", "href=\"Shapes.Use.html#twice\"",
            "href=\"index.html\"", "class=\"api-sig\"", "class=\"lede\""] do
          checkHas api frag
        -- the signature on the index retains its cross-links (to the module's page)
        checkHas api "<a href=\"Shapes.Basic.html#Shape\">Shape</a>"
        -- api.json is the same index, for machines
        let text ← IO.FS.readFile (out / "api.json")
        let .ok j := Lean.Json.parse text | throw (IO.userError "api.json is not JSON")
        let some (.arr mods) := (j.getObjVal? "modules").toOption | throw (IO.userError "api.json has no modules")
        checkEq 2 mods.size
        let some (.arr decls) := (j.getObjVal? "decls").toOption | throw (IO.userError "api.json has no decls")
        check (decls.size ≥ 16) "api.json lost declarations"
        let some area := decls.find? (fun d => field d "name" == "Shape.area") | throw (IO.userError "Shape.area is not in api.json")
        checkEq "Shapes.Basic" (field area "module")
        checkEq "Shapes.Basic.html#Shape.area" (field area "href")
        check (has (field area "sig") "Shape") (field area "sig")
        check (has (field area "doc") "The area of a shape") (field area "doc")
        -- the search index: modules, declaration docs and signatures
        let idx ← IO.FS.readFile (out / "search.js")
        let some rows := searchRows? idx | throw (IO.userError "search.js is not the index")
        let some modRow := rows.find? (fun r => field r "k" == "module" && field r "n" == "Shapes.Basic")
          | throw (IO.userError "the module is not searchable")
        checkEq "Shapes.Basic.html" (field modRow "u")
        let some areaRow := rows.find? (fun r => field r "n" == "Shape.area")
          | throw (IO.userError "Shape.area is not in the search index")
        checkEq "Shapes.Basic.html#Shape.area" (field areaRow "u")
        check (has (field areaRow "s") "Shape") (field areaRow "s")
        let some point := rows.find? (fun r => field r "n" == "Point")
          | throw (IO.userError "Point is not in the search index")
        check (has (field point "d") "plane") (field point "d") },
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
    { name := "wiz doc --serve: the client is only in served pages, and the server serves the tree and its sources", run := fun _ => do
        let dir ← mkTree pkgFiles
        -- (the static site: neither the live client nor the positions it needs)
        let plain ← makeSite dir
        let basic ← IO.FS.readFile (plain / "Shapes.Basic.html")
        check (!has basic "doc-live.js") "a plain page carries the live client"
        check (!has basic "wiz-doc-serve") "a plain page carries the live data"
        check (!has basic "data-doc-line") "a plain page carries live positions"
        -- (a served site: the page presents the client, and the server answers.
        -- `freePort` reserves a port and closes it, so the server can lose the race to
        -- another process in between; retry with a fresh port rather than `skip`. An
        -- unexplained skip fails CI's skip gate, and three failed binds are a real
        -- failure, not a missing capability.)
        let out := dir / "live"
        let attempt (port : UInt16) : IO Bool := do
          let child ← IO.Process.spawn
            { cmd := ← wiz, args := #["doc", (dir / "src").toString, "-o", out.toString,
                "--serve", "--port", toString port, "--lsp", "8765"], stdout := .null, stderr := .piped }
          try
            match ← connectSoon port with
            | .none => do
              try child.kill catch _ => pure ()
              let err ← child.stderr.readToEnd
              unless err.trimAscii.isEmpty do IO.eprintln err
              pure false
            | .some (r, w) => do
              let index ← httpReq r w "/index.html"
              check (has index "200 OK") s!"GET /index.html: {index.take 200}"
              check (has index "<title>") index
              let page ← httpGet port "/Shapes.Basic.html"
              check (has page "200 OK") s!"GET /Shapes.Basic.html: {page.take 200}"
              checkHas page "<script type=\"module\" src=\"doc-live.js\"></script>"
              checkHas page "id=\"wiz-doc-serve\""
              checkHas page "\"lsp\":\"ws://127.0.0.1:8765\""
              checkHas page "data-doc-line="
              -- (the scripts the page imports are in the served tree)
              checkHas (← httpGet port "/doc-live.js") "readGoalState"
              checkHas (← httpGet port "/lsp-client.js") "export class LspClient"
              checkHas (← httpGet port "/goals.js") "export function renderGoalResult"
              -- (the module's source, for the client to open in the server)
              let src ← httpGet port "/sources/Shapes.Basic.wiz"
              check (has src "200 OK") s!"GET /sources: {src.take 200}"
              checkHas src "structure Point"
              -- (the landing and API pages stay static even when served)
              check (!has (← httpGet port "/index.html") "doc-live.js") "the index carries the live client"
              check (!has (← httpGet port "/api.html") "doc-live.js") "the API index carries the live client"
              -- (no path escapes the generated tree)
              check (has (← httpGet port "/../etc/passwd") "404") "a path above the site is served"
              pure true
          finally
            try child.kill catch _ => pure ()
        let rec go : Nat → IO Unit
          | 0 => throw (IO.userError "wiz doc --serve: the server did not bind a port in three attempts")
          | n + 1 => do
            let port ← freePort
            if ← attempt port then pure () else go n
        go 3 },
    { name := "wiz doc --serve: --port and --lsp need --serve", run := fun _ => do
        let o ← IO.Process.output { cmd := ← wiz, args := #["doc", "lib/Prelude.wiz", "-o", "/tmp/wiz-doc-noserve", "--lsp", "8765"] }
        check (o.exitCode == 2) s!"exit {o.exitCode}"
        checkHas o.stderr "need --serve" },
    { name := "wiz doc --reference: implicits, a class with two instances, an infix row, doc markup, a module without docs", run := fun _ => do
        let dir ← mkTree refPkgFiles
        let out := dir / "site"
        let ref := dir / "reference"
        discard <| runOut (← wiz) ["doc", (dir / "src").toString, "-o", out.toString,
          "--web", (dir / "no-web").toString, "--reference", ref.toString]
        let md ← IO.FS.readFile (ref / "index.md")
        -- (the header counts, and the manual links its sections and declarations)
        checkHas md "2 modules"
        checkHas md "## Contents"
        checkHas md "#notation"
        checkHas md "## Notation and precedence"
        -- (a declaration with an implicit argument: the elaborated type keeps it; names
        -- are global, not module-qualified, so the anchor is the bare name)
        checkHas md "<a id=\"ident\"></a>"
        checkHas md "def · `Ref/A.wiz:"
        checkHas md "{A : Type} → A → A"
        -- (a class and its two instances, with their types)
        checkHas md "<a id=\"Sized\"></a>"
        checkHas md "**Instances of this class (2)**"
        checkHas md "Sized Pair"
        checkHas md "Sized Nat"
        -- (its field, with a doc comment)
        checkHas md "<a id=\"Sized.size\"></a>"
        checkHas md "— how big it is"
        -- (the module's own infix operator, with precedence and associativity)
        checkHas md "| `+?` | infixl | 33 | left |"
        -- (doc comments are Markdown, links included)
        checkHas md "<strong>markup</strong>"
        checkHas md "<a href=\"#Sized\"><code>Sized</code></a>"
        -- (a module without doc comments is still a section, with its declaration)
        checkHas md "## Ref.Empty"
        checkHas md "<a id=\"quiet\"></a>"
        -- (the generated page links to the manual, and the manual to the pages)
        let html ← IO.FS.readFile (out / "reference.html")
        checkHas html "id=\"module-Ref.A\""
        checkHas html "id=\"ident\""
        let page ← IO.FS.readFile (out / "Ref.A.html")
        checkHas page "href=\"reference.html#ident\""
        checkHas page "href=\"reference.html#module-Ref.A\""
        -- (--check passes on what was just written, and fails when it changes)
        let o ← runOut (← wiz) ["doc", (dir / "src").toString, "-o", (dir / "site2").toString,
          "--web", (dir / "no-web").toString, "--reference", ref.toString, "--check"]
        checkHas o "is up to date"
        IO.FS.writeFile (ref / "index.md") (md ++ "\nstale\n")
        let p ← IO.Process.output { cmd := ← wiz, args := #["doc", (dir / "src").toString,
          "-o", (dir / "site3").toString, "--web", (dir / "no-web").toString,
          "--reference", ref.toString, "--check"] }
        check (p.exitCode == 1) s!"--check exit {p.exitCode}: {p.stdout}{p.stderr}"
        check (has p.stderr "is out of date") p.stderr },
    { name := "wiz doc --reference: every command kind is a section with its kind and signature", run := fun _ => do
        let dir ← mkTree kindsPkgFiles
        let out := dir / "site"
        let ref := dir / "reference"
        discard <| runOut (← wiz) ["doc", (dir / "src").toString, "-o", out.toString,
          "--web", (dir / "no-web").toString, "--reference", ref.toString]
        let md ← IO.FS.readFile (ref / "index.md")
        -- (one subsection per declaration, with the kind and the source)
        for k in ["def", "partial def", "axiom", "extern", "foreign type", "glue", "c struct",
            "structure", "class", "inductive", "coinductive", "sealed inductive", "instance",
            "theorem", "abbrev"] do
          checkHas md s!"{k} · `Kinds/All.wiz:"
        -- (the anchors are the fully qualified names, and the signature is the type)
        for n in ["aDef", "aEqns", "aPartial", "anAxiom", "anExtern", "aHandle", "aGlue",
            "AKindsPair", "AStructure", "AStructure.area", "AClass", "anInstance",
            "AnInductive", "ACoinductive", "ASealed", "aTheorem", "aLemma", "anAbbrev"] do
          checkHas md s!"<a id=\"{n}\"></a>"
        checkHas md "```text\nNat → Nat\n```"
        check (!has md "Nat.succ") "a declaration's body is in the manual" },
    libDocCase
  ]

def groups : List Group := [docGroup]

end Tests.Doc
