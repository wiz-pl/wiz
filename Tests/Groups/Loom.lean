import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-! ## Web.Loom: the Loom UI framework for Wiz (lib/Web/Loom.wiz)

The framework's own half is pure, so these cases are elaboration and evaluation:
deterministic SSR, lens-addressed local state and its patches, keyed reorder, event
dispatch, escaping, and the quantity-1 `Owned` state cell. `web/framework/test.mjs`
runs the browser half (patch application and event delegation) under Node against the
same tree, `web/framework/gen.wiz`. -/

/-- A counter app (props-free), a keyed list, and `Msg`, shared by the cases. -/
def loomPrelude : String :=
  "import IO\nimport Optic\nimport Web.Loom\n" ++
  "inductive Msg where\n  | inc\n" ++
  "structure Model where\n  count : Nat\n" ++
  "def countL : Lens Model Nat := fun s => (s.count, fun n => Model.mk n)\n" ++
  "def view (s : Model) : Loom.VNode Msg :=\n" ++
  "  Loom.el \"div\" [Loom.class \"counter\"]\n" ++
  "    [Loom.el \"p\" List.nil [Loom.text \"count \", Loom.text (Nat.toString s.count)],\n" ++
  "     Loom.on \"click\" Msg.inc (Loom.el \"button\" List.nil [Loom.text \"+\"])]\n" ++
  "def app : Loom.App Model Msg := Loom.App.mk (Model.mk 0)\n" ++
  "  (fun m s => match m with | .inc => Loom.setState countL Nat.succ s) view\n" ++
  "def item (n : Nat) : Loom.VNode Msg :=\n" ++
  "  Loom.keyed (Nat.toString n) (Loom.el \"li\" List.nil [Loom.text (Nat.toString n)])\n" ++
  "def list (ns : List Nat) : Loom.VNode Msg :=\n" ++
  "  Loom.el \"ul\" List.nil (Loom.map item ns)\n"

/-- Elaborate with every library importable; no errors, and these infos. -/
def okLoom (input : String) (infos : List String := []) : IO Unit := do
  let s := runFrontend (R := ZeroOneMany) input { trustedModule := Tests.libModule, loader := ← libLoader }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render input
  unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
  checkEq (repr infos).pretty (repr (s.messages.toList.map (·.text))).pretty

/-- Exactly one error, mentioning `fragment`, with every library importable. -/
def failsLoom (input : String) (fragment : String) : IO Unit := do
  let s := runFrontend (R := ZeroOneMany) input { trustedModule := Tests.libModule, loader := ← libLoader }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render input
  unless errs.size == 1 do throw (IO.userError s!"expected one error, got {errs.size}: {errs}")
  unless (errs[0]!.splitOn fragment).length > 1 do
    throw (IO.userError s!"error does not mention '{fragment}':\n{errs[0]!}")

def loomGroup : Group where
  name := "loom"
  exercise := "lib/Web/Loom.wiz (web UI framework)"
  cases := [
    { name := "SSR: a component tree renders deterministic HTML", run := fun _ =>
        okLoom (loomPrelude ++
          "#eval Loom.App.html app (Model.mk 2)\n" ++
          "#eval String.eq (Loom.App.html app (Model.mk 2)) (Loom.App.html app (Model.mk 2))")
          [r#""<div class=\"counter\"><p>count 2</p><button data-wiz-on-click=\"0\">+</button></div>""#,
           ".true"] },
    { name := "state: a dispatch is a lens update, and its patch is one text node", run := fun _ =>
        okLoom (loomPrelude ++
          "#eval Loom.App.html app (Loom.App.dispatch app (Model.mk 2) 0)\n" ++
          "#eval Loom.App.patches app (Model.mk 2) (Model.mk 3)")
          [r#""<div class=\"counter\"><p>count 3</p><button data-wiz-on-click=\"0\">+</button></div>""#,
           r#""[{\"op\":\"text\",\"path\":\"0.0.0\",\"text\":\"count 3\"}]""#] },
    { name := "keyed lists: a rotation is two moves, not a re-render", run := fun _ =>
        okLoom (loomPrelude ++
          "#eval Loom.patchesJson (Loom.Rendered.diff (Loom.render (list [1, 2, 3])) (Loom.render (list [2, 3, 1])))\n" ++
          "#eval Loom.patchesJson (Loom.Rendered.diff (Loom.render (list [1, 2])) (Loom.render (list [1, 2])))")
          [r#""[{\"op\":\"move\",\"path\":\"0\",\"src\":1,\"dst\":0},{\"op\":\"move\",\"path\":\"0\",\"src\":2,\"dst\":1}]""#,
           r#""[]""#] },
    { name := "events: the handler's event name is checked", run := fun _ =>
        okLoom (loomPrelude ++
          "#eval Loom.App.html app (Loom.App.event app (Model.mk 2) \"click\" 0)\n" ++
          "#eval Loom.App.html app (Loom.App.event app (Model.mk 2) \"keydown\" 0)\n" ++
          "#eval Loom.App.html app (Loom.App.dispatch app (Model.mk 2) 9)")
          [r#""<div class=\"counter\"><p>count 3</p><button data-wiz-on-click=\"0\">+</button></div>""#,
           r#""<div class=\"counter\"><p>count 2</p><button data-wiz-on-click=\"0\">+</button></div>""#,
           r#""<div class=\"counter\"><p>count 2</p><button data-wiz-on-click=\"0\">+</button></div>""#] },
    { name := "escaping: text and attributes are escaped; raw is the trust boundary", run := fun _ =>
        okLoom ("import Web.Loom\ninductive Msg where\n  | x\n" ++
          "#eval Loom.toHtml (Loom.text \"<b> & 'x'\" : Loom.VNode Msg)\n" ++
          "#eval Loom.toHtml (Loom.raw \"<b>ok</b>\" : Loom.VNode Msg)\n" ++
          "#eval Loom.toHtml (Loom.el \"p\" [Loom.attr \"title\" \"a\\\"b\"] [Loom.text \"x\"] : Loom.VNode Msg)")
          [r#""&lt;b&gt; &amp; &#39;x&#39;""#,
           r#""<b>ok</b>""#,
           r#""<p title=\"a&quot;b\">x</p>""#] },
    { name := "events: two events on one element are two attributes", run := fun _ =>
        okLoom ("import Web.Loom\ninductive Msg where\n  | a\n  | b\n" ++
          "#eval Loom.toHtml (Loom.on \"click\" Msg.a (Loom.on \"keydown\" Msg.b (Loom.el \"button\" List.nil [Loom.text \"x\"])) : Loom.VNode Msg)")
          [r#""<button data-wiz-on-click=\"0\" data-wiz-on-keydown=\"1\">x</button>""#] },
    { name := "owned state: a quantity-1 cell is updated and ends once", run := fun _ =>
        okLoom ("import Web.Loom\n" ++
          "#eval Loom.Owned.end (Loom.Owned.update (Loom.Owned.new 1) Nat.succ)\n" ++
          "#eval Loom.Owned.end (Loom.Owned.set (Loom.Owned.new 1) 7)")
          ["2", "7"] },
    { name := "owned state: using the cell twice is a type error", run := fun _ =>
        failsLoom ("import Web.Loom\n" ++
          "def bad (1 o : Loom.Owned Nat) : Nat :=\n" ++
          "  let a := Loom.Owned.read o (fun _ => 1);\n" ++
          "  let b := Loom.Owned.read o (fun _ => 2);\n" ++
          "  a + b\n") "declared with quantity 1 but used ω" },
    { name := "owned state: dropping the cell is a type error", run := fun _ =>
        failsLoom ("import Web.Loom\n" ++
          "def worse (1 o : Loom.Owned Nat) : Nat := 0\n") "declared with quantity 1 but used 0" },
    { name := "composition: mapMsg lifts a child's messages and keeps the handler index", run := fun _ =>
        -- A child component with its own `Msg` composes into a page: the wrapper maps
        -- every handler (and only the handlers), so the page's dispatch sees `Page.child`.
        okLoom ("import IO\nimport Web.Loom\n" ++
          "inductive Child where\n  | tap\n" ++
          "inductive Page where\n  | child (m : Child)\n" ++
          "structure Model where\n  tag : Nat\n" ++
          "def child : Loom.VNode Child :=\n" ++
          "  Loom.on \"click\" Child.tap (Loom.el \"button\" List.nil [Loom.text \"x\"])\n" ++
          "def app : Loom.App Model Page := Loom.App.mk (Model.mk 0)\n" ++
          "  (fun m s => match m with | .child _ => Model.mk 1)\n" ++
          "  (fun _ => Loom.el \"div\" List.nil [Loom.mapMsg Page.child child])\n" ++
          "#eval Loom.toHtml (Loom.mapMsg Page.child child)\n" ++
          "#eval (Loom.App.dispatch app (Model.mk 0) 0).tag\n" ++
          "#eval (Loom.App.dispatch app (Model.mk 0) 1).tag")
          [r#""<button data-wiz-on-click=\"0\">x</button>""#, "1", "0"] },
    { name := "Widget: a slider and a plot render to the prefixed bundle, and an event patches it", run := fun _ =>
        -- Web.Widget's display format is the kernel's contract (`WIZ_WIDGET:` plus the
        -- bundle JSON); the plot's placeholder is `div.wiz-plot-canvas`. `handle` re-enters
        -- the session with the callback and diffs old against new.
        okLoom ("import Web.Widget\n" ++
          "def ws : List Widget.Widget :=\n" ++
          "  .cons (Widget.slider \"gain\" \"input\" \"0.50\" \"onGain\")\n" ++
          "    (.cons (Widget.plot \"trace\" \"click\" \"{}\" \"onGain\") .nil)\n" ++
          "def cb (e : Widget.Event) (wss : List Widget.Widget) : List Widget.Widget :=\n" ++
          "  List.map (fun w => match String.eq w.id e.widget with\n" ++
          "    | .true => Widget.setValue w e.value\n" ++
          "    | .false => w) wss\n" ++
          "#eval String.startsWith (Widget.display ws) Widget.prefix\n" ++
          "#eval String.contains (Widget.display ws) \"wiz-plot-canvas\"\n" ++
          "#eval String.contains (Widget.display ws) \"data-wiz-widget-kind\"\n" ++
          "#eval List.length (Widget.widgetsOf (Widget.display ws))\n" ++
          "#eval String.contains (Widget.handle cb (Widget.display ws) \"gain\" \"input\" \"0.75\") \"patches\"\n" ++
          "#eval String.contains (Widget.handle cb (Widget.display ws) \"gain\" \"input\" \"0.75\") \"\\\"op\\\"\"")
          [".true", ".true", ".true", "2", ".true", ".true"] },
    { name := "Widget: a Plot.Chart becomes a display-only widget whose fragment is the SVG", run := fun _ =>
        -- `Widget.plotOf` is the `lib/Plot.wiz` adapter: the SVG replaces the plot
        -- placeholder, so the notebook needs no front-end renderer for it.
        okLoom ("import Plot\nimport Web.Widget\n" ++
          "def chart : Plot.Chart :=\n" ++
          "  Plot.labels \"x\" \"y\" (Plot.chart \"W\" (Plot.frame [\n" ++
          "    Plot.line \"a\" [Plot.ptNat 0 1, Plot.ptNat 1 3, Plot.ptNat 2 2]]))\n" ++
          "def w : Widget.Widget := Widget.plotOf \"sales\" chart\n" ++
          "def ws : List Widget.Widget := List.cons w List.nil\n" ++
          "#eval String.eq w.kind \"plot\"\n" ++
          "#eval String.isEmpty w.callback\n" ++
          "#eval String.contains (Widget.html ws) \"<svg\"\n" ++
          "#eval String.contains (Widget.html ws) \"wiz-plot\"\n" ++
          "#eval Bool.not (String.contains (Widget.html ws) \"wiz-plot-canvas\")\n" ++
          "#eval String.startsWith (Widget.display ws) Widget.prefix")
          [".true", ".true", ".true", ".true", ".true", ".true"] }
  ]

builtin_initialize registerGroup loomGroup

end Tests.Elab
