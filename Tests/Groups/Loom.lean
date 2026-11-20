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
  "def mainView (s : Model) : Loom.VNode Msg :=\n" ++
  "  Loom.el \"div\" [Loom.class \"counter\"]\n" ++
  "    [Loom.el \"p\" List.nil [Loom.text \"count \", Loom.text (Nat.toString s.count)],\n" ++
  "     Loom.on \"click\" Msg.inc (Loom.el \"button\" List.nil [Loom.text \"+\"])]\n" ++
  "def app : Loom.App Model Msg := Loom.App.mk (Model.mk 0)\n" ++
  "  (fun m s => match m with | .inc => Loom.setState countL Nat.succ s) mainView\n" ++
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

/-- The state format's little prelude (`Web.Draft`, `Web.Playground`). -/
def draftPrelude : String :=
  "import Web.Draft\nimport Web.Editor\nimport Web.Examples\nimport Web.Loom\nimport Web.Playground\n" ++
  "def custom : Draft.State := Draft.State.mk \"def one : Nat := 1\\n\" \"\"\n" ++
  "def listsState : Draft.State := Draft.State.mk (Examples.codeOf \"lists\") \"lists\"\n" ++
  "def ready : Page := Page.effect Page.initial \"enable\" \"1\" \"\"\n"

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
    { name := "events: onPrevent marks the handler and the runtime decides", run := fun _ =>
        okLoom ("import Web.Loom\ninductive Msg where\n  | a\n  | b\n" ++
          "#eval Loom.toHtml (Loom.onPrevent \"keydown\" Msg.a (Loom.el \"textarea\" List.nil List.nil) : Loom.VNode Msg)\n" ++
          "#eval Loom.toHtml (Loom.onPrevent \"keydown\" Msg.b (Loom.on \"input\" Msg.a (Loom.el \"textarea\" List.nil List.nil)) : Loom.VNode Msg)")
          [r#""<textarea data-wiz-on-keydown=\"0\" data-wiz-prevent-keydown=\"1\"></textarea>""#,
           r#""<textarea data-wiz-on-keydown=\"0\" data-wiz-prevent-keydown=\"1\" data-wiz-on-input=\"1\"></textarea>""#] },
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
    { name := "state: base64url round-trips text, and refuses non-canonical input", run := fun _ =>
        okLoom (draftPrelude ++
          "#eval Draft.base64UrlEncode \"hello world\\n\"\n" ++
          "#eval String.eq (match Draft.base64UrlDecode (Draft.base64UrlEncode \"λ → ∀ 😀\") with | .some s => s | .none => \"\") \"λ → ∀ 😀\"\n" ++
          "#eval Draft.base64UrlDecode \"ab\"\n" ++
          "#eval Draft.base64UrlDecode \"a\"\n" ++
          "#eval Draft.base64UrlDecode \"%\"")
          [r#""aGVsbG8gd29ybGQK""#, ".true", ".none", ".none", ".none"] },
    { name := "state: the fragment is a preset id or the base64url code", run := fun _ =>
        okLoom (draftPrelude ++
          "#eval Draft.encodeFragment listsState\n" ++
          "#eval match Draft.decodeFragment \"#preset=lists\" with | .some s => s.preset | .none => \"none\"\n" ++
          "#eval String.eq (match Draft.decodeFragment (Draft.encodeFragment custom) with | .some s => s.code | .none => \"\" ) custom.code\n" ++
          "#eval Draft.decodeFragment \"#preset=nope\"\n" ++
          "#eval Draft.decodeFragment \"#code=ab\"\n" ++
          "#eval Draft.decodeFragment \"\"")
          ["\"#preset=lists\"", r#""lists""#, ".true", ".none", ".none", ".none"] },
    { name := "state: the draft is versioned JSON, and a stale preset is dropped", run := fun _ =>
        okLoom (draftPrelude ++
          "#eval String.eq (match Draft.parseDraft (Draft.serializeDraft custom) with | .some s => s.code | .none => \"\" ) custom.code\n" ++
          "#eval match Draft.parseDraft \"{\\\"version\\\":1,\\\"code\\\":\\\"custom\\\",\\\"preset\\\":\\\"lists\\\"}\" with | .some s => s.preset | .none => \"none\"\n" ++
          "#eval Draft.parseDraft \"{\\\"version\\\":2,\\\"code\\\":\\\"x\\\"}\"\n" ++
          "#eval Draft.parseDraft \"not json\"")
          [".true", r#""""#, ".none", ".none"] },
    { name := "state: the embedded Prelude is added only when there is no import", run := fun _ =>
        okLoom (draftPrelude ++
          "#eval String.eq (Draft.withPrelude \"def one : Nat := 1\") \"import Prelude\\n\\ndef one : Nat := 1\"\n" ++
          "#eval String.eq (Draft.withPrelude \"import Prelude\\ndef one : Nat := 1\") \"import Prelude\\ndef one : Nat := 1\"\n" ++
          "#eval String.eq (Draft.withPrelude \"  import Std\\ndef one : Nat := 1\") \"  import Std\\ndef one : Nat := 1\"\n" ++
          "#eval String.eq (Draft.withPrelude \"imported : Nat := 1\") \"import Prelude\\n\\nimported : Nat := 1\"")
          [".true", ".true", ".true", ".true"] },
    { name := "page: a step asks for effects and an ack clears them", run := fun _ =>
        okLoom (draftPrelude ++
          "#eval Page.requests Page.initial\n" ++
          "#eval String.contains (Page.requests (Page.update PageMsg.share \"\" Page.initial)) \"\\\"kind\\\":\\\"share\\\"\"\n" ++
          "#eval String.contains (Page.requests (Page.update PageMsg.share \"\" Page.initial)) \"#preset=basics\"\n" ++
          "#eval Page.requests (Page.ack (Page.ack (Page.update PageMsg.share \"\" Page.initial) \"share\") \"sync\")\n" ++
          "#eval String.contains (Page.requests (Page.update PageMsg.save \"\" Page.initial)) \"\\\"kind\\\":\\\"save\\\"\"")
          [r#""[]""#, ".true", ".true", r#""[]""#, ".true"] },
    { name := "page: an effect updates the page without a request", run := fun _ =>
        okLoom (draftPrelude ++
          "#eval (Page.effect Page.initial \"finished\" \"ok\\n3 : Nat\" \"done in 4 ms\").output.count\n" ++
          "#eval (Page.effect Page.initial \"finished\" \"ok\\n3 : Nat\" \"done in 4 ms\").output.statusKind\n" ++
          "#eval (Page.effect Page.initial \"failed\" \"error: x\" \"exit code 3\").output.count\n" ++
          "#eval (Page.effect Page.initial \"failed\" \"error: x\" \"exit code 3\").output.statusKind\n" ++
          "#eval (Page.effect Page.initial \"enable\" \"1\" \"\").editor.disabled\n" ++
          "#eval Page.requests (Page.effect Page.initial \"finished\" \"ok\" \"done\")\n" ++
          "#eval (Page.update (PageMsg.editor WebEditor.Msg.input) \"custom\" ready).preset\n" ++
          "#eval (Page.update (PageMsg.editor WebEditor.Msg.input) (Examples.codeOf \"lists\") ready).preset")
          [r#""2 lines""#, r#""ready""#, r#""exit code 3""#, r#""error""#, ".false", r#""[]""#,
           r#""""#, r#""lists""#] },
    { name := "page: the load precedence is fragment, draft, default", run := fun _ =>
        okLoom (draftPrelude ++
          "#eval (Page.effect Page.initial \"load\" (Draft.encodeFragment listsState) \"\").preset\n" ++
          "#eval String.eq (Page.effect Page.initial \"load\" (Draft.encodeFragment listsState) \"\").editor.text (Examples.codeOf \"lists\")\n" ++
          "#eval String.eq (Page.effect Page.initial \"load\" \"\" (Draft.serializeDraft custom)).editor.text custom.code\n" ++
          "#eval String.eq (Page.effect Page.initial \"load\" \"#nope\" \"\").editor.text (Examples.codeOf Examples.defaultExampleId)\n" ++
          "#eval (Page.effect Page.initial \"load\" \"#nope\" \"\").note")
          [r#""lists""#, ".true", ".true", ".true", r#""ignored an invalid playground link""#] },
    { name := "page: the keyboard policy consumes only its shortcuts", run := fun _ =>
        okLoom (draftPrelude ++
          "#eval Page.consume (Loom.splitEvent \"keydown\\n5\\nEnter\\nc\") ready\n" ++
          "#eval Page.consume (Loom.splitEvent \"keydown\\n5\\nEnter\") ready\n" ++
          "#eval Page.consume (Loom.splitEvent \"keydown\\n5\\ns\\ncm\") ready\n" ++
          "#eval Page.consume (Loom.splitEvent \"click\\n5\\n\") ready\n" ++
          "#eval (Page.update PageMsg.key \"Enter\\nc\" ready).loads\n" ++
          "#eval (Page.update PageMsg.key \"Enter\" ready).loads\n" ++
          "#eval (Page.update PageMsg.key \"s\\nm\" ready).save")
          [".true", ".false", ".true", ".false", "1", "0", "1"] },
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
