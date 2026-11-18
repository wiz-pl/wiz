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
          "def worse (1 o : Loom.Owned Nat) : Nat := 0\n") "declared with quantity 1 but used 0" }
  ]

builtin_initialize registerGroup loomGroup

end Tests.Elab
