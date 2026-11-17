import Tests.Elab

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-! ## Web.React: a React-style UI framework for Wiz (lib/Web/React.wiz)

The framework's own half is pure, so these cases are elaboration and evaluation:
deterministic SSR, lens-addressed local state and its patches, keyed reorder, event
dispatch, escaping, and the quantity-1 `Owned` state cell. `web/framework/test.mjs`
runs the browser half (patch application and event delegation) under Node against the
same tree, `web/framework/gen.wiz`. -/

/-- A counter app (props-free), a keyed list, and `Msg`, shared by the cases. -/
def reactPrelude : String :=
  "import IO\nimport Optic\nimport Web.React\n" ++
  "inductive Msg where\n  | inc\n" ++
  "structure Model where\n  count : Nat\n" ++
  "def countL : Lens Model Nat := fun s => (s.count, fun n => Model.mk n)\n" ++
  "def view (s : Model) : React.VNode Msg :=\n" ++
  "  React.el \"div\" [React.class \"counter\"]\n" ++
  "    [React.el \"p\" List.nil [React.text \"count \", React.text (Nat.toString s.count)],\n" ++
  "     React.on \"click\" Msg.inc (React.el \"button\" List.nil [React.text \"+\"])]\n" ++
  "def app : React.App Model Msg := React.App.mk (Model.mk 0)\n" ++
  "  (fun m s => match m with | .inc => React.setState countL Nat.succ s) view\n" ++
  "def item (n : Nat) : React.VNode Msg :=\n" ++
  "  React.keyed (Nat.toString n) (React.el \"li\" List.nil [React.text (Nat.toString n)])\n" ++
  "def list (ns : List Nat) : React.VNode Msg :=\n" ++
  "  React.el \"ul\" List.nil (React.map item ns)\n"

/-- Elaborate with every library importable; no errors, and these infos. -/
def okReact (input : String) (infos : List String := []) : IO Unit := do
  let s := runFrontend (R := ZeroOneMany) input { trustedModule := Tests.libModule, loader := ← libLoader }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render input
  unless errs.isEmpty do throw (IO.userError s!"unexpected errors:\n{"\n".intercalate errs.toList}")
  checkEq (repr infos).pretty (repr (s.messages.toList.map (·.text))).pretty

/-- Exactly one error, mentioning `fragment`, with every library importable. -/
def failsReact (input : String) (fragment : String) : IO Unit := do
  let s := runFrontend (R := ZeroOneMany) input { trustedModule := Tests.libModule, loader := ← libLoader }
  let errs := (s.messages.filter (·.severity == .error)).map fun m => m.render input
  unless errs.size == 1 do throw (IO.userError s!"expected one error, got {errs.size}: {errs}")
  unless (errs[0]!.splitOn fragment).length > 1 do
    throw (IO.userError s!"error does not mention '{fragment}':\n{errs[0]!}")

def reactGroup : Group where
  name := "react"
  exercise := "lib/Web/React.wiz (web UI framework)"
  cases := [
    { name := "SSR: a component tree renders deterministic HTML", run := fun _ =>
        okReact (reactPrelude ++
          "#eval React.App.html app (Model.mk 2)\n" ++
          "#eval String.eq (React.App.html app (Model.mk 2)) (React.App.html app (Model.mk 2))")
          [r#""<div class=\"counter\"><p>count 2</p><button data-wiz-on-click=\"0\">+</button></div>""#,
           ".true"] },
    { name := "state: a dispatch is a lens update, and its patch is one text node", run := fun _ =>
        okReact (reactPrelude ++
          "#eval React.App.html app (React.App.dispatch app (Model.mk 2) 0)\n" ++
          "#eval React.App.patches app (Model.mk 2) (Model.mk 3)")
          [r#""<div class=\"counter\"><p>count 3</p><button data-wiz-on-click=\"0\">+</button></div>""#,
           r#""[{\"op\":\"text\",\"path\":\"0.0.0\",\"text\":\"count 3\"}]""#] },
    { name := "keyed lists: a rotation is two moves, not a re-render", run := fun _ =>
        okReact (reactPrelude ++
          "#eval React.patchesJson (React.Rendered.diff (React.render (list [1, 2, 3])) (React.render (list [2, 3, 1])))\n" ++
          "#eval React.patchesJson (React.Rendered.diff (React.render (list [1, 2])) (React.render (list [1, 2])))")
          [r#""[{\"op\":\"move\",\"path\":\"0\",\"src\":1,\"dst\":0},{\"op\":\"move\",\"path\":\"0\",\"src\":2,\"dst\":1}]""#,
           r#""[]""#] },
    { name := "events: the handler's event name is checked", run := fun _ =>
        okReact (reactPrelude ++
          "#eval React.App.html app (React.App.event app (Model.mk 2) \"click\" 0)\n" ++
          "#eval React.App.html app (React.App.event app (Model.mk 2) \"keydown\" 0)\n" ++
          "#eval React.App.html app (React.App.dispatch app (Model.mk 2) 9)")
          [r#""<div class=\"counter\"><p>count 3</p><button data-wiz-on-click=\"0\">+</button></div>""#,
           r#""<div class=\"counter\"><p>count 2</p><button data-wiz-on-click=\"0\">+</button></div>""#,
           r#""<div class=\"counter\"><p>count 2</p><button data-wiz-on-click=\"0\">+</button></div>""#] },
    { name := "escaping: text and attributes are escaped; raw is the trust boundary", run := fun _ =>
        okReact ("import Web.React\ninductive Msg where\n  | x\n" ++
          "#eval React.toHtml (React.text \"<b> & 'x'\" : React.VNode Msg)\n" ++
          "#eval React.toHtml (React.raw \"<b>ok</b>\" : React.VNode Msg)\n" ++
          "#eval React.toHtml (React.el \"p\" [React.attr \"title\" \"a\\\"b\"] [React.text \"x\"] : React.VNode Msg)")
          [r#""&lt;b&gt; &amp; &#39;x&#39;""#,
           r#""<b>ok</b>""#,
           r#""<p title=\"a&quot;b\">x</p>""#] },
    { name := "events: two events on one element are two attributes", run := fun _ =>
        okReact ("import Web.React\ninductive Msg where\n  | a\n  | b\n" ++
          "#eval React.toHtml (React.on \"click\" Msg.a (React.on \"keydown\" Msg.b (React.el \"button\" List.nil [React.text \"x\"])) : React.VNode Msg)")
          [r#""<button data-wiz-on-click=\"0\" data-wiz-on-keydown=\"1\">x</button>""#] },
    { name := "owned state: a quantity-1 cell is updated and ends once", run := fun _ =>
        okReact ("import Web.React\n" ++
          "#eval React.Owned.end (React.Owned.update (React.Owned.new 1) Nat.succ)\n" ++
          "#eval React.Owned.end (React.Owned.set (React.Owned.new 1) 7)")
          ["2", "7"] },
    { name := "owned state: using the cell twice is a type error", run := fun _ =>
        failsReact ("import Web.React\n" ++
          "def bad (1 o : React.Owned Nat) : Nat :=\n" ++
          "  let a := React.Owned.read o (fun _ => 1);\n" ++
          "  let b := React.Owned.read o (fun _ => 2);\n" ++
          "  a + b\n") "declared with quantity 1 but used ω" },
    { name := "owned state: dropping the cell is a type error", run := fun _ =>
        failsReact ("import Web.React\n" ++
          "def worse (1 o : React.Owned Nat) : Nat := 0\n") "declared with quantity 1 but used 0" }
  ]

builtin_initialize registerGroup reactGroup

end Tests.Elab
