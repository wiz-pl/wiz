import Lean.Data.Json
import Wiz.Query
import Wiz.Rig.Instances
import Wiz.Infoview
import Wiz.Actions
import Wiz.Inlay
import Wiz.Semantic
import Wiz.Completion
import Wiz.Signature
import Wiz.Refs
import Wiz.Symbols
import Wiz.Socket
import Wiz.WebSocket
import Std.Sync.Channel

/-!
# The language server

`wiz lsp` speaks the Language Server Protocol over stdin/stdout: JSON-RPC messages with
`Content-Length` headers. It keeps every open document's text and a query engine
(`Query.lean`), so after an edit only the commands from the edit on are elaborated
again. Supported: diagnostics (`publishDiagnostics`), hover (the type of the identifier
under the cursor), go to definition (also into libraries), completion of global names,
and the infoview's requests (`wiz/plainGoal`, `wiz/interactiveGoals`, …; the protocol is
in `wiz-notes/infoview-protocol.md`): goals and expected types read from the info tree,
printed as tagged text whose tags are refs into the document's **session table**.
With `--infoview SOCK` it also serves infoviews on a Unix socket, and with `--ws PORT` on
a WebSocket (`serveWith`).

Positions: LSP counts lines and UTF-16 code units; we count Unicode characters, which
agree except for characters outside the Basic Multilingual Plane.
-/

namespace Wiz.LSP

open Lean (Json)

abbrev St := CommandState ZeroOneMany

structure Doc where
  text : String
  version : Option Int := none
  engine : Query.Engine ZeroOneMany := {}
  state : St := {}
  /-- the session: refs in `table` are valid while it stays the same -/
  session : Nat := 0
  table : Array (Subterm ZeroOneMany) := #[]
  /-- interactive results already given in this session (so polling reuses their refs) -/
  memo : Std.HashMap String Json := {}
  /-- code actions offered in this session, for `codeAction/resolve` -/
  actions : Array Actions.Action := #[]

structure Server where
  docs : Std.HashMap String Doc := {}
  /-- library modules: name ↦ (path, source) -/
  libs : Std.HashMap String (String × String) := {}
  /-- the modules from the toolchain's `lib/`, whose `builtin` registrations are trusted -/
  trusted : List String := []
  /-- (27a) `--trust-native` and `--native-fuel` -/
  trustNative : Bool := false
  nativeFuel : Nat := NativeRun.defaultFuel
  /-- (28) solvers: `--sat-solver`, `--solver-timeout` -/
  smt : Smt.Config := {}
  /-- the last session number handed out (sessions are unique over the server's life) -/
  sessions : Nat := 0
  /-- the client asked for `wiz/elaborated` notifications -/
  elaboratedNotes : Bool := false
  /-- the client resolves code actions' edits lazily (`codeAction/resolve`) -/
  resolveEdits : Bool := false
  /-- (`--infoview`) the editor's cursor, as far as its requests tell: (uri, position) -/
  cursor : Option (String × Json) := none
  /-- (`--infoview`) the last `wiz/infoview/cursor` sent, so the same one is not sent twice -/
  lastCursor : Option Json := none
  /-- (references, rename) the library modules that aren't the toolchain's, elaborated
  with their info trees: by module, with the hash of the source they were made from -/
  modules : Std.HashMap String (UInt64 × St) := {}

/-- Line and column (0-based) of a character offset. -/
def toPos (text : String) (off : Nat) : Json :=
  let pre := (text.toList.take off)
  let line := pre.count '\n'
  let col := (pre.reverse.takeWhile (· != '\n')).length
  Json.mkObj [("line", line), ("character", col)]

/-- The character offset of an LSP position. -/
def ofPos (text : String) (line col : Nat) : Nat := Id.run do
  let cs := text.toList
  let mut l := 0
  let mut i := 0
  while l < line && i < cs.length do
    if cs[i]! == '\n' then l := l + 1
    i := i + 1
  pure (i + col)

def range (text : String) (info : SourceInfo) : Json :=
  Json.mkObj [("start", toPos text info.start), ("end", toPos text (max info.stop (info.start + 1)))]

-- (the whole elaborator is specialised to `ZeroOneMany` here; the default limit of
-- 200000 heartbeats no longer covers compiling that)
set_option maxHeartbeats 800000 in
/-- Elaborate a text (incrementally, reusing `eng`) with the libraries available to `import`. -/
def elabText (srv : Server) (eng : Query.Engine ZeroOneMany) (text : String) : St × Query.Engine ZeroOneMany :=
  let libs := srv.libs
  let trusted := srv.trusted
  let init : St := { loader := fun m => (libs.get? m).map (·.2), termInfo := true,
                     trustedModule := trusted.contains, trustNative := srv.trustNative, nativeFuel := srv.nativeFuel, smt := srv.smt }
  let key₀ := hash (libs.toList.map (·.2.2) |>.toString)
  Query.elaborate eng text init key₀

set_option maxHeartbeats 800000 in
/-- Elaborate a document (incrementally) with the libraries available to `import`. -/
def elaborate (srv : Server) (doc : Doc) : Doc :=
  let (s, eng) := elabText srv doc.engine doc.text
  { doc with state := s, engine := eng }

/-- The modules `import` can reach, with their sources (for code actions). -/
def Server.importable (srv : Server) : List (String × String) :=
  srv.libs.toList.map fun (n, (_, src)) => (n, src)

/-- `textDocument/completion` (`Completion.lean`): a `CompletionList`. Patched copies of
the document are elaborated with its engine (the commands before the cursor are reused)
and then forgotten. -/
def completion (srv : Server) (doc : Doc) (off : Nat) : Json :=
  let r := Completion.complete
    { text := doc.text, off, state := doc.state, elabText := fun t => (elabText srv doc.engine t).1,
      modules := (srv.libs.toList.map (·.1)).toArray.qsort (· < ·) }
  let items := r.items.map fun (i : Completion.Item) =>
    Json.mkObj ([("label", Json.str i.label), ("kind", i.kind), ("sortText", Json.str (i.sortText ++ i.label)),
                 ("filterText", Json.str i.label),
                 ("textEdit", Json.mkObj [("range", Json.mkObj [("start", toPos doc.text i.start), ("end", toPos doc.text off)]),
                                          ("newText", Json.str i.insert)])] ++
                (if i.detail.isEmpty then [] else [("detail", Json.str i.detail)]) ++
                -- (11s) the global's doc comment
                (match i.global.bind doc.state.docOf? with
                 | some d => [("documentation", Json.mkObj [("kind", "markdown"), ("value", Json.str d)])]
                 | none => []))
  Json.mkObj [("isIncomplete", r.incomplete), ("items", Json.arr items)]

def diagnostic (srv : Server) (doc : Doc) (m : Msg) : Json :=
  let code := if m.code.isEmpty then [] else
    [("code", Json.str m.code),
     ("data", Json.mkObj ((Actions.messageData doc.state m doc.text srv.importable).map fun (k, vs) =>
        (k, if k == "name" then Json.str (vs.headD "") else Json.arr (vs.map Json.str).toArray)))]
  Json.mkObj ([("range", range doc.text m.info),
               ("severity", (match m.severity with | .error => 1 | .warning => 2 | .info => 3 : Nat)),
               ("source", "wiz"), ("message", m.text)] ++ code)

def diagnostics (srv : Server) (uri : String) (doc : Doc) : Json :=
  let ds := doc.state.messages.toList.map (diagnostic srv doc)
  Json.mkObj [("jsonrpc", "2.0"), ("method", "textDocument/publishDiagnostics"),
              ("params", Json.mkObj [("uri", uri), ("diagnostics", Json.arr ds.toArray)])]

def infoviewMethods : List String :=
  ["wiz/plainGoal", "wiz/plainTermGoal", "wiz/interactiveGoals", "wiz/interactiveTermGoal", "wiz/subtermInfo",
   "wiz/interactiveInfo"]

def capabilities : Json :=
  Json.mkObj [("capabilities", Json.mkObj [
    ("textDocumentSync", (1 : Nat)), ("hoverProvider", true), ("definitionProvider", true),
    ("declarationProvider", true),
    -- (also so that editors report cursor moves, for `--infoview`)
    ("documentHighlightProvider", true),
    ("referencesProvider", true), ("renameProvider", Json.mkObj [("prepareProvider", true)]),
    ("completionProvider", Json.mkObj [("triggerCharacters", Json.arr #["."])]),
    ("signatureHelpProvider", Json.mkObj [("triggerCharacters", Json.arr #[" ", "("]), ("retriggerCharacters", Json.arr #[" "])]),
    ("inlayHintProvider", true),
    ("semanticTokensProvider", Json.mkObj [("legend", Json.mkObj [("tokenTypes", Json.arr #["keyword"]), ("tokenModifiers", Json.arr #[])]),
                                           ("full", true)]),
    ("documentSymbolProvider", true), ("workspaceSymbolProvider", true), ("foldingRangeProvider", true),
    ("codeActionProvider", Json.mkObj [("codeActionKinds", Json.arr #["quickfix", "refactor.rewrite"]),
                                       ("resolveProvider", true)]),
    ("experimental", Json.mkObj [("wizInfoview", Json.mkObj [("version", (1 : Nat)),
      ("methods", Json.arr (infoviewMethods.map Json.str).toArray),
      ("notifications", Json.arr #["wiz/elaborated"])])])]),
    ("serverInfo", Json.mkObj [("name", "wiz")])]

/-! ## The infoview -/

/-- Tagged text as JSON; the tags' ids are shifted by `base` (the table's size before). -/
partial def ttJson (subs : Array (Subterm ZeroOneMany)) (base : Nat) : TT → Json
  | .text s => Json.mkObj [("text", s)]
  | .append xs => Json.mkObj [("append", Json.arr (xs.map (ttJson subs base)))]
  | .tag id t =>
    let sub := subs[id]!
    let tag := Json.mkObj ([("ref", Json.num (base + id)), ("kind", Json.str sub.kind)] ++
      (sub.name.toList.map fun n => ("name", Json.str n)))
    Json.mkObj [("tag", Json.arr #[tag, ttJson subs base t])]

/-- Run a tagged printer, adding its subterms to the document's table. -/
def withTable (doc : Doc) (x : StateM (Array (Subterm ZeroOneMany)) α) (k : α → (TT → Json) → Json) : Doc × Json :=
  let (a, subs) := x.run #[]
  let base := doc.table.size
  ({ doc with table := doc.table ++ subs }, k a (ttJson subs base))

def goalJson (g : TaggedGoal) (tj : TT → Json) : Json :=
  Json.mkObj [
    ("hyps", Json.arr (g.hyps.map fun (x, t, v) => Json.mkObj [("names", Json.arr #[Json.str x]),
      ("type", tj t), ("val", match v with | some v => tj v | none => Json.null)])),
    ("type", tj (if goalTarget g.target.flatten != g.target.flatten then .append #[.text "(", g.target, .text ")"] else g.target)),
    ("goalPrefix", "⊢ "),
    ("userName", match g.userName with | some n => Json.str n | none => Json.null)]

def plainGoals (gs : Array (GoalView ZeroOneMany)) (traces : Array String := #[]) (g : Option (Globals ZeroOneMany) := none) : Json :=
  let shown := gs.map (·.show g)
  let rendered := if shown.isEmpty then "no goals" else s!"```wiz\n{"\n\n".intercalate shown.toList}\n```"
  let rendered := if traces.isEmpty then rendered else s!"{rendered}\n\n{"\n\n".intercalate traces.toList}"
  Json.mkObj [("rendered", rendered), ("goals", Json.arr (shown.map Json.str)), ("messages", Json.arr (traces.map Json.str))]

/-- The info messages (`trace`, `trace_state`) of the tactic at `info`, in order: the
infoview shows them under its goals. -/
def tracesAt (st : St) (info : SourceInfo) : Array String :=
  (st.messages.filter fun m => m.severity == .info && info.start ≤ m.info.start && m.info.start < info.stop).map (·.text)

/-- Where a library module's source is, as a URI. -/
def location (srv : Server) (uri : String) (doc : Doc) (n : Name) : Json :=
  match doc.state.declSites.get? n with
  | some (info, "") => Json.mkObj [("uri", uri), ("range", range doc.text info)]
  | some (info, m) => match srv.libs.get? m with
    | some (path, src) => Json.mkObj [("uri", "file://" ++ path), ("range", range src info)]
    | none => Json.null
  | none => Json.null

/-! ## Syntax, imports and instances (11q) -/

/-- The source of a module (`""`: the document) and its URI. -/
def moduleSource (srv : Server) (uri : String) (doc : Doc) (m : String) : Option (String × String) :=
  if m.isEmpty then some (uri, doc.text) else (srv.libs.get? m).map fun (path, src) => ("file://" ++ path, src)

/-- A target (`Query.Target`) as an LSP `Location`. -/
def targetJson (srv : Server) (uri : String) (doc : Doc) : Query.Target → Json
  | .site info m => match moduleSource srv uri doc m with
    | some (u, src) => Json.mkObj [("uri", u), ("range", range src info)]
    | none => Json.null
  | .module m => match srv.libs.get? m with
    | some (path, _) => Json.mkObj [("uri", "file://" ++ path), ("range", range "" {})]
    | none => Json.null

/-- Where a target is, for people: `this file, line 3` or `Prelude, line 212`. -/
def targetText (srv : Server) (uri : String) (doc : Doc) : Query.Target → String
  | .site info m => match moduleSource srv uri doc m with
    | some (_, src) => s!"{if m.isEmpty then "this file" else m}, line {(lineCol src info.start).1 + 1}"
    | none => if m.isEmpty then "this file" else m
  | .module m => match srv.libs.get? m with
    | some (path, _) => path
    | none => m

/-- The first line of the command at a target (`syntax:75 (name := neg) "-" term:75 : term`). -/
def targetLine (srv : Server) (uri : String) (doc : Doc) : Query.Target → Option String
  | .site info m => do
    let (_, src) ← moduleSource srv uri doc m
    let text := String.ofList ((src.toList.drop info.start).take (info.stop - info.start))
    let line := (text.splitOn "\n").headD ""
    pure (if line.length > 120 then (line.take 117).toString ++ "…" else line)
  | .module _ => none

/-- What a handler is, in words. -/
def handlerText : SyntaxHandler → String
  | .rule .. => "macro rule"
  | .fn what f => s!"{what} {f}"

/-- The text of a range of the document, on one line (cut at 80 characters). -/
def rangeText (doc : Doc) (info : SourceInfo) : String :=
  let t := String.ofList ((doc.text.toList.drop info.start).take (info.stop - info.start))
  let t := " ".intercalate ((t.splitOn "\n").map (·.trimAscii.toString))
  if t.length > 80 then (t.take 77).toString ++ "…" else t

/-- The expansion a hover shows (cut at 600 characters). -/
def expansionText (e : Syntax) : String :=
  let t := e.reprint
  if t.length > 600 then (t.take 597).toString ++ "…" else t

/-- How a hover names the identifier at `off`: its name, except for a local a macro
introduced at the range of other source (Feral's `v_26` for a call `double (v.len)`, at
the call: Elab/ProcMacro.lean, `locateMarked`), which is named by that source when it
is short and on one line. -/
def identLabel (doc : Doc) (off : Nat) (n : Name) : String :=
  match Query.identAt doc.state off with
  | some (.ident i _ true _ _) =>
    let src := String.ofList ((doc.text.toList.drop i.start).take (i.stop - i.start))
    if src != n && !src.contains '\n' && src.length ≤ 60 && !src.isEmpty then src else n
  | _ => n

/-- The hover of a use of syntax or an `import` (`Query.syntaxAt`), as Markdown. -/
def syntaxHover (srv : Server) (uri : String) (doc : Doc) (es : Array (Info ZeroOneMany)) : Option String := do
  let e ← es[0]?
  let st := doc.state
  let mut parts : Array String := #[]
  -- the syntax and its type (the expected type where it was checked), as Lean shows it
  let ty := st.infos.findSome? fun
    | .term r g _ => if r.start == e.info.start && r.stop == e.info.stop then some (g.target.pretty g.names (some st.globals)) else none
    | _ => none
  -- else an identifier there (not checked against a type: a function applied, say)
  let ty := ty.orElse fun _ => st.infos.findSome? fun
    | .ident r _ _ names t => if r.start == e.info.start && r.stop == e.info.stop then some (t.pretty names (some st.globals)) else none
    | _ => none
  for x in es do
    match x with
    | .importMod _ m =>
      parts := parts.push s!"```wiz\nimport {m}\n```\nmodule `{m}`: {targetText srv uri doc (.module m)}"
    | .syntaxRef _ r =>
      let (what, name) := match r with
        | .kind k => ("syntax", k)
        | .cat c => ("syntax category", c)
      let head := match r, ty with
        | .kind _, some t => s!"```wiz\n{rangeText doc e.info} : {t}\n```\n"
        | _, _ => ""
      let site := Query.refSite st r
      let decl := match site.bind (targetLine srv uri doc) with
        | some l => s!"\n```wiz\n{l}\n```"
        | none => ""
      let at_ := match site with
        | some t => s!" ({targetText srv uri doc t})"
        | none => ""
      parts := parts.push s!"{head}{what} `{name}`{at_}{decl}"
    | .expansion _ _ h out =>
      let at_ := match Query.handlerSite st h with
        | some t => s!" ({targetText srv uri doc t})"
        | none => ""
      let body := match out with
        | some o => s!", expands to\n```wiz\n{expansionText o}\n```"
        | none => ""
      parts := parts.push s!"by {handlerText h}{at_}{body}"
    | _ => pure ()
  -- the instances found there (`a + b`: `Add Nat`)
  for i in st.infos do
    if let .inst r ns cls t := i then
      if r.start == e.info.start && r.stop == e.info.stop then
        parts := parts.push s!"instance `{t.pretty ns (some st.globals)} : {cls.pretty ns (some st.globals)}`"
  if parts.isEmpty then none else some ("\n\n".intercalate parts.toList)

/-- Names a command declares that the infoview doesn't list: what the elaborator makes
for its own use. -/
def auxiliaryDecl (n : Name) : Bool :=
  (n.splitOn "✝").length > 1 ||
  [".desc", ".casesOn", ".rec", ".ind", ".below", ".brecOn", ".noConfusion", ".sizeOf", ".elim", ".Tag"].any (n.endsWith ·)

/-- `wiz/interactiveInfo`: what the infoview shows at the cursor besides the goals and the
expected type. -/
def infoItems (srv : Server) (uri : String) (doc : Doc) (off : Nat) :
    StateM (Array (Subterm ZeroOneMany)) (Array (String × SourceInfo × String × Option String × Option TT × Json)) := do
  let st := doc.state
  let mut items := #[]
  -- the use of syntax (or the import) at the cursor
  for e in Query.syntaxAt st off do
    match e with
    | .importMod r m =>
      items := items.push ("import", r, s!"import {m}", some (targetText srv uri doc (.module m)), none,
        targetJson srv uri doc (.module m))
    | .syntaxRef r ref =>
      let (title, site) := match ref with
        | .kind k => (s!"syntax {k}", Query.refSite st ref)
        | .cat c => (s!"syntax category {c}", Query.refSite st ref)
      let at_ := match site with
        | some t => s!" ({targetText srv uri doc t})"
        | none => ""
      items := items.push ("syntax", r, title ++ at_, site.bind (targetLine srv uri doc), none,
        (site.map (targetJson srv uri doc)).getD Json.null)
    | .expansion r _ h out =>
      let site := Query.handlerSite st h
      let at_ := match site with
        | some t => s!" ({targetText srv uri doc t})"
        | none => ""
      items := items.push ("expansion", r, s!"{if out.isSome then "expanded" else "elaborated"} by {handlerText h}{at_}",
        out.map expansionText, none, (site.map (targetJson srv uri doc)).getD Json.null)
    | _ => pure ()
  -- the instances found at the innermost application
  for i in Query.instancesAt st off do
    if let .inst r ns cls t := i then
      let (nsr, tys) := (ns, ns.map fun _ => (none : Option (Term ZeroOneMany)))
      items := items.push ("instance", r, s!"instance {t.pretty ns (some st.globals)}", some (t.pretty ns (some st.globals)),
        some (← cls.prettyTagged nsr tys (some st.globals)), Json.null)
  -- the declarations of the command at the cursor
  for n in Query.declsAt st off do
    if auxiliaryDecl n then continue
    let some d := st.globals.find? n | continue
    let some (r, _) := st.declSites.get? n | continue
    items := items.push ("declaration", r, n, none, some (← d.type.prettyTagged [] [] (some st.globals)),
      targetJson srv uri doc (.site r ""))
  -- the messages at the cursor (`#check`, `#eval`, traces, errors)
  for m in st.messages do
    if m.info.start ≤ off && (off < m.info.stop || off == m.info.start) then
      let sev := match m.severity with | .error => "error" | .warning => "warning" | .info => "info"
      items := items.push ("message", m.info, sev, some m.text, none, Json.null)
  pure items

/-- The type of a subterm, from the kernel, if every variable in scope has a known type. -/
def subtermType (g : Globals ZeroOneMany) (sub : Subterm ZeroOneMany) : Option (Term ZeroOneMany) := do
  let tys ← sub.types.reverse.mapM id
  let ctx := (sub.names.reverse.zip tys).foldl (fun (ctx : Ctx ZeroOneMany) (x, ty) =>
    ctx.bind x (QPoly.const QuantitySyntax.explicitDefault) (Wiz.eval g ctx.env ty)) { globals := { g with sortHolesOk := true }, erased := true, proof := true }
  match Wiz.infer ctx sub.term with
  | .ok (ty, _) => some (quote g ctx.lvl ty)
  | .error _ => none

/-- The JSON number or string at `path`, if any. -/
def get? (j : Json) (path : List String) : Option Json :=
  path.foldlM (fun j k => (j.getObjVal? k).toOption) j

def getStr (j : Json) (path : List String) : String :=
  match get? j path with
  | some (.str s) => s
  | _ => ""

def getNat (j : Json) (path : List String) : Nat :=
  match get? j path with
  | some j => (j.getNat?.toOption).getD 0
  | none => 0

/-- Answer an infoview request on an open document. -/
def infoview (srv : Server) (uri : String) (doc : Doc) (method : String) (msg : Json) :
    Except (Int × String) (Doc × Json) := do
  let st := doc.state
  let off := ofPos doc.text (getNat msg ["params", "position", "line"]) (getNat msg ["params", "position", "character"])
  let memo (key : String) (x : Doc × Json) : Doc × Json :=
    match doc.memo.get? key with
    | some j => (doc, j)
    | none => let (d, j) := x; ({ d with memo := d.memo.insert key j }, j)
  match method with
  | "wiz/plainGoal" =>
    pure (doc, match Query.goalsAt st off with
      | some (_, info, gs) => plainGoals gs (tracesAt st info) (some st.globals)
      | none => Json.null)
  | "wiz/plainTermGoal" =>
    pure (doc, match Query.termGoalAt st off with
      | some (info, g) => Json.mkObj [("goal", g.show (some st.globals)), ("range", range doc.text info)]
      | none => Json.null)
  | "wiz/interactiveGoals" =>
    match Query.goalsAt st off with
    | none => pure (doc, Json.null)
    | some (key, info, gs) =>
      let k (tgs : Array TaggedGoal) (tj : TT → Json) : Json :=
        Json.mkObj [("goals", Json.arr (tgs.map (goalJson · tj))), ("range", range doc.text info),
                    ("session", doc.session), ("messages", Json.arr ((tracesAt st info).map Json.str))]
      pure (memo s!"goals {key}" (withTable doc (gs.mapM (·.tagged (some st.globals))) k))
  | "wiz/interactiveTermGoal" =>
    match Query.termGoalAt st off with
    | none => pure (doc, Json.null)
    | some (info, g) =>
      let k (tg : TaggedGoal) (tj : TT → Json) : Json :=
        Json.mkObj [("goal", goalJson tg tj), ("range", range doc.text info), ("session", doc.session)]
      pure (memo s!"term {info.start} {info.stop}" (withTable doc (g.tagged (some st.globals)) k))
  | "wiz/interactiveInfo" =>
    let k (items : Array (String × SourceInfo × String × Option String × Option TT × Json)) (tj : TT → Json) : Json :=
      if items.isEmpty then Json.null else
      Json.mkObj [("items", Json.arr (items.map fun (kind, r, title, text, ty, loc) => Json.mkObj [
          ("kind", kind), ("range", range doc.text r), ("title", title),
          ("text", match text with | some t => Json.str t | none => Json.null),
          ("type", match ty with | some t => tj t | none => Json.null),
          ("location", loc)])),
        ("session", doc.session)]
    pure (memo s!"info {off}" (withTable doc (infoItems srv uri doc off) k))
  | _ => -- wiz/subtermInfo
    let some session := (get? msg ["params", "session"]).bind (·.getNat?.toOption) | throw (-32602, "missing session")
    let some r := (get? msg ["params", "ref"]).bind (·.getNat?.toOption) | throw (-32602, "missing ref")
    if session != doc.session then throw (-32801, "stale session")
    let some sub := doc.table[r]? | throw (-32801, "unknown ref")
    let defn := match sub.kind, sub.name with
      | "const", some n => location srv uri doc n
      | _, _ => Json.null
    let k (ty : Option TT) (tj : TT → Json) : Json :=
      Json.mkObj [("text", sub.term.pretty sub.names (some st.globals)), ("kind", sub.kind),
        ("name", match sub.name with | some n => Json.str n | none => Json.null),
        ("type", match ty with | some t => tj t | none => Json.null),
        ("definition", defn), ("session", doc.session)]
    pure (memo s!"sub {r}" (withTable doc ((subtermType st.globals sub).mapM (·.prettyTagged sub.names sub.types (some st.globals))) k))

/-- A code action as JSON: with its edit, or (`resolveId`) with what `codeAction/resolve` needs. -/
def codeAction (srv : Server) (uri : String) (doc : Doc) (a : Actions.Action) (resolveId : Option Nat) : Json :=
  let diags := match a.fixes.bind (doc.state.messages[·]?) with
    | some m => [("diagnostics", Json.arr #[diagnostic srv doc m])]
    | none => []
  let rest := match resolveId with
    | some k => [("data", Json.mkObj [("uri", uri), ("session", doc.session), ("id", k)])]
    | none =>
      let edits := a.edits.map fun e =>
        Json.mkObj [("range", Json.mkObj [("start", toPos doc.text e.start), ("end", toPos doc.text e.stop)]),
                    ("newText", e.text)]
      [("edit", Json.mkObj [("changes", Json.mkObj [(uri, Json.arr edits)])])]
  Json.mkObj ([("title", Json.str a.title), ("kind", Json.str a.kind)] ++ diags ++ rest)

/-! ## References and rename (11x) -/

/-- The modules besides the open documents where a global's uses can be: the library
modules that aren't the toolchain's (a grail package's own and its dependencies'),
each elaborated once per source (kept in `srv.modules`). -/
def packageModules (srv : Server) : Server × Array (String × String × St) := Id.run do
  let mut srv := srv
  let mut out : Array (String × String × St) := #[]
  for (m, (path, src)) in srv.libs.toList do
    if srv.trusted.contains m then continue
    let uri := "file://" ++ path
    if srv.docs.contains uri then continue
    let h := hash src
    let st := match srv.modules.get? m with
      | some (h', st) => if h' == h then st else (elabText srv {} src).1
      | none => (elabText srv {} src).1
    srv := { srv with modules := srv.modules.insert m (h, st) }
    out := out.push (uri, src, st)
  (srv, out)

/-- The places of what is at `off` of `doc`: (uri, text, ranges) per document. A
global's in every open document and the package's modules, a local's in `doc`. -/
def referencesOf (srv : Server) (uri : String) (doc : Doc) (off : Nat) :
    Server × Option (Refs.Target × SourceInfo × Array (String × String × Array SourceInfo)) := Id.run do
  let some (t, r) := Refs.targetAt doc.state off | return (srv, none)
  match t with
  | .local .. => (srv, some (t, r, #[(uri, doc.text, Refs.rangesIn doc.state doc.text t)]))
  | .global _ =>
    let (srv, mods) := packageModules srv
    let docs := srv.docs.toList.toArray.map fun (u, d) => (u, d.text, d.state)
    let all := (docs ++ mods).map fun (u, text, st) => (u, text, Refs.rangesIn st text t)
    (srv, some (t, r, all.filter (!·.2.2.isEmpty)))

/-- Is a global declared in the toolchain's library (so that rename must refuse it)? -/
def inToolchain (srv : Server) (doc : Doc) (n : Name) : Bool :=
  match doc.state.declSites.get? n with
  | some (_, m) => !m.isEmpty && srv.trusted.contains m
  | none => true
/-! ## Symbols and folding (11v) -/

partial def symbolJson (doc : Doc) (sym : Symbols.Symbol) : Json :=
  Json.mkObj ([("name", Json.str sym.name), ("kind", sym.kind), ("range", range doc.text sym.range),
               ("selectionRange", range doc.text sym.range)] ++
              (if sym.detail.isEmpty then [] else [("detail", Json.str sym.detail)]) ++
              (if sym.children.isEmpty then [] else [("children", Json.arr (sym.children.map (symbolJson doc)))]))

/-- `workspace/symbol`: the declarations of the open documents and their imports whose
name contains `query` (ignoring case), at most 300. -/
def workspaceSymbols (srv : Server) (query : String) : Json := Id.run do
  let q := query.toLower
  let mut seen : Std.HashSet String := {}
  let mut out : Array Json := #[]
  -- the documents' own declarations, then the libraries'
  for own in [true, false] do
    for (uri, doc) in srv.docs.toList do
      for n in doc.state.globals.order do
        if out.size ≥ 300 then break
        let m := match doc.state.declSites.get? n with
          | some (_, m) => m
          | none => ""
        if m.isEmpty != own || Symbols.hidden n || seen.contains n then continue
        if !q.isEmpty && (n.toLower.splitOn q).length < 2 then continue
        let loc := location srv uri doc n
        if loc == Json.null then continue
        seen := seen.insert n
        out := out.push (Json.mkObj ([("name", Json.str n), ("kind", Symbols.kindOf doc.state.globals n false), ("location", loc)] ++
          (if m.isEmpty then [] else [("containerName", Json.str m)])))
  Json.arr out

/-- Handle one message; returns the replies (and notifications) to send. -/
def handle (srv : Server) (msg : Json) : Server × Array Json := Id.run do
  let method := getStr msg ["method"]
  let id := (msg.getObjVal? "id").toOption
  let reply (result : Json) : Json :=
    Json.mkObj [("jsonrpc", "2.0"), ("id", id.getD Json.null), ("result", result)]
  let replyError (code : Int) (message : String) : Json :=
    Json.mkObj [("jsonrpc", "2.0"), ("id", id.getD Json.null),
                ("error", Json.mkObj [("code", code), ("message", message)])]
  let uri := getStr msg ["params", "textDocument", "uri"]
  match method with
  | "initialize" =>
    let wants := get? msg ["params", "capabilities", "experimental", "wizElaborated"] == some (Json.bool true)
    let resolve := match get? msg ["params", "capabilities", "textDocument", "codeAction", "resolveSupport", "properties"] with
      | some (.arr ps) => ps.contains (Json.str "edit")
      | _ => false
    ({ srv with elaboratedNotes := wants, resolveEdits := resolve }, #[reply capabilities])
  | "shutdown" => (srv, #[reply Json.null])
  | "textDocument/didOpen" | "textDocument/didChange" =>
    let text := if method == "textDocument/didOpen" then getStr msg ["params", "textDocument", "text"]
      else match get? msg ["params", "contentChanges"] with
        | some (.arr cs) => match cs.back? with
          | some c => getStr c ["text"]
          | none => ""
        | _ => ""
    let version := (get? msg ["params", "textDocument", "version"]).bind (·.getInt?.toOption)
    let old := (srv.docs.get? uri).getD { text }
    let session := srv.sessions + 1
    let doc := elaborate srv { old with text, version, session, table := #[], memo := {}, actions := #[] }
    let note := Json.mkObj [("jsonrpc", "2.0"), ("method", "wiz/elaborated"),
      ("params", Json.mkObj [("uri", uri), ("version", match version with | some v => Json.num v | none => Json.null),
                             ("session", session)])]
    ({ srv with docs := srv.docs.insert uri doc, sessions := session },
     #[diagnostics srv uri doc] ++ (if srv.elaboratedNotes then #[note] else #[]))
  | "textDocument/didClose" => ({ srv with docs := srv.docs.erase uri }, #[])
  | "textDocument/inlayHint" =>
    let some doc := srv.docs.get? uri | return (srv, #[reply (Json.arr #[])])
    let pos (k : String) := ofPos doc.text (getNat msg ["params", "range", k, "line"]) (getNat msg ["params", "range", k, "character"])
    let hs := (Inlay.hintsIn doc.state doc.text (pos "start") (pos "end")).map fun h =>
      Json.mkObj [("position", toPos doc.text h.at_), ("label", Json.str h.label), ("kind", (1 : Nat))]
    (srv, #[reply (Json.arr hs)])
  | "textDocument/semanticTokens/full" =>
    let some doc := srv.docs.get? uri | return (srv, #[reply Json.null])
    let data := Semantic.encode doc.text (Semantic.keywords doc.state doc.text)
    (srv, #[reply (Json.mkObj [("data", Json.arr (data.map fun (n : Nat) => (n : Json)))])])
  | "textDocument/references" | "textDocument/documentHighlight" | "textDocument/prepareRename" | "textDocument/rename" =>
    let some doc := srv.docs.get? uri | return (srv, #[reply Json.null])
    let off := ofPos doc.text (getNat msg ["params", "position", "line"]) (getNat msg ["params", "position", "character"])
    let rangeIn (text : String) (r : SourceInfo) : Json :=
      Json.mkObj [("start", toPos text r.start), ("end", toPos text r.stop)]
    match method with
    | "textDocument/documentHighlight" =>
      match Refs.targetAt doc.state off with
      | some (t, _) => (srv, #[reply (Json.arr ((Refs.rangesIn doc.state doc.text t).map fun r =>
          Json.mkObj [("range", rangeIn doc.text r), ("kind", (1 : Nat))]))])
      | none => (srv, #[reply Json.null])
    | "textDocument/prepareRename" =>
      match Refs.targetAt doc.state off with
      | some (.global n, _) =>
        if inToolchain srv doc n then (srv, #[replyError (-32803) s!"{n} is declared in the toolchain's library"]) else
        match Refs.targetAt doc.state off with
        | some (_, r) => (srv, #[reply (Json.mkObj [("range", rangeIn doc.text r), ("placeholder", Json.str (Refs.textAt doc.text r))])])
        | none => (srv, #[reply Json.null])
      | some (_, r) => (srv, #[reply (Json.mkObj [("range", rangeIn doc.text r), ("placeholder", Json.str (Refs.textAt doc.text r))])])
      | none => (srv, #[reply Json.null])
    | "textDocument/references" =>
      let (srv, res) := referencesOf srv uri doc off
      match res with
      | some (_, _, docs) =>
        (srv, #[reply (Json.arr (docs.flatMap fun (u, text, rs) => rs.map fun r =>
          Json.mkObj [("uri", Json.str u), ("range", rangeIn text r)]))])
      | none => (srv, #[reply Json.null])
    | _ =>
      let new := getStr msg ["params", "newName"]
      if !Refs.validName new then return (srv, #[replyError (-32602) s!"'{new}' is not a name"])
      let (srv, res) := referencesOf srv uri doc off
      match res with
      | some (t, _, docs) =>
        if let .global n := t then
          if inToolchain srv doc n then return (srv, #[replyError (-32803) s!"{n} is declared in the toolchain's library"])
        let name := match t with
          | .global n => n
          | .local x .. => x
        -- edit the places that spell the whole name (not `p.norm` for `Point.norm`)
        let changes := docs.filterMap fun (u, text, rs) =>
          let es := (rs.filter (Refs.textAt text · == name)).map fun r =>
            Json.mkObj [("range", rangeIn text r), ("newText", Json.str new)]
          if es.isEmpty then none else some (u, Json.arr es)
        (srv, #[reply (Json.mkObj [("changes", Json.mkObj changes.toList)])])
      | none => (srv, #[replyError (-32602) "nothing to rename here"])
  | "textDocument/documentSymbol" =>
    let some doc := srv.docs.get? uri | return (srv, #[reply (Json.arr #[])])
    (srv, #[reply (Json.arr ((Symbols.documentSymbols doc.state).map (symbolJson doc)))])
  | "textDocument/foldingRange" =>
    let some doc := srv.docs.get? uri | return (srv, #[reply (Json.arr #[])])
    let rs := (Symbols.foldingRanges doc.state doc.text).map fun (a, b, k) =>
      Json.mkObj ([("startLine", (a : Json)), ("endLine", (b : Json))] ++ (if k.isEmpty then [] else [("kind", Json.str k)]))
    (srv, #[reply (Json.arr rs)])
  | "workspace/symbol" => (srv, #[reply (workspaceSymbols srv (getStr msg ["params", "query"]))])
  | "textDocument/codeAction" =>
    let some doc := srv.docs.get? uri | return (srv, #[reply (Json.arr #[])])
    let pos (k : String) := ofPos doc.text (getNat msg ["params", "range", k, "line"]) (getNat msg ["params", "range", k, "character"])
    let acts := Actions.actionsAt doc.state doc.text (pos "start") (pos "end") srv.importable
    let base := doc.actions.size
    let json := acts.mapIdx fun i a => codeAction srv uri doc a (if srv.resolveEdits then some (base + i) else none)
    ({ srv with docs := srv.docs.insert uri { doc with actions := doc.actions ++ acts } }, #[reply (Json.arr json)])
  | "codeAction/resolve" =>
    let auri := getStr msg ["params", "data", "uri"]
    let some doc := srv.docs.get? auri | return (srv, #[replyError (-32801) "unknown document"])
    let some session := (get? msg ["params", "data", "session"]).bind (·.getNat?.toOption) | return (srv, #[replyError (-32602) "missing session"])
    let some k := (get? msg ["params", "data", "id"]).bind (·.getNat?.toOption) | return (srv, #[replyError (-32602) "missing id"])
    if session != doc.session then return (srv, #[replyError (-32801) "the document changed"])
    let some a := doc.actions[k]? | return (srv, #[replyError (-32801) "unknown action"])
    (srv, #[reply (codeAction srv auri doc a none)])
  | "wiz/plainGoal" | "wiz/plainTermGoal" | "wiz/interactiveGoals" | "wiz/interactiveTermGoal" | "wiz/subtermInfo"
  | "wiz/interactiveInfo" =>
    let some doc := srv.docs.get? uri | return (srv, #[replyError (-32602) s!"unknown document {uri}"])
    match infoview srv uri doc method msg with
    | .ok (doc, j) => ({ srv with docs := srv.docs.insert uri doc }, #[reply j])
    | .error (c, m) => (srv, #[replyError c m])
  | "textDocument/signatureHelp" =>
    let some doc := srv.docs.get? uri | return (srv, #[reply Json.null])
    let off := ofPos doc.text (getNat msg ["params", "position", "line"]) (getNat msg ["params", "position", "character"])
    match Signature.helpAt doc.state doc.text off (fun t => (elabText srv doc.engine t).1) with
    | some h =>
      let ps := h.params.map fun (a, b) => Json.mkObj [("label", Json.arr #[(a : Nat), (b : Nat)])]
      let docs := match h.doc with
        | some d => [("documentation", Json.mkObj [("kind", "markdown"), ("value", Json.str d)])]
        | none => []
      (srv, #[reply (Json.mkObj [("signatures", Json.arr #[Json.mkObj ([("label", Json.str h.label), ("parameters", Json.arr ps)] ++ docs)]),
                                 ("activeSignature", (0 : Nat)), ("activeParameter", h.active)])])
    | none => (srv, #[reply Json.null])
  | "textDocument/hover" | "textDocument/definition" | "textDocument/declaration" | "textDocument/completion" =>
    let some doc := srv.docs.get? uri | return (srv, #[reply Json.null])
    let off := ofPos doc.text (getNat msg ["params", "position", "line"]) (getNat msg ["params", "position", "character"])
    match method with
    | "textDocument/hover" =>
      let md? := match syntaxHover srv uri doc (Query.syntaxAt doc.state off) with
        | some md => some md
        | none => (Query.hoverAt doc.state off).map fun (n, ty) =>
            -- (11s) a global's doc comment, as Markdown under its type (a local has none)
            let isLocal := match Query.identAt doc.state off with
              | some (.ident _ _ true _ _) => true
              | _ => false
            let docs := if isLocal then "" else match doc.state.docOf? n with
              | some d => s!"\n\n---\n\n{d}"
              | none => ""
            s!"```wiz\n{identLabel doc off n} : {ty}\n```{docs}"
      match md? with
      | some md => (srv, #[reply (Json.mkObj [("contents", Json.mkObj [("kind", "markdown"), ("value", md)])])])
      | none => (srv, #[reply Json.null])
    | "textDocument/definition" | "textDocument/declaration" =>
      -- one location, or (several macro rules, say) a list
      let ts := (Query.targetsAt doc.state off (decl := method == "textDocument/declaration")).filterMap fun t =>
        match targetJson srv uri doc t with
        | .null => none
        | j => some j
      (srv, #[reply (if ts.size == 1 then ts[0]! else if ts.isEmpty then Json.null else Json.arr ts)])
    | _ => (srv, #[reply (completion srv doc off)])
  | _ => (srv, if id.isSome then #[reply Json.null] else #[])

/-! ## The infoview socket (`wiz lsp --infoview SOCK`, protocol §8)

Besides stdio, the server listens on a Unix socket; infoviews (agent/infoview-clients'
terminal and web clients) connect to it. The editor never tells the server where its
cursor is, so the server infers it from the editor's requests: any request with a
`position` (hover, `documentHighlight`, definition, completion, the `wiz/*` methods…)
and a `codeAction` (at its range's start; editors ask for code actions on every cursor
move). On a move, and after each elaboration of the cursor's document, every connected
infoview gets the notification `wiz/infoview/cursor` `{textDocument: {uri}, position,
session}`, then pulls with ordinary `wiz/*` requests on the socket. -/

/-- The cursor an editor message reveals, if any: (uri, position). -/
def cursorOf (msg : Json) : Option (String × Json) := do
  let uri := getStr msg ["params", "textDocument", "uri"]
  if uri.isEmpty || (msg.getObjVal? "id").toOption.isNone then none
  match get? msg ["params", "position"], get? msg ["params", "range", "start"] with
  | some p, _ => pure (uri, p)
  | none, some p => if getStr msg ["method"] == "textDocument/codeAction" then pure (uri, p) else none
  | none, none => none

/-- The `wiz/infoview/cursor` notification for a cursor (with its document's session). -/
def cursorNote (srv : Server) (uri : String) (pos : Json) : Json :=
  let session : Json := match srv.docs.get? uri with
    | some d => d.session
    | none => Json.null
  Json.mkObj [("jsonrpc", "2.0"), ("method", "wiz/infoview/cursor"),
    ("params", Json.mkObj [("textDocument", Json.mkObj [("uri", uri)]), ("position", pos), ("session", session)])]

/-- After the editor's message `msg` was handled: the cursor note to send infoviews, if
the cursor moved or its document was elaborated again. The first document opened
before any cursor move puts the cursor at its start. -/
def infoviewCursor (srv : Server) (msg : Json) : Server × Option Json :=
  let method := getStr msg ["method"]
  let uri := getStr msg ["params", "textDocument", "uri"]
  let cur : Option (String × Json) :=
    if method == "textDocument/didOpen" || method == "textDocument/didChange" then
      match srv.cursor with
      | some (u, p) => if u == uri then some (u, p) else none
      | none => some (uri, Json.mkObj [("line", (0 : Nat)), ("character", (0 : Nat))])
    else match cursorOf msg with
      | some (u, p) => if srv.docs.contains u then some (u, p) else none
      | none => none
  match cur with
  | none => (srv, none)
  | some (u, p) =>
    let note := cursorNote srv u p
    let srv := { srv with cursor := some (u, p) }
    if srv.lastCursor == some note then (srv, none) else ({ srv with lastCursor := some note }, some note)

/-- Handle a message from an infoview: the `wiz/*` requests (sessions and refs are the
editor's), `initialize` (answered, changing nothing), and nothing else. -/
def handleInfoview (srv : Server) (msg : Json) : Server × Array Json :=
  let method := getStr msg ["method"]
  match (msg.getObjVal? "id").toOption with
  | none => (srv, #[])
  | some id =>
    if infoviewMethods.contains method then handle srv msg
    else if method == "initialize" || method == "shutdown" then
      (srv, #[Json.mkObj [("jsonrpc", "2.0"), ("id", id), ("result", if method == "initialize" then capabilities else Json.null)]])
    else (srv, #[Json.mkObj [("jsonrpc", "2.0"), ("id", id),
      ("error", Json.mkObj [("code", (-32601 : Int)), ("message", s!"{method} is not available on the infoview socket")])]])

/-- Read one message: headers, a blank line, then `Content-Length` bytes of JSON. -/
partial def readMessage (stdin : IO.FS.Stream) : IO (Option Json) := do
  let mut len := 0
  repeat
    let line ← stdin.getLine
    if line.isEmpty then return none
    let line := line.trimAscii.toString
    if line.isEmpty then break
    if line.startsWith "Content-Length:" then len := ((line.drop 15).trimAscii.toString).toNat!
  let body ← stdin.read len.toUSize
  match Json.parse (String.fromUTF8! body) with
  | .ok j => pure (some j)
  | .error _ => pure (some Json.null)

def writeMessage (stdout : IO.FS.Stream) (j : Json) : IO Unit := do
  let body := j.compress
  stdout.putStr s!"Content-Length: {body.utf8ByteSize}\r\n\r\n{body}"
  stdout.flush

/-- An infoview's connection, as the server's loop sees it. -/
structure Conn where
  /-- its socket (to shut it down) -/
  fd : UInt32
  send : Json → IO Unit
  /-- a WebSocket client, which may also open and edit documents and ask anything an
  editor may (the web infoview is its own editor); the Unix socket's infoviews only pull -/
  editing : Bool := false
  /-- (a WebSocket client) it asked for `wiz/elaborated` notifications -/
  elaborated : Bool := false

/-- What the server waits for in `--infoview`/`--ws` mode: messages from every side. -/
inductive Event where
  | editor (msg : Json)
  /-- the editor's stream ended (or it sent `exit`) -/
  | editorDone
  | connected (k : Nat) (conn : Conn)
  | infoview (k : Nat) (msg : Json)
  | disconnected (k : Nat)

instance : Inhabited Event := ⟨.editorDone⟩

/-- Where the server listens besides stdio. -/
structure Listen where
  /-- `--infoview SOCK`: a Unix socket for infoviews (§8.1) -/
  infoview : Option String := none
  /-- `--ws [ADDR:]PORT`: a WebSocket (§8.2) on (address, port); port 0 takes a free one -/
  ws : Option (UInt32 × UInt16) := none
  /-- (11w) the directory of the web infoview's files (`web/build.sh`'s output), which the
  WebSocket's port also serves over HTTP (`WebSocket.webAssets`) -/
  web : Option String := none

/-- Handle a message from a WebSocket client: like an infoview's, but documents may be
opened and edited, and every request is answered. Its `initialize` changes only its own
settings: `wizElaborated` (`wants`, returned updated) asks for `wiz/elaborated` after each
elaboration of a document it opened or changed. -/
def handleWs (srv : Server) (wants : Bool) (msg : Json) : Server × Array Json × Bool :=
  if getStr msg ["method"] == "initialize" then
    let (srv, out) := handleInfoview srv msg
    (srv, out, get? msg ["params", "capabilities", "experimental", "wizElaborated"] == some (Json.bool true))
  else
    let (srv', out) := handle { srv with elaboratedNotes := wants } msg
    ({ srv' with elaboratedNotes := srv.elaboratedNotes }, out, wants)

/-- Serve the editor on `stdio` (if any) until `exit`, and infoviews on the sockets of
`listen`: several kinds of threads (the editor's reader, an acceptor per socket, a reader
per infoview) feed one channel, and this loop handles the messages in order, so the
server's state is never shared. `ready` gets the WebSocket's port once it listens.
Without `stdio`, the server runs until it is killed. -/
partial def serveWith (libs : Std.HashMap String (String × String)) (stdio : Option (IO.FS.Stream × IO.FS.Stream))
    (listen : Listen) (ready : UInt16 → IO Unit := fun _ => pure ()) (trusted : List String := [])
    (native : Bool × Nat := (false, NativeRun.defaultFuel)) (smt : Smt.Config := {}) : IO Unit := do
  let ch ← Std.Channel.Sync.new (α := Event)
  let next ← IO.mkRef 0
  let fresh : IO Nat := next.modifyGet fun k => (k, k + 1)
  let rec readEditor (input : IO.FS.Stream) : IO Unit := do
    match ← readMessage input with
    | none => ch.send .editorDone
    | some m => ch.send (.editor m); if getStr m ["method"] == "exit" then pure () else readEditor input
  let rec readLoop (k : Nat) (recv : IO (Option Json)) : IO Unit := do
    match ← (try recv catch _ => pure none) with
    | none => ch.send (.disconnected k)
    | some m => ch.send (.infoview k m); readLoop k recv
  -- the Unix socket: Content-Length framing, as on stdio
  let unixConn (fd : UInt32) (r w : IO.FS.Handle) : IO Unit := do
    let k ← fresh
    let out := IO.FS.Stream.ofHandle w
    ch.send (.connected k { fd, send := writeMessage out })
    readLoop k (readMessage (IO.FS.Stream.ofHandle r))
  -- a WebSocket: the handshake (on this connection's own thread), then a message per frame
  let wsConn (fd : UInt32) (r w : IO.FS.Handle) : IO Unit := do
    let (r, w) := (IO.FS.Stream.ofHandle r, IO.FS.Stream.ofHandle w)
    unless ← (try WebSocket.accept r w listen.web catch _ => pure false) do Socket.shutdown fd; return
    let k ← fresh
    ch.send (.connected k { fd, send := fun j => WebSocket.sendText w j.compress, editing := true })
    readLoop k do
      let some text ← WebSocket.recvText r w | return none
      pure (some ((Json.parse text).toOption.getD Json.null))
  let rec acceptLoop (lfd : UInt32) (serveConn : UInt32 → IO.FS.Handle → IO.FS.Handle → IO Unit) : IO Unit := do
    match ← (try some <$> Socket.accept lfd catch _ => pure none) with
    | none => pure ()
    | some (fd, r, w) =>
      let _ ← IO.asTask (prio := .dedicated) (serveConn fd r w)
      acceptLoop lfd serveConn
  let unixFd ← listen.infoview.mapM Socket.listen
  if let (some fd, some _) := (unixFd, listen.infoview) then
    let _ ← IO.asTask (prio := .dedicated) (acceptLoop fd unixConn)
  let wsFd ← listen.ws.mapM fun (addr, port) => Socket.tcpListen addr port
  -- the WebSocket listener: from `--ws`, or (11w) started by `wiz/browserInfoview`
  let wsRef ← IO.mkRef wsFd
  if let some (fd, port) := wsFd then
    let _ ← IO.asTask (prio := .dedicated) (acceptLoop fd wsConn)
    ready port
  -- (11w) `wiz/browserInfoview` from the editor: listen on a WebSocket (on 127.0.0.1, a
  -- free port) unless already listening, and say where the page is
  let browser (msg : Json) : IO Json := do
    let port ← match ← wsRef.get with
      | some (_, p) => pure p
      | none =>
        let (fd, p) ← Socket.tcpListen Socket.loopback 0
        wsRef.set (some (fd, p))
        let _ ← IO.asTask (prio := .dedicated) (acceptLoop fd wsConn)
        ready p
        pure p
    let res : Json := match listen.web with
      | some _ => Json.mkObj [("port", port.toNat), ("url", s!"http://127.0.0.1:{port}/infoview.html?port={port}&follow=1")]
      | none => Json.mkObj [("port", port.toNat), ("url", Json.null),
          ("message", "the web infoview is not built: run web/build.sh in a checkout, or use a release toolchain")]
    pure (Json.mkObj [("jsonrpc", "2.0"), ("id", (msg.getObjVal? "id").toOption.getD Json.null), ("result", res)])
  if let some (input, _) := stdio then
    let _ ← IO.asTask (prio := .dedicated) (readEditor input)
  let rec loop (srv : Server) (conns : Std.HashMap Nat Conn) : IO (Std.HashMap Nat Conn) := do
    -- send to one infoview; a failed write drops it
    let sendTo (conns : Std.HashMap Nat Conn) (k : Nat) (js : Array Json) := do
      let some c := conns.get? k | pure conns
      try for j in js do c.send j
          pure conns
      catch _ => Socket.shutdown c.fd; pure (conns.erase k)
    let broadcast (conns : Std.HashMap Nat Conn) (note : Option Json) := do
      let mut conns := conns
      if let some n := note then
        for k in conns.keys do conns ← sendTo conns k #[n]
      pure conns
    match ← ch.recv with
    | .editorDone => pure conns
    | .editor msg =>
      if getStr msg ["method"] == "exit" then return conns
      if getStr msg ["method"] == "wiz/browserInfoview" then
        let r ← try browser msg catch e =>
          pure (Json.mkObj [("jsonrpc", "2.0"), ("id", (msg.getObjVal? "id").toOption.getD Json.null),
            ("error", Json.mkObj [("code", (-32603 : Int)), ("message", s!"cannot listen: {e}")])])
        if let some (_, output) := stdio then writeMessage output r
        return ← loop srv conns
      let (srv, out) := handle srv msg
      if let some (_, output) := stdio then
        for j in out do writeMessage output j
      let (srv, note) := infoviewCursor srv msg
      loop srv (← broadcast conns note)
    | .connected k c =>
      let conns := conns.insert k c
      let conns ← match srv.cursor with
        | some (u, p) => sendTo conns k #[cursorNote srv u p]
        | none => pure conns
      loop srv conns
    | .infoview k msg =>
      let some c := conns.get? k | loop srv conns
      if !c.editing then
        let (srv, out) := handleInfoview srv msg
        return ← loop srv (← sendTo conns k out)
      -- a WebSocket client: its `exit` closes its connection only
      if getStr msg ["method"] == "exit" then
        Socket.shutdown c.fd
        return ← loop srv (conns.erase k)
      let (srv, out, wants) := handleWs srv c.elaborated msg
      let conns ← sendTo (conns.insert k { c with elaborated := wants }) k out
      let (srv, note) := infoviewCursor srv msg
      loop srv (← broadcast conns note)
    | .disconnected k =>
      if let some c := conns.get? k then Socket.shutdown c.fd
      loop srv (conns.erase k)
  let conns ← loop { libs, trusted, trustNative := native.1, nativeFuel := native.2, smt } {}
  -- stop the other threads: the acceptors and every infoview's reader see the end
  if let (some fd, some sock) := (unixFd, listen.infoview) then Socket.close fd sock
  if let some (fd, _) ← wsRef.get then Socket.closeFd fd
  for (_, c) in conns do Socket.shutdown c.fd

/-- `serveWith` for the editor on `input`/`output` and infoviews on the Unix socket `sock`. -/
def serveInfoview (libs : Std.HashMap String (String × String)) (input output : IO.FS.Stream) (sock : String)
    (trusted : List String := []) : IO Unit :=
  serveWith libs (some (input, output)) { infoview := some sock } (trusted := trusted)

/-- Serve until `exit`: on stdin/stdout (unless `stdio := false`), and on the sockets of
`listen`. -/
partial def serve (libs : Std.HashMap String (String × String)) (listen : Listen := {}) (stdio : Bool := true)
    (trusted : List String := []) (native : Bool × Nat := (false, NativeRun.defaultFuel)) (smt : Smt.Config := {}) : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  -- (11w) always through `serveWith`: `wiz/browserInfoview` may start a WebSocket later
  let ready (port : UInt16) := IO.eprintln s!"wiz lsp: WebSocket on port {port}"
  serveWith libs (if stdio then some (stdin, stdout) else none) listen ready trusted native smt

end Wiz.LSP
