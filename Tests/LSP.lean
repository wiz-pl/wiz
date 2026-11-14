import Wiz
import Tests.Harness

open Wiz

set_option compiler.extract_closed false

namespace Tests.LSP

abbrev St := CommandState ZeroOneMany

def prelude : IO String := IO.FS.readFile "lib/Prelude.wiz"

/-- Elaborate `src` (which imports the prelude) as the language server does. -/
def elabSrc (src : String) (termInfo : Bool := true) : IO St := do
  let p ← prelude
  let init : St := { trustedModule := Tests.libModule, loader := fun m => if m == "Prelude" then some p else none, termInfo }
  pure (Query.elaborate {} src init).1

/-- The character offset just after the `k`th occurrence of `needle` (plus `delta`). -/
def offAfter (src needle : String) (delta : Int := 0) (k : Nat := 0) : Nat :=
  let pre := (src.splitOn needle).take (k + 1)
  let n := (needle.length * k) + (pre.foldl (· + ·.length) 0) + needle.length
  (n + delta).toNat

def goalsText (s : St) (off : Nat) : String :=
  match Query.goalsAt s off with
  | some (_, _, gs) => if gs.isEmpty then "no goals" else "\n\n".intercalate (gs.map (·.show)).toList
  | none => "none"

def termGoalText (s : St) (off : Nat) : String :=
  match Query.termGoalAt s off with
  | some (_, g) => g.show
  | none => "none"

/-! ## The language server, through `LSP.handle` -/

def req (s : String) : Lean.Json := (Lean.Json.parse s).toOption.get!

def server : IO LSP.Server := do
  pure { libs := ({} : Std.HashMap String (String × String)).insert "Prelude" ("lib/Prelude.wiz", ← prelude),
         trusted := ["Prelude"] }

def lineCol (src : String) (off : Nat) : Nat × Nat :=
  let pre := src.toList.take off
  (pre.count '\n', (pre.reverse.takeWhile (· != '\n')).length)

def posJson (src : String) (off : Nat) : String :=
  let (l, c) := lineCol src off
  s!"\{\"line\":{l},\"character\":{c}}"

/-- Open `src` as `file:///t.wiz`; returns the server and the messages it sent. -/
def openDoc (src : String) (init : Lean.Json := req "{\"jsonrpc\":\"2.0\",\"id\":0,\"method\":\"initialize\",\"params\":{}}")
    (srv? : Option LSP.Server := none) : IO (LSP.Server × Array Lean.Json) := do
  let (srv, _) := LSP.handle (← match srv? with | some s => pure s | none => server) init
  let msg := Lean.Json.mkObj [("jsonrpc", "2.0"), ("method", "textDocument/didOpen"),
    ("params", Lean.Json.mkObj [("textDocument", Lean.Json.mkObj [("uri", "file:///t.wiz"), ("version", (1 : Nat)), ("text", src)])])]
  pure (LSP.handle srv msg)

/-- A request at a position; returns the server and the reply's `result` (or `error`). -/
def ask (srv : LSP.Server) (method : String) (src : String) (off : Nat) : LSP.Server × Lean.Json :=
  let (srv, out) := LSP.handle srv (req s!"\{\"jsonrpc\":\"2.0\",\"id\":9,\"method\":\"{method}\",\"params\":\{\"textDocument\":\{\"uri\":\"file:///t.wiz\"},\"position\":{posJson src off}}}")
  (srv, result out[0]!)
where
  result (j : Lean.Json) : Lean.Json :=
    (j.getObjVal? "result").toOption.getD ((j.getObjVal? "error").toOption.getD Lean.Json.null)

def has (j : Lean.Json) (s : String) : Bool := (j.compress.splitOn s).length > 1

/-- Concatenate the text of tagged text. -/
partial def flatten (j : Lean.Json) : String :=
  match (j.getObjVal? "text").toOption, (j.getObjVal? "append").toOption, (j.getObjVal? "tag").toOption with
  | some (.str s), _, _ => s
  | _, some (.arr xs), _ => String.join (xs.toList.map flatten)
  | _, _, some (.arr #[_, t]) => flatten t
  | _, _, _ => "?"

/-- The refs of tagged text, outermost first. -/
partial def refs (j : Lean.Json) : List (Nat × Lean.Json) :=
  match (j.getObjVal? "append").toOption, (j.getObjVal? "tag").toOption with
  | some (.arr xs), _ => xs.toList.flatMap refs
  | _, some (.arr #[t, x]) => ((t.getObjValAs? Nat "ref").toOption.getD 0, t) :: refs x
  | _, _ => []

def tacticSrc : String :=
  "import Prelude\ndef id' : (A : Type) → A → A := by\n  intro A\n  intro x\n  exact x\n"

def group : Group where
  name := "lsp"
  parallel := true
  exercise := "Stage 11 (infoview)"
  cases := [
    { name := "modules in isolation are elaborated once per process", run := fun _ => do
        let pre ← prelude
        let size : IO Nat := do pure (← isoCacheZOM.get).size
        isoCacheZOM.set {}
        let msgs (s : St) := s.messages.toList.map (·.text)
        let src := "import Prelude\ndef x : Nat := 1 + 1\ndef bad : Nat := true\n"
        let s₁ := runFrontend (R := ZeroOneMany) src { trustedModule := Tests.libModule, loader := fun m => if m == "Prelude" then some pre else none }
        -- (each state is looked at before the table: that fixes the order)
        check ((msgs s₁).length == 1) s!"{msgs s₁}"
        let n ← size
        check (n ≥ 1) "nothing kept"
        -- again, from a loader that is another closure: the same, from the table
        let s₂ := runFrontend (R := ZeroOneMany) src { trustedModule := Tests.libModule, loader := fun m => if m == "Prelude" then some pre else none }
        checkEq (msgs s₁) (msgs s₂)
        checkEq n (← size)
        checkEq s₁.globals.order.size s₂.globals.order.size
        -- the loader is the file's own after a hit: a module the first loader didn't have
        let loader (m : Name) := if m == "Prelude" then some pre else if m == "Extra" then some "import Prelude\ndef extra : Nat := 3\n" else none
        let s₃ := runFrontend (R := ZeroOneMany) "import Prelude\nimport Extra\ndef y : Nat := extra\n" { loader, trustedModule := Tests.libModule }
        checkEq ([] : List String) (msgs s₃)
        -- another Prelude text, other settings: other entries
        let s₄ := runFrontend (R := ZeroOneMany) "import Prelude\ndef y : Nat := preExtra\n"
          { trustedModule := Tests.libModule, loader := fun m => if m == "Prelude" then some (pre ++ "\ndef preExtra : Nat := 0\n") else none }
        checkEq ([] : List String) (msgs s₄)
        let k₁ ← size
        let s₆ := runFrontend (R := ZeroOneMany) src { trustedModule := Tests.libModule, loader := fun m => if m == "Prelude" then some pre else none, termInfo := true }
        checkEq (msgs s₁) (msgs s₆)
        check ((← size) > k₁) "termInfo shares an entry"
        -- a state that is not initial is not cached; an import cycle isn't either
        isoCacheZOM.set {}
        let s₅ := runFrontend (R := ZeroOneMany) "import A\n" { trustedModule := Tests.libModule, loader := fun m => if m == "A" then some "import B\n" else if m == "B" then some "import A\n" else none }
        check (s₅.messages.size ≥ 1) "no cycle error"
        let s₇ := runFrontend (R := ZeroOneMany) "import Prelude\n" { trustedModule := Tests.libModule, loader := fun m => if m == "Prelude" then some pre else none, pristine := false }
        checkEq ([] : List String) (msgs s₇)
        checkEq 0 (← size) },
    { name := "info tree: hovers are unchanged", run := fun _ => do
        let src := "import Prelude\ndef double (n : Nat) : Nat := n + n\ndef four : Nat := double 2\n"
        for ti in [false, true] do
          let s ← elabSrc src ti
          checkEq "(some (double, Nat → Nat))" (toString (Query.hoverAt s (offAfter src "double 2" (-3))))
          checkEq "(some (n, Nat))" (toString (Query.hoverAt s (offAfter src ":= n" (-1)))) },
    { name := "13p–q: an updated field's hover and definition; a numeral pattern's variable", run := fun _ => do
        let src := "import Prelude\nstructure In where\n  x : Nat\n  y : Nat\nstructure Out where\n  i : In\n  n : Nat\n" ++
          "def f (o : Out) : Out := { o with n := 0, i.y := 1 }\ndef g : Nat → Nat\n  | 0 => 0\n  | k + 1 => k\n"
        let s ← elabSrc src
        checkEq "(some (Out.n, Nat))" (toString (Query.hoverAt s (offAfter src "with n" (-1))))
        checkEq "(some (In.y, Nat))" (toString (Query.hoverAt s (offAfter src "i.y" (-1))))
        let line (n : Name) : Option Nat := (Query.definitionAt s (offAfter src (if n == "n" then "with n" else "i.y") (-1))).map
          fun (_, i, _) => ((src.toList.take i.start).count '\n')
        -- (a projection is declared by its structure)
        checkEq (some 4) (line "n")
        checkEq (some 1) (line "y")
        checkEq "(some (k, Nat))" (toString (Query.hoverAt s (offAfter src "| k" (-1)))) },
    { name := "info tree: tactic states before, between and after tactics", run := fun _ => do
        let s ← elabSrc tacticSrc
        -- on `by`: the goal the block started with
        checkEq "⊢ (A : Type) → A → A" (goalsText s (offAfter tacticSrc ":= by" (-1)))
        checkEq "A : Type\n⊢ A → A" (goalsText s (offAfter tacticSrc "intro A"))
        checkEq "A : Type\n⊢ A → A" (goalsText s (offAfter tacticSrc "intro A" (-3)))
        -- at the start of the next line: still after `intro A`
        checkEq "A : Type\n⊢ A → A" (goalsText s (offAfter tacticSrc "intro A\n"))
        checkEq "A : Type\nx : A\n⊢ A" (goalsText s (offAfter tacticSrc "intro x"))
        checkEq "no goals" (goalsText s (offAfter tacticSrc "exact x"))
        checkEq "none" (goalsText s 3) },
    { name := "info tree: goals survive an error (unsolved goals, a failing tactic)", run := fun _ => do
        let src := "import Prelude\ndef bad : Nat → Bool := by intro n\n"
        let s ← elabSrc src
        checkEq "n : Nat\n⊢ Bool" (goalsText s (offAfter src "intro n"))
        check (s.messages.any (·.code == "unsolved-goals")) "no code on the unsolved goals error"
        let src := "import Prelude\ndef bad : Nat → Nat := by\n  intro n\n  exact true\n"
        let s ← elabSrc src
        checkEq "n : Nat\n⊢ Nat" (goalsText s (offAfter src "exact true")) },
    { name := "info tree: holes and expected types", run := fun _ => do
        let src := "import Prelude\ndef f (n : Nat) (b : Bool) : Nat := Nat.add n _\n"
        for ti in [false, true] do
          let s ← elabSrc src ti
          checkEq "n : Nat\nb : Bool\n⊢ Nat" (termGoalText s (offAfter src "n _" (-1)))
        let s ← elabSrc src
        -- an argument, and the head (an identifier: its type)
        checkEq "n : Nat\nb : Bool\n⊢ Nat" (termGoalText s (offAfter src "add n" (-1)))
        checkEq "⊢ Nat → Nat → Nat" (termGoalText s (offAfter src "Nat.add" (-2)))
        let src := "import Prelude\ndef g : Nat := let k : Nat := 1; ?hole\n"
        let s ← elabSrc src
        checkEq "k : Nat := 1\n⊢ Nat" (termGoalText s (offAfter src "?hole" (-1))) },
    { name := "info tree: matches, unknown identifiers and declarations", run := fun _ => do
        let src := "import Prelude\ninductive T where\n  | a\n  | b (t : T)\n  | c (x y : Nat)\ndef f (t : T) : Nat := match t with\n  | .a => 0\ndef g : T → Nat\n  | .b _ => 1\ndef h := Nat.add 1 2\ndef k : Nat := lenght\n"
        let s ← elabSrc src
        let ms := s.infos.filterMap fun i => match i with
          | .matchCases _ m => some s!"{m.type} {m.covered} {m.catchAll} {m.columns}"
          | _ => none
        checkEq "#[T [a] false 1, T [b] false 1]" (toString ms)
        checkEq 2 (s.messages.filter (·.code == "missing-case")).size
        check (s.messages.any (·.code == "unknown-identifier")) "unknown-identifier code"
        check (s.infos.any fun i => i matches .unknownIdent _ "lenght" _) "no unknown identifier info"
        let ds := s.infos.filterMap fun i => match i with
          | .decl _ n names ty ann _ => some s!"{n} {ty.pretty names} {ann}"
          | _ => none
        check (ds.contains "h Nat false") s!"decl infos: {ds}" },
    { name := "info tree: through the shared cache", run := fun _ => do
        let p ← prelude
        let init : St := { trustedModule := Tests.libModule, loader := fun m => if m == "Prelude" then some p else none, termInfo := true }
        let src := tacticSrc ++ "def f (n : Nat) : Nat := Nat.add n _\ndef h := Nat.add 1 2\n"
        let dir ← IO.FS.createTempDir
        let (cold, _) ← Cache.elaborateCached (some dir) [] src init 0
        let (warm, hits) ← Cache.elaborateCached (some dir) [] src init 0
        check (hits > 0) "nothing came from the cache"
        checkEq cold.infos.size warm.infos.size
        for off in [offAfter src "intro A", offAfter src "intro x", offAfter src "n _" (-1), offAfter src "Nat.add 1"] do
          checkEq (goalsText cold off) (goalsText warm off)
          checkEq (termGoalText cold off) (termGoalText warm off) },
    { name := "tagged printing agrees with the printer", run := fun _ => do
        let p ← prelude
        let st := runFrontend (R := ZeroOneMany) "import Prelude" { trustedModule := Tests.libModule, loader := fun _ => some p }
        for n in st.globals.order do
          let some d := st.globals.find? n | continue
          for t in [d.type] ++ d.value.toList do
            let (tt, subs) := (t.prettyTagged [] []).run #[]
            unless tt.flatten == t.pretty do
              throw (IO.userError s!"{n}: {tt.flatten} ≠ {t.pretty}")
            check (subs.size > 0) s!"{n}: no tags" },
    { name := "tagged printing with notation agrees with the printer, and tags the parts (11r)", run := fun _ => do
        let p ← prelude
        let st := runFrontend (R := ZeroOneMany) "import Prelude\ndef t (n : Nat) : List Nat := [n + 2, 3]"
          { trustedModule := Tests.libModule, loader := fun _ => some p }
        let g := st.globals
        for n in g.order do
          let some d := g.find? n | continue
          for t in [d.type] ++ d.value.toList do
            let (tt, _) := (t.prettyTagged [] [] (some g)).run #[]
            unless tt.flatten == t.pretty [] (some g) do
              throw (IO.userError s!"{n}: {tt.flatten} ≠ {t.pretty [] (some g)}")
        let some d := g.find? "t" | throw (IO.userError "no t")
        let some v := d.value | throw (IO.userError "no value")
        let (tt, subs) := (v.prettyTagged [] [] (some g)).run #[]
        checkEq "fun n => [n + 2, 3]" tt.flatten
        -- the variable, the numerals, the sum and the list are subterms of their own
        let shown := subs.toList.map fun sub => sub.term.pretty sub.names (some g)
        for x in ["n", "2", "3", "n + 2", "[n + 2, 3]"] do
          check (shown.contains x) s!"no tag for {x}: {shown}" }
  ]

/-- Apply a `WorkspaceEdit` (for `file:///t.wiz`) to `src`. -/
def applyEdit (src : String) (edit : Lean.Json) : String :=
  let edits := match LSP.get? edit ["changes", "file:///t.wiz"] with
    | some (.arr es) => es
    | _ => #[]
  let at_ (e : Lean.Json) (k : String) : Nat :=
    LSP.ofPos src (LSP.getNat e ["range", k, "line"]) (LSP.getNat e ["range", k, "character"])
  Actions.apply src (edits.map fun e => { start := at_ e "start", stop := at_ e "end", text := LSP.getStr e ["newText"] })

/-- The code actions at an offset of the open document. -/
def codeActions (srv : LSP.Server) (src : String) (off : Nat) : LSP.Server × Array Lean.Json :=
  let p := posJson src off
  let (srv, out) := LSP.handle srv (req s!"\{\"jsonrpc\":\"2.0\",\"id\":5,\"method\":\"textDocument/codeAction\",\"params\":\{\"textDocument\":\{\"uri\":\"file:///t.wiz\"},\"range\":\{\"start\":{p},\"end\":{p}},\"context\":\{\"diagnostics\":[]}}}")
  match (out[0]!.getObjVal? "result").toOption with
  | some (.arr as) => (srv, as)
  | _ => (srv, #[])

def titled (as : Array Lean.Json) (t : String) : Option Lean.Json :=
  as.find? fun a => LSP.getStr a ["title"] == t

/-- The diagnostics' codes after opening `src`. -/
def codes (src : String) (srv? : Option LSP.Server := none) : IO (List String) := do
  let (_, out) ← openDoc src (srv? := srv?)
  match LSP.get? out[0]! ["params", "diagnostics"] with
  | some (.arr ds) => pure (ds.toList.map fun d => LSP.getStr d ["code"])
  | _ => pure []

def subtermInfo (srv : LSP.Server) (session ref : Nat) : LSP.Server × Lean.Json :=
  let (srv, out) := LSP.handle srv (req s!"\{\"jsonrpc\":\"2.0\",\"id\":11,\"method\":\"wiz/subtermInfo\",\"params\":\{\"textDocument\":\{\"uri\":\"file:///t.wiz\"},\"session\":{session},\"ref\":{ref}}}")
  (srv, (out[0]!.getObjVal? "result").toOption.getD ((out[0]!.getObjVal? "error").toOption.getD Lean.Json.null))

/-- The completion items at an offset of the open document: (label, newText, detail),
in the order given, and whether every item's edit starts at `start` (when given). -/
def completions (srv : LSP.Server) (src : String) (off : Nat) : Array (String × String × String) :=
  let (_, r) := ask srv "textDocument/completion" src off
  match LSP.get? r ["items"] with
  | some (.arr is) => is.map fun i => (LSP.getStr i ["label"], LSP.getStr i ["textEdit", "newText"], LSP.getStr i ["detail"])
  | _ => #[]

def labels (cs : Array (String × String × String)) : List String := cs.toList.map (·.1)

/-- The source of the completion cases. -/
def completionSrc : String :=
  "import Prelude\nstructure Point where\n  px : Nat\n  py : Nat\n" ++
  "def Point.norm (p : Point) : Nat := p.px\n" ++
  "def foo (n : Nat) (pt : Point) : Nat := Nat.add n pt.\n" ++
  "def bar (k : Nat) : Nat := Nat.ad\n" ++
  "def baz (len : Nat) (lb : Bool) : Nat := l\n" ++
  "def qux (m : Nat) : Nat := Nat.succ \n" ++
  "def t (A : Type) : A → A := by\n  intro x\n  ex\n" ++
  "de\n"

/-- The body of the infoview socket case. -/
def socketCase : IO Unit := do
        let dir ← IO.FS.createTempDir
        let sock := (dir / "iv.sock").toString
        -- the editor's end of an in-process pipe, and the server on the other end
        let ((srvIn, srvOut), (edIn, edOut)) ← Socket.pair
        let (ed, edW) := (IO.FS.Stream.ofHandle edIn, IO.FS.Stream.ofHandle edOut)
        let done ← IO.asTask (prio := .dedicated)
          (LSP.serveInfoview (← server).libs (IO.FS.Stream.ofHandle srvIn) (IO.FS.Stream.ofHandle srvOut) sock ["Prelude"])
        let next (h : IO.FS.Stream) : IO Lean.Json := do
          let some j ← LSP.readMessage h | throw (IO.userError "the stream ended")
          pure j
        let src := "import Prelude\ndef k : Nat → Bool → Nat := by\n  intro n\n  intro b\n  exact n\n"
        LSP.writeMessage edW (req "{\"jsonrpc\":\"2.0\",\"id\":0,\"method\":\"initialize\",\"params\":{}}")
        check (has (← next ed) "documentHighlightProvider") "documentHighlight not asked for"
        LSP.writeMessage edW (Lean.Json.mkObj [("jsonrpc", "2.0"), ("method", "textDocument/didOpen"),
          ("params", Lean.Json.mkObj [("textDocument", Lean.Json.mkObj [("uri", "file:///t.wiz"), ("version", (1 : Nat)), ("text", src)])])])
        check (has (← next ed) "publishDiagnostics") "no diagnostics"
        -- an infoview connects (retrying, like the clients) and is told where the cursor is
        let rec conn : Nat → IO (IO.FS.Handle × IO.FS.Handle)
          | 0 => Socket.connect sock
          | n + 1 => do try Socket.connect sock catch _ => do IO.sleep 50; conn n
        let (ivIn, ivOut) ← conn 100
        let (iv, ivW) := (IO.FS.Stream.ofHandle ivIn, IO.FS.Stream.ofHandle ivOut)
        let c ← next iv
        checkEq "wiz/infoview/cursor" (LSP.getStr c ["method"])
        checkEq "{\"character\":0,\"line\":0}" (LSP.get? c ["params", "position"]).get!.compress
        let session := LSP.getNat c ["params", "session"]
        -- the editor's cursor moves: a documentHighlight (answered null), then a hover at the same place
        let pos := posJson src (offAfter src "intro n")
        LSP.writeMessage edW (req s!"\{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"textDocument/documentHighlight\",\"params\":\{\"textDocument\":\{\"uri\":\"file:///t.wiz\"},\"position\":{pos}}}")
        checkEq "null" ((← next ed).getObjVal? "result" |>.toOption.get!).compress
        LSP.writeMessage edW (req s!"\{\"jsonrpc\":\"2.0\",\"id\":2,\"method\":\"textDocument/hover\",\"params\":\{\"textDocument\":\{\"uri\":\"file:///t.wiz\"},\"position\":{pos}}}")
        let _ ← next ed
        let c ← next iv
        checkEq (req pos).compress (LSP.get? c ["params", "position"]).get!.compress
        checkEq session (LSP.getNat c ["params", "session"])
        -- the infoview pulls the goals there, on the socket, and asks about a subterm
        LSP.writeMessage ivW (req s!"\{\"jsonrpc\":\"2.0\",\"id\":7,\"method\":\"wiz/interactiveGoals\",\"params\":\{\"textDocument\":\{\"uri\":\"file:///t.wiz\"},\"position\":{pos}}}")
        let r ← next iv
        checkEq "7" (LSP.get? r ["id"]).get!.compress
        let some (.arr #[g]) := LSP.get? r ["result", "goals"] | throw (IO.userError s!"goals: {r.compress}")
        let ty := (LSP.get? g ["type"]).get!
        checkEq "Bool → Nat" (flatten ty)
        let some (ref, _) := (refs ty).find? fun (_, t) => LSP.getStr t ["name"] == "Bool" | throw (IO.userError "no Bool")
        LSP.writeMessage ivW (Lean.Json.mkObj [("jsonrpc", "2.0"), ("id", (8 : Nat)), ("method", "wiz/subtermInfo"),
          ("params", Lean.Json.mkObj [("textDocument", Lean.Json.mkObj [("uri", "file:///t.wiz")]), ("session", session), ("ref", ref)])])
        checkEq "Bool" (LSP.getStr (← next iv) ["result", "text"])
        -- other methods are refused on the socket
        LSP.writeMessage ivW (req "{\"jsonrpc\":\"2.0\",\"id\":9,\"method\":\"textDocument/hover\",\"params\":{}}")
        check (has (← next iv) "-32601") "hover answered on the socket"
        -- an edit: the infoview hears of the new session at the same cursor
        LSP.writeMessage edW (Lean.Json.mkObj [("jsonrpc", "2.0"), ("method", "textDocument/didChange"),
          ("params", Lean.Json.mkObj [("textDocument", Lean.Json.mkObj [("uri", "file:///t.wiz"), ("version", (2 : Nat))]),
                                      ("contentChanges", Lean.Json.arr #[Lean.Json.mkObj [("text", src ++ "\n")]])])])
        let _ ← next ed
        let c ← next iv
        checkEq (req pos).compress (LSP.get? c ["params", "position"]).get!.compress
        check (LSP.getNat c ["params", "session"] != session) "same session after an edit"
        -- `exit`: the server stops and removes the socket
        LSP.writeMessage edW (req "{\"jsonrpc\":\"2.0\",\"method\":\"exit\"}")
        match ← IO.wait done with
        | .ok () => pure ()
        | .error e => throw e
        check (!(← System.FilePath.pathExists sock)) "the socket file is still there"
        check ((← LSP.readMessage iv).isNone) "the infoview's connection is still open"


/-- The body of the WebSocket case: an editor on stdio (a socket pair), and two
WebSocket clients, one of which edits a document of its own. -/
def wsCase : IO Unit := do
        let ((srvIn, srvOut), (edIn, edOut)) ← Socket.pair
        let (ed, edW) := (IO.FS.Stream.ofHandle edIn, IO.FS.Stream.ofHandle edOut)
        let port ← IO.Promise.new
        let done ← IO.asTask (prio := .dedicated)
          (LSP.serveWith (← server).libs (some (IO.FS.Stream.ofHandle srvIn, IO.FS.Stream.ofHandle srvOut))
            { ws := some (Socket.loopback, 0) } (fun p => port.resolve p) ["Prelude"])
        let port := port.result!.get
        let next (h : IO.FS.Stream) : IO Lean.Json := do
          let some j ← LSP.readMessage h | throw (IO.userError "the stream ended")
          pure j
        let tcp : IO (IO.FS.Stream × IO.FS.Stream) := do
          let (r, w) ← Socket.tcpConnect Socket.loopback port
          pure (IO.FS.Stream.ofHandle r, IO.FS.Stream.ofHandle w)
        let mask := some (ByteArray.mk #[0x37, 0xfa, 0x21, 0x3d])
        let send (w : IO.FS.Stream) (j : Lean.Json) := WebSocket.sendText w j.compress mask
        let recv (r w : IO.FS.Stream) : IO Lean.Json := do
          let some t ← WebSocket.recvText r w (server := false) | throw (IO.userError "the WebSocket closed")
          match Lean.Json.parse t with
          | .ok j => pure j
          | .error e => throw (IO.userError s!"not JSON ({e}): {t}")
        -- a page from another site is refused; so is a plain HTTP request
        let (r, w) ← tcp
        match ← WebSocket.connect r w s!"127.0.0.1:{port}" (origin := some "https://example.com") with
        | .ok () => throw (IO.userError "a foreign origin was let in")
        | .error e => check ((e.splitOn "403").length > 1) s!"refused how: {e}"
        let (r, w) ← tcp
        w.putStr "GET / HTTP/1.1\r\nHost: x\r\n\r\n"; w.flush
        check (((← r.getLine).splitOn "426").length > 1) "a plain GET was not refused"
        -- the editor opens a document
        let src := "import Prelude\ndef k : Nat → Bool → Nat := by\n  intro n\n  intro b\n  exact n\n"
        LSP.writeMessage edW (req "{\"jsonrpc\":\"2.0\",\"id\":0,\"method\":\"initialize\",\"params\":{}}")
        let _ ← next ed
        LSP.writeMessage edW (Lean.Json.mkObj [("jsonrpc", "2.0"), ("method", "textDocument/didOpen"),
          ("params", Lean.Json.mkObj [("textDocument", Lean.Json.mkObj [("uri", "file:///t.wiz"), ("version", (1 : Nat)), ("text", src)])])])
        let _ ← next ed
        -- a local page connects and is told where the cursor is
        let (iv, ivW) ← tcp
        match ← WebSocket.connect iv ivW s!"127.0.0.1:{port}" (origin := some s!"http://127.0.0.1:{port + 1}") with
        | .ok () => pure ()
        | .error e => throw (IO.userError s!"handshake: {e}")
        let c ← recv iv ivW
        checkEq "wiz/infoview/cursor" (LSP.getStr c ["method"])
        -- the editor's cursor moves; the page hears of it and pulls the goals
        let pos := posJson src (offAfter src "intro n")
        LSP.writeMessage edW (req s!"\{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"textDocument/hover\",\"params\":\{\"textDocument\":\{\"uri\":\"file:///t.wiz\"},\"position\":{pos}}}")
        let _ ← next ed
        let c ← recv iv ivW
        checkEq (req pos).compress (LSP.get? c ["params", "position"]).get!.compress
        let session := LSP.getNat c ["params", "session"]
        send ivW (req s!"\{\"jsonrpc\":\"2.0\",\"id\":7,\"method\":\"wiz/interactiveGoals\",\"params\":\{\"textDocument\":\{\"uri\":\"file:///t.wiz\"},\"position\":{pos}}}")
        let r ← recv iv ivW
        checkEq "7" (LSP.get? r ["id"]).get!.compress
        let some (.arr #[g]) := LSP.get? r ["result", "goals"] | throw (IO.userError s!"goals: {r.compress}")
        checkEq "Bool → Nat" (flatten (LSP.get? g ["type"]).get!)
        checkEq session (LSP.getNat r ["result", "session"])
        -- a ping is answered (by the client's `recv`, which skips the pong); then a request
        -- split into two fragments, the second after a ping
        WebSocket.writeFrame ivW WebSocket.opPing "hi".toUTF8 mask
        let msg := (req "{\"jsonrpc\":\"2.0\",\"id\":8,\"method\":\"shutdown\"}").compress.toUTF8
        let half := msg.size / 2
        let frag (fin : Bool) (op : UInt8) (bs : ByteArray) : ByteArray :=
          let f := WebSocket.frameBytes op bs mask
          f.set! 0 (if fin then f.get! 0 else f.get! 0 &&& 0x7f)
        ivW.write (frag false WebSocket.opText (msg.extract 0 half)); ivW.flush
        WebSocket.writeFrame ivW WebSocket.opPing .empty mask
        ivW.write (frag true 0 (msg.extract half msg.size)); ivW.flush
        checkEq "8" (LSP.get? (← recv iv ivW) ["id"]).get!.compress
        -- the page opens a document of its own (a long one: a 16-bit frame length) and gets
        -- its diagnostics, and hovers in it: the cursor moves there, for every infoview
        let mine := "import Prelude\n" ++ String.join ((List.range 40).map fun i => s!"def d{i} : Nat := {i}\n") ++ "def bad : Nat := true\n"
        send ivW (Lean.Json.mkObj [("jsonrpc", "2.0"), ("method", "textDocument/didOpen"),
          ("params", Lean.Json.mkObj [("textDocument", Lean.Json.mkObj [("uri", "file:///w.wiz"), ("version", (1 : Nat)), ("text", mine)])])])
        let d ← recv iv ivW
        checkEq "textDocument/publishDiagnostics" (LSP.getStr d ["method"])
        let some (.arr #[_]) := LSP.get? d ["params", "diagnostics"] | throw (IO.userError s!"diagnostics: {d.compress}")
        let mpos := posJson mine (offAfter mine "def d3 : Na" (-1))
        send ivW (req s!"\{\"jsonrpc\":\"2.0\",\"id\":9,\"method\":\"textDocument/hover\",\"params\":\{\"textDocument\":\{\"uri\":\"file:///w.wiz\"},\"position\":{mpos}}}")
        check (has (← recv iv ivW) "Nat") "no hover"
        let c ← recv iv ivW
        checkEq "file:///w.wiz" (LSP.getStr c ["params", "textDocument", "uri"])
        -- the page's `initialize` sets its own settings only: it asks for `wiz/elaborated`,
        -- and gets it for its edits; the editor (which didn't ask) doesn't for its own
        send ivW (req "{\"jsonrpc\":\"2.0\",\"id\":10,\"method\":\"initialize\",\"params\":{\"capabilities\":{\"experimental\":{\"wizElaborated\":true}}}}")
        check (has (← recv iv ivW) "wizInfoview") "no capabilities"
        send ivW (Lean.Json.mkObj [("jsonrpc", "2.0"), ("method", "textDocument/didChange"),
          ("params", Lean.Json.mkObj [("textDocument", Lean.Json.mkObj [("uri", "file:///w.wiz"), ("version", (2 : Nat))]),
                                      ("contentChanges", Lean.Json.arr #[Lean.Json.mkObj [("text", mine ++ "\n")]])])])
        checkEq "textDocument/publishDiagnostics" (LSP.getStr (← recv iv ivW) ["method"])
        checkEq "wiz/elaborated" (LSP.getStr (← recv iv ivW) ["method"])
        let _ ← recv iv ivW  -- (the cursor's document was elaborated again: its note)
        LSP.writeMessage edW (Lean.Json.mkObj [("jsonrpc", "2.0"), ("method", "textDocument/didChange"),
          ("params", Lean.Json.mkObj [("textDocument", Lean.Json.mkObj [("uri", "file:///t.wiz"), ("version", (2 : Nat))]),
                                      ("contentChanges", Lean.Json.arr #[Lean.Json.mkObj [("text", src ++ "\n")]])])])
        checkEq "textDocument/publishDiagnostics" (LSP.getStr (← next ed) ["method"])
        LSP.writeMessage edW (req "{\"jsonrpc\":\"2.0\",\"id\":3,\"method\":\"shutdown\"}")
        checkEq "3" (LSP.get? (← next ed) ["id"]).get!.compress
        -- a second page connects and hears of the cursor too
        let (iv2, iv2W) ← tcp
        match ← WebSocket.connect iv2 iv2W s!"localhost:{port}" with
        | .ok () => pure ()
        | .error e => throw (IO.userError s!"handshake: {e}")
        checkEq "file:///w.wiz" (LSP.getStr (← recv iv2 iv2W) ["params", "textDocument", "uri"])
        -- a page's `exit` closes its own connection; the editor's stops the server
        send iv2W (req "{\"jsonrpc\":\"2.0\",\"method\":\"exit\"}")
        check ((← WebSocket.recvText iv2 iv2W (server := false)).isNone) "still open after exit"
        LSP.writeMessage edW (req "{\"jsonrpc\":\"2.0\",\"method\":\"exit\"}")
        match ← IO.wait done with
        | .ok () => pure ()
        | .error e => throw e
        check ((← WebSocket.recvText iv ivW (server := false)).isNone) "the page's connection is still open"
        check ((← (try some <$> Socket.tcpConnect Socket.loopback port catch _ => pure none)).isNone) "still listening"

def serverGroup : Group where
  name := "lsp-server"
  parallel := true
  exercise := "Stage 11 (infoview, code actions)"
  cases := [
    { name := "infoview methods are advertised", run := fun _ => do
        let (_, out) := LSP.handle (← server) (req "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"initialize\",\"params\":{}}")
        for m in ["wiz/plainGoal", "wiz/interactiveGoals", "wiz/subtermInfo", "codeActionProvider", "experimental"] do
          check (has out[0]! m) s!"no {m}" },
    { name := "wiz/plainGoal and wiz/plainTermGoal", run := fun _ => do
        let src := tacticSrc ++ "def f (n : Nat) : Nat := Nat.add n _\n"
        let (srv, _) ← openDoc src
        let (srv, r) := ask srv "wiz/plainGoal" src (offAfter src "intro x")
        checkEq "[\"A : Type\\nx : A\\n⊢ A\"]" (LSP.get? r ["goals"] |>.get!).compress
        checkEq "```wiz\nA : Type\nx : A\n⊢ A\n```" (LSP.getStr r ["rendered"])
        let (srv, r) := ask srv "wiz/plainGoal" src (offAfter src "exact x")
        checkEq "no goals" (LSP.getStr r ["rendered"])
        let (srv, r) := ask srv "wiz/plainGoal" src 2
        checkEq Lean.Json.null r
        let (_, r) := ask srv "wiz/plainTermGoal" src (offAfter src "n _" (-1))
        checkEq "n : Nat\n⊢ Nat" (LSP.getStr r ["goal"])
        check (has r "\"range\"") "no range" },
    { name := "wiz/interactiveGoals: tagged text, refs and wiz/subtermInfo", run := fun _ => do
        let src := "import Prelude\ndef k : Nat → Bool → Nat := by\n  intro n\n  intro b\n  exact n\n"
        let (srv, _) ← openDoc src
        let (srv, r) := ask srv "wiz/interactiveGoals" src (offAfter src "intro n")
        let session := LSP.getNat r ["session"]
        let some (.arr #[g]) := LSP.get? r ["goals"] | throw (IO.userError s!"goals: {r.compress}")
        let some ty := LSP.get? g ["type"] | throw (IO.userError "no type")
        checkEq "Bool → Nat" (flatten ty)
        let some (.arr #[h]) := LSP.get? g ["hyps"] | throw (IO.userError "hyps")
        checkEq "[\"n\"]" (LSP.get? h ["names"]).get!.compress
        checkEq "Nat" (flatten (LSP.get? h ["type"]).get!)
        -- the same request again gives the same refs
        let (srv, r') := ask srv "wiz/interactiveGoals" src (offAfter src "intro n")
        checkEq r.compress r'.compress
        -- `Bool`: a constant from the prelude
        let some (ref, tag) := (refs ty).find? fun (_, t) => LSP.getStr t ["name"] == "Bool"
          | throw (IO.userError s!"no Bool tag in {ty.compress}")
        checkEq "const" (LSP.getStr tag ["kind"])
        let (srv, info) := subtermInfo srv session ref
        checkEq "Bool" (LSP.getStr info ["text"])
        checkEq "Type" (flatten (LSP.get? info ["type"]).get!)
        check ((LSP.getStr info ["definition", "uri"]).endsWith "lib/Prelude.wiz") s!"definition: {info.compress}"
        -- the whole arrow
        let (pref, _) := (refs ty).head!
        let (srv, info) := subtermInfo srv session pref
        checkEq "pi" (LSP.getStr info ["kind"])
        checkEq "Type" (flatten (LSP.get? info ["type"]).get!)
        -- after a change the refs are stale
        let (srv, _) := LSP.handle srv (req "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didChange\",\"params\":{\"textDocument\":{\"uri\":\"file:///t.wiz\",\"version\":2},\"contentChanges\":[{\"text\":\"import Prelude\\n\"}]}}")
        let (srv, err) := subtermInfo srv session ref
        checkEq (-32801 : Int) ((err.getObjValAs? Int "code").toOption.getD 0)
        let (_, out) := LSP.handle srv (req "{\"jsonrpc\":\"2.0\",\"id\":3,\"method\":\"wiz/plainGoal\",\"params\":{\"textDocument\":{\"uri\":\"file:///nope.wiz\"},\"position\":{\"line\":0,\"character\":0}}}")
        check (has out[0]! "-32602") s!"unknown document: {out[0]!.compress}" },
    { name := "wiz/interactiveTermGoal and the wiz/elaborated notification", run := fun _ => do
        let src := "import Prelude\ndef f (n : Nat) : Nat := Nat.add n ?x\n"
        let init := req "{\"jsonrpc\":\"2.0\",\"id\":0,\"method\":\"initialize\",\"params\":{\"capabilities\":{\"experimental\":{\"wizElaborated\":true}}}}"
        let (srv, out) ← openDoc src init
        check (out.any (has · "wiz/elaborated")) "no wiz/elaborated"
        let (_, r) := ask srv "wiz/interactiveTermGoal" src (offAfter src "?x" (-1))
        checkEq "Nat" (flatten (LSP.get? r ["goal", "type"]).get!)
        checkEq "\"x\"" (LSP.get? r ["goal", "userName"]).get!.compress
        let (_, out) ← openDoc src
        check (!(out.any (has · "wiz/elaborated"))) "unasked wiz/elaborated" },
    { name := "code action: did you mean", run := fun _ => do
        let src := "import Prelude\ndef double (n : Nat) : Nat := n + n\ndef four : Nat := doubel 2\n"
        let (srv, out) ← openDoc src
        check (has out[0]! "\"code\":\"unknown-identifier\"") s!"diagnostic: {out[0]!.compress}"
        check (has out[0]! "\"suggestions\":[\"double\"]") s!"data: {out[0]!.compress}"
        let (_, as) := codeActions srv src (offAfter src "doubel" (-2))
        let some a := titled as "Did you mean 'double'?" | throw (IO.userError s!"actions: {as.map (·.compress)}")
        let src' := applyEdit src (LSP.get? a ["edit"]).get!
        checkEq ([] : List String) (← codes src') },
    { name := "code action: add missing cases (match and equations)", run := fun _ => do
        let ty := "import Prelude\ninductive T where\n  | a\n  | b (t : T)\n  | c (x y : Nat)\n"
        for body in ["def f (t : T) : Nat := match t with\n  | .a => 0\n", "def g : T → Nat\n  | .b _ => 1\n"] do
          let src := ty ++ body
          check ((← codes src).contains "missing-case") "no missing-case code"
          let (srv, out) ← openDoc src
          let some (.arr ds) := LSP.get? out[0]! ["params", "diagnostics"] | throw (IO.userError "no diagnostics")
          let some d := ds.find? (LSP.getStr · ["code"] == "missing-case") | throw (IO.userError "no missing-case")
          let off := LSP.ofPos src (LSP.getNat d ["range", "start", "line"]) (LSP.getNat d ["range", "start", "character"])
          let (_, as) := codeActions srv src off
          let some a := titled as "Add missing cases" | throw (IO.userError s!"actions: {as.map (·.compress)}")
          let src' := applyEdit src (LSP.get? a ["edit"]).get!
          check (!((← codes src').contains "missing-case")) s!"still missing cases:\n{src'}"
          check ((src'.splitOn "\n  | .c x y => ?c").length > 1) s!"edited:\n{src'}" },
    { name := "code action: add type ascription (and codeAction/resolve)", run := fun _ => do
        let src := "import Prelude\ndef h := Nat.add 1 2\n"
        let init := req "{\"jsonrpc\":\"2.0\",\"id\":0,\"method\":\"initialize\",\"params\":{\"capabilities\":{\"textDocument\":{\"codeAction\":{\"resolveSupport\":{\"properties\":[\"edit\"]}}}}}}"
        let (srv, _) ← openDoc src init
        let (srv, as) := codeActions srv src (offAfter src "def h" (-1))
        let some a := titled as "Add type ascription" | throw (IO.userError s!"actions: {as.map (·.compress)}")
        check (LSP.get? a ["edit"]).isNone "edit not deferred"
        let resolve (srv : LSP.Server) : LSP.Server × Lean.Json :=
          let (srv, out) := LSP.handle srv (Lean.Json.mkObj [("jsonrpc", "2.0"), ("id", (6 : Nat)), ("method", "codeAction/resolve"), ("params", a)])
          (srv, out[0]!)
        let (srv, r) := resolve srv
        let src' := applyEdit src (LSP.get? r ["result", "edit"]).get!
        checkEq "import Prelude\ndef h : Nat := Nat.add 1 2\n" src'
        checkEq ([] : List String) (← codes src')
        let (srv, _) := LSP.handle srv (req "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didChange\",\"params\":{\"textDocument\":{\"uri\":\"file:///t.wiz\",\"version\":2},\"contentChanges\":[{\"text\":\"import Prelude\\n\"}]}}")
        let (_, r) := resolve srv
        check (has r "-32801") s!"stale resolve: {r.compress}" },
    { name := "error codes: the common errors carry theirs", run := fun _ => do
        let pre := "import Prelude\nstructure P where\n  count : Nat\n  total : Nat\ninductive Color where\n  | red\n  | green\n"
        for (code, body) in [
            ("no-such-field", "def f (p : P) : Nat := p.cuont\n"),
            ("no-such-field", "def f (p : P) : P := { p with cuont := 1 }\n"),
            ("unknown-constructor", "def c : Color := .gren\n"),
            ("unknown-constructor", "def c (x : Color) : Nat := match x with\n  | .red => 0\n  | .gren => 1\n"),
            ("missing-case", "def c (x : Color) : Nat := match x with\n  | .red => 0\n"),
            ("type-mismatch", "def b : Nat := Bool.true\n"),
            ("wrong-argument-count", "def g : Nat := Nat.succ 1 2\n"),
            ("unsolved-hole", "def u : Nat := (fun (A : Type) => 0) _\n"),
            ("unknown-identifier", "def i : Nat := nope\n"),
            ("parse-error", "def := 1\n")] do
          let cs ← codes (pre ++ body)
          check (cs.contains code) s!"{code}: got {cs} for\n{body}"
        let cs ← codes "import Prelud\n"
        check (cs.contains "unknown-module") s!"unknown-module: got {cs}"
        -- every code in `ErrorCode.all` has a row in docs/error-codes.md, and every row a code
        let doc ← IO.FS.readFile "docs/error-codes.md"
        let rows := (doc.splitOn "\n").filterMap fun l =>
          if l.startsWith "| `" then some ((((l.drop 3).toString.splitOn "`").headD "")) else none
        for c in ErrorCode.all do
          check (rows.contains c) s!"docs/error-codes.md has no row for {c}"
        for c in rows do
          check (ErrorCode.all.contains c) s!"docs/error-codes.md lists {c}, which is not in ErrorCode.all" },
    { name := "code action: did you mean (fields, namespace, constructors)", run := fun _ => do
        let pre := "import Prelude\nstructure P where\n  count : Nat\n  total : Nat\ninductive Box where\n  | mk (n : Nat)\ndef Box.double : Box → Nat\n  | .mk n => n + n\ninductive Color where\n  | red\n  | green\n"
        for (body, needle, title, fixed) in [
            ("def f (p : P) : Nat := p.cuont\n", "p.cuont", "Did you mean 'count'?", "p.count\n"),
            ("def f (b : Box) : Nat := b.duoble\n", "b.duoble", "Did you mean 'double'?", "b.double\n"),
            ("def f (p : P) : P := { p with totl := 1 }\n", "totl", "Did you mean 'total'?", "{ p with total := 1 }\n"),
            ("def c : Color := .gren\n", ".gren", "Did you mean 'green'?", ":= .green\n"),
            ("def c (x : Color) : Nat := match x with\n  | .red => 0\n  | .gren => 1\n", "| .gren", "Did you mean 'green'?", "| .green => 1\n")] do
          let src := pre ++ body
          let (srv, out) ← openDoc src
          check (has out[0]! s!"\"suggestions\":[\"{(title.splitOn "'").getD 1 ""}\"]") s!"data: {out[0]!.compress}"
          let (_, as) := codeActions srv src (offAfter src needle (-1))
          let some a := titled as title | throw (IO.userError s!"{body}: actions: {as.map (·.compress)}")
          let src' := applyEdit src (LSP.get? a ["edit"]).get!
          check (src'.endsWith fixed) s!"edited:\n{src'}"
          checkEq ([] : List String) (← codes src') },
    { name := "code action: did you mean (imports), add the missing import", run := fun _ => do
        let extra := "import Prelude\ndef extraThing : Nat := 3\ninductive Shade where\n  | dark\n"
        let srv ← server
        let srv := { srv with libs := srv.libs.insert "Extra.Things" ("lib/Extra/Things.wiz", extra) }
        -- a misspelt module
        let src := "import Prelude\nimport Extra.Thing\ndef y : Nat := extraThing\n"
        let (srv1, out) ← openDoc src (srv? := some srv)
        check (has out[0]! "\"code\":\"unknown-module\"") s!"diagnostic: {out[0]!.compress}"
        let (_, as) := codeActions srv1 src (offAfter src "Extra.Th")
        let some a := titled as "Did you mean 'Extra.Things'?" | throw (IO.userError s!"actions: {as.map (·.compress)}")
        let src' := applyEdit src (LSP.get? a ["edit"]).get!
        checkEq "import Prelude\nimport Extra.Things\ndef y : Nat := extraThing\n" src'
        checkEq ([] : List String) (← codes src' (srv? := some srv))
        -- a name another module declares (also a constructor `T.c` of a type it declares)
        for (use, needle) in [("extraThing", "extraThing"), ("Shade.dark", "Shade.dark")] do
          let src := s!"import Prelude\ndef y := {use}\n"
          let (srv1, _) ← openDoc src (srv? := some srv)
          let (_, as) := codeActions srv1 src (offAfter src needle (-1))
          let some a := titled as "Add `import Extra.Things`" | throw (IO.userError s!"{use}: actions: {as.map (·.compress)}")
          let src' := applyEdit src (LSP.get? a ["edit"]).get!
          checkEq s!"import Prelude\nimport Extra.Things\ndef y := {use}\n" src'
          checkEq ([] : List String) (← codes src' (srv? := some srv))
        -- not for a name no module declares
        let src := "import Prelude\ndef y : Nat := extraThings\n"
        let (srv1, _) ← openDoc src (srv? := some srv)
        let (_, as) := codeActions srv1 src (offAfter src "extraThings" (-1))
        check (!(as.any (has · "Add `import"))) s!"actions: {as.map (·.compress)}" },
    { name := "code action: make implicit arguments explicit (@f) or inferred (drop the @)", run := fun _ => do
        let pre := "import Prelude\ndef myId {A : Type} (x : A) : A := x\n"
        let src := pre ++ "def v : Nat := myId Nat 1\n"
        let (srv, out) ← openDoc src
        check (has out[0]! "\"code\":\"wrong-argument-count\"") s!"diagnostic: {out[0]!.compress}"
        let (_, as) := codeActions srv src (offAfter src "myId Nat" (-5))
        let some a := titled as "Give the implicit arguments explicitly: @myId" | throw (IO.userError s!"actions: {as.map (·.compress)}")
        let src' := applyEdit src (LSP.get? a ["edit"]).get!
        checkEq (pre ++ "def v : Nat := @myId Nat 1\n") src'
        checkEq ([] : List String) (← codes src')
        -- the other way round
        let src := pre ++ "def w : Nat := @myId 1\n"
        let (srv, out) ← openDoc src
        check (has out[0]! "\"severity\":1") s!"no error: {out[0]!.compress}"
        let (_, as) := codeActions srv src (offAfter src "@myId 1" (-1))
        let some a := titled as "Let the implicit arguments of myId be inferred: drop the @" | throw (IO.userError s!"actions: {as.map (·.compress)}")
        let src' := applyEdit src (LSP.get? a ["edit"]).get!
        checkEq (pre ++ "def w : Nat := myId 1\n") src'
        checkEq ([] : List String) (← codes src')
        -- not when the count is right
        let src := pre ++ "def z : Nat := Nat.succ 1 2\n"
        let (srv, _) ← openDoc src
        let (_, as) := codeActions srv src (offAfter src "Nat.succ" (-1))
        check (!(as.any (has · "implicit"))) s!"actions: {as.map (·.compress)}" },
    { name := "11q: go to definition and declaration of syntax, a macro use's hover", run := fun _ => do
        let src := "import Prelude\nsyntax (name := twice) \"twice\" term:max : term\nmacro_rules\n  | `(term| twice $x) => `(term| Nat.add $x $x)\ndef two : Nat := 2\ndef four : Nat := twice two\n"
        let (srv, _) ← openDoc src
        let line (r : Lean.Json) : Nat := LSP.getNat r ["range", "start", "line"]
        let use := offAfter src "twice two" (-7)
        -- definition: the macro rule that expanded it; declaration: the `syntax`
        let (srv, r) := ask srv "textDocument/definition" src use
        checkEq "file:///t.wiz" (LSP.getStr r ["uri"])
        checkEq 3 (line r)
        let (srv, r) := ask srv "textDocument/declaration" src use
        checkEq 1 (line r)
        -- the argument is still an identifier of its own
        let (srv, r) := ask srv "textDocument/definition" src (offAfter src "twice two" (-1))
        checkEq 4 (line r)
        -- the hover: the syntax, its type, where it is declared and what it expands to
        let (srv, r) := ask srv "textDocument/hover" src use
        let md := LSP.getStr r ["contents", "value"]
        for part in ["twice two : Nat", "syntax `term.twice` (this file, line 2)", "by macro rule (this file, line 4)",
                     "expands to\n```wiz\nNat.add two two\n```"] do
          check ((md.splitOn part).length > 1) s!"no {part} in the hover:\n{md}"
        -- the pattern of the rule refers to the syntax too; the template records nothing
        -- (its ranges are the rule's, not the use's)
        let (srv, r) := ask srv "textDocument/declaration" src (offAfter src "term| twice" (-2))
        checkEq 1 (line r)
        let (_, r) := ask srv "textDocument/hover" src (offAfter src "Nat.add $x" (-5))
        checkEq Lean.Json.null r },
    { name := "11q: Prelude notation, syntax categories and imports", run := fun _ => do
        let src := "import Prelude\ndeclare_syntax_cat greeting\nsyntax \"hi\" : greeting\nsyntax \"greet\" greeting : term\ndef three : Nat := 1 + 2\n"
        let (srv, _) ← openDoc src
        let pre ← prelude
        let preLine (needle : String) : Nat := ((pre.splitOn needle).headD "").toList.count '\n'
        -- `+`: the `infixl` in the Prelude (the rule and the syntax are one command)
        for m in ["textDocument/definition", "textDocument/declaration"] do
          let (_, r) := ask srv m src (offAfter src "1 +" (-1))
          check ((LSP.getStr r ["uri"]).endsWith "lib/Prelude.wiz") s!"{m}: {r.compress}"
          checkEq (preLine "infixl:65 \" + \"") (LSP.getNat r ["range", "start", "line"])
        let (srv, r) := ask srv "textDocument/hover" src (offAfter src "1 +" (-1))
        let md := LSP.getStr r ["contents", "value"]
        check ((md.splitOn "Add Nat").length > 1) s!"no instance in the hover:\n{md}"
        check ((md.splitOn "expands to\n```wiz\nHAdd.hAdd 1 2").length > 1) s!"no expansion in the hover:\n{md}"
        -- a category's name, where a rule uses it and in the rule's target
        for needle in ["\"greet\" greeting", ": greeting"] do
          let (_, r) := ask srv "textDocument/definition" src (offAfter src needle (-2))
          checkEq 1 (LSP.getNat r ["range", "start", "line"])
        -- the module of an import
        let (srv, r) := ask srv "textDocument/definition" src (offAfter src "import Pre" (-1))
        check ((LSP.getStr r ["uri"]).endsWith "lib/Prelude.wiz") s!"import: {r.compress}"
        let (_, r) := ask srv "textDocument/hover" src (offAfter src "import Pre" (-1))
        check (has r "module `Prelude`") s!"import hover: {r.compress}" },
    { name := "11w: at the start of a tactic, the goals before it (inside it, after)", run := fun _ => do
        let src := "import Prelude\ndef k : (A : Type) → A → Nat → A := by\n  intro A\n  intro x\n  intro n\n  exact x\n"
        let (srv, _) ← openDoc src
        let at_ := offAfter src "  exact" (-5)
        let (srv, r) := ask srv "wiz/plainGoal" src at_
        checkEq "[\"A : Type\\nx : A\\nn : Nat\\n⊢ A\"]" (LSP.get? r ["goals"] |>.get!).compress
        let (srv, r) := ask srv "wiz/interactiveGoals" src at_
        check (has r "\"names\":[\"A\"]") s!"interactive: {r.compress}"
        let (srv, r) := ask srv "wiz/plainGoal" src (at_ + 2)
        checkEq "no goals" (LSP.getStr r ["rendered"])
        -- the first tactic: before it, the block's goal
        let (_, r) := ask srv "wiz/plainGoal" src (offAfter src "  intro A" (-7))
        checkEq "[\"⊢ (A : Type) → A → Nat → A\"]" (LSP.get? r ["goals"] |>.get!).compress },
    { name := "11w: hovers, expected types and definitions inside tactic arguments and list literals", run := fun _ => do
        let src := "import Prelude\ndef f (n : Nat) : Nat := by\n  exact Nat.add n 1\ndef xs (k : Nat) : List Nat := [k, 2]\n"
        let (srv, _) ← openDoc src
        let (srv, r) := ask srv "textDocument/hover" src (offAfter src "add n" (-1))
        check (has r "n : Nat") s!"hover in exact: {r.compress}"
        let (srv, r) := ask srv "textDocument/definition" src (offAfter src "Nat.add n" (-4))
        check ((LSP.getStr r ["uri"]).endsWith "lib/Prelude.wiz") s!"definition in exact: {r.compress}"
        let (srv, r) := ask srv "wiz/plainTermGoal" src (offAfter src "add n" (-1))
        checkEq "n : Nat\n⊢ Nat" (LSP.getStr r ["goal"])
        -- a list literal (a procedural macro): its elements are the user's
        let (_, r) := ask srv "textDocument/hover" src (offAfter src "[k" (-1))
        check (has r "k : Nat") s!"hover in a list literal: {r.compress}" },
    { name := "11q: binders, pattern variables, declarations, messages and instances in the infoview", run := fun _ => do
        let src := "import Prelude\ndef pred (n : Nat) : Nat := match n with\n  | .zero => 0\n  | .succ m => m\nstructure P where\n  x : Nat\n  y : Bool\n#check pred 3\ndef six : Nat := 2 * 3\n"
        let (srv, _) ← openDoc src
        -- a binder: its type (hover), its context (the expected type request)
        let (srv, r) := ask srv "textDocument/hover" src (offAfter src "(n" (-1))
        check (has r "n : Nat") s!"binder hover: {r.compress}"
        let (srv, r) := ask srv "wiz/plainTermGoal" src (offAfter src "(n" (-1))
        checkEq "⊢ Nat" (LSP.getStr r ["goal"])
        -- a pattern variable: the arm's context
        let (srv, r) := ask srv "wiz/plainTermGoal" src (offAfter src ".succ m" (-1))
        -- (`m` is the constructor's field, as a definition: `m : Nat := n✝`)
        let g := LSP.getStr r ["goal"]
        check ((g.splitOn "\nm : Nat").length > 1 && g.endsWith "⊢ Nat") s!"pattern variable: {r.compress}"
        let item (r : Lean.Json) (kind : String) : List Lean.Json := match LSP.get? r ["items"] with
          | some (.arr is) => is.toList.filter (LSP.getStr · ["kind"] == kind)
          | _ => []
        -- a command: what it declares (a structure: its constructor and fields)
        let (srv, r) := ask srv "wiz/interactiveInfo" src (offAfter src "structure P" (-1))
        let ds := (item r "declaration").map fun d => s!"{LSP.getStr d ["title"]} : {flatten (LSP.get? d ["type"]).get!}"
        for d in ["P : Type", "P.x : P → Nat", "P.y : P → Bool"] do
          check (ds.contains d) s!"no {d} in {ds}"
        check (ds.any (·.startsWith "P.mk : ")) s!"no constructor in {ds}"
        let (srv, r) := ask srv "wiz/interactiveInfo" src (offAfter src "def pred" (-1))
        checkEq ["pred : Nat → Nat"] ((item r "declaration").map fun d => s!"{LSP.getStr d ["title"]} : {flatten (LSP.get? d ["type"]).get!}")
        -- `#check`: its message
        let (srv, r) := ask srv "wiz/interactiveInfo" src (offAfter src "#check" (-2))
        checkEq ["pred 3 : Nat"] ((item r "message").map (LSP.getStr · ["text"]))
        -- an instance argument, at the notation that needed it; and the syntax
        let (_, r) := ask srv "wiz/interactiveInfo" src (offAfter src "2 *" (-1))
        checkEq ["HMul Nat Nat Nat"] ((item r "instance").map fun i => flatten (LSP.get? i ["type"]).get!)
        check ((item r "syntax").length == 1 && (item r "expansion").length == 1) s!"syntax items: {r.compress}" },
    { name := "inlay hints: the types of fun and let binders written without one", run := fun _ => do
        let src := "import Prelude\ndef f : Nat → Nat := fun x => Nat.succ x\ndef g : Nat := let n := 2\n  Nat.add n n\n" ++
          "def h : Nat → Bool → Nat := fun a b => a\ndef k : Nat → Nat := fun (y : Nat) => y\n"
        let (srv, _) ← openDoc src
        let (_, out) := LSP.handle srv (req s!"\{\"jsonrpc\":\"2.0\",\"id\":7,\"method\":\"textDocument/inlayHint\",\"params\":\{\"textDocument\":\{\"uri\":\"file:///t.wiz\"},\"range\":\{\"start\":{posJson src 0},\"end\":{posJson src src.length}}}}")
        let some (.arr hs) := LSP.get? out[0]! ["result"] | throw (IO.userError s!"{out[0]!.compress}")
        let got := hs.toList.map fun h => (LSP.ofPos src (LSP.getNat h ["position", "line"]) (LSP.getNat h ["position", "character"]), LSP.getStr h ["label"])
        checkEq [(offAfter src "fun x", " : Nat"), (offAfter src "let n", " : Nat"), (offAfter src "fun a", " : Nat"),
                 (offAfter src "fun a b", " : Bool")] got },
    { name := "semantic tokens: the keywords of declared syntax, a keyword-scoped DSL's inside it", run := fun _ => do
        let src := "import Prelude\ndeclare_syntax_cat calc_e (keywords := calc_kw)\n" ++
          "syntax (name := var) ident : calc_e\nsyntax (name := host) \"[\" term \"]\" : calc_e\n" ++
          "syntax:20 (name := ifE) \"when\" calc_e \"yes\" calc_e:20 \"no\" calc_e:20 : calc_e\n" ++
          "syntax (name := calc) \"run_calc\" calc_e \"done\" : term\n" ++
          "macro_rules\n  | `(term| run_calc [ $t ] done) => `(term| $t)\n" ++
          "macro_rules\n  | `(term| run_calc when $c yes $a no $b done) => `(term| match run_calc $c done with | .true => run_calc $a done | .false => run_calc $b done)\n" ++
          "def no (yes : Nat) : Nat := yes\n" ++
          "#eval run_calc when [Bool.true] yes [no 1] no [3] done\n" ++
          "def k : Nat → Nat := by\n  intro n\n  exact n\n"
        let (srv, _) ← openDoc src
        let (_, out) := LSP.handle srv (req "{\"jsonrpc\":\"2.0\",\"id\":3,\"method\":\"textDocument/semanticTokens/full\",\"params\":{\"textDocument\":{\"uri\":\"file:///t.wiz\"}}}")
        let some (.arr d) := LSP.get? out[0]! ["result", "data"] | throw (IO.userError s!"{out[0]!.compress}")
        let d := d.toList.map fun j => j.getNat?.toOption.getD 0
        -- decode: absolute (line, column, length)
        let rec go : List Nat → Nat → Nat → List (Nat × Nat × Nat)
          | dl :: dc :: len :: _ :: _ :: rest, l, c =>
            let l' := l + dl
            let c' := if dl == 0 then c + dc else dc
            (l', c', len) :: go rest l' c'
          | _, _, _ => []
        let toks := go d 0 0
        let line := 11
        let text := (src.splitOn "\n")[line]!
        let words := (toks.filter (·.1 == line)).map fun (_, c, len) => String.ofList ((text.toList.drop c).take len)
        checkEq ["run_calc", "when", "yes", "no", "done"] words
        -- `no` and `yes` outside the DSL are names
        check (!(toks.any fun (l, _, _) => l == 10)) s!"line 10: {toks}"
        -- a tactic name
        check (toks.any fun (l, c, len) => l == 13 && c == 2 && len == 5) s!"intro: {toks}" },
    { name := "completion: locals and expected type, globals, dot completion, tactics, commands", run := fun _ => do
        let src := completionSrc
        let (srv, _) ← openDoc src
        -- `l`: the locals first (with their types), then the globals ending in `Nat`
        let cs := completions srv src (offAfter src ":= l")
        -- (the innermost first)
        checkEq ["lb", "len"] ((labels cs).take 2)
        checkEq ("len", "len", "Nat") cs[1]!
        checkEq ["lb", "len", "let"] (labels cs)
        -- no prefix: the locals, then the globals ending in the expected `Nat`, then the rest
        let cs := labels (completions srv src (offAfter src "Nat.succ "))
        checkEq "m" cs[0]!
        let (i, j) := (cs.idxOf "List.length", cs.idxOf "Bool.true")
        check (i < j && j < cs.length) s!"ranking: {cs}"
        -- `pt.`: the fields and the functions taking a `Point` first (not `Point.mk`)
        let cs := completions srv src (offAfter src "n pt.")
        checkEq ["pt.px", "pt.py", "pt.norm"] (labels cs)
        checkEq ("pt.px", "pt.px", "Nat") cs[0]!
        -- `Nat.ad`: in a namespace
        checkEq ["Nat.add"] (labels (completions srv src (offAfter src "Nat := Nat.ad" (k := 1))))
        -- a tactic, and a command
        checkEq ["exact"] (labels (completions srv src (offAfter src "  ex")))
        let ts := labels (completions srv src (offAfter src "intro x\n  "))
        for t in ["intro", "exact", "apply", "rfl"] do check (ts.contains t) s!"tactic {t}: {ts}"
        check (!ts.contains "Nat.add") s!"globals at a tactic: {ts}"
        checkEq ["declare_syntax_cat", "def", "deriving"] (labels (completions srv src (offAfter src "\nde")))
        -- `import`
        let src := "import Pre"
        let (srv, _) ← openDoc src
        checkEq ["Prelude"] (labels (completions srv src src.length))
        -- the edit replaces the word: `Nat.ad` ↦ `Nat.add`
        let src := completionSrc
        let (srv, _) ← openDoc src
        let (_, r) := ask srv "textDocument/completion" src (offAfter src "Nat := Nat.ad" (k := 1))
        let some (.arr is) := LSP.get? r ["items"] | throw (IO.userError s!"{r.compress}")
        let e := is[0]!
        let st := LSP.ofPos src (LSP.getNat e ["textEdit", "range", "start", "line"]) (LSP.getNat e ["textEdit", "range", "start", "character"])
        let edit : Actions.Edit := { start := st, stop := offAfter src "Nat := Nat.ad" (k := 1), text := LSP.getStr e ["textEdit", "newText"] }
        let edited := Actions.apply src #[edit]
        check ((edited.splitOn ":= Nat.add\ndef baz").length > 1) s!"edited:\n{edited}" },
    { name := "completion: the keywords of a keyword-scoped DSL (13j)", run := fun _ => do
        let src := "import Prelude\ndeclare_syntax_cat calc_e (keywords := calc_kw)\n" ++
          "syntax (name := var) ident : calc_e\nsyntax (name := host) \"[\" term \"]\" : calc_e\n" ++
          "syntax:20 (name := ifE) \"when\" calc_e \"yes\" calc_e:20 \"no\" calc_e:20 : calc_e\n" ++
          "syntax (name := calc) \"run_calc\" calc_e \"done\" : term\n" ++
          "#eval run_calc when [0] ye\n#eval run_calc wh\n"
        let (srv, _) ← openDoc src
        checkEq ["yes"] (labels (completions srv src (offAfter src "] ye")))
        checkEq ["when"] (labels (completions srv src (offAfter src "run_calc wh"))) },
    { name := "code action: fill a hole from its expected type", run := fun _ => do
        let src := "import Prelude\nstructure Point where\n  px : Nat\n  py : Nat\n" ++
          "inductive T where\n  | a\n  | b (t : T)\n  | c (x y : Nat)\n" ++
          "def p : Point := _\ndef q (f : T → Nat) : Nat := f ?t\ndef r : Nat → Bool := ?f\n"
        let (srv, _) ← openDoc src
        let fill (srv : LSP.Server) (at_ : Nat) (title : String) : IO String := do
          let (_, as) := codeActions srv src at_
          let some a := titled as title | throw (IO.userError s!"no {title}: {as.map (·.compress)}")
          pure (applyEdit src (LSP.get? a ["edit"]).get!)
        let e ← fill srv (offAfter src "Point := _" (-1)) "Fill with an anonymous constructor"
        check ((e.splitOn "def p : Point := ⟨?px, ?py⟩\n").length > 1) s!"edited:\n{e}"
        -- an argument: in parentheses
        let e ← fill srv (offAfter src "f ?t" (-1)) "Fill with '.c'"
        check ((e.splitOn "f (.c ?x ?y)\n").length > 1) s!"edited:\n{e}"
        let e ← fill srv (offAfter src "f ?t" (-1)) "Fill with '.a'"
        check ((e.splitOn "f .a\n").length > 1) s!"edited:\n{e}"
        let e ← fill srv (offAfter src ":= ?f" (-1)) "Fill with 'fun x => ?body'"
        check ((e.splitOn ":= fun x => ?body\n").length > 1) s!"edited:\n{e}"
        -- what the fillings leave is only holes
        let (_, out) ← openDoc e
        let some (.arr ds) := LSP.get? out[0]! ["params", "diagnostics"] | throw (IO.userError "no diagnostics")
        for d in ds do
          check ((LSP.getStr d ["message"]).startsWith "could not infer") s!"diagnostic: {d.compress}" },
    { name := "signature help: the binders of the function being applied (11u)", run := fun _ => do
        let src := "import Prelude\ndef a : Nat := Nat.add 1 \ndef b (xs : List Nat) : Nat := List.length \n" ++
          "def c (f : Nat → Bool → Nat) : Nat := Nat.succ (f 2 \n"
        let (srv, _) ← openDoc src
        let (srv, r) := ask srv "textDocument/signatureHelp" src (offAfter src "Nat.add 1 ")
        checkEq "Nat.add (_ : Nat) (_ : Nat) : Nat" (LSP.getStr ((LSP.get? r ["signatures"]).get!.getArrVal? 0 |>.toOption.get!) ["label"])
        checkEq (1 : Nat) (LSP.getNat r ["activeParameter"])
        let (srv, r) := ask srv "textDocument/signatureHelp" src (offAfter src "List.length ")
        let sig := (LSP.get? r ["signatures"]).get!.getArrVal? 0 |>.toOption.get!
        checkEq "List.length {A : Type} (_ : List A) : Nat" (LSP.getStr sig ["label"])
        let some (.arr ps) := LSP.get? sig ["parameters"] | throw (IO.userError s!"{sig.compress}")
        checkEq 1 ps.size
        checkEq (0 : Nat) (LSP.getNat r ["activeParameter"])
        -- inside parentheses, a local function
        let (_, r) := ask srv "textDocument/signatureHelp" src (offAfter src "(f 2 ")
        check (has r "Bool") s!"f: {r.compress}"
        checkEq (1 : Nat) (LSP.getNat r ["activeParameter"]) },
    { name := "doc comments in hovers, completion items and signature help (11s)", run := fun _ => do
        let src := "import Prelude\n/-- Twice `n`: `double 2 = 4`. -/\ndef double (n : Nat) : Nat := Nat.add n n\n" ++
          "def four : Nat := double 2\ndef five : Nat := Nat.add 4 \ndef six : Nat := doub\n"
        let (srv, _) ← openDoc src
        -- hover: the type, then the doc as Markdown
        let (srv, r) := ask srv "textDocument/hover" src (offAfter src ":= doub" (-1))
        let md := LSP.getStr r ["contents", "value"]
        checkEq "```wiz\ndouble : Nat → Nat\n```\n\n---\n\nTwice `n`: `double 2 = 4`." md
        -- a local has none
        let (srv, r) := ask srv "textDocument/hover" src (offAfter src "Nat.add n" (-1))
        check (!(has r "---")) s!"local: {r.compress}"
        -- the Prelude's (lib/ is documented)
        let (srv, r) := ask srv "textDocument/hover" src (offAfter src "five : Nat := Nat.ad")
        check (has r "Addition") s!"Nat.add: {r.compress}"
        -- completion items
        let (srv, r) := ask srv "textDocument/completion" src (offAfter src "six : Nat := doub")
        let some (.arr is) := LSP.get? r ["items"] | throw (IO.userError s!"{r.compress}")
        let some i := is.find? (LSP.getStr · ["label"] == "double") | throw (IO.userError s!"{r.compress}")
        checkEq "Twice `n`: `double 2 = 4`." (LSP.getStr i ["documentation", "value"])
        checkEq "markdown" (LSP.getStr i ["documentation", "kind"])
        -- signature help
        let (_, r) := ask srv "textDocument/signatureHelp" src (offAfter src "Nat.add 4 ")
        check (has r "Addition") s!"signature: {r.compress}" },
    { name := "references, document highlights and rename, across the package's modules (11y)", run := fun _ => do
        let lib := "import Prelude\ndef helper (n : Nat) : Nat := Nat.succ n\ndef useHelper : Nat := helper 1\n"
        let src := "import Prelude\nimport Lib\ndef double (n : Nat) : Nat := Nat.add n n\ndef four : Nat := double 2\n" ++
          "def eight : Nat := double (double (helper 2))\n"
        let srv0 ← server
        let srv0 := { srv0 with libs := srv0.libs.insert "Lib" ("/pkg/Lib.wiz", lib) }
        let (srv, _) := LSP.handle srv0 (req "{\"jsonrpc\":\"2.0\",\"id\":0,\"method\":\"initialize\",\"params\":{}}")
        let (srv, _) := LSP.handle srv (Lean.Json.mkObj [("jsonrpc", "2.0"), ("method", "textDocument/didOpen"),
          ("params", Lean.Json.mkObj [("textDocument", Lean.Json.mkObj [("uri", "file:///t.wiz"), ("version", (1 : Nat)), ("text", src)])])])
        let locs (r : Lean.Json) : List (String × Nat × Nat) := match r with
          | .arr ls => ls.toList.map fun l => (LSP.getStr l ["uri"], LSP.getNat l ["range", "start", "line"], LSP.getNat l ["range", "start", "character"])
          | _ => []
        -- a global of this file: its declaration and its three uses
        let (srv, r) := ask srv "textDocument/references" src (offAfter src "four : Nat := dou")
        checkEq [("file:///t.wiz", 2, 4), ("file:///t.wiz", 3, 18), ("file:///t.wiz", 4, 19), ("file:///t.wiz", 4, 27)] (locs r)
        -- a global of a package module: there too
        let (srv, r) := ask srv "textDocument/references" src (offAfter src "(helper" (-2))
        let sorted := (locs r).toArray.qsort fun a b => a.1 < b.1 || (a.1 == b.1 && (a.2.1 < b.2.1 || (a.2.1 == b.2.1 && a.2.2 < b.2.2)))
        checkEq [("file:///pkg/Lib.wiz", 1, 4), ("file:///pkg/Lib.wiz", 2, 23), ("file:///t.wiz", 4, 35)] sorted.toList
        -- a local: the binder and its uses
        let (srv, r) := ask srv "textDocument/documentHighlight" src (offAfter src "Nat.add n" (-1))
        let some (.arr hs) := some r | throw (IO.userError s!"{r.compress}")
        checkEq 3 hs.size
        -- the toolchain's library can't be renamed
        let (srv, r) := ask srv "textDocument/prepareRename" src (offAfter src "Nat.ad")
        check (has r "toolchain") s!"prepareRename: {r.compress}"
        -- rename a global: every document, and the package module
        let (srv', out) := LSP.handle srv (req s!"\{\"jsonrpc\":\"2.0\",\"id\":8,\"method\":\"textDocument/rename\",\"params\":\{\"textDocument\":\{\"uri\":\"file:///t.wiz\"},\"position\":{posJson src (offAfter src "four : Nat := dou")},\"newName\":\"twice\"}}")
        let some e := LSP.get? out[0]! ["result"] | throw (IO.userError s!"{out[0]!.compress}")
        let src' := applyEdit src e
        check ((src'.splitOn "double").length == 1) s!"renamed:\n{src'}"
        checkEq ([] : List String) (← codes (src'.replace "import Lib\n" "" |>.replace "(helper 2)" "2"))
        let (_, out) := LSP.handle srv' (req s!"\{\"jsonrpc\":\"2.0\",\"id\":8,\"method\":\"textDocument/rename\",\"params\":\{\"textDocument\":\{\"uri\":\"file:///t.wiz\"},\"position\":{posJson src (offAfter src "(helper" (-2))},\"newName\":\"aid\"}}")
        check (has out[0]! "file:///pkg/Lib.wiz") s!"rename in Lib: {out[0]!.compress}"
        -- a local
        let (_, out) := LSP.handle srv (req s!"\{\"jsonrpc\":\"2.0\",\"id\":8,\"method\":\"textDocument/rename\",\"params\":\{\"textDocument\":\{\"uri\":\"file:///t.wiz\"},\"position\":{posJson src (offAfter src "Nat.add n" (-1))},\"newName\":\"m\"}}")
        let src' := applyEdit src (LSP.get? out[0]! ["result"]).get!
        check ((src'.splitOn "def double (m : Nat) : Nat := Nat.add m m\n").length > 1) s!"renamed:\n{src'}" },
    { name := "document symbols, workspace symbols and folding ranges (11v)", run := fun _ => do
        let src := "import Prelude\n/- a block\n   comment -/\nstructure Point where\n  px : Nat\n  py : Nat\n" ++
          "def Point.norm (p : Point) : Nat := p.px\ndef k : Nat → Nat := by\n  intro n\n  exact n\n"
        let (srv, _) ← openDoc src
        let (srv, out) := LSP.handle srv (req "{\"jsonrpc\":\"2.0\",\"id\":3,\"method\":\"textDocument/documentSymbol\",\"params\":{\"textDocument\":{\"uri\":\"file:///t.wiz\"}}}")
        let some (.arr syms) := LSP.get? out[0]! ["result"] | throw (IO.userError s!"{out[0]!.compress}")
        checkEq ["Point", "Point.norm", "k"] (syms.toList.map (LSP.getStr · ["name"]))
        checkEq (23 : Nat) (LSP.getNat syms[0]! ["kind"])
        let kids := match LSP.get? syms[0]! ["children"] with
          | some (.arr ks) => ks.toList.map (LSP.getStr · ["name"])
          | _ => []
        for f in ["Point.px", "Point.py"] do check (kids.contains f) s!"children: {kids}"
        checkEq "Point → Nat" (LSP.getStr syms[1]! ["detail"])
        checkEq (7 : Nat) (LSP.getNat syms[2]! ["range", "start", "line"])
        -- workspace symbols: by a part of the name, ignoring case
        let (srv, out) := LSP.handle srv (req "{\"jsonrpc\":\"2.0\",\"id\":4,\"method\":\"workspace/symbol\",\"params\":{\"query\":\"NORM\"}}")
        let some (.arr ws) := LSP.get? out[0]! ["result"] | throw (IO.userError s!"{out[0]!.compress}")
        -- (the open documents' own declarations first, then the libraries')
        checkEq "Point.norm" (LSP.getStr ws[0]! ["name"])
        checkEq "file:///t.wiz" (LSP.getStr ws[0]! ["location", "uri"])
        check (ws.toList.any (LSP.getStr · ["name"] == "TacticM.normalize")) s!"{ws.map (·.compress)}"
        let (_, out) := LSP.handle srv (req "{\"jsonrpc\":\"2.0\",\"id\":4,\"method\":\"workspace/symbol\",\"params\":{\"query\":\"Nat.add\"}}")
        check (has out[0]! "lib/Prelude.wiz") s!"Nat.add in the Prelude: {out[0]!.compress}"
        -- folding: the comment, the structure, the `by` block's definition
        let (_, out) := LSP.handle srv (req "{\"jsonrpc\":\"2.0\",\"id\":5,\"method\":\"textDocument/foldingRange\",\"params\":{\"textDocument\":{\"uri\":\"file:///t.wiz\"}}}")
        let some (.arr fs) := LSP.get? out[0]! ["result"] | throw (IO.userError s!"{out[0]!.compress}")
        let rs := fs.toList.map fun f => (LSP.getNat f ["startLine"], LSP.getNat f ["endLine"], LSP.getStr f ["kind"])
        for r in [(1, 2, "comment"), (3, 5, ""), (7, 9, "")] do
          check (rs.contains r) s!"folding {r}: {rs}" },
    { name := "infoview socket: cursor notifications, requests answered on the socket", run := fun _ => do
        -- a watchdog: a broken server must fail the case, not hang the suite (and since
        -- the process would wait for it, the case ends with an explicit exit)
        let _ ← IO.asTask (prio := .dedicated) (do IO.sleep 60000; IO.eprintln "timed out"; IO.Process.exit 3 : IO Unit)
        try socketCase; IO.Process.exit 0
        catch e => IO.eprintln e; IO.Process.exit 1 },
    { name := "WebSocket: handshake (RFC 6455's example), frames", run := fun _ => do
        checkEq "s3pPLMBiTxaQ9kYGzzhZRbK+xOo=" (WebSocket.acceptKey "dGhlIHNhbXBsZSBub25jZQ==")
        checkEq "2fd4e1c67a2d28fced849ee1bb76e7391b93eb12"
          (String.join ((WebSocket.sha1 "The quick brown fox jumps over the lazy dog".toUTF8).toList.map fun b =>
            let h := Nat.toDigits 16 b.toNat; String.ofList (if h.length < 2 then '0' :: h else h)))
        checkEq "Zm9vYmE=" (WebSocket.base64 "fooba".toUTF8)
        for o in ["null", "http://localhost:8766", "http://127.0.0.1", "vscode-webview://abc"] do
          check (WebSocket.localOrigin o) s!"{o} refused"
        for o in ["https://example.com", "http://localhost.example.com", "http://127.0.0.1.nip.io:80"] do
          check (!WebSocket.localOrigin o) s!"{o} let in"
        -- frames of each length class, masked and not, read back
        let ((r, w), (r', w')) ← Socket.pair
        let (r, w, r', w') := (IO.FS.Stream.ofHandle r, IO.FS.Stream.ofHandle w, IO.FS.Stream.ofHandle r', IO.FS.Stream.ofHandle w')
        for n in [0, 125, 126, 65535, 65536, 200000] do
          let text := String.ofList (List.replicate n 'x')
          WebSocket.sendText w text (some (ByteArray.mk #[9, 8, 7, 6]))
          checkEq (some text) (← WebSocket.recvText r' w')
          WebSocket.sendText w' text
          checkEq (some text) (← WebSocket.recvText r w (server := false))
        -- an unmasked frame from a client breaks the protocol
        WebSocket.sendText w "x"
        checkEq none (← WebSocket.recvText r' w') },
    { name := "inside a feral block: hovers, go to definition and errors at the Feral source", run := fun _ => do
        -- the server's library: Prelude, Feral and the runtime of lowered code
        let mut libs := (← server).libs
        -- plus whatever Optic/FeralCore import on this tree (Result, Logic, OpticDerive and
        -- Deriving arrive with the cohesion stack); a module whose file is absent is skipped
        for (m, p) in [("Optic", "lib/Optic.wiz"), ("Region", "lib/Region.wiz"), ("Text", "lib/Text.wiz"),
                       ("Feral", "lib/Feral.wiz"), ("FeralCore", "drafts/feral/lib/FeralCore.wiz"),
                       ("Result", "lib/Result.wiz"), ("Logic", "lib/Logic.wiz"),
                       ("OpticDerive", "lib/OpticDerive.wiz"), ("Deriving", "lib/Deriving.wiz")] do
          if ← System.FilePath.pathExists p then
            libs := libs.insert m (p, ← IO.FS.readFile p)
        let srv : LSP.Server := { (← server) with libs, trusted := ["Prelude", "Optic", "Region", "Text", "Feral"] }
        let (srv, _) := LSP.handle srv (req "{\"jsonrpc\":\"2.0\",\"id\":0,\"method\":\"initialize\",\"params\":{}}")
        let src := "import FeralCore\nimport Feral\nferal\n  fn double (n : U64) : U64 := n + n\n" ++
          "  fn f (x : U64) : U64 := {\n    let mut v := Vec.new;\n    v.push x;\n    double (v.len)\n  }\nend\n"
        let msg := Lean.Json.mkObj [("jsonrpc", "2.0"), ("method", "textDocument/didOpen"),
          ("params", Lean.Json.mkObj [("textDocument", Lean.Json.mkObj [("uri", "file:///t.wiz"), ("version", (1 : Nat)), ("text", src)])])]
        let (srv, out) := LSP.handle srv msg
        check (!has (Lean.Json.arr out) "\"severity\":1") s!"errors: {(Lean.Json.arr out).compress}"
        -- the type first; then (for a node of Feral's grammar) its `syntax`
        let hover (srv : LSP.Server) (off : Nat) (want : String) : IO Unit := do
          let md := LSP.getStr (ask srv "textDocument/hover" src off).2 ["contents", "value"]
          check (md.startsWith s!"```wiz\n{want}\n```") s!"expected {want}, got\n{md}"
        hover srv (offAfter src "push x" (-1)) "x : U64"
        hover srv (offAfter src "double (v" (-4)) "double : U64 → Result U64"
        -- a call's value is named by the call (not by the lowering's local `v_…`)
        hover srv (offAfter src "double (v" (-3)) "double (v.len) : U64"
        -- go to definition: `fn double`, line 4
        let (srv, r) := ask srv "textDocument/definition" src (offAfter src "double (v" (-4))
        checkEq "file:///t.wiz" (LSP.getStr r ["uri"])
        checkEq 3 (LSP.getNat r ["range", "start", "line"])
        checkEq 2 (LSP.getNat r ["range", "start", "character"])
        -- a type error of the lowering (unchecked) is at the expression, line 13 (not the item, line 8)
        let bad ← IO.FS.readFile "drafts/feral/rejected/surface/E0499_two_mut.wiz"
        let bad := bad.replace "\nferal\n" "\n#unchecked feral\n"
        let msg := Lean.Json.mkObj [("jsonrpc", "2.0"), ("method", "textDocument/didChange"),
          ("params", Lean.Json.mkObj [("textDocument", Lean.Json.mkObj [("uri", "file:///t.wiz"), ("version", (2 : Nat))]),
            ("contentChanges", Lean.Json.arr #[Lean.Json.mkObj [("text", bad)]])])]
        let (_, out) := LSP.handle srv msg
        let diags := out.toList.flatMap fun j => match (j.getObjVal? "params" >>= (·.getObjVal? "diagnostics")).toOption with
          | some (.arr ds) => ds.toList
          | _ => []
        check (diags.any fun d => LSP.getNat d ["range", "start", "line"] == 12 && has d "type mismatch")
          s!"no type mismatch on line 13: {(Lean.Json.arr diags.toArray).compress}" },
    { name := "11w: the web infoview's files over HTTP on the WebSocket's port (fixed list, local origins)", run := fun _ => do
        let dir ← IO.FS.createTempDir
        IO.FS.writeFile (dir / "infoview.html") "<p>page</p>"
        IO.FS.writeFile (dir / "secret.txt") "no"
        -- one request, through `accept`, on a socket pair: the answer's text
        let ask (req : String) (web : Option String := some dir.toString) : IO (Bool × String) := do
          let ((r, w), (r', w')) ← Socket.pair
          let (r, w, r', w') := (IO.FS.Stream.ofHandle r, IO.FS.Stream.ofHandle w, IO.FS.Stream.ofHandle r', IO.FS.Stream.ofHandle w')
          w.putStr req; w.flush
          let ok ← WebSocket.accept r' w' web
          let mut out := ""
          for _ in [0:20] do
            let l ← r.getLine
            out := out ++ l
            if l.isEmpty || (out.splitOn "\r\n\r\n").length > 1 then break
          pure (ok, out)
        let (ok, out) ← ask "GET /infoview.html?port=1&follow=1 HTTP/1.1\r\nHost: 127.0.0.1\r\n\r\n"
        check (!ok && (out.splitOn "200 OK").length > 1 && (out.splitOn "text/html").length > 1) s!"page: {out}"
        let (_, out) ← ask "GET / HTTP/1.1\r\n\r\n"
        check ((out.splitOn "200 OK").length > 1) s!"index: {out}"
        for path in ["/secret.txt", "/../infoview.html", "/wiz-infoview.wasm", "/infoview.html/x"] do
          let (_, out) ← ask s!"GET {path} HTTP/1.1\r\n\r\n"
          check ((out.splitOn "404").length > 1) s!"{path}: {out}"
        let (_, out) ← ask "GET /infoview.html HTTP/1.1\r\nOrigin: https://example.com\r\n\r\n"
        check ((out.splitOn "403").length > 1) s!"foreign origin: {out}"
        -- without the directory (plain `--ws`): no files at all
        let (_, out) ← ask "GET /infoview.html HTTP/1.1\r\n\r\n" none
        check ((out.splitOn "426").length > 1) s!"no web directory: {out}" },
    { name := "WebSocket transport (--ws): infoview requests, editing, origins", run := fun _ => do
        let _ ← IO.asTask (prio := .dedicated) (do IO.sleep 60000; IO.eprintln "timed out"; IO.Process.exit 3 : IO Unit)
        try wsCase; IO.Process.exit 0
        catch e => IO.eprintln e; IO.Process.exit 1 }
  ]

/-- The Neovim plugin (editors/nvim, stage 11p): abbreviations and the infoview, in a
headless nvim against the real `wiz lsp`. Skipped when there is no `nvim` (the dev shell
has one). -/
def nvimGroup : Group where
  name := "nvim"
  exercise := "editors/nvim (stage 11p)"
  cases := [
    { name := "wiz.nvim: abbreviations, and the infoview against wiz lsp (editors/nvim/tests/run.sh)", run := fun _ => do
        let out ← IO.Process.output { cmd := "sh", args := #["editors/nvim/tests/run.sh"] }
        if out.stdout.startsWith "skipped" then skip ((out.stdout.replace "skipped: " "").trimAscii.toString)
        else unless out.exitCode == 0 do
          throw (IO.userError s!"editors/nvim/tests/run.sh failed:\n{out.stdout}{out.stderr}") }
  ]

/-- This module's test groups, which `Tests/Main.lean` runs: one per line, in sorted
order, so that branches adding groups rarely touch the same lines. A new group also
needs a shard in `.github/test-shards.json` (CI checks). -/
def groups : List Group :=
  group ::
  nvimGroup ::
  serverGroup ::
  []

end Tests.LSP
