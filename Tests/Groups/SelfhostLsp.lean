import Tests.Elab
import Tests.Groups.SelfhostCli
import Wiz.LSP

open Wiz

-- Closed terms are normally evaluated at program start-up; that would execute
-- unimplemented `sorry`s before any test runs.
set_option compiler.extract_closed false

namespace Tests.Elab

/-!
# The self-hosted language server (stage 21, D8)

`wiz-selfhost lsp` speaks the JSON-RPC subset the playground's self-hosted shim answers
(`web/selfhost-lsp-shim.js`): `initialize`, full-text `didOpen`/`didChange`/`didClose`,
`publishDiagnostics`, `wiz/elaborated`, and the plain infoview queries (which answer
`null`). The cases drive the real binary over a pipe, as `Tests/Groups/Grail.lean` does
for the Lean-hosted `grail lsp`: a session of messages in, the framed messages out.

The goldens pin the *messages* (order, method names, the shapes the host emits) and the
framing (`Content-Length` is the body's UTF-8 byte count, so a reader that counted
characters would desynchronise; the document in the second case has characters above
U+007F).
-/

/-- Run the self-hosted compiler's `lsp` in a fresh directory holding `files`, send
`msgs` (a whole session), and return the framed output, its stderr and the exit code.
`timeout` bounds a server that does not exit. -/
def selfhostLspSession (exe : System.FilePath) (dir : System.FilePath)
    (files : Array (String × String)) (msgs : List Lean.Json) :
    IO (UInt32 × String × String) := do
  for (name, text) in files do
    if let some sub := (System.FilePath.mk name).parent then IO.FS.createDirAll (dir / sub)
    IO.FS.writeFile (dir / name) text
  let child ← IO.Process.spawn
    { cmd := "timeout", args := #["120", exe.toString, "lsp"], cwd := dir,
      stdin := .piped, stdout := .piped, stderr := .piped }
  let (stdin, child) ← child.takeStdin
  let input := IO.FS.Stream.ofHandle stdin
  for m in msgs do LSP.writeMessage input m
  let out ← child.stdout.readToEnd
  let err ← child.stderr.readToEnd
  let code ← child.wait
  pure (code, out, err)

/-- The messages of a framed stream: the `Content-Length` must equal the body's UTF-8
byte count, and every body must parse (a wrong length desynchronises the stream). -/
def lspMessages (raw : String) : IO (List Lean.Json) := do
  let mut out : List Lean.Json := []
  -- a body from this server never holds a raw CR/LF (they are `\r`/`\n` escapes), so
  -- the separator after a header is unambiguous
  for chunk in (raw.splitOn "Content-Length: ").drop 1 do
    let parts := chunk.splitOn "\r\n\r\n"
    let some len := parts[0]!.trimAscii.toString.toNat? | throw (IO.userError s!"bad Content-Length: {chunk.take 80}")
    let body := "\r\n\r\n".intercalate (parts.drop 1)
    unless body.utf8ByteSize == len do
      throw (IO.userError s!"Content-Length {len} but the body is {body.utf8ByteSize} bytes:\n{body.take 200}")
    match Lean.Json.parse body with
    | .ok j => out := j :: out
    | .error e => throw (IO.userError s!"a message is not JSON ({e}):\n{body.take 200}")
  pure out.reverse

/-- The `n`th message, or an error naming what arrived. -/
def lspAt (msgs : List Lean.Json) (n : Nat) : IO Lean.Json :=
  match msgs[n]? with
  | some m => pure m
  | none => throw (IO.userError s!"no message {n}: {msgs.length} messages")

/-- The value at `path`: object keys, and a decimal path element indexes an array
(`LSP.get?` walks objects only, and a diagnostic is an array element). -/
def jpath (j : Lean.Json) (path : List String) : Option Lean.Json :=
  path.foldlM (fun cur k => match cur with
    | .arr xs => match k.toNat? with
      | some n => xs[n]?
      | none => none
    | _ => (cur.getObjVal? k).toOption) j

/-- The string at `path` (`""` when absent). -/
def lspStr (j : Lean.Json) (path : List String) : String :=
  match jpath j path with
  | some (.str s) => s
  | _ => ""

def lspNat (j : Lean.Json) (path : List String) : Nat :=
  match jpath j path with
  | some v => (v.getNat?.toOption).getD 0
  | none => 0

/-- The string array at `path`. -/
def lspStrs (j : Lean.Json) (path : List String) : List String :=
  match jpath j path with
  | some (.arr xs) => xs.toList.map (fun x => match x with | .str s => s | _ => "")
  | _ => []

/-- A request. -/
def lspReq (id : Nat) (method : String) (params : Lean.Json := Lean.Json.mkObj []) : Lean.Json :=
  Lean.Json.mkObj [("jsonrpc", "2.0"), ("id", Lean.Json.num id), ("method", method), ("params", params)]

/-- A notification. -/
def lspNote (method : String) (params : Lean.Json) : Lean.Json :=
  Lean.Json.mkObj [("jsonrpc", "2.0"), ("method", method), ("params", params)]

/-- A `textDocument` argument. -/
def lspTextDoc (uri text : String) (version : Nat) : Lean.Json :=
  Lean.Json.mkObj [("uri", uri), ("languageId", "wiz"), ("version", Lean.Json.num version), ("text", text)]

def lspLspGood : String := "import Prelude
def one : Nat := 1
def two : Nat := 2
"

def lspLspBad : String := "import Prelude
def one : Nat := 1
def two : Nat := nope
"

/-- The session sent by the first case: a bad document, a hover, a plain goal, an
unknown method, the fixed document, then shutdown/close/exit. -/
def lspLspMsgs (uri : String) : List Lean.Json :=
  [ lspReq 1 "initialize" (Lean.Json.mkObj [("capabilities",
      Lean.Json.mkObj [("experimental", Lean.Json.mkObj [("wizElaborated", Lean.Json.bool true)])])]),
    lspNote "textDocument/didOpen" (Lean.Json.mkObj [("textDocument", lspTextDoc uri lspLspBad 1)]),
    lspReq 2 "textDocument/hover" (Lean.Json.mkObj [("textDocument", Lean.Json.mkObj [("uri", uri)]),
      ("position", Lean.Json.mkObj [("line", 2), ("character", 5)])]),
    lspReq 3 "wiz/plainGoal" (Lean.Json.mkObj [("textDocument", Lean.Json.mkObj [("uri", uri)]),
      ("position", Lean.Json.mkObj [("line", 2), ("character", 5)])]),
    lspReq 4 "textDocument/definition" (Lean.Json.mkObj [("textDocument", Lean.Json.mkObj [("uri", uri)]),
      ("position", Lean.Json.mkObj [("line", 2), ("character", 5)])]),
    lspNote "textDocument/didChange" (Lean.Json.mkObj [
      ("textDocument", Lean.Json.mkObj [("uri", uri), ("version", 2)]),
      ("contentChanges", Lean.Json.arr #[Lean.Json.mkObj [("text", lspLspGood)]])]),
    lspReq 5 "shutdown",
    lspNote "textDocument/didClose" (Lean.Json.mkObj [("textDocument", Lean.Json.mkObj [("uri", uri)])]),
    lspNote "exit" (Lean.Json.mkObj []) ]

def selfhostLspGroup : Group where
  name := "selfhost-lsp"
  exercise := "stage 21 (D8): the self-hosted language server"
  shard := "selfhost"
  cases := [
    { name := "lsp: a session's messages, in the host's shapes", run := fun _ =>
        withSelfhostCli fun exe => do
        let uri := "untitled:test.wiz"
        let dir ← IO.FS.createTempDir
        let (code, out, err) ← selfhostLspSession exe dir #[] (lspLspMsgs uri)
        checkEq 0 code
        checkEq "" err
        let msgs ← lspMessages out
        checkEq 9 msgs.length
        -- initialize: the capabilities the server answers, the host's experimental block
        let init ← lspAt msgs 0
        checkEq 1 ((jpath init ["id"]).bind (fun j => j.getNat?.toOption) |>.getD 0)
        checkEq 1 (lspNat init ["result", "capabilities", "textDocumentSync"])
        checkEq 1 (lspNat init ["result", "capabilities", "experimental", "wizInfoview", "version"])
        checkEq ["wiz/plainGoal", "wiz/plainTermGoal"]
          (lspStrs init ["result", "capabilities", "experimental", "wizInfoview", "methods"])
        checkEq ["wiz/elaborated"]
          (lspStrs init ["result", "capabilities", "experimental", "wizInfoview", "notifications"])
        checkEq "wiz-selfhost" (lspStr init ["result", "serverInfo", "name"])
        -- didOpen: the error, positioned at its command, with `check`'s code and source
        let diag ← lspAt msgs 1
        checkEq "textDocument/publishDiagnostics" (lspStr diag ["method"])
        checkEq uri (lspStr diag ["params", "uri"])
        checkEq 1 (lspNat diag ["params", "diagnostics", "0", "severity"])
        checkEq "wiz" (lspStr diag ["params", "diagnostics", "0", "source"])
        checkEq "unknown-identifier" (lspStr diag ["params", "diagnostics", "0", "code"])
        checkEq "unknown identifier nope" (lspStr diag ["params", "diagnostics", "0", "message"])
        -- the third line of the document, 0-based (import, def one, def two)
        checkEq 2 (lspNat diag ["params", "diagnostics", "0", "range", "start", "line"])
        checkEq 0 (lspNat diag ["params", "diagnostics", "0", "range", "start", "character"])
        -- wiz/elaborated: the session the client asked for
        let elabMsg ← lspAt msgs 2
        checkEq "wiz/elaborated" (lspStr elabMsg ["method"])
        checkEq 1 (lspNat elabMsg ["params", "session"])
        checkEq 1 (lspNat elabMsg ["params", "version"])
        -- hover: null (the shim answers null too)
        let hover ← lspAt msgs 3
        check ((jpath hover ["result"]) == some .null) "hover is null"
        -- the plain infoview query: null (no info tree)
        let goal ← lspAt msgs 4
        check ((jpath goal ["result"]) == some .null) "the plain goal is null"
        -- an unimplemented method: MethodNotFound, as the shim answers the interactive ones
        let defn ← lspAt msgs 5
        checkEq (-32601) ((jpath defn ["error", "code"]).bind (·.getInt?.toOption) |>.getD 0)
        -- didChange: the fixed document has no diagnostics, and a new session
        let fixed ← lspAt msgs 6
        checkEq "textDocument/publishDiagnostics" (lspStr fixed ["method"])
        checkEq 0 (match jpath fixed ["params", "diagnostics"] with
          | some (.arr ds) => ds.size
          | _ => 99)
        checkEq 2 (lspNat (← lspAt msgs 7) ["params", "session"])
        -- shutdown: null; didClose and exit say nothing
        let shut ← lspAt msgs 8
        check ((jpath shut ["result"]) == some .null) "shutdown is null" },
    { name := "lsp: Content-Length is UTF-8 bytes, and initialize's root resolves imports", run := fun _ =>
        withSelfhostCli fun exe => do
        let doc := "import M\ndef greeting : String := \"λ\"\ndef bad : Nat := nope\n"
        let files := #[("M.wiz", "import Prelude\ndef fromM : Nat := 7\n"), ("sub/a.wiz", doc)]
        let dir ← IO.FS.createTempDir
        let path := (dir / "sub" / "a.wiz").toString
        let uri := s!"file://{path}"
        let msgs :=
          [ lspReq 1 "initialize" (Lean.Json.mkObj [("rootUri", s!"file://{dir}")]),
            lspNote "textDocument/didOpen" (Lean.Json.mkObj [("textDocument", lspTextDoc uri doc 1)]),
            lspNote "exit" (Lean.Json.mkObj []) ]
        let (code, out, err) ← selfhostLspSession exe dir files msgs
        checkEq 0 code
        checkEq "" err
        let got ← lspMessages out
        checkEq 2 got.length
        let diag ← lspAt got 1
        checkEq uri (lspStr diag ["params", "uri"])
        -- `import M` resolved against the root `initialize` named: the document's own
        -- directory (`sub/`) has no `M.wiz`. The report is the document's own:
        -- one error, on line 2 (0-based), after a line with a non-ASCII character
        checkEq 1 (match jpath diag ["params", "diagnostics"] with
          | some (.arr ds) => ds.size
          | _ => 99)
        checkEq 2 (lspNat diag ["params", "diagnostics", "0", "range", "start", "line"])
        checkEq "unknown-identifier" (lspStr diag ["params", "diagnostics", "0", "code"]) },
    { name := "lsp: no options, and a flag before it is the host's error", run := fun _ =>
        withSelfhostCli fun exe => do
        let (c, _, err) ← cliRun exe #[] #["lsp", "--bogus"]
        checkEq 2 c
        cliCheck err "unknown flag: --bogus" "lsp flag"
        let (c, _, err) ← cliRun exe #[] #["-I", "lib", "lsp"]
        checkEq 2 c
        cliCheck err "unknown flag: -I" "lsp option" },
    { name := "lsp: plainTermGoal and plainGoal answer from the check's entries", run := fun _ =>
        withSelfhostCli fun exe => do
        let doc := "import Prelude\ndef k (n : Nat) : Nat := by\n  change Nat\n  exact n\n\ndef plain : Nat := 3\n"
        let uri := "file:///tmp/selfhost-goals.wiz"
        -- (line, character): a tactic, the last tactic, after it, outside any `by`, a
        -- plain body, and a `by` body
        let queries := [(2, 4, "wiz/plainGoal"), (3, 4, "wiz/plainGoal"),
          (3, 9, "wiz/plainGoal"), (5, 19, "wiz/plainGoal"),
          (5, 19, "wiz/plainTermGoal"), (2, 4, "wiz/plainTermGoal")]
        let msgs :=
          [ lspReq 1 "initialize",
            lspNote "textDocument/didOpen" (Lean.Json.mkObj [("textDocument", lspTextDoc uri doc 1)]) ] ++
          (queries.toArray.mapIdx fun i (line, char, method) =>
            lspReq (10 + i) method (Lean.Json.mkObj [
              ("textDocument", Lean.Json.mkObj [("uri", uri)]),
              ("position", Lean.Json.mkObj [("line", Lean.Json.num line), ("character", Lean.Json.num char)])])).toList ++
          [ lspNote "exit" (Lean.Json.mkObj []) ]
        let dir ← IO.FS.createTempDir
        let (code, out, err) ← selfhostLspSession exe dir #[] msgs
        checkEq 0 code
        checkEq "" err
        let got ← lspMessages out
        checkEq (2 + queries.length) got.length
        -- the host, for the same document and positions: the values below are compared
        -- field by field (host `Wiz/LSP.lean`: `plainTermGoal` is `{goal, range}` from
        -- `Query.termGoalAt`; `plainGoal` is `plainGoals`' `{rendered, goals, messages}`)
        let prelude ← IO.FS.readFile "lib/Prelude.wiz"
        let srv : LSP.Server :=
          { libs := ({} : Std.HashMap String (String × String)).insert "Prelude" ("lib/Prelude.wiz", prelude),
            trusted := ["Prelude"] }
        let (srv, _) ← LSP.handle srv (lspReq 100 "initialize")
        let (srv, _) ← LSP.handle srv (lspNote "textDocument/didOpen"
          (Lean.Json.mkObj [("textDocument", lspTextDoc uri doc 1)]))
        let mut srv := srv
        let mut qi := 0
        for (line, char, method) in queries do
          let (srv', hostOut) ← LSP.handle srv (lspReq (200 + qi) method (Lean.Json.mkObj [
            ("textDocument", Lean.Json.mkObj [("uri", uri)]),
            ("position", Lean.Json.mkObj [("line", Lean.Json.num line), ("character", Lean.Json.num char)])]))
          srv := srv'
          let host := match hostOut.find? (fun m => (jpath m ["id"] |>.bind (·.getNat?.toOption)) == some (200 + qi)) with
            | some m => (jpath m ["result"]).getD .null
            | none => .null
          let self := match jpath (← lspAt got (2 + qi)) ["result"] with
            | some r => r
            | none => .null
          if method == "wiz/plainTermGoal" then
            checkEq (lspStr host ["goal"]) (lspStr self ["goal"])
            for k in ["start", "end"] do
              checkEq (lspNat host ["range", k, "line"]) (lspNat self ["range", k, "line"])
              checkEq (lspNat host ["range", k, "character"]) (lspNat self ["range", k, "character"])
          else
            checkEq (lspStrs host ["goals"]) (lspStrs self ["goals"])
            checkEq (lspStr host ["rendered"]) (lspStr self ["rendered"])
            checkEq (lspStrs host ["messages"]) (lspStrs self ["messages"])
          qi := qi + 1
        -- and the concrete expectations (so a host change is visible here too)
        checkEq ["n : Nat\n⊢ Nat"] (lspStrs (← lspAt got 2) ["result", "goals"])
        -- at the last tactic, and after it (the end of its line): no goals left
        checkEq [] (lspStrs (← lspAt got 3) ["result", "goals"])
        checkEq "no goals" (lspStr (← lspAt got 4) ["result", "rendered"])
        check ((jpath (← lspAt got 5) ["result"]) == some .null) "outside a by block, plainGoal is null"
        checkEq "⊢ Nat" (lspStr (← lspAt got 6) ["result", "goal"])
        checkEq 5 (lspNat (← lspAt got 6) ["result", "range", "start", "line"])
        checkEq 19 (lspNat (← lspAt got 6) ["result", "range", "start", "character"])
        -- inside the `by` body the expected type is the body's (`n : Nat ⊢ Nat`)
        checkEq "n : Nat\n⊢ Nat" (lspStr (← lspAt got 7) ["result", "goal"])
        checkEq 1 (lspNat (← lspAt got 7) ["result", "range", "start", "line"]) }
  ]

builtin_initialize registerGroup selfhostLspGroup

end Tests.Elab
