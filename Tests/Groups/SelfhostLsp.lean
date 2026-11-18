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
`publishDiagnostics`, `wiz/elaborated`, the plain infoview queries (which answer
`null`), and the navigation methods (`textDocument/documentSymbol`, `definition`,
`references`: `selfhost/LspNav.wiz`). The cases drive the real binary over a pipe, as
`Tests/Groups/Grail.lean` does for the Lean-hosted `grail lsp`: a session of messages in,
the framed messages out.

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
    | .ok j => out := out ++ [j]
    | .error e => throw (IO.userError s!"a message is not JSON ({e}):\n{body.take 200}")
  pure out

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

/-- The `fields` of each object in the array at `path`, as strings (`["name"]` for a
symbol array's names). -/
def lspArrayStrs (j : Lean.Json) (path fields : List String) : List String :=
  match jpath j path with
  | some (.arr xs) => xs.toList.map fun x => lspStr x fields
  | _ => []

/-- The `fields` of each object in the array at `path`, as natural numbers. -/
def lspArrayNats (j : Lean.Json) (path fields : List String) : List Nat :=
  match jpath j path with
  | some (.arr xs) => xs.toList.map fun x => lspNat x fields
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
    lspReq 4 "textDocument/completion" (Lean.Json.mkObj [("textDocument", Lean.Json.mkObj [("uri", uri)]),
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
        -- the navigation methods' providers (`LspNav.wiz`), which the host enables too
        check ((jpath init ["result", "capabilities", "definitionProvider"]) == some (.bool true))
          "definitionProvider"
        check ((jpath init ["result", "capabilities", "referencesProvider"]) == some (.bool true))
          "referencesProvider"
        check ((jpath init ["result", "capabilities", "documentSymbolProvider"]) == some (.bool true))
          "documentSymbolProvider"
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
    { name := "lsp: documentSymbol, definition and references", run := fun _ =>
        withSelfhostCli fun exe => do
        -- one definition (`double`) and two uses; the body is on its own line, so the
        -- symbol's range must cover it
        let doc := "import Prelude\ndef double (n : Nat) : Nat :=\n  n\ndef one : Nat := double 1\ndef two : Nat := double 2\n"
        let dir ← IO.FS.createTempDir
        let path := (dir / "a.wiz").toString
        let uri := s!"file://{path}"
        let docUri := Lean.Json.mkObj [("uri", uri)]
        let atUse := Lean.Json.mkObj [("textDocument", docUri),
          ("position", Lean.Json.mkObj [("line", 3), ("character", 17)])]
        let msgs :=
          [ lspReq 1 "initialize" (Lean.Json.mkObj [("rootUri", s!"file://{dir}")]),
            lspNote "textDocument/didOpen" (Lean.Json.mkObj [("textDocument", lspTextDoc uri doc 1)]),
            lspReq 2 "textDocument/documentSymbol" (Lean.Json.mkObj [("textDocument", docUri)]),
            lspReq 3 "textDocument/definition" atUse,
            -- (the host ignores `context.includeDeclaration`; `Refs.rangesIn` includes
            -- the declaration's name, so this does too)
            lspReq 4 "textDocument/references" (Lean.Json.mkObj [("textDocument", docUri),
              ("position", Lean.Json.mkObj [("line", 3), ("character", 17)]),
              ("context", Lean.Json.mkObj [("includeDeclaration", Lean.Json.bool false)])]),
            lspReq 5 "shutdown",
            lspNote "exit" (Lean.Json.mkObj []) ]
        let (code, out, err) ← selfhostLspSession exe dir #[] msgs
        checkEq 0 code
        checkEq "" err
        let got ← lspMessages out
        checkEq 6 got.length
        -- documentSymbol: `DocumentSymbol[]` (the host's `symbolJson`), one per
        -- declaration in source order, with the host's kinds (kindFunction 12)
        let syms ← lspAt got 2
        checkEq ["double", "one", "two"] (lspArrayStrs syms ["result"] ["name"])
        checkEq [12, 12, 12] (lspArrayNats syms ["result"] ["kind"])
        -- the range is the command's, so it covers the body (line 2, `  n`)
        checkEq 1 (lspNat syms ["result", "0", "range", "start", "line"])
        checkEq 0 (lspNat syms ["result", "0", "range", "start", "character"])
        checkEq 2 (lspNat syms ["result", "0", "range", "end", "line"])
        -- selectionRange is the name in the declaration
        checkEq 1 (lspNat syms ["result", "0", "selectionRange", "start", "line"])
        checkEq 4 (lspNat syms ["result", "0", "selectionRange", "start", "character"])
        checkEq 10 (lspNat syms ["result", "0", "selectionRange", "end", "character"])
        -- the host omits `children` when a declaration has none
        check ((jpath syms ["result", "0", "children"]).isNone) "no children for a def"
        -- definition: the use of `double` jumps to its declaration's whole range
        let defn ← lspAt got 3
        checkEq uri (lspStr defn ["result", "uri"])
        checkEq 1 (lspNat defn ["result", "range", "start", "line"])
        checkEq 0 (lspNat defn ["result", "range", "start", "character"])
        checkEq 2 (lspNat defn ["result", "range", "end", "line"])
        checkEq 3 (lspNat defn ["result", "range", "end", "character"])
        -- references: the declaration's name and both uses, in source order (the third
        -- line is the declaration, the fourth and fifth the uses at column 17)
        let refs ← lspAt got 4
        checkEq [uri, uri, uri] (lspArrayStrs refs ["result"] ["uri"])
        checkEq [1, 3, 4] (lspArrayNats refs ["result"] ["range", "start", "line"])
        checkEq [4, 17, 17] (lspArrayNats refs ["result"] ["range", "start", "character"]) },
    { name := "lsp: definition crosses an import; a local has no location", run := fun _ =>
        withSelfhostCli fun exe => do
        let doc := "import M\ndef three : Nat := fromM\ndef f (x : Nat) : Nat := x\n"
        let mod := "import Prelude\ndef fromM : Nat := 7\n"
        let dir ← IO.FS.createTempDir
        let path := (dir / "a.wiz").toString
        let uri := s!"file://{path}"
        let docUri := Lean.Json.mkObj [("uri", uri)]
        let msgs :=
          [ lspReq 1 "initialize" (Lean.Json.mkObj [("rootUri", s!"file://{dir}")]),
            lspNote "textDocument/didOpen" (Lean.Json.mkObj [("textDocument", lspTextDoc uri doc 1)]),
            -- `fromM` on line 1 (0-based), column 20
            lspReq 2 "textDocument/definition" (Lean.Json.mkObj [("textDocument", docUri),
              ("position", Lean.Json.mkObj [("line", 1), ("character", 20)])]),
            -- the use of the parameter `x` on line 2, column 25: no binder positions
            lspReq 3 "textDocument/definition" (Lean.Json.mkObj [("textDocument", docUri),
              ("position", Lean.Json.mkObj [("line", 2), ("character", 25)])]),
            -- and its references are the binder and the use, in that command
            lspReq 4 "textDocument/references" (Lean.Json.mkObj [("textDocument", docUri),
              ("position", Lean.Json.mkObj [("line", 2), ("character", 25)])]),
            lspReq 5 "shutdown",
            lspNote "exit" (Lean.Json.mkObj []) ]
        -- (`M.wiz` must be on disk: the loader reads the import; the open document
        -- itself is the buffer's text, as in the shim)
        let (code, out, err) ← selfhostLspSession exe dir #[("M.wiz", mod)] msgs
        checkEq 0 code
        checkEq "" err
        let got ← lspMessages out
        checkEq 6 got.length
        -- the imported module's `Location`: its path as a file URI, the command's range
        -- (`def fromM : Nat := 7` is line 1 there)
        let defn ← lspAt got 2
        checkEq s!"file://{dir}/M.wiz" (lspStr defn ["result", "uri"])
        checkEq 1 (lspNat defn ["result", "range", "start", "line"])
        checkEq 0 (lspNat defn ["result", "range", "start", "character"])
        checkEq 20 (lspNat defn ["result", "range", "end", "character"])
        -- a local name: no definition location (the frontend keeps no binder positions)
        let loc ← lspAt got 3
        check ((jpath loc ["result"]) == some .null) "a local definition is null"
        -- but its references are in-file, within its command
        let refs ← lspAt got 4
        checkEq [2, 2] (lspArrayNats refs ["result"] ["range", "start", "line"])
        checkEq [7, 25] (lspArrayNats refs ["result"] ["range", "start", "character"]) },
    { name := "lsp: no options, and a flag before it is the host's error", run := fun _ =>
        withSelfhostCli fun exe => do
        let (c, _, err) ← cliRun exe #[] #["lsp", "--bogus"]
        checkEq 2 c
        cliCheck err "unknown flag: --bogus" "lsp flag"
        let (c, _, err) ← cliRun exe #[] #["-I", "lib", "lsp"]
        checkEq 2 c
        cliCheck err "unknown flag: -I" "lsp option" }
  ]

builtin_initialize registerGroup selfhostLspGroup

end Tests.Elab
