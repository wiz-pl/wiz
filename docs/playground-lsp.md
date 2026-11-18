# The playground's goals panel: the language-server contract

The playground (`web/playground.html`) evaluates Wiz locally: the self-hosted frontend
and kernel compiled to WebAssembly (stage 11ab). Since the playground-LSP work its Goals
pane is served **in the page by default** (`web/selfhost-lsp-shim.js`, the same Wasm
engine), so the published page has a pane with no server to start; with an endpoint in
the page's URL it can also be a **language client** of an external server, showing that
server's tactic state, expected type and diagnostics. Either way clicking a hypothesis or
a subterm selects its source span in the editor.

The client is transport-agnostic and the page has no new dependency: `web/lsp-client.js`
is JSON-RPC 2.0 over a WebSocket, `web/goals.js` renders the answers, and
`web/playground-lsp.js` connects the two to the textarea. A language server that speaks
the protocol below — the Lean one today, a self-hosted one later — is a drop-in: the page
cannot tell them apart.

## Pointing the page at a server

```sh
web/build-playground.sh web/out          # or use the published site
wiz lsp --ws 8765 --no-stdio             # the server, on 127.0.0.1:8765
python3 -m http.server -d web/out 8000   # the page, over HTTP
# then open http://127.0.0.1:8000/playground.html?lsp=ws://127.0.0.1:8765
```

* With **no `lsp` parameter the in-page server is the default** (`?lsp=selfhost` names it
  explicitly): the pane's diagnostics and `#check`/`#eval` answers come from the same Wasm
  engine, with nothing to start. `?lsp=off` (also `none`, `0`, `false`) turns the pane
  off, and the page stays a local checker.
* `?lsp=ws://host:port` (optionally with a path) uses an external server instead.
  `?lsp=8765` is shorthand for `ws://127.0.0.1:8765`; a value without a scheme gets
  `ws://`.
* In JavaScript the same thing is a config object:
  `startInfoview({editor, panel, config: {url}})` (the page uses this) or
  `new LspClient({url, WebSocketImpl})` for the client alone. The config may also set
  `WebSocketImpl` (default `globalThis.WebSocket`), `requestTimeout` and `languageId`, so
  a self-hosted server that needs its own transport plugs in without touching the page.
* A page served over `https://` cannot open a `ws://` socket (mixed content); use a
  `wss://` endpoint or serve the page over `http://`.
* With no endpoint or a failed connection the pane says "no language server" (and how
  to start one), and the playground keeps working as a local checker. Nothing is logged
  to the console and no promise is left unhandled.

The server can be the repository's Lean server (`wiz lsp --ws`, stage 11o) or any
self-hosted implementation of this document. The server may be given together with
`--infoview SOCK`; the playground does not use the Unix socket.

## Transport

* **RFC 6455 WebSocket.** One JSON-RPC 2.0 message per **text** frame. There is no
  `Content-Length` header and no stdio framing: the WebSocket's frame is the message.
  The client sends UTF-8 text frames and reads text frames; binary frames are ignored.
* **Handshake.** The client sends `initialize` (id 1), waits for the result, sends the
  `initialized` notification, and only then the document notifications and requests.
* **`initialize` params** (what a server may rely on):

  ```json
  {
    "processId": null,
    "clientInfo": {"name": "wiz-playground"},
    "rootUri": null,
    "workspaceFolders": null,
    "capabilities": {
      "general": {"positionEncodings": ["utf-16"]},
      "workspace": {"workspaceFolders": false, "configuration": false},
      "window": {"workDoneProgress": false},
      "textDocument": {
        "synchronization": {"dynamicRegistration": false, "willSave": false, "didSave": false},
        "publishDiagnostics": {"relatedInformation": false, "versionSupport": true},
        "hover": {"contentFormat": ["markdown", "plaintext"]},
        "completion": {"completionItem": {"snippetSupport": false,
                         "documentationFormat": ["markdown", "plaintext"]}}
      },
      "experimental": {"wizElaborated": true, "wizInfoview": true}
    }
  }
  ```

  `experimental.wizElaborated: true` asks for the `wiz/elaborated` notification. The
  panel re-reads the state on it, but `publishDiagnostics` is enough: a server that does
  not implement `wiz/elaborated` needs no change.
* **The result of `initialize`** should carry `capabilities.textDocumentSync: 1`,
  `capabilities.experimental.wizInfoview` (version and methods; the pane labels the
  server with it) and `serverInfo`. A missing `wizInfoview` block is not fatal: the
  client tries the methods anyway.
* **Server → client requests** are not used. The client answers them with
  `MethodNotFound` (`-32601`) rather than hanging.
* **Leaving the page.** On `pagehide` the client sends `textDocument/didClose` and closes
  the socket. A server that ignores `didClose` still sees the socket close.

## Position encoding: UTF-16

Lines are 0-based. A `character` is a **UTF-16 code unit** in its line, as the Language
Server Protocol's default `positionEncoding` (`"utf-16"`) says and as a JavaScript
string index counts. `\n` starts the next line; every other character counts one unit
except characters outside the Basic Multilingual Plane, which count two. Ranges are
end-exclusive.

The client announces `general.positionEncodings: ["utf-16"]` and implements no other
encoding: a server that answers with a `positionEncoding` must answer `"utf-16"`. Byte
offsets are never used, and line endings are whatever the editor holds (`\n` in the
playground; a `\r` before a `\n` counts as one character on the line, as in LSP).

The Lean server counts Unicode scalar values, which agrees with UTF-16 for every
character in the BMP (it is off only for astral characters). A self-hosted server should
count UTF-16 units; if it counts scalar values instead, it must make the same BMP-only
assumption. The playground's positions come from `textarea.selectionStart`, i.e. a
UTF-16 index.

## Documents

* **Full-text synchronisation** (`textDocumentSync: 1`). There are no incremental
  changes and no range requests.
* `textDocument/didOpen` sends
  `{"textDocument": {"uri", "languageId": "wiz", "version": 1, "text"}}`. A page uses one
  document of its own, `file:///playground-<random>.wiz`, so two tabs never overwrite
  each other. The URI need not name a file on disk; the server must accept it.
* `textDocument/didChange` sends the **whole new text**:
  `{"textDocument": {"uri", "version": n}, "contentChanges": [{"text": "…"}]}`.
* `textDocument/didClose` is sent when the page goes away, if the server is still
  connected.
* After every `didOpen`/`didChange` the server sends
  `textDocument/publishDiagnostics` for that document (§ Diagnostics). The client
  treats the notification as "the document is elaborated now" and re-asks for goals.
* Optionally, if the client asked for it, `wiz/elaborated`
  `{"uri", "version", "session"}` after the diagnostics; the panel also re-asks on it.

## Requests

`TextDocumentPositionParams` below means
`{"textDocument": {"uri"}, "position": {"line", "character"}}`.

| method | params | result |
|---|---|---|
| `wiz/interactiveGoals` | `TextDocumentPositionParams` | `null` or `{goals: [InteractiveGoal], range, session, messages?: [string], tree?: TaggedText}` |
| `wiz/interactiveTermGoal` | `TextDocumentPositionParams` | `null` or `{goal: InteractiveGoal, range, session, tree?: TaggedText}` |
| `wiz/plainGoal` | `TextDocumentPositionParams` | `null` or `{goals: [string], rendered: string, messages?: [string]}` |
| `wiz/plainTermGoal` | `TextDocumentPositionParams` | `null` or `{goal: string, range}` |
| `wiz/subtermInfo` | `{"textDocument": {"uri"}, "session", "ref"}` | `null` or `{text, kind, name?, type?: TaggedText, definition?: Location, session}` |
| `textDocument/completion` | `TextDocumentPositionParams` | `{isIncomplete: false, items: [CompletionItem]}` |

The panel asks for the goals and the expected type at the caret. `wiz/interactiveGoals`
and `wiz/interactiveTermGoal` are preferred because they carry tagged text; the plain
methods are the fallback (§ Fallback). `wiz/subtermInfo` is optional: it fills the
"Selected subterm" box when a tagged subterm is clicked, and a `MethodNotFound` answer
is silently ignored. `wiz/interactiveInfo` exists in the protocol but the panel does not
use it yet.

### Shapes

```text
InteractiveGoal = {"hyps": [Hyp], "type": TaggedText, "goalPrefix"?: "⊢ ",
                   "userName"?: string | null, "range"?: Range}
Hyp             = {"names": [string], "type": TaggedText, "val"?: TaggedText | null,
                   "range"?: Range}
Range           = {"start": {"line", "character"}, "end": {"line", "character"}}

TaggedText = {"text": string}
           | {"append": [TaggedText, ...]}
           | {"tag": [SubtermTag, TaggedText]}
SubtermTag = {"ref": nat, "kind": Kind, "name"?: string, "range"?: Range}
Kind       = "var" | "const" | "sort" | "app" | "lam" | "pi" | "let" | "sigma"
           | "pair" | "proj" | "eq" | "lit" | "data" | "other"
```

Flattening a `TaggedText` (concatenate every `text`) is exactly the plain printing of the
term, i.e. the string `wiz/plainGoal` shows. Tags nest; the innermost tag under the mouse
is the subterm. `name` is the global's full name for `const` and the printed local name
for `var`.

`session` is a number that changes on every `didOpen`/`didChange` of the document; `ref`
is an index into that session's table. A `ref` is only valid with the session it came
from: a stale pair is answered with `ContentModified` (`-32801`) and the client simply
re-asks for the state. Sessions and refs are per document; a client must not use one
document's refs on another.

### Optional fields the panel already uses

These are extensions, not requirements. The protocol shape above is what a server has
to produce; each field below upgrades the panel when it is present:

* **`Hyp.range`** — the source span of the hypothesis (its binder or name). Clicking a
  hypothesis selects this span. Without it, a click selects the enclosing goal's range.
* **`SubtermTag.range`** — the source span of that subterm. Clicking a tagged subterm
  selects it. Without it, the click falls back to `closest` enclosing span (the goal's
  range, else nothing).
* **`InteractiveGoal.range`** — the goal's own range, when a state has several goals at
  different places. Without it the result's `range` is used for every goal.
* **`tree`** on a goals/term-goal result — tagged text of the term or syntax at the
  cursor, drawn as an indented tree below the goals. A tagged expected type is already
  drawn as a tree from `InteractiveGoal.type`, so this is for a server that has a syntax
  tree of its own. Without it, the panel draws the goals as text.
* **`wiz/elaborated`** — lets the panel re-read the state without waiting for the next
  `publishDiagnostics`.
* **`messages`** on `wiz/interactiveGoals` — the `trace`/`trace_state` texts at the
  state; shown below the goals.

None of these is needed for compatibility, and a response that omits all of them still
renders (tagged text without a span is still selectable text; a click just has nowhere
to jump).

## Completions

The editor is a plain `<textarea>`, so completions are asked for explicitly: **Ctrl-Space**
(also Cmd-Space) requests them at the caret, and the panel shows the answer as a list above
Goals. ArrowUp/ArrowDown choose, **Tab** or **Enter** inserts the chosen label over the
identifier before the caret, **Escape** closes the list, and typing closes it (the list
would be stale). Clicking an entry inserts it too. There is no automatic popup: a textarea
has no menu, and a popup anchored at the caret would need a hidden mirror element for the
geometry, which this pane does not carry.

The request is `textDocument/completion` with `TextDocumentPositionParams`; the result is
an LSP `CompletionList`, `{"isIncomplete": false, "items": [{"label", "kind"?, "detail"?}]}`.
The client uses `label`, `kind` (an LSP `CompletionItemKind` number) and `detail`; other
fields are ignored. A server may return an empty list for "nothing here"; the panel shows
"no completions".

The in-page server would answer from the module's `wiz_playground_names : String → String`
export (`web/playground-exports.wiz`): it runs the same check as the diagnostics
(`runCommands`) and would return `{"v":1,"names":[{"label","kind"}, …]}` — the frontend's
**global environment**, newest declaration first, each name once, with `kind` an LSP
`CompletionItemKind` (7 a type, 3 a function, 6 otherwise). The shim caches the answer per
document text and filters by the identifier prefix before the caret (letters, digits, `_`,
`'` and `.`; case-insensitive), capped at 200 items.

**In this build the export is not wired** (there is no `export` line and the function is not
in `web/build-playground.sh`'s exported list): the first wasm build of it overflowed the
module's stack while listing the environment (a recursion in the C runtime's list handling
that the function's own control flow does not explain), so it is left out and the shim's
safe fallback answers an **empty list** ("no completions"). The protocol, the shim, the
client and the Ctrl-Space popup are complete and tested against a stub engine; re-enable
the export once the wasm path is fixed. An external server (`?lsp=ws://…`) answers
completions normally, so the popup is useful there today.

Two honest limits even with the export: **local binders are not listed** (a definition's
parameters, a `fun`'s variables, a tactic's hypotheses — the self-hosted frontend exposes
the scope only while it elaborates a command and keeps no info tree), and a module whose
export fails answers an empty list rather than an error.

## Expected types (`wiz/plainTermGoal`)

The in-page server answers `wiz/plainTermGoal` at the caret from the **position index** in
the check answer: `wiz_playground_check` returns

```json
{"v":1,"lines":[…],
 "index":[{"s":16,"e":44,"kind":"term","expected":"Nat"}, …]}
```

where `s`/`e` are **code-point** offsets into the checked text (end-exclusive; the shim
turns them into UTF-16 and subtracts the Prelude prefix), and `expected` is the type the
frontend checked that node against, printed in the node's own context. A lookup is the
**innermost entry of the kind `term` containing the caret** (a caret at an entry's end
counts, as in an editor right after a term); the answer is
`{"goal": "<expected>", "range": {…}}`, or `null` when no recorded node contains it.

How the index is made, and what it really is:

* **Spans are a side table, not syntax.** `Syntax` stays
  `missing | atom | ident | node kind args` — no node grows a range and no match on it
  changes. `selfhost/Parse.wiz` (section "Spans", at the end of the file) has `SpT`, a tree
  of kinds and offsets, and `spansAt`: after a command is parsed, it walks the tree beside
  the lexer's tokens (every token the parser consumed is exactly one leaf, in source order,
  because the parser's descriptors emit what they consume and the position-only ones emit
  nothing), so one left-to-right pass recovers every node's start and stop. A tree the
  parser did not build (a macro expansion, a rewrite, `.missing`) has no span, and
  `spCheck` checks a span against the syntax node's kind at every step, so a stale pairing
  is dropped, never guessed.
* **The recorder is in the elaborator.** `checkT` (the "check this against a type" entry)
  records `(span, "term", expected)` when it is entered with a span; `ES` carries the
  entries (a new `infos` field) and `command` moves them into `Globals.infos` when the
  command succeeds. `stepCommand` turns the side table on only when the playground asks
  (`Globals.watching`), so the compiler and `wiz check` pay one `Bool` check per command
  and no span walk.
* **Where it threads** (for the parity work on `Frontend.wiz`/`Parse.wiz`): the `SpT`
  threading is a last parameter on `checkT`, `inferT`, `inferT1`, `inferT2`, `inferHead`,
  `checkLams`, `checkTuple`, `letT`, `inferLams`, `defT`, `defNames`, `command` and
  `defStep`, and a `List (Option SpT)` on `appArgsT`/`appArgsNamed`/`appExpected` (one span
  per argument). Everything else passes `.none`. `ES` grew one field, `Globals` two
  (`infos`, `watch`) — a constructor arity change, as `selfhost` changes are announced.

**What is not recorded.** A command whose syntax tree the frontend rewrites before
elaborating has no spans there: `def` with pattern-matching defaults or derived equations
(`withDefault`), structural-recursion reordering, `instance` bodies, and the elaborations
inside tactics (a `by` block's *own* expected type is recorded; the terms its tactics
elaborate are not). `#check`/`#eval` have no expected type of their own, so the caret on
their argument answers `null` (their arguments still get entries when an application
checks them). The recorder is the same code the compiler runs; with the index off (any
other caller) it is dead weight of one `none`.

## Tactic states (`wiz/plainGoal`)

The same index carries `kind: "goal"` entries: `{"s","e","kind":"goal","goals":[…]}`,
where `goals` holds the state `tacGoalsShow` prints, one goal per blank-line-separated
block (`"no goals"` for a finished proof). `wiz/plainGoal` at the caret answers the
**innermost `goal` entry containing it** as `{goals, rendered, range}`; `rendered` is a
` ```wiz ` fence around the goals, as the Lean server sends, and `null` means the caret
is outside any recorded state.

Where the entries come from (`selfhost/Frontend.wiz`): `elabBy` records the state
**before each tactic step**, keyed by the step's span (`runTacticSteps` interleaves the
spans from `tacticStepsSp`, which follows `firstTactic` into the syntax so a step's span
is the tactic the interpreter runs). It also records the state at the `by` itself, and a
zero-width entry at the block's **end** with the final state, so a caret at the block's
end reads "no goals" for a finished proof. The state is taken from the interpreter
(`STacState`) at that moment, so it is the same text an error message would print.

Limits: a block that fails to elaborate has no index at all (the command's error drops
its entries); `try`/`first`/`repeat` show the state before the compound step, not the
states inside a branch; and a tactic whose syntax the frontend rewrites has no span, so
its step is skipped. Tactic goals need stage 3's spans (above) and the A13 tactic engine,
both in the tree.

## Fallback ladder

1. Ask `wiz/interactiveGoals` and `wiz/interactiveTermGoal`.
2. If either fails — `MethodNotFound` from an older or self-hosted server, an
   `InvalidParams` because the document is not open yet, any JSON-RPC error — ask the
   plain method instead: `wiz/plainGoal`, `wiz/plainTermGoal`.
3. If both fail, the panel shows the server's error text once; the local Wasm checker is
   unaffected.

`null` means "nothing at this position" (outside a `by` block, say) and is rendered as
"nothing at the cursor"; `goals: []` means "no goals" (the proof is complete). A server
that implements only `wiz/plainGoal`/`wiz/plainTermGoal` works: the panel shows the text,
the expected type as text, and (for `plainTermGoal`) its range is clickable.

## Diagnostics

`textDocument/publishDiagnostics` is
`{"uri", "diagnostics": [{"range", "severity"?, "source"?, "code"?, "message"}]}`;
`severity` is LSP's 1 error, 2 warning, 3 information, 4 hint. The panel lists them with
their severity and position; clicking one selects its range. An empty array clears the
list. Versions are ignored. `code`/`data` (the code-action machinery) are not used by
the playground.

## Errors and timeouts

| code | meaning for the panel |
|---|---|
| `-32601` | Method not implemented: the plain-method fallback (§ Fallback). |
| `-32602` | Invalid params (usually the document is not open): shown, then the fallback. |
| `-32801` | Stale session or ref (`ContentModified`): re-ask for the state; a stale `subtermInfo` is dropped silently. |
| other | Shown as the panel's message. |

Requests time out after 10 seconds (the handshake after 5); a closed socket rejects
pending requests and moves the pane to "the language server disconnected", with a
reconnect button. Any of these is caught: the page never has an unhandled rejection.

## What a self-hosted LSP must implement to be a drop-in

Implement the numbered items; (1)–(6) make the panel fully useful, (7) is optional
polish. Nothing in the playground is specific to the Lean server beyond this list.

1. **Transport.** A WebSocket (RFC 6455) at a URL the page can name, with JSON-RPC 2.0
   text frames and one message per frame. Host and origin: a page on `127.0.0.1` or
   `localhost` sends that as `Origin`, a `file://` page sends none or `null`.
2. **Handshake.** `initialize` answered with `capabilities.textDocumentSync: 1` and
   `capabilities.experimental.wizInfoview = {version, methods}` (and `serverInfo`);
   `initialized` accepted (doing nothing is fine); `shutdown` and `exit` answered or
   ignored without breaking the connection.
3. **Positions.** 0-based lines and UTF-16 code units, per `general.positionEncodings`;
   exclusive range ends.
4. **Documents.** Open/change/close with full text, per-connection (or shared) document
   state, `file:///playground-<random>.wiz` URIs accepted without a file on disk, and
   `publishDiagnostics` after each open/change.
5. **Sessions.** A session number that changes on every open/change, and refs valid with
   it; `-32801` for stale pairs.
6. **Goals.** `wiz/interactiveGoals` (hypotheses with names/types/values, target, tagged
   text, the state's range) and `wiz/interactiveTermGoal` (the expected type), plus the
   `wiz/plainGoal`/`wiz/plainTermGoal` fallbacks so degraded servers still work.
7. **Optional.** `textDocument/completion` (§ Completions), `wiz/subtermInfo`,
   `wiz/elaborated`, `Hyp.range`, `SubtermTag.range`, `InteractiveGoal.range`, `tree`.

The server must not require `stdin` (the page is its own editor), must tolerate any
number of clients (one document each), and may share state between them as the Lean
server does.

## Tests and tools

* `node web/playground_lsp_test.mjs` — the client and panel against a mock server: the
  handshake, `didOpen` with empty diagnostics, goals/term rendering with spans and the
  term tree, a diagnostics update after `didChange`, the plain fallback, close and
  reconnect, the no-server path and no unhandled rejections. It needs no Wiz build.
* `node web/selfhost_lsp_test.mjs` — the in-page server under Node with a stub engine:
  the command splitter, the check JSON and index, the handshake, diagnostics, completions
  (prefix filtering, the empty prefix, a module without the export), the goal and
  expected-type answers from the index (including an astral character), and the page's
  wiring (Ctrl-Space, Tab).
* `node web/playground_test.mjs` — the Wasm module itself: the engine's output, the
  check's `index` (a definition's expected type, a `by` block's state before its step and
  at its end) and the names export.
* `node web/mock_lsp_server.mjs [PORT]` — the same mock as a server, for trying the page
  by hand: it prints `ws://127.0.0.1:PORT` to put in `?lsp=`.
* `web/test.sh` runs the test beside the other web tests; `web/build-site.sh` and
  `web/check-site.sh` ship the new modules and fail if an import does not resolve.
