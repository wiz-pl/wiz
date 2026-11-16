# The Wiz language-server protocol: `wiz/*` extensions and the playground contract

`wiz lsp` is a standard language server (stdio, `Content-Length` framing, JSON-RPC 2.0).
On top of LSP it speaks a small protocol of its own for the **infoviews** (tactic
state, expected type, tagged subterms) and for the playground's goals panel. This page
is that protocol: every `wiz/*` method and notification, the experimental capability
flags, the error codes, and which server implements what.

Sections 0–8 keep the numbers of the old design notes (`wiz-notes/infoview-protocol.md`,
now a pointer here), so a source comment that says "protocol §8" still means §8 below.

**Servers.** Three implementations exist; only the first is on `master`.

| short name | where | status |
|---|---|---|
| **host** | `wiz lsp` (`Wiz/LSP.lean`, `Wiz/WebSocket.lean`, `c/sockets.c`) | the reference; stages 11a–11x |
| **shim** | the playground's in-page server (`web/selfhost-lsp-shim.js`, `?lsp=selfhost`), calling the self-hosted frontend's Wasm exports `wiz_playground_eval` and `wiz_playground_check` (`web/playground-exports.wiz`) | not merged yet (playground-LSP stages 0 and 1) |
| **lsp-core** | the pure LSP core in Wiz (`lib/Lsp/Core.wiz`, driven by `lib/Lsp/Loop.wiz` and `lib/Lsp/Stdio.wiz`; a toy elaborator in `lib/Lsp/Fake.wiz`) | not merged yet (concurrency plan E1–E2) |

**Clients.** Neovim (`editors/nvim/lua/wiz/infoview.lua`, `lsp.lua`), the terminal
infoview (`infoview/Tui.wiz`, `lib/Infoview.wiz`), the web infoview (`web/infoview.html`,
`web/infoview.js`, `web/Web.wiz`), the playground's goals panel (`web/lsp-client.js`,
`web/goals.js`, `web/playground-lsp.js`) and the MCP bridge (`tools/wiz-mcp`, §11).

## Method index

`TDPP` is `TextDocumentPositionParams`,
`{"textDocument": {"uri"}, "position": {"line", "character"}}`. C→S is client to
server, S→C server to client.

| method | dir | kind | params | result | host | shim | lsp-core |
|---|---|---|---|---|---|---|---|
| `wiz/plainGoal` | C→S | request | `TDPP` | `null` or `{goals, rendered, messages}` | yes | yes, other shape (§10) | yes, other shape (§10) |
| `wiz/plainTermGoal` | C→S | request | `TDPP` | `null` or `{goal, range}` | yes | yes | yes |
| `wiz/interactiveGoals` | C→S | request | `TDPP` | `null` or `{goals, range, session, messages}` | yes | `-32601` | `-32601` |
| `wiz/interactiveTermGoal` | C→S | request | `TDPP` | `null` or `{goal, range, session}` | yes | `-32601` | `-32601` |
| `wiz/subtermInfo` | C→S | request | `{textDocument: {uri}, session, ref}` | `{text, kind, name, type, definition, session}` | yes | `-32601` | `-32601` |
| `wiz/interactiveInfo` | C→S | request | `TDPP` | `null` or `{items, session}` | yes | `-32601` | `-32601` |
| `wiz/browserInfoview` | C→S | request | none | `{port, url, message?}` | yes (stdio editor only) | `-32601` | `-32601` |
| `wiz/elaborated` | S→C | notification | `{uri, version, session}` | – | yes, if asked | yes, if asked | yes, if asked |
| `wiz/infoview/cursor` | S→C | notification | `{textDocument: {uri}, position, session}` | – | yes (infoview socket, WebSocket) | no | no |

No server sends a request to the client. The standard LSP methods each server answers
are in §10.

## 0. Conventions

* **Positions** are LSP positions, `{"line", "character"}`, 0-based; ranges are
  end-exclusive. What `character` counts differs between the servers, and between the
  clients:

  | | counts | `positionEncoding` |
  |---|---|---|
  | host | Unicode scalar values (code points) | not advertised; the client's `general.positionEncodings` is ignored |
  | shim | UTF-16 code units (it converts the frontend's code-point offsets) | `"utf-16"` |
  | lsp-core | UTF-16 code units at the protocol edge, code points inside | `"utf-16"` |
  | playground panel (`web/lsp-client.js`) | UTF-16 (`textarea.selectionStart`); sends `general.positionEncodings: ["utf-16"]` | – |
  | web infoview (`web/infoview.js`) | code points (`Array.from`) | – |
  | MCP bridge | passes the caller's numbers through, documented as code points | – |

  The two counts agree inside the Basic Multilingual Plane; they differ only on a line
  with a character outside it (an emoji, a mathematical alphanumeric). See §10.
* **Documents** must be open (`textDocument/didOpen`). Sync is full text
  (`textDocumentSync: 1`); a `didChange`'s last content change is the whole text.
  The host re-elaborates (incrementally) before it reads the next message, so a request
  after a change always sees the new text; lsp-core instead queues a request until
  elaboration has passed its position (§10).
* **Results are pull-based.** A client asks at a position; `null` means "nothing here"
  (not an error).

## 1. Capabilities

**Server → client.** The host's `initialize` result carries, under
`capabilities.experimental`:

```json
"experimental": {
  "wizInfoview": {
    "version": 1,
    "methods": ["wiz/plainGoal", "wiz/plainTermGoal", "wiz/interactiveGoals",
                "wiz/interactiveTermGoal", "wiz/subtermInfo", "wiz/interactiveInfo"],
    "notifications": ["wiz/elaborated"]
  }
}
```

`wiz/browserInfoview` is not listed (it is editor-only). The other servers differ:

| server | `version` | `methods` | `notifications` | `serverInfo` |
|---|---|---|---|---|
| host | `1` (a number) | the six above | `["wiz/elaborated"]` | `{"name": "wiz"}` |
| shim | `1` | `["wiz/plainGoal", "wiz/plainTermGoal"]` | absent (it sends `wiz/elaborated` anyway) | `{"name": "wiz-selfhost", "version": "prototype"}` |
| lsp-core | `"0.1"` (a string) | `["wiz/plainGoal", "wiz/plainTermGoal"]` | absent (it sends `wiz/elaborated` anyway) | `{"name": "wiz-lsp-core", "version": "0.1"}` |

The playground panel reads `version` as `version || 0` and labels the server with it;
a missing block is not fatal (the client tries the methods anyway).

**Client → server.** A client that wants the `wiz/elaborated` notification sets
`"capabilities": {"experimental": {"wizElaborated": true}}` in its `initialize` params.
Without it no server sends it (a plain editor would only log it). The host keeps the
setting per connection: the stdio editor's and each WebSocket page's are separate.
Neovim, the terminal infoview, the web infoview and the playground panel set it; the
MCP bridge does not. The playground panel also sends `experimental.wizInfoview: true`,
which no server reads.

## 2. Tagged text

Interactive results print terms as **tagged text** (the shape Lean's infoview uses):

```text
TaggedText = {"text": string}
           | {"append": [TaggedText, ...]}
           | {"tag": [SubtermTag, TaggedText]}
SubtermTag = {"ref": nat, "kind": Kind, "name"?: string}
Kind       = "var" | "const" | "sort" | "app" | "lam" | "pi" | "let" | "sigma" | "pair"
           | "proj" | "eq" | "lit" | "data" | "other"
```

* Flattening (concatenating every `text` in order) gives exactly the plain printing of
  the term (`#check` syntax, the same string `wiz/plainGoal` shows).
* Every printed subterm is a `tag`; tags nest (an application's tag contains its head's
  and its arguments' tags). The innermost tag under the mouse is the subterm to
  highlight; its `ref` is the handle for `wiz/subtermInfo`.
* `name` is present for `"const"` (the global's full name, e.g. `"Nat.add"`) and `"var"`
  (the local's printed name), so a client can show it without a round trip.

Example: `Nat → Nat` as a goal type:

```json
{"tag": [{"ref": 4, "kind": "pi"},
  {"append": [{"tag": [{"ref": 5, "kind": "const", "name": "Nat"}, {"text": "Nat"}]},
              {"text": " → "},
              {"tag": [{"ref": 6, "kind": "const", "name": "Nat"}, {"text": "Nat"}]}]}]}
```

Only the host produces tagged text.

## 3. Sessions and refs

* Each open document has a **session**: a number that changes whenever the document
  changes (`didOpen`, `didChange`) and that `didClose` ends. Every interactive result
  carries `"session": n`. All three servers number sessions and send the number in
  `wiz/elaborated`; only the host has refs.
* A `ref` is an index into that document's session table. It is valid only together
  with the session it came from: `wiz/subtermInfo` takes both and fails with
  `ContentModified` (`-32801`) when the session is gone. Clients then drop their
  refs and re-request goals (or wait for `wiz/elaborated`).
* Asking twice for the same goals in one session returns the same refs (results are
  memoised per session), so a client polling on cursor moves doesn't grow the table.
* Refs are never shared between documents.

## 4. Requests

All take `TDPP` except `wiz/subtermInfo` and `wiz/browserInfoview`. A request for a
document that is not open fails with `-32602` on every server.

### `wiz/plainGoal`: the tactic state at the cursor, as text

Which state (host): inside a `by` block, the goals **after** the innermost tactic whose
range contains the cursor (its end included, so the cursor right after `intro x` shows
the state after it). Exception (11w): with the cursor exactly at the start of a tactic
(in front of its first character), the goals **before** it (of the outermost tactic
starting there), as Lean shows them. Between tactics, the goals after the last tactic
that ends before the cursor; before the first tactic (on `by` itself), the goals the
block started with. Outside every `by` block: `null`.

Result: `{"rendered": string, "goals": [string], "messages": [string]}` or `null`.
Each goal is its hypotheses, one per line (`x : T`, or `x : T := v` for a `let`), then
`⊢ type`, the same text as the "unsolved goals" error. `rendered` is Markdown: the goals
in a ` ```wiz ` block separated by blank lines, or `no goals`. `messages` are the texts
of the info messages (`trace`, `trace_state`) of the tactic the state belongs to, in
order; `rendered` has them after the goals, separated by blank lines.

```json
→ {"jsonrpc":"2.0","id":7,"method":"wiz/plainGoal",
   "params":{"textDocument":{"uri":"file:///t.wiz"},"position":{"line":2,"character":9}}}
← {"jsonrpc":"2.0","id":7,"result":{
     "goals":["A : Type\nx : A\n⊢ A"],
     "rendered":"```wiz\nA : Type\nx : A\n⊢ A\n```", "messages":[]}}
```

The shim and lsp-core answer with a different shape (§10).

### `wiz/plainTermGoal`: the expected type at the cursor

The innermost elaborated term at the cursor with a known expected type: a hole (`_`,
`?x`), an argument, a body, a `by` block, an identifier (its type, when nothing
encloses it more tightly), a binder or pattern variable (its type in its context, 11q).
Result: `{"goal": string, "range": Range}` or `null`; `goal` is formatted like one goal
of `wiz/plainGoal`, `range` is the term's range.

```json
← {"jsonrpc":"2.0","id":8,"result":{"goal":"n : Nat\n⊢ Nat",
     "range":{"start":{"line":1,"character":27},"end":{"line":1,"character":28}}}}
```

### `wiz/interactiveGoals`: the tactic state, as tagged text

Host only. Same position rule as `wiz/plainGoal`. Result `null` or:

```text
{"goals": [InteractiveGoal], "range": Range, "session": nat, "messages": [string]}
InteractiveGoal = {"hyps": [Hyp], "type": TaggedText, "goalPrefix": "⊢ ",
                   "userName": string | null}
Hyp = {"names": [string], "type": TaggedText, "val": TaggedText | null}
```

`range` is the tactic (or `by` block) the state belongs to. `names` has one name per
hypothesis today (the array leaves room for grouping `x y : Nat`). `userName` is the
name of a `?x` hole when there is one, else `null`. Empty `goals` = no goals left.
`messages` is as in `wiz/plainGoal`.

### `wiz/interactiveTermGoal`: the expected type, as tagged text

Host only. Same position rule as `wiz/plainTermGoal`. Result `null` or
`{"goal": InteractiveGoal, "range": Range, "session": nat}`.

### `wiz/subtermInfo`: what a tagged subterm is

Host only. Params: `{"textDocument": {"uri"}, "session": nat, "ref": nat}`. Result:

```text
{"text": string,                 the subterm, printed
 "kind": Kind, "name": string | null,
 "type": TaggedText | null,      its type (new refs, same session); null when the
                                 kernel can't infer it (e.g. under a lambda)
 "definition": Location | null,  for a "const": where it was declared (a library
                                 module gives a file:// URI of its source)
 "session": nat}
```

Errors: `-32602` when `session` or `ref` is missing, `-32801` when `session` is not the
document's current one or `ref` is not in its table.

### `wiz/interactiveInfo`: everything else at the cursor (11q)

Host only. Result `null` (nothing) or `{"items": [Item], "session": nat}`:

```text
Item = {"kind": "syntax" | "expansion" | "import" | "instance" | "declaration" | "message",
        "range": Range, "title": string, "text": string | null,
        "type": TaggedText | null, "location": Location | null}
```

In order: the use of syntax at the cursor (`syntax`: title `syntax term.twice (this
file, line 2)`, text the first line of the declaring command, location it; `expansion`:
title `expanded by macro rule (Prelude, line 212)` / `elaborated by tactic Tactic.intro`,
text the expansion (one step) or null, location the rule or function), or the `import`
(text the module's path, location its file); the instances found at the innermost
application (`text` the instance term, `type` its class type, tagged); the declarations
of the command at the cursor (`title` the name, `type` its type, tagged; elaborator
auxiliaries left out); the messages whose range contains the cursor (`title` the
severity, `text` the message). Tags in `type` are refs of the session, as in §3.

Related (11q): `textDocument/declaration` is advertised. On a use of syntax, definition
goes to what expanded it (macro rule, procedural macro, tactic) and declaration to its
`syntax`; either may be a list. A binder or pattern variable has a hover (`x : T`).

### `wiz/browserInfoview`: open the web infoview (11w)

Host only, and only from the stdio editor (from a WebSocket page it gets the catch-all
`null`; on the infoview socket, `-32601`). No params. The server listens on a WebSocket
on 127.0.0.1 (a free port) unless it already does (`--ws`), and answers
`{"port": n, "url": string | null, "message"?: string}`. `url`
(`http://127.0.0.1:n/infoview.html?port=n&follow=1`) is null when the server has no web
infoview files (`--web DIR`, `share/wiz/web`, `web/out`); `message` says why. The port
serves those files over HTTP (§8.2) and the page follows the editor's cursor. If it
cannot listen: `-32603` (`cannot listen: …`). Neovim's `:WizInfoviewBrowser` uses it.

## 5. Notifications

### `wiz/elaborated` (server → client)

`{"uri": string, "version": int | null, "session": nat}`, sent only to clients that
asked (§1), right after the `textDocument/publishDiagnostics` it belongs to. Infoviews
re-request the state at their cursor when it arrives. When it is sent differs (§10):
the host after every `didOpen`/`didChange`; the shim after each finished check, dropping
one a newer text overtook; lsp-core once a document is completely elaborated (after its
200 ms debounce and every command), so several quick changes give one.

### `wiz/infoview/cursor` (server → infoview)

Host only; see §8.1.

## 6. Errors

JSON-RPC error objects (`{"code", "message"}`) in place of `result`:

| code | name | host | shim | lsp-core |
|---|---|---|---|---|
| `-32700` | ParseError | – (a malformed body is read as `null` and ignored) | the text is not JSON | the body is not JSON |
| `-32600` | InvalidRequest | – | – | `method` is not a string |
| `-32601` | MethodNotFound | only on the infoview socket (§8.1); on stdio and the WebSocket an unknown request is answered `null` | any request but `initialize`, `shutdown`, `wiz/plainGoal`, `wiz/plainTermGoal`, `textDocument/hover` | the same five are the only requests answered |
| `-32602` | InvalidParams | document not open; `session`/`ref` missing (`subtermInfo`); `codeAction/resolve` without `session`/`id`; a rename to a non-name, or with nothing to rename | document not open | document not open |
| `-32603` | InternalError | `wiz/browserInfoview` cannot listen | an exception in a handler | – |
| `-32002` | ServerNotInitialized | – (requests before `initialize` are answered) | – | any request but `initialize` before it |
| `-32800` | RequestCancelled | – (`$/cancelRequest` is ignored: requests are answered synchronously) | – | a queued request named by `$/cancelRequest` |
| `-32801` | ContentModified | stale `session`/`ref` (`subtermInfo`); stale or unknown code action (`codeAction/resolve`) | – | a queued request whose document changed or was closed |
| `-32803` | RequestFailed | rename or prepare-rename of a name declared in the toolchain's library | – | – |

## 7. Code actions (host; standard LSP)

* `initialize` advertises `"codeActionProvider": {"codeActionKinds": ["quickfix",
  "refactor.rewrite"], "resolveProvider": true}`.
* Every diagnostic whose message has an error code carries `code` (the stable codes of
  `Wiz/Core/ErrorCode.lean`, listed in [error-codes.md](error-codes.md)) and `data`.
  `data` is `{}` except:

  | `code` | `data` |
  |---|---|
  | `unknown-identifier` | `{"name": string, "suggestions": [string]}` (edit distance ≤ 2, globals and locals in scope) |
  | `no-such-field`, `unknown-constructor`, `unknown-module` | `{"name": string, "suggestions": [string]}` |
  | `missing-case` | `{"missing": [string]}` (constructors without a case) |

* `textDocument/codeAction` returns `CodeAction[]`: *Did you mean 'x'?* (quickfix, one
  per suggestion), *Add `import M`* (quickfix), *Add missing cases* (quickfix), the
  explicit-`@` and drop-the-`@` fixes for an argument count off by the implicits, hole
  fillings from the expected type, and *Add type ascription* (refactor.rewrite, on the
  name of a `def` without a type). If the client's `initialize` said
  `textDocument.codeAction.resolveSupport.properties` contains `"edit"`, the actions come
  without `edit` and with `"data": {"uri", "session", "id"}`; `codeAction/resolve` fills
  in `edit` (a `WorkspaceEdit` with `changes`), or fails with `-32801` if the document
  changed since. Otherwise the edits come inline.
* The shim's diagnostics have `source: "wiz-selfhost"` and a code (`parse-error`) only
  on a parse error; lsp-core's have `source: "wiz"` and no code. Neither offers code
  actions.

## 8. Transports

### 8.1 The infoview socket: `wiz lsp --infoview SOCK` (host, 11l)

Besides stdio, the host listens on the Unix socket `SOCK` (unlinking a stale socket file
first, never another kind of file; removing it on `exit`). Any number of infoviews may
connect, at any time (the terminal infoview retries every 0.5 s); the socket uses the
same `Content-Length` framing as stdio, and an infoview sends no `initialize` (if it
does, it gets the capabilities and nothing changes).

* **The cursor.** The editor never reports its cursor, so the server infers it from
  the editor's stdio messages: every *request* with `params.textDocument.uri` and
  `params.position` (`hover`, `documentHighlight`, `definition`, `completion`, the
  `wiz/*` methods, …), and `textDocument/codeAction` at `params.range.start`
  (editors ask for code actions on every cursor move). The server advertises
  `documentHighlightProvider` so that editors send it on every move. Requests for a
  document that is not open don't move it.
* **`wiz/infoview/cursor`** `{"textDocument": {"uri"}, "position", "session"}` goes
  to every connected infoview (a) when the cursor moves, (b) after each elaboration
  (`didOpen`/`didChange`) of the cursor's document, with the new session, and (c) to
  an infoview right after it connects, if there is a cursor. The first document
  opened before any cursor move puts the cursor at its start (0:0). The same
  notification (uri, position, session) is not sent twice in a row. `session` is `null`
  when the document is not open.
* **Requests on the socket**: the six methods of `wizInfoview.methods` (§1), with ids
  the infoview chooses; the answers go back on the same connection. Sessions, refs and
  memoised results are shared with the editor (one server state; messages from all
  connections are handled in arrival order). `initialize` and `shutdown` are answered;
  any other request gets `-32601`; notifications are ignored.
* A connection whose write fails is dropped; `exit` (or the end of stdin) closes every
  connection and the socket.

### 8.2 The WebSocket: `wiz lsp --ws [ADDR:]PORT` (host, 11o)

A WebSocket (RFC 6455) on `127.0.0.1:PORT` (another IPv4 address only if `ADDR` is
given; port 0 takes a free one, and the server prints `wiz lsp: WebSocket on port N` on
stderr). It may be given together with `--infoview SOCK`; `--no-stdio` runs the server
without an editor on stdin (it then runs until killed).

* **Handshake.** `GET` with `Upgrade: websocket` and `Sec-WebSocket-Key` (anything
  else: `405`/`426`). **Origin check**: a request with an `Origin` header is let in only
  if it is `null` (a local file), `vscode-webview://…`, or `http(s)://` on `localhost`,
  `127.0.0.1` or `[::1]` (any port); others get `403`. No `Origin` (non-browser
  clients) is let in. No subprotocol, no extensions. With web infoview files available
  (§4, `wiz/browserInfoview`), a plain `GET` serves them.
* **Framing.** One JSON-RPC message per **text** frame (no `Content-Length`); binary
  frames are accepted too (UTF-8 JSON). Fragmented messages are reassembled; pings are
  answered; a close frame is answered and ends the connection. Client frames must be
  masked. Messages over 256 MiB close the connection.
* **Semantics.** A WebSocket connection is an infoview of 8.1 (it gets
  `wiz/infoview/cursor`), **and may also act as an editor**: it may open, change and
  close documents and send any request the stdio editor may; answers and
  `publishDiagnostics` for its documents go back on its connection. Its requests with a
  position move the shared cursor. Its `initialize` is answered with the capabilities
  and records only its own `wizElaborated`; its `exit` closes its connection only.
  Documents and sessions are shared with the stdio editor and every other page (one
  server state), so a page should pick a URI of its own (say
  `file:///scratch-<random>.wiz`).

### 8.3 The other servers' transports

* **shim**: no socket. `selfhostSocketClass` is a stand-in with the WebSocket surface
  `LspClient` uses; `SelfhostServer.handle(text) → [message]` takes one JSON-RPC message
  (or a batch array) and returns the replies, the shape of a planned Wasm export
  `wiz_lsp_handle : String → String`. Documents are per connection (per page).
* **lsp-core**: pure (`Lsp.feed`, `Lsp.work` and `Lsp.wake` return unframed JSON texts);
  the driver frames them. `lib/Lsp/Stdio.wiz` is a stdio driver (`Content-Length`,
  `Fd.poll`), which for now runs only when compiled by the Lean toolchain (`wiz build`).

## 9. The playground's goals panel (a client of this protocol)

The playground (`web/playground.html`) evaluates Wiz locally: the self-hosted frontend
and kernel compiled to WebAssembly (stage 11ab). With an endpoint in the page's URL it is
also a **language client**: the Goals pane shows the server's tactic state, expected
type and diagnostics, and clicking a hypothesis or a subterm selects its source span.
`web/lsp-client.js` is JSON-RPC 2.0 over a WebSocket, `web/goals.js` renders the answers,
and `web/playground-lsp.js` connects the two to the textarea.

### Pointing the page at a server

```sh
web/build-playground.sh web/out          # or use the published site
wiz lsp --ws 8765 --no-stdio             # the server, on 127.0.0.1:8765
python3 -m http.server -d web/out 8000   # the page, over HTTP
# then open http://127.0.0.1:8000/playground.html?lsp=ws://127.0.0.1:8765
```

* `?lsp=ws://host:port` (optionally with a path) is the endpoint. `?lsp=8765` is
  shorthand for `ws://127.0.0.1:8765`; a value without a scheme gets `ws://`; `?lsp=off`
  or no parameter means no server, and the pane says so. Once the shim is merged,
  `?lsp=selfhost` selects the in-page server instead.
* In JavaScript: `startInfoview({editor, panel, config: {url}})` or
  `new LspClient({url, WebSocketImpl})`. The config may also set `WebSocketImpl`
  (default `globalThis.WebSocket`), `requestTimeout` and `languageId`; the shim plugs in
  through `WebSocketImpl`.
* A page served over `https://` cannot open a `ws://` socket (mixed content); use
  `wss://` or serve the page over `http://`.
* With no endpoint or a failed connection the pane says "no language server", and the
  playground keeps working as a local checker. Nothing is logged to the console and no
  promise is left unhandled.

### What the client sends

* **Handshake.** `initialize` (id 1), wait for the result, `initialized`, then the
  document notifications and requests. The `initialize` params:

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
        "hover": {"contentFormat": ["markdown", "plaintext"]}
      },
      "experimental": {"wizElaborated": true, "wizInfoview": true}
    }
  }
  ```

* **Documents.** One document per page, `file:///playground-<random>.wiz` (the server
  must accept a URI with no file on disk): `didOpen` with `languageId: "wiz"` and
  `version: 1`; `didChange` with the whole new text; `didClose` on `pagehide`, then the
  socket closes.
* **Server → client requests** are answered `-32601` rather than left hanging.
* **Timeouts.** Requests time out after 10 s (the handshake after 5 s). The client's own
  error codes are `-32098` (not connected, or timed out) and `-32097` (closed). A closed
  socket rejects pending requests and the pane offers a reconnect button.

### Fallback ladder

1. Ask `wiz/interactiveGoals` and `wiz/interactiveTermGoal`.
2. If either fails (`-32601` from the shim or lsp-core, `-32602` because the document is
   not open yet, any JSON-RPC error), ask `wiz/plainGoal` / `wiz/plainTermGoal` instead.
3. If both fail, the pane shows the server's error text once; the local Wasm checker is
   unaffected.

`null` is rendered "nothing at the cursor"; `goals: []` is "no goals". `-32801` makes
the pane re-ask; a stale `subtermInfo` is dropped silently. `wiz/subtermInfo` is used
when a tagged subterm is clicked (`-32601` is ignored). `wiz/interactiveInfo` is wrapped
in `LspClient` but the pane does not use it yet. `textDocument/publishDiagnostics` or
`wiz/elaborated` makes the pane re-read the state; it also re-reads 400 ms after a
change, in case neither comes.

### Optional fields the pane uses

No server sends these yet, except where noted; each upgrades the pane when present, and
a response without them still renders.

* `Hyp.range`, `SubtermTag.range`, `InteractiveGoal.range`: source spans; a click
  selects them (without them, the result's `range`).
* `tree` on a goals or term-goal result: tagged text drawn as an indented tree.
* `range` on a `wiz/plainGoal` result (the shim sends it): the span of the state.

## 10. Server parity

A self-hosted `wiz lsp` is a drop-in when it answers what the host answers, in the same
shapes. Where the servers stand:

| point | host | shim | lsp-core | gap |
|---|---|---|---|---|
| `wiz/plainGoal` shape | `{goals, rendered, messages}`; `rendered` a ` ```wiz ` fence or `no goals` | `{goals, rendered, range}`; fence or `no goals`; no `messages` | `{goals, rendered}`; `rendered` the goals joined by blank lines, no fence, `""` for none; no `messages` | shim and lsp-core lack `messages`; lsp-core's `rendered` is not Markdown; the shim adds `range` |
| goal and expected-type content | from the info tree | from the check's `index`, which `wiz_playground_check` does not emit yet, so always `null` today | from the `Lsp.Info` entries an elaborator returns (only `Fake.wiz` so far) | no self-hosted elaborator answers goals yet |
| interactive methods (`interactiveGoals`, `interactiveTermGoal`, `subtermInfo`, `interactiveInfo`) | yes | `-32601` | `-32601` | no tagged text and no refs outside the host |
| `wiz/browserInfoview`, `--infoview`, `--ws`, `wiz/infoview/cursor` | yes | no (in-page) | no (stdio driver only) | |
| `wizInfoview.version` | `1` | `1` | `"0.1"` (a string) | lsp-core's is a string |
| `wizInfoview.notifications` | `["wiz/elaborated"]` | absent | absent | both send `wiz/elaborated` without listing it |
| `wiz/elaborated` timing | every `didOpen`/`didChange` | every finished check; superseded ones dropped | once per complete elaboration (debounced) | clients must not count notifications |
| positions | code points; no `positionEncoding` | UTF-16; `positionEncoding: "utf-16"` | UTF-16; `positionEncoding: "utf-16"` | the host is off by one per astral character before the cursor on its line |
| `publishDiagnostics` | `{uri, diagnostics}`; `code`/`data`, `source: "wiz"` | `{uri, version, diagnostics}`; `source: "wiz-selfhost"`, code only `parse-error` | `{uri, version, diagnostics}`; `source: "wiz"`, no code | no error codes or quick fixes outside the host; the host omits `version` |
| `didClose` | drops the document | drops it | drops it and publishes empty diagnostics | |
| unknown request | `null` (stdio, WebSocket); `-32601` (infoview socket) | `-32601` | `-32601` | the host answers `null` where LSP expects `-32601` |
| request before `initialize` | answered | answered | `-32002` | |
| request ahead of elaboration | n/a (synchronous) | answered from the last check | queued until elaboration passes it; `-32801` on a change, `-32800` on `$/cancelRequest` | |
| standard methods | hover, definition, declaration, references, documentHighlight, rename and prepareRename, completion, signatureHelp, inlayHint, semanticTokens/full, documentSymbol, workspace/symbol, foldingRange, codeAction and codeAction/resolve | `textDocument/hover` (always `null`; `hoverProvider: false`) | `textDocument/hover` (plaintext, from `hover` infos) | everything but hover |

For the playground pane the shim and lsp-core already suffice at the plain level of §9:
the pane falls back to the plain methods on `-32601`.

## 11. Other clients: the MCP bridge (`tools/wiz-mcp`)

`tools/wiz-mcp` (an MCP server for coding agents) runs one `wiz lsp` per worktree and
maps its tools onto the protocol. This describes it as of the batch-D pull requests
(#425–#437, not merged yet), which run the daemon on stdio with no listening socket and
add the navigation tools. Its `initialize` sends `capabilities: {}` (so no
`wiz/elaborated` and no position encoding), with `rootUri` and `workspaceFolders` set to
the workspace; positions are passed through and documented as code points.

| MCP tool | LSP method |
|---|---|
| `goals` | `wiz/interactiveGoals`, or `wiz/plainGoal` with `plain: true` |
| `term_goal` | `wiz/plainTermGoal` |
| `diagnostics`, and `check` with `source: "lsp"` | `didOpen` → `publishDiagnostics` → `didClose` |
| `hover`, `signature_help`, `definition` (`declaration: true` asks `textDocument/declaration`), `references`, `document_symbols`, `workspace_symbols`, `completion`, `inlay_hints`, `code_actions`, `rename` | the `textDocument/*` or `workspace/symbol` method of the same name |

An LSP error reply becomes the tool error `lsp_refused` (the daemon is kept); a
timeout, a closed connection or another failure becomes `timeout`, `lsp_closed` or
`lsp_error` and restarts the daemon. Its other tool errors (`path_denied`,
`invalid_args`, `not_found`, `io_error`, `wiz_not_found`, `lsp_startup`) are the
bridge's own. On the MCP side it answers `-32602` (a bad tool call), `-32601` (an
unknown method), `-32002` (an unreadable resource) and `-32603`. Details:
`tools/wiz-mcp/README.md`.

## 12. Not yet on master

Stages 11ae–11ag, on a branch not merged yet, change this protocol:

* **Widgets (11af):** `wiz/interactiveGoals` gains `widgets: [{title, html, range,
  goals}]` (sanitised static HTML that the client must still sandbox).
* **Position encodings (11ag):** the host negotiates `general.positionEncodings`
  (UTF-16 by default, UTF-8 on request) and converts at every LSP edge, which closes the
  host's position gap of §10.
* **User-defined extensions (11ae):** language-server hooks declared in Wiz (hover,
  completion items, infoview widgets).

§1, §4 and §10 change when they land.

## Tests and tools

* `lsp-server` test group (`Tests/LSP.lean`): the host in-process, with an editor on a
  socket pair, an infoview on the socket and WebSocket clients.
* `node web/playground_lsp_test.mjs`: the client and pane against a mock server
  (handshake, diagnostics, goals with spans and the tree, the plain fallback, reconnect,
  no unhandled rejections); no Wiz build needed. `node web/mock_lsp_server.mjs [PORT]`
  runs the same mock as a server for trying the page by hand.
* `infoview/test.sh` (the terminal infoview against `infoview/stub_server.py`),
  `editors/nvim/tests/run.lua` and `tools/wiz-mcp/run-tests.sh`.
* Not on master yet: `web/selfhost_lsp_test.mjs` (the shim) and the `lsp-core` test
  group (`Tests/Groups/LspCore.lean`).
* `web/test.sh` runs the web tests; `web/build-site.sh` and `web/check-site.sh` ship
  the modules and fail if an import does not resolve.
