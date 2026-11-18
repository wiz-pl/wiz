# The infoview protocol

`wiz lsp` speaks the Language Server Protocol, and on top of it a small set of `wiz/*`
requests and notifications that infoviews use: the tactic state and expected type at the
cursor, printed as tagged text whose subterms can be inspected one by one, plus what else
is at the cursor (syntax and its expansion, imports, instances, declarations, messages).
This page describes version 1 of that extension as `Wiz/LSP.lean` implements it, the
transports an infoview can reach the server on, and the clients in the repository: the
Neovim infoview (`editors/nvim/lua/wiz/infoview.lua`), the terminal infoview
(`infoview/Tui.wiz`, with its layout in `lib/Infoview.wiz`) and the web infoview and
playground (`web/infoview.js`, `web/goals.js`, `web/lsp-client.js`, `web/tagged.js`). The
design follows Lean's infoview closely: results are pulled at a position, and interactive
results carry handles that are only valid for one elaboration of the document.

## Conventions

- Messages use the ordinary LSP framing (`Content-Length` headers, JSON-RPC 2.0), except
  on the WebSocket, where each frame carries one message body.
- Positions are LSP positions (`line`, `character`, 0-based), but the server counts
  Unicode characters rather than UTF-16 code units. The two agree except outside the
  Basic Multilingual Plane. Ranges are LSP ranges with an exclusive end.
- Documents must be open. Sync is full text (`textDocumentSync: 1`). Each `didOpen` or
  `didChange` is elaborated (incrementally, through the query engine in `Wiz/Query.lean`)
  before the next message is read, so a request after a change always sees the new text.
- Results are pull-based: a client asks at a position, and `null` means there is nothing
  there; it is not an error.

## Capabilities

The `initialize` result (`capabilities` in `Wiz/LSP.lean`) advertises the extension under
`capabilities.experimental`:

```json
"wizInfoview": {
  "version": 1,
  "methods": ["wiz/plainGoal", "wiz/plainTermGoal", "wiz/interactiveGoals",
              "wiz/interactiveTermGoal", "wiz/subtermInfo", "wiz/interactiveInfo"],
  "notifications": ["wiz/elaborated"]
}
```

The method list is `infoviewMethods`. A client that wants the `wiz/elaborated`
notification asks for it in its own `initialize` params, with
`capabilities.experimental.wizElaborated: true`; without that the server never sends it,
so a plain editor does not have to log notifications it does not understand.

## Tagged text

Interactive results print terms as tagged text, the shape Lean's infoview uses
(`ttJson` in `Wiz/LSP.lean`; the printer is `Term.prettyTagged` in `Wiz/Core/Pretty.lean`):

```
TaggedText = {"text": string}
           | {"append": [TaggedText]}
           | {"tag": [SubtermTag, TaggedText]}
SubtermTag = {"ref": nat, "kind": Kind, "name"?: string}
Kind = "var" | "const" | "sort" | "app" | "lam" | "pi" | "let" | "sigma" | "pair"
     | "proj" | "eq" | "lit" | "data" | "other"
```

Concatenating every `text` in order gives exactly the plain printing of the term, the same
string the plain requests return. Every printed subterm is a tag, and tags nest, so the
innermost tag under the mouse is the subterm to highlight. `name` is present for a
constant (its full name) and for a variable (its printed name), so a client can show it
without a round trip.

## Sessions and refs

Every elaboration of a document gets a new session number (the server's counter, so
sessions are never reused across documents). A ref is an index into the document's
session table, the subterms that interactive results have printed so far, and it is
valid only with the session it came from. Interactive results carry `"session": n`.

Results are memoised per session: asking twice for the same goals returns the same refs,
so a client that polls on every cursor move does not grow the table. When a ref's session
is gone, `wiz/subtermInfo` fails with `ContentModified`, and the client drops its refs and
asks again (or waits for `wiz/elaborated`).

## Requests

All requests except `wiz/subtermInfo` take `TextDocumentPositionParams`.

**`wiz/plainGoal`** returns the tactic state at the cursor as text. Inside a `by` block it
is the state after the innermost tactic whose range contains the cursor (its end
included); with the cursor exactly at the start of a tactic, the state before it, as Lean
shows it; between tactics, the state after the last tactic ending before the cursor;
before the first tactic, the state the block started with (`Query.goalsAt`). Outside every
`by` block the result is `null`. Otherwise it is
`{"rendered": string, "goals": [string], "messages": [string]}`. Each goal is its
hypotheses, one per line (`x : T`, or `x : T := v` for a `let`), then `⊢ type`: the same
text as an "unsolved goals" error. `messages` are the info messages (`trace`,
`trace_state`) of the tactic the state belongs to (`tracesAt`). `rendered` is Markdown:
the goals in a fenced `wiz` block, or `no goals`, followed by the messages.

**`wiz/plainTermGoal`** returns the expected type at the cursor: that of the innermost
checked term or hole there, else the type of the identifier there (`Query.termGoalAt`).
The result is `{"goal": string, "range": Range}` or `null`.

**`wiz/interactiveGoals`** has the same position rule as `wiz/plainGoal` and returns
`null` or:

```
{"goals": [InteractiveGoal], "range": Range, "session": nat, "messages": [string]}
InteractiveGoal = {"hyps": [Hyp], "type": TaggedText, "goalPrefix": "⊢ ",
                   "userName": string | null}
Hyp = {"names": [string], "type": TaggedText, "val": TaggedText | null}
```

`range` is the tactic or `by` block the state belongs to. `names` holds one name today;
the array leaves room for grouping `x y : Nat`. `userName` is the name of a `?x` hole, if
any. An empty `goals` array means no goals are left.

**`wiz/interactiveTermGoal`** has the same position rule as `wiz/plainTermGoal` and returns
`null` or `{"goal": InteractiveGoal, "range": Range, "session": nat}`.

**`wiz/subtermInfo`** takes `{"textDocument": {"uri"}, "session": nat, "ref": nat}` and
describes one tagged subterm:

```
{"text": string, "kind": Kind, "name": string | null,
 "type": TaggedText | null, "definition": Location | null, "session": nat}
```

`type` is inferred by the kernel (`subtermType`); it is `null` when that is not possible,
for example under a `fun` whose binder type is not in the term. Its tags are new refs in
the same session. `definition` is set for a constant: its declaration site, with a
`file://` URI for a library module.

**`wiz/interactiveInfo`** returns `null` or `{"items": [Item], "session": nat}`, where

```
Item = {"kind": "syntax" | "expansion" | "import" | "instance" | "declaration" | "message",
        "range": Range, "title": string, "text": string | null,
        "type": TaggedText | null, "location": Location | null}
```

The items come in this order (`infoItems`): the use of syntax at the cursor and how it
was expanded (a macro rule, with the expansion's text, or the function that elaborated
it), or the `import` there; the instances found at the innermost application, with the
class as tagged `type`; the declarations of the command at the cursor, with their types
(auxiliary declarations the elaborator made for itself are left out, `auxiliaryDecl`);
and the messages whose range contains the cursor, with the severity as `title`.

**`wiz/browserInfoview`** is sent by the editor only, with no params. It makes the server
listen on a WebSocket on `127.0.0.1` (a free port) unless it already does, and answers
`{"port": n, "url": string | null, "message"?: string}`. `url` opens the web infoview in
follow mode; it is `null`, with a `message`, when the server has no web infoview files
(given by `--web DIR`, else `share/wiz/web` in a release or `web/out` in a checkout).
Neovim's `:WizInfoviewBrowser` uses it.

## The `wiz/elaborated` notification

Sent only to clients that asked for it, after the diagnostics of every `didOpen` and
`didChange`: `{"uri": string, "version": int | null, "session": nat}`. An infoview
re-requests the state at its cursor when it arrives.

## Errors

| code     | when |
|----------|------|
| `-32602` | InvalidParams: the document is not open, or a parameter is missing |
| `-32801` | ContentModified: `session` is not the document's current one, or `ref` is not in its table |
| `-32601` | MethodNotFound: a request on the Unix infoview socket that infoviews may not send |

## Code actions

Code actions are standard LSP, but the conventions belong with the protocol. The server
advertises `codeActionProvider` with kinds `quickfix` and `refactor.rewrite` and
`resolveProvider: true`. Diagnostics carry an error `code` (see
[the error codes](../error-codes.md)) and, where a fix exists, a `data` object with what
it needs (`messageData` in `Wiz/Actions.lean`): `{"name", "suggestions"}` for
`unknown-identifier`, `no-such-field`, `unknown-constructor` and `unknown-module`, and
`{"missing"}` for `missing-case`. The actions include "Did you mean", adding a missing
`import`, "Add missing cases", making implicit arguments explicit or inferred, filling a
hole from its expected type, and "Add type ascription".

If the client's `initialize` lists `edit` in
`textDocument.codeAction.resolveSupport.properties`, actions come without their edit and
with `"data": {"uri", "session", "id"}`, and `codeAction/resolve` fills the edit in (or
fails with `-32801` if the document has changed since). Otherwise the edits come inline.

## Transports

**stdio.** The editor's connection, as for any language server.

**`wiz lsp --infoview SOCK`.** Besides stdio, the server listens on a Unix socket, with
the same `Content-Length` framing. Any number of infoviews may connect at any time. The
editor never reports its cursor, so the server infers it from the editor's requests: any
request with `textDocument.uri` and `position` (hover, definition, completion, the `wiz/*`
methods), and `textDocument/codeAction` at the start of its range, since editors ask for
code actions on every cursor move (`cursorOf`). The server advertises
`documentHighlightProvider` for the same reason. Requests about a document that is not
open do not move the cursor.

The server tells every connected infoview where the cursor is with the notification
`wiz/infoview/cursor`, `{"textDocument": {"uri"}, "position", "session"}`: when the
cursor moves, after each elaboration of the cursor's document, and to a new infoview when
it connects (`infoviewCursor`, `cursorNote`). The first document opened before any move
puts the cursor at its start. The same notification is never sent twice in a row, so a
hover, highlight and code action for one move give one notification. On the socket an
infoview may send the `wiz/*` requests and `initialize` (which changes nothing); anything
else gets `-32601` (`handleInfoview`). Sessions, refs and memoised results are shared
with the editor: there is one server state, and messages from all connections are handled
in arrival order (`serveWith`).

**`wiz lsp --ws [ADDR:]PORT`.** A WebSocket (RFC 6455, `Wiz/WebSocket.lean`) on
`127.0.0.1`, or another IPv4 address if one is given; port 0 takes a free one and the
server prints the port on stderr. It can be combined with `--infoview`, and `--no-stdio`
runs the server without an editor on stdin. The handshake requires a `GET` with
`Upgrade: websocket`. A request with an `Origin` header is let in only from a local page:
`null` (a local file), `vscode-webview://`, or `http(s)://` on `localhost`, `127.0.0.1`
or `[::1]` (`localOrigin`); a browser page on any site could otherwise talk to the
server. With web infoview files available, a plain `GET` of one of those files (and only
those, by exact name: `webAssets`) is served over HTTP on the same port.

Each text or binary frame holds one JSON-RPC message; fragments are joined, pings
answered, client frames must be masked, and messages over 256 MiB end the connection. A
WebSocket client is an infoview (it gets `wiz/infoview/cursor`) and may also act as an
editor: it may open, change and close documents and send any request
(`handleWs`). Its `initialize` sets only its own `wizElaborated` preference, and its
`exit` closes only its connection. Documents are shared between all connections, so a
page should open a URI of its own; the web infoview picks `file:///scratch-<random>.wiz`.

## Clients

- **Neovim** (`editors/nvim/lua/wiz/infoview.lua`) asks for `wiz/interactiveGoals`,
  `wiz/interactiveTermGoal` and `wiz/interactiveInfo` as the cursor moves, highlights
  subterms by kind, and asks `wiz/subtermInfo` for the subterm under the cursor in the
  infoview buffer. `:WizInfoviewBrowser` opens the web infoview through
  `wiz/browserInfoview`.
- **The terminal infoview** (`infoview/Tui.wiz`) either connects to `--infoview SOCK` and
  follows `wiz/infoview/cursor`, or starts its own `wiz lsp` with `wizElaborated` set for
  a file and position given on the command line.
- **The web infoview** (`web/infoview.js` on top of `web/playground-lsp.js`,
  `web/lsp-client.js` and `web/goals.js`) talks to `--ws`. It is its own editor by
  default; with `?follow=1` it shows the editor's cursor instead and opens no document of
  its own. The playground mounts the same pane (one implementation for both pages and for
  both transports) and falls back to the plain requests. Its rendering also accepts
  optional `range` fields on hypotheses and tags, which `wiz lsp` does not send today.

## Tests

`Tests/LSP.lean` drives the handlers directly and over real sockets, including the cursor
notification and `wiz/subtermInfo` on an infoview connection; `Tests/Groups/Tactic.lean`
checks that tactic traces reach `wiz/plainGoal`; `Tests/Groups/Infoview.lean` covers the
Wiz side of the clients (`lib/Infoview.wiz`, `lib/Tagged.wiz`). The clients have their
own tests in `web/*_test.mjs` and `infoview/pty_test.py`.
