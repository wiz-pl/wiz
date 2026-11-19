# The playground's goals panel: the language-server contract

The playground (`web/playground.html`) evaluates Wiz locally: the self-hosted frontend
and kernel compiled to WebAssembly (stage 11ab). Since the playground-LSP work its Goals
pane is served **in the page by default** (`web/selfhost-lsp-shim.js`, the same Wasm
engine), so the published page has a pane with no server to start; with an endpoint in
the page's URL it can also be a **language client** of an external server, showing that
server's tactic state, expected type and diagnostics. With an external server that
implements the interactive methods, clicking a hypothesis or a tagged subterm selects its
source span in the editor; the in-page server answers the plain goal methods and the
editor's completion, hover and definition from its own check index (the interactive
tagged methods remain an external server's, so a tagged tree is only clickable there).

The editor is a plain `<textarea>` with no dependency: `web/editor-model.js` has the pure
rules (UTF-16 positions, the ranges diagnostics underline, completion filtering and
insertion), `web/squiggles.js` and `web/completions.js` draw them, and
`web/playground-lsp.js` connects them to the textarea. The page itself is one app in the
repo's own Loom framework (`lib/Web/Loom.wiz`, § The page's runtime); the goals pane is
an island in it.

The client is transport-agnostic and the page has no new dependency: `web/lsp-client.js`
is JSON-RPC 2.0 over a WebSocket, `web/goals.js` renders the answers, and
`web/playground-lsp.js` connects the two to the textarea. A language server that speaks
the protocol below — the Lean one today, a self-hosted one later — is a drop-in: the page
cannot tell them apart.

`web/playground-lsp.js` is also the standalone browser infoview (`web/infoview.html`,
served by `wiz lsp --ws` and `web/bridge.sh`): the same pane, the same rendering and the
same requests, so the two pages and both transports have one implementation. The page's
half (`web/infoview.js`) only maps its URL to an endpoint and passes `follow`/`info`/
`onRender` to the pane; `web/infoview_page_test.mjs` covers that mapping. In follow mode
(`?follow=1`, what `wiz/browserInfoview` opens) the pane opens no document of its own —
the server shares the editor's — and moves with the `wiz/infoview/cursor` notification.

## Pointing the page at a server

```sh
web/build-playground.sh web/out          # or use the published site
wiz lsp --ws 8765 --no-stdio             # the server, on 127.0.0.1:8765; prints its token T
python3 -m http.server -d web/out 8000   # the page, over HTTP
# then open http://127.0.0.1:8000/playground.html?lsp=ws://127.0.0.1:8765&token=T
```

* **The token.** `wiz lsp --ws` lets in only a client that presents its token (`?token=T`
  in the socket's URL, or `Authorization: Bearer T`), and answers anything else with
  `401` before the WebSocket opens. Without it, any program on the machine could connect,
  open documents and have them elaborated with your privileges (the `Origin` check
  stops other web sites, not local programs). The token is fresh for every launch and
  printed on stderr; `--token-file FILE` reads it from FILE instead (and creates FILE,
  mode 0600, with a fresh one if it does not exist). The page's `?token=` goes into the
  socket's URL and is never shown in the pane. `--ws-insecure` turns the check off
  (loopback only, with a warning).
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
  The pane takes three more options the standalone page uses: `follow` (view another
  editor's document, moved by `goTo`), `info` (an element for the selected subterm, the
  page's `#info`) and `onRender(view)` (a hook after every render, for the page's status
  line).
* A page served over `https://` cannot open a `ws://` socket (mixed content); use a
  `wss://` endpoint or serve the page over `http://`.
* With no endpoint or a failed connection the pane says "no language server" (and how
  to start one), and the playground keeps working as a local checker. Nothing is logged
  to the console and no promise is left unhandled.
* `?squiggles=off` disables the underlines under the editor's diagnostics, and
  `?completions=off` the completion popup (§ The editor). There is no `?ui` switch: the
  runtime page is the playground.

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

`web/editor-model.js` has both conversions (`positionFromOffset`,
`codePointPositionFromOffset`, `utf16OffsetFromCodePoints`) and the Node tests pin that
they differ only for characters outside the BMP. The page sends the UTF-16 one; the
code-point helpers exist for a server that counts `String.codes`.

## The editor

Assuming a text field is enough is what makes the playground feel unlike an editor. Three
pieces fix that without replacing the textarea, and none of them adds a dependency:

* **Squiggles.** `web/squiggles.js` draws every diagnostic range as a wavy underline
  under the offending source. It puts the editor in a positioned wrapper and places a
  **mirror** over it: an absolutely positioned `div` with the textarea's font, padding and
  wrapping, holding the same text with a `<span class="squiggle sev-ERROR">` around each
  range, transparent text and a coloured `text-decoration`. The layer never takes a
  pointer event (`pointer-events: none`), so typing, selection and scrolling stay the
  textarea's, and its colour and caret are untouched. This is the fragile part of
  decorating a plain textarea — the mirror only lines up if the font metrics and the wrap
  points match — which is why `web/squiggles.js` copies `getComputedStyle(editor)` on
  every layout and why `web/playground.css` repeats the same declarations on both sides.
  If they ever drift, only the underline's position is wrong. `?squiggles=off` (also
  0/none/false) turns the layer off; the Goals pane's list still selects the spans.

  The ranges are computed by `squiggleSegments` (`web/editor-model.js`), which repairs
  what real servers send: a range with **no end** underlines the token at its start (one
  character on whitespace, nothing past the end of the text); an **empty** range does the
  same; a range past the text is clamped; a **multi-line** range becomes one span per
  line (no newline inside a span); two **overlapping** ranges merge, keeping the stricter
  severity and both messages. Diagnostics without a `range.start` are not drawn.

* **Caret → server.** The caret is sent on selection changes — `keyup`, `click`,
  `mouseup`, `select`, `focus` — debounced by 120 ms (`positionDebounce`), as
  `TextDocumentPositionParams` of `wiz/interactiveGoals` and `wiz/interactiveTermGoal`,
  with the plain-method fallback of § Fallback. An edit sends `didChange` at once and
  only this refresh is debounced, so the position asked about is in text the server has;
  an answer whose document version changed while it was in flight is discarded. A move
  to the position the pane already answered is skipped; `publishDiagnostics`/
  `wiz/elaborated` always re-ask, because the session changed. A selection sends its
  **start** (where the caret is), as an editor's caret query does.

* **Completions.** `web/completions.js` asks `textDocument/completion` on Ctrl/⌘-Space
  and, debounced by 120 ms, after typing an identifier character (not inside a `--`
  comment). The popup is a `div role="listbox"` fixed at the caret (monospace columns:
  `character × charWidth`), filtered by the identifier prefix at the caret and capped at
  100 items. Up/Down/PageUp/PageDown move (wrapping), Enter and Tab accept, Escape and a
  blur close it; while it is open those keys belong to the popup, so no newline or tab is
  inserted underneath. Accepting replaces the range of the item's `textEdit` when the
  server sent one and its end is still the caret (an answer for an older caret is
  re-anchored on the current identifier prefix), else the identifier prefix before the
  caret with `insertText` (or the `label`); snippet placeholders are stripped if a server
  sends them despite `snippetSupport: false`. The edit is a normal `input` event, so the
  existing `didChange` path re-sends the document. A `MethodNotFound`, an empty list or
  an error just leaves the popup closed; `?completions=off` disables it.

The page's `initialize` advertises `textDocument.completion` (with
`contextSupport: true` and `snippetSupport: false`), so a server can rely on the client
asking.

## The page's runtime

The whole page is one Loom app. `web/playground.js` (the entry point) points at the body
and calls `mount(body, { module, transport })` from `web/framework/mount.js`, which loads
`wiz-playground-ui.mjs` (built by `web/build-playground-ui.sh` from
`web/playground-ui.wiz`), mounts its SSR and delegates DOM events. The app
(`Web.Playground.pageApp`) renders the header and its examples menu, the editor, the
goals container, the output pane and the footer; its state is `Page`.

```sh
web/build-playground.sh web/out         # the engine (wiz-playground.mjs)
web/build-playground-ui.sh web/out      # the page (wiz-playground-ui.mjs)
# open http://127.0.0.1:8000/playground.html
```

The UI is its own Wasm instance, so a trap or restart in the engine does not touch it.
The page keeps the effects (the engine, the goals client, the editor overlays) and
reports their results through the module's `wiz_loom_*` entry points. There is no second
page: if the runtime module cannot start (it was not built, the network refused it, or
its ABI is not the Loom one), the mount point says so in plain text with the reason and
the build documentation — it does not fall back to a hand-written UI.
`web/playground_ui_test.mjs` mounts the real module under Node with the driver and the
DOM double and checks the panes, the examples menu, the status pair, the count, the value
classes and the entry points.

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

## The editor: hover and go-to-definition

The pane is not the only server feature the page shows. Two standard requests make the
textarea an editor:

* **Hover.** When the caret rests after a mouse click or selection, or after an
  arrow/Home/End/Page key, the page sends `textDocument/hover` at that position and
  draws the answer in a small card under the caret. The server's Markdown is rendered as
  text lines (a fenced block stays code, `---` is a rule) and never as HTML, so a server
  cannot inject markup. The card is not shown while typing; keyboard navigation shows it
  again when the caret stops. `?hover=off` (also `0`, `none`, `false`) turns the feature
  off, and the `startInfoview({..., hover: false})` option does the same in JavaScript.
* **Go to definition.** F12 or Ctrl/⌘-click sends `textDocument/definition` at the
  caret. A location in the document the page has open (`file:///playground-….wiz`)
  moves the caret and selects the name; a definition in a library file has no page here,
  so the card shows `Prelude.wiz:7:1` and the editor is left alone. Escape, typing,
  scrolling or leaving the field close the card.

Both requests use `TextDocumentPositionParams` and the same UTF-16 positions as the rest
of the client. A server that answers `null` (nothing at that character) or
`MethodNotFound` is silent: the page keeps working as before. The in-page server
(`web/selfhost-lsp-shim.js`) answers both from the check's declaration index (see
§ Completions): a declaration of the module being checked gives its signature as
Markdown and its own span as the `Location`; a Prelude global or a local binder is
`null`, because the index covers this module only. With `?lsp=ws://…` both come from the
Lean server, which also knows the library and local scopes. `web/hover.js` is the page
half (the content rules and the card), and `web/hover_test.mjs` tests it without a
browser.

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
| `textDocument/hover` | `TextDocumentPositionParams` | `null` or `Hover` (Markdown contents and a range) |
| `textDocument/definition` | `TextDocumentPositionParams` | `null`, a `Location`, or a `Location[]` |
| `textDocument/completion` | `TextDocumentPositionParams` + optional `context: {triggerKind, triggerCharacter?}` | `null`, `[CompletionItem]` or `{isIncomplete, items: [CompletionItem]}` |

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

The editor is a plain `<textarea>`, so the popup is an overlay (`web/completions.js`):
**Ctrl-Space** asks at the caret, and typing an identifier character asks after a short
debounce. ArrowUp/ArrowDown/PageUp/PageDown move, **Enter** or **Tab** accepts, **Escape**
closes, and a non-identifier key or a blur closes it. The item's `textEdit` is applied
when its range ends at the caret; a stale answer is re-anchored on the identifier prefix
at the caret instead (so typing more while an answer is in flight cannot duplicate the
suffix). `insertText`/`label` and snippet placeholders are the fallbacks. The accepted
item goes through the normal `input` event, so the document is re-sent by the existing
`didChange` path. `?completions=off` disables the popup.

The request is `textDocument/completion` with `TextDocumentPositionParams` and an optional
`context: {triggerKind, triggerCharacter?}`; the result is an LSP `CompletionList`,
`{"isIncomplete": false, "items": [{"label", "kind"?, "detail"?, "textEdit"?}]}`, or a bare
array. The client uses `label`, `kind`, `detail`, `sortText`/`filterText` and the edit.

The in-page server answers from the check answer's `index`: the module's declarations are
recorded there as `{"s", "e", "kind": "decl", "name", "detail", "ckind"}` — the source
name, the type as the kernel prints it, an LSP `CompletionItemKind` (7 a type, 3 a
function, 6 otherwise), and the declaration's code-point span. The shim filters the
declarations by the identifier before the caret (letters, digits, `_`, `'` and `.`;
case-insensitive, capped at 200), and gives each item a `textEdit` over that prefix. It is
the **same check** that produces the diagnostics, cached on the document, so a name the
check accepted is one the list has, and there is no second Wasm call.

The index covers **the module being checked**, not the embedded Prelude: a Prelude global
is in scope but not listed, and a local binder (a definition's parameter, a `fun`'s
variable, a tactic's hypothesis) is not listed either — the frontend exposes the scope
only while it elaborates a command and keeps no info tree. An external server
(`?lsp=ws://…`) answers those too.

## Expected types (`wiz/plainTermGoal`)

The in-page server answers `wiz/plainTermGoal` at the caret from the **position index** in
the check answer: `wiz_playground_check` returns

```json
{"v":1,"lines":[…],
 "index":[{"s":16,"e":44,"kind":"term","expected":"Nat"},
          {"s":16,"e":21,"kind":"decl","name":"twice","detail":"(n : Nat) → Nat","ckind":3}, …]}
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
  records `(span, "term", expected)` when it is entered with a span; the entries go into
  the same `ES.snaps`/`LspEntry` list the external `wiz lsp` uses, and `command` moves
  them into the document's entries when the command succeeds. `stepCommand` turns the
  side table on only when the playground asks (`Globals.watching`), so the compiler and
  `wiz check` pay one `Bool` check per command and no span walk.
* **Where it threads** (for the parity work on `Frontend.wiz`/`Parse.wiz`): the `SpT`
  threading is a last parameter on `checkT`, `inferT`, `inferT1`, `inferT2`, `inferHead`,
  `checkLams`, `checkTuple`, `letT`, `inferLams`, `defT`, `defNames`, `command` and
  `defStep`, and a `List (Option SpT)` on `appArgsT`/`appArgsNamed`/`appExpected` (one span
  per argument). Everything else passes `.none`. `LspEntry` grew a `decl` constructor and
  `LspCtx` a `watch` flag; `Globals`/`ES` keep their existing shapes — a constructor
  arity change, as `selfhost` changes are announced.

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
where `goals` holds the state's goals as `tacGoalsList` prints them (`[]` for a finished
proof). `wiz/plainGoal` at the caret answers the
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
their severity and position and underlines the same ranges in the editor (§ The editor);
clicking one selects its range. An empty array clears the list and the underlines. A
diagnostic's `range` may have no `end`, an empty `end`, or span lines: the editor
underlines the token at its start for the first two and one span per line for the last.
A publish whose `version` is older than the one already stored for the URI is ignored;
a server that sends no version keeps last-arrival order. `code`/`data` (the code-action
machinery) are not used by the playground.

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
   `localhost` sends that as `Origin`, a `file://` page sends none or `null`. The page
   adds the `?token=` of its own URL to the socket's URL; a server should refuse an
   upgrade without its token, as `wiz lsp --ws` does.
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
7. **Optional.** `wiz/subtermInfo`, `wiz/elaborated`, `Hyp.range`, `SubtermTag.range`,
   `InteractiveGoal.range`, `tree`, and the editor's `textDocument/hover` /
   `textDocument/definition` (without them the card stays closed and F12 does nothing).
8. **Optional, for the editor.** `textDocument/completion` (an array or a
   `CompletionList`; `textEdit`/`insertText`/`filterText`/`sortText` honoured), so
   Ctrl-Space and typing have something to show. Without it the popup stays closed.

The server must not require `stdin` (the page is its own editor), must tolerate any
number of clients (one document each), and may share state between them as the Lean
server does.

## Tests and tools

* `node web/playground_lsp_test.mjs` — the client, the panel and the page under Node
  against `web/mock_lsp_server.mjs` and the in-page shim: the handshake, `didOpen` with
  empty diagnostics, goals/term rendering with spans and the term tree, a diagnostics
  update after `didChange`, the plain fallback, close and reconnect, `textDocument/completion`
  (items, `textEdit`, the caret's position params), the squiggles and the popup's wiring,
  hover and go-to-definition, follow mode (no document of its own), the separate `info`
  box, the page hook, the token (a client without it, or with a wrong one, is refused; the
  page's `?token=` gets in), the no-server path and no unhandled rejections. It needs no
  Wiz build.
* `node web/selfhost_lsp_test.mjs` — the in-page server under Node with a stub engine:
  the command splitter, the check JSON and index, the handshake, diagnostics, completion
  (`CompletionItem` with `textEdit`), hover (Markdown) and definition (`Location`) from
  the index, the goal and expected-type answers (including an astral character), and the
  page's wiring.
* `node web/editor_test.mjs` — the editor's pure rules: UTF-16 versus code-point
  positions (including an astral character), squiggle ranges (no end, empty, multi-line,
  overlapping, past the text), and completion lists (shapes, filtering, ordering, the
  keyboard's index arithmetic, `textEdit`/`insertText`/snippet insertion).
* `node web/editor_dom_test.mjs` — the same two overlays against
  `web/framework/minidom.mjs`: what the squiggle layer draws, the popup's keys, the
  insertion and its `input` event, closing on blur/Escape, and the URL flags.
* `node web/playground_test.mjs` — the Wasm module itself: the engine's output, the
  check's `index` (a definition's expected type and declaration span, a `by` block's
  state before its step and at its end).
* `node web/infoview_page_test.mjs` — the standalone page's URL rule (`?port=`, `?lsp=`)
  and its status text; the pane it mounts is the test above.
* `node web/playground_ui_test.mjs` — the page: its module mounted under Node with the
  framework's driver and DOM double, then the page's `wiz_loom_*` calls and the examples
  menu.
* `node web/mock_lsp_server.mjs [PORT]` — the same mock as a server, for trying the page
  by hand: it prints `ws://127.0.0.1:PORT` to put in `?lsp=`.
* `node web/hover_test.mjs` — the hover card and go-to-definition: the three LSP content
  shapes and the line rules (fences, a rule, the length limit), `Location` / `LocationLink`
  / array definitions, and the widget's keys (Escape, F12, Ctrl-click, typing) against
  `web/framework/minidom.mjs`. No browser, no server, no Wiz build.
* `web/test.sh` runs the tests beside the other web tests; `web/build-site.sh` and
  `web/check-site.sh` ship the new modules (and `framework/`) and fail if an import does
  not resolve.
