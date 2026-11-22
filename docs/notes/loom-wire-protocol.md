# The Loom wire protocol and the shared runtime model

Status: P0 slice, 2026-11-22, off `integration/train10` (`0c85dd743`). This note is the
**single canonical description** for this cluster: the host / Loom runtime / SSR shell /
designer-builder split, the data path of each surface, the wire's role, the one
validation table and the adopt-and-listen contract. Other notes and code comments point
here instead of restating them; a second prose copy is a bug.

The P0 slice in this branch is deliberately narrow and is implemented in five places:

| piece | canonical file | what it is |
|---|---|---|
| shared runtime model, data paths, validation table, adopt contract | this note | prose, one copy |
| envelope, P0 channels, payload schemas, monitor, caps | `web/framework/wire.js` | browser-free ES module, no DOM |
| adopt/replace decision, SSR hash, error element | `web/framework/adopt.js` | browser-free ES module, no DOM |
| DOM seam and mount ABI | `web/framework/runtime.js`, `driver.js`, `mount.js` | unchanged semantics; `driver.start` asks `adopt.js` before touching a node |
| browser-free contract tests | `web/framework/wire_test.mjs` | encode/decode, monitor transitions, adopt/replace, validation table |

`docs/notes/loom-thin-js.md` keeps the JavaScript line budget and the staged page
inventory; its ownership table is its own JavaScript view, and this note wins when they
differ. `lib/Web/Loom.wiz` states only what the renderer guarantees.

P0 does **not** migrate a page onto the wire. The playground still uses `step`/`effect`/
`requests`/`js_patch`; the legacy adapter is the compatibility mode. P0 establishes the
canonical model, the envelope and its monitor, and the adopt contract that runs *before*
the first message. The page migration, the Wiz-side `Wire.check` generated from the same
table, events/patches, widgets and the LSP bridge are P1/P2 (§9).

---

## 1. Who owns what

| owner | is | owns | never owns |
|---|---|---|---|
| **host** | the page's JavaScript (`web/framework/{mount,driver,runtime,wire,adopt}.js`, `web/*.js`) | sockets, the LSP transport, DOM measurement/geometry, focus trap, clipboard, storage, fetch, applying patches, the widget sanitiser | app state, what a hover means, a tokeniser, class-name choice |
| **Loom runtime** | the Wiz→Wasm module (`lib/Web/*.wiz`, `web/*-ui.wiz`) | app state, effects-as-requests, view trees, patches, the drawer's open/closed state, span assembly, hover-card assembly from a typed payload, the wire monitor | raw DOM APIs, the network, a second lexer, HTML received from the host |
| **SSR shell** | `Wiz.Doc.Site`/`Build` output, plus any server-rendered island HTML | static HTML, static CSS links, static highlighted code, `data-wiz-*` attributes, the SSR hash | interactivity, patches, state |
| **designer/builder** | `wiz doc` / `grail doc`, `wiz wire gen`, `wiz run web/gen-styles.wiz` | docs pages, the language registry, rendered spans, generated sheets, the wire adapter and monitor table, class-registry cross-checks | running package code, a browser, the runtime |

Three clarifications remove the apparent contradictions:

* **"SSR shell" is not "Loom SSR".** `wiz doc` is Lean and writes strings; it does not
  call `Loom.toHtml`. In this cluster "Loom SSR" means `Loom.render`'s HTML used by an
  island or a test, or the HTML the `data-wiz-ssr` verifier hashes — not the docs-page
  generator.
* The designer/builder produces **data and static bytes**. It never ships a tokeniser, a
  stylesheet injector, a hover provider, or package code into the page.
* **A second Wiz→Wasm driver exists**: `web/tagged.js`'s `stepper` drives the docs
  signature hover with `wiz_doc_init`/`wiz_doc_step`. It has the same ownership split
  (host events/patch, runtime state) but a different ABI and no `Loom.Patch`; it is not an
  island. The shared model applies to it; the wire's typed channels apply to Loom
  runtimes, not to this legacy stepper.

## 2. The data path

| surface | produced | carried as | validated | applied / patched |
|---|---|---|---|---|
| **static fenced snippet** | `Wiz.Doc.Highlight` during `wiz doc` | HTML: `<pre><code class="language-X">` + `<span class="hl-*">` | build: registry, class enum, escaping, size caps | static DOM; **no patch, no JS** |
| **live fenced snippet** | Lean LSP answer (`wizHighlight` inside `wiz.hover/1` / an update); the P2 in-page index supplies hover facts only, never spans | `payload` field, then runtime span data | wire: outer schema + caps; runtime: span range/class check | Loom `span` nodes inside the hover/goals view; normal patch |
| **hover** | `Query.innermost` in the Lean server (or the P2 selfhost index) | `wiz.hover/1` | payload decoder (fields/caps), then card renderer (URIs, caps) | `Hover`/`Goals`/`DocLive` view; normal patch |
| **drawer panel** | runtime state (`Drawer.open`) over the same `Goals`/`Hover` models | a `setAttr "class"` and/or insert patch | semantic layer (`Loom.App.event`); host pre-validates the patch | patch applier; focus/trap is host work |
| **style** | `Style`/`Class` values in Wiz at build time | one generated `.css` asset + class strings in HTML/patches | generator: keys, collisions, public names, contrast; sanitiser: payload classes | `<link>` for the sheet; one `setAttr "class"` per state change; never inline |
| **widget markup** | a package or the kernel | `wiz.widget/1` | wire: schema/field caps; host: element/attribute/class allowlist | host `createElement`/`createTextNode` from the checked tree |

The rule in one line: **the runtime decides, the builder bakes, the host applies, the SSR
shell is inert.** No layer does another layer's job on the same data.

### What travels on the wire, and what does not

* **Class names are not a message type.** Static HTML carries them. A runtime patch
  carries them only as a `class` *attribute value* inside `wiz.patch/1` (one sorted
  `setAttr` from `Class.attr`). The monitor treats that value as opaque; the class policy
  is a **render** boundary for third-party markup, not an envelope rule.
* **`wizHighlight`** is nested in `wiz.hover/1` (`result.data.wizHighlight`) or in a
  doc-live update item. The wire checks its outer schema and caps; the runtime checks
  that spans are non-negative, monotone, inside the source's UTF-16 length, and use one
  of the eight `hl-*` names. A failure renders the block plain, never a channel error.
* **`wiz.hover/1`** is a typed payload on `lsp.results` or `doclive.updates`; the payload
  decoder checks fields/caps, the card renderer checks `definition.uri` and the field
  caps, and the card is built with `Loom.text` (never `Loom.raw`).
* **`wiz.widget/1`** keeps today's rule: the wire checks the bundle's shape/caps, then
  `sanitizeWidgetMarkup` rebuilds the body from a checked tree. A refused payload is a
  card, not a connection error.
* **Patches** are `wiz.patch/1 {base, rev, ops}` on `editor.patches`; the host
  pre-validates paths/ops and applies atomically. `resync` is `replace ""` — it is not
  hydration and must not be presented as adoption.

## 3. The wire's role

The wire is the typed message path between a Loom runtime (Wiz, usually Wasm) and its
JavaScript host. It is **not** a renderer and **not** a hydration mechanism:

* `mount` chooses adopt or replace before the first wire message (§4), from the SSR hash.
* `resync` is a typed call (`{method:"resync"}`) whose answer is a normal patch whose
  first op is `{op:"replace", path:"", html:<current SSR>}`. It is replace-by-patch, not
  adoption.
* The runtime decides state and trees; the host applies patches and forwards browser
  capabilities. The wire only makes those messages typed, ordered, correlated and
  bounded.

### 3.1 Envelope

One JSON object per message. P0 uses the exact version `wiz.loom.wire/1`; a mismatch is
refused, never downgraded.

```json
{"v":"wiz.loom.wire/1","ch":"editor.calls","op":"call","src":"host","seq":1,
 "id":7,"payload":{"schema":"wiz.call/1","method":"run","args":{}}}
```

| field | required | meaning |
|---|---|---|
| `v` | yes | exact `"wiz.loom.wire/1"` |
| `ch` | yes | a registered channel (`editor.calls`, `editor.replies`, `wire` in P0) |
| `op` | yes | the label (`call`, `reply`, `request`, `result`, `cancel`, `ack`, `fail`, `close`, `error`) |
| `src` | yes | `"host"` or `"runtime"`; the sender |
| `seq` | yes | per-`(ch, src)`, starts at 1, strictly +1 |
| `id` | calls/effects | `uint32`; unique per connection and initiator; a reply carries the same id and the opposite `src` |
| `base`/`rev` | patches/updates | the applied revision and the runtime revision (P1) |
| `ack` | optional | the highest peer `seq` processed (advisory backpressure) |
| `payload` | yes except `close` | an object with a `schema` |

`encode` sorts object keys and drops `undefined` fields, so two encoders that build the
same message produce the same bytes. `decode` rejects `__proto__`/`constructor`/
`prototype`, enforces the UTF-8, frame, depth, array and key caps, and requires the
exact version and the channel's payload schema.

### 3.2 P0 channels

Four unidirectional channels per bundle in the full design; P0 registers the two
call/reply directions plus the diagnostic escape hatch:

| channel | sender | ops | payloads |
|---|---|---|---|
| `editor.calls` | host → runtime | `call`, `result`, `cancel`, `ack`, `close` | `wiz.call/1`, `wiz.effect-result/1`, `wiz.cancel/1`, `wiz.ack/1`, — |
| `editor.replies` | runtime → host | `reply`, `request`, `fail`, `close` | `wiz.call-reply/1`, `wiz.effect/1`, `wiz.failure/1`, — |
| `wire` | runtime → host | `error` | `wiz.wire.error/1` |

The call/reply interaction:

1. host `call {id, method, args}` on `editor.calls`;
2. the runtime either `reply {id, ok, value}` on `editor.replies`, or `request {id,
   kind, payload}` (an effect the host must perform), or `fail {id, code}`;
3. on a `request`, the host performs the effect, sends `result {id, ok, value}` on
   `editor.calls`, and the runtime replies.

`id` is the correlation; `call` returns before the reply, so several calls can be in
flight. The runtime processes them in arrival order; replies may be out of order. P0's
methods are `run`, `save`, `share`, `sync`, `edit`, `load`, `panel`, `ack`, `resync`;
`mode:"query"` is the asynchronous form of the read-only `ask` fast path. `editor.events`
and `editor.patches` are **not registered** in P0, so a message that names them is a
`Wire.Error.channel` (an unregistered capability), not a silent fallback.

The `wire` channel is deliberately not session-typed: it is the one diagnostic escape
hatch, so the monitor can report after closing the offending channel and a diagnostic is
never lost because the channel it describes is gone.

### 3.3 Caps

`CAPS` in `web/framework/wire.js` is the single numeric table: frame 1 MiB, envelope
64 KiB, generic payload 256 KiB, editor text 1 MiB, patch HTML 256 KiB/op, 4096 ops per
batch, path depth 64 / length 256, widget markup 2,000,000 chars, 10,000 spans /
256 KiB, JSON depth 32 / array 4096, 64 in-flight calls, outbox 256 messages / 1 MiB,
monitor recursion depth 64. A violation is `Wire.Error.cap`, never a truncation.

## 4. The adopt-and-listen SSR contract

P0 implements the contract in `web/framework/adopt.js` and calls it from
`driver.start` **before** the first render and before any wire message.

1. The container carries `data-wiz-island` (presence, not value), `data-wiz-props`
   (JSON), and `data-wiz-ssr` (the server's hash of its HTML **including class
   attributes**).
2. The client computes its own SSR of the initial state (`wiz_loom_html`) and a hash of
   it. A runtime may instead export `wiz_loom_ssr_hash`, a read-only entry point that
   returns the same string; the host asks for the runtime's hash first and only hashes
   `html` when the export is absent.
3. **Equal → adopt**: attach the delegated listeners and the state, touch no node. A
   `<textarea>` keeps its value/selection, `<details>` its open state, the page its
   scroll.
4. **Unequal, missing or absent hash → replace** through `runtime.js` (today's `mount`),
   with one warning naming the reason. Never a half-adopt.
5. **Module/ABI failure → leave the static DOM** and write one plain-text reason into a
   `data-wiz-error` element; no retry, no second UI. The exception still propagates, so
   a page that wants its own message can catch it.

The hash is **FNV-1a 32-bit over the UTF-8 bytes of the HTML string**, lower-case eight
hex digits (`hashHtml` in `adopt.js`). The input is the renderer's HTML for the
container's children (the same string `wiz_loom_html` returns), not the container
wrapper; hashing the exact string includes class attributes, attribute values and text,
so the server and the client agree only on the same render. It is an identity/build
check, not a security hash: a collision costs one replace, never a partial adopt. The
exact hash inputs remain the open item recorded in the design notes; until the owner
picks, this is the working contract.

`data-wiz-props` is parsed and passed to the runtime through the transport
(`globalThis.wizTransport.props` and the module factory's `transport`), not through a
second init ABI. A malformed props attribute is a warning and no props; the static DOM
still stands.

There is **no general hydration diff**. The wire does not reconcile nodes, does not
adopt a subtree after the first message, and `resync` is not adoption.

## 5. Who validates what

One table, so the notes and the code cannot disagree. "Failure" is the whole-payload
refusal unless stated. Rows 3–7 and 10 are the wire's six points; `VALIDATION` in
`web/framework/wire.js` exports the same six rows, and `wire_test.mjs` checks both copies
agree.

| # | boundary | implementation | validates | deliberately does not validate | failure |
|---|---|---|---|---|---|
| 1 | language registry (build) | `Wiz/Doc/Highlight.lean` + `--languages` | JSON schema, names/aliases, duplicate/reserved `wiz`, class subset, spec shape | token semantics | run fails with file/entry, no partial page |
| 2 | static highlighter (build) | `Wiz.Doc.Highlight` | escaping, the fixed class enum, per-block/page caps, unknown language | DOM, runtime | block plain escaped |
| 3 | generated adapter (host) | `web/framework/wire.js#encode` | method/channel/op legal, payload fields/caps, fresh id | markup, class tokens | throws before send |
| 4 | transport (host) | `web/framework/wire.js#decode` | frame size, UTF-8, `JSON.parse` reviver, depth/array caps, exact `v` | business fields | connection refused/closed |
| 5 | envelope monitor (runtime) | `web/framework/wire.js#Monitor` (P0 reference); `lib/Web/Wire.wiz` in P1 | `ch/op/src/seq/id/base/rev`, transition legality, caps, open ids | HTML, URLs, class tokens | channel closed, no state, no patch |
| 6 | payload decoder (runtime) | `web/framework/wire.js#validatePayload` | field type/length/range, schema known, unknown fields ignored | what the text means | `Wire.Error.payload`, no state |
| 7 | semantic layer (runtime) | `Page.step`/`Page.effect`, `DocLive.effect` | handler index/event (`Loom.App.event`), draft/format, result shape | DOM | no state change |
| 8 | span validator (runtime) | `Hover`/`Goals` span assembler | exact `wizHighlight` schema, monotone in-range spans, **eight** `hl-*` only, caps | token correctness | whole block plain text |
| 9 | widget sanitiser (host) | `web/widgets.js` | elements, attributes, `javascript:`/`data:`/`url(...)`; class tokens `wz-*` + eight `hl-*` (P3) | appearance, whether a rule exists | whole payload refused, card |
| 10 | patch pre-validator/applier (host) | `web/framework/runtime.js#applyPatches` | every path resolves, op known, index/depth in range | class semantics | discard batch + one `resync` |
| 11 | CSS generator (build) | `web/gen-styles.wiz` + `build-css.sh --check` | key prefix, collision gate, public names exactly the eight / `wz-` shape, no `url(`/`@import`/`style=`, contrast | page composition | build fails |
| 12 | hover card renderer (runtime) | `Hover`/`Goals` | `safeUrl` for `definition.uri`, field caps, `Loom.text` only | prose | field dropped / no card |
| 13 | adopt verifier (host) | `web/framework/adopt.js#decideAdopt` | SSR hash equality, island/ABI presence | content | replace, or static DOM + text reason |

The split that matters: **the monitor validates shape, the renderer validates markup.**
A class token is never an envelope error; a bad span or payload class is a display
refusal.

Rows 1–2, 8–9 and 11–12 belong to the highlighting and CSS notes; their paths are the
design's, not this slice's. P0 implements rows 3–6 (the reference monitor and decoder)
and 13 (the adopt verifier); row 7 is the existing semantic handler and row 10 the
existing patch applier.

## 6. Failure and ordering

* Per `(ch, src)`, messages are totally ordered by `seq`; across channels there is no
  total order. A patch and a reply are tied by `rev`/`id`, not by a global sequence.
* A protocol violation changes no state, emits no patch, and closes **that channel**,
  not the page. A version/hash mismatch closes the **connection** before anything is
  rendered. A timeout retires one call and leaves the page usable.
* `reply` for an id never opened is `Wire.Error.id`; `result` for an id the runtime did
  not request is `Wire.Error.id`; a late reply after `cancel` is ignored once (the race
  is legitimate), not fatal.
* `close` ends one channel; a message after it is `Wire.Error.state`. `wire.error` is
  accepted after a channel closes because it is the diagnostic channel.
* Never a hang: the runtime step is pure and total, no `Chan.recv`, no MVar, no blocking
  FFI. Every host wait has a deadline; every deadline has a `cancel`.
* Never a partial DOM: every patch batch is pre-validated against the current tree
  before any mutation; a failure discards the batch and requests one `resync`.

## 7. Where the code and the model point

| question | answer |
|---|---|
| what is canonical for the model? | this note |
| what is canonical for the envelope/monitor? | `web/framework/wire.js` (P0 reference; generated Wiz monitor in P1) |
| what is canonical for adopt? | `web/framework/adopt.js` |
| what is canonical for the patch paths? | `web/framework/runtime.js` (unchanged) |
| what is canonical for the mount/step ABI? | `web/framework/mount.js` + `driver.js` (unchanged) |
| what is canonical for the renderer/SSR? | `lib/Web/Loom.wiz` |
| what is canonical for the JS line budget? | `docs/notes/loom-thin-js.md` |

Code comments in those files point here rather than repeating the ownership/data-path/
validation prose. `mount.js` keeps only the mount API and the host capabilities;
`runtime.js` keeps only the child-index path format; `driver.js` keeps the event string
and the ABI; `lib/Web/Loom.wiz` keeps the renderer's guarantees.

## 8. Tests in this slice

`node web/framework/wire_test.mjs` (no browser, no Wiz) pins:

* `encode`/`decode` round trips for the P0 call/reply/request/result envelopes, the
  canonical key order, and the exact version.
* The transport refusals: wrong version, unknown channel/op, a bad `src`, a duplicate
  or gapped `seq`, an unknown payload schema, a field cap, a frame cap, a reserved key.
* The monitor transitions: call → request → result → reply, pipelined ids, a reply
  before a call, a result without a request, a duplicate id, a cancel and a late reply,
  `close` then a message.
* `hashHtml` fixed vectors; the same vectors are evaluated by `Wire.ssrHash` in
  `Tests/Groups/Wire.lean`, so the two implementations cannot drift silently.
* The adopt/replace decision on a `minidom` container: equal hash adopts without moving
  a textarea or a `<details>`, an unequal/missing hash replaces with one warning, and a
  module failure leaves the static DOM plus a text `data-wiz-error`.
* The `VALIDATION` rows 3–7 and 10 agree with the table in this note.

`web/framework/test.sh` runs it with the existing Node-only tests. The Wiz-side test for
the adopt hash is `Tests/Groups/Wire.lean` (§9).

## 9. P1 and later

* **P1 — events and patches.** `editor.events` (`text`/`key`/`select`/`focus`/`blur`/
  `flush`) and `editor.patches`; delta text; `base`/`rev` coalescing; the pre-validated
  atomic patch apply and `resync`; the outbox/in-flight caps; the keystroke and Run
  budgets; the playground/infoview migration. The patch applier stays
  `runtime.js#applyPatches`.
* **P1 — the Wiz-side wire.** `lib/Web/Wire.wiz` with the protocol values, `Wire.check`
  generated from the same `VALIDATION` table, `wiz_loom_wire_version`/
  `wiz_loom_wire_hash`, and the `Tests/Groups/Wire.lean` duality/monitor cases. P0 already
  ships the module's `Wire.version` and `Wire.ssrHash` with their vectors; P1 adds the
  protocol. P0's `wire.js` monitor is the executable reference it must agree with (the
  conformance trace makes drift a failing test).
* **P2 — capabilities.** `widgets.events`/`widgets.updates`, `lsp.requests`/
  `lsp.results`, `doclive.asks`/`doclive.updates`, the hover/span payloads and their
  render-time validators.
* **P3 — the package extension and the shim removal.** `Package.capability`/
  `Package.wire`, out-of-tree adapters, and deletion of the legacy adapter/kind strings.
* **Out of scope everywhere:** a general hydration diff. `mount` only adopts or
  replaces; `resync` is a replace patch.
