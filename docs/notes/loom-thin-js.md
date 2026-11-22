# Loom pages: the JavaScript is a mount point

**Status:** design + stages 1–7 and the editor remainder (`thin-js-34` for 1–4;
`loom-edit` for the editor's pure rules and `host.edit`; `loom-56` for 5–6;
`thin-js-7` for the in-page server's pure half and the last paint rules, all off
`integration/train9`, 2026-11-21). The migration is staged; each stage is independently
landable. Stage 2 (one page, no fallback), stage 3 (the state format and the effect
protocol), stage 4 (the keyboard policy and the overlays), the editor's pure rules and
`host.edit`, stages 5–6 and stage 7 are on the merged branch.

The browser side of Wiz's pages has grown to about 5.1k lines of production JavaScript
(`web/*.js`, not counting tests), and most of it is not browser capability: it is page
state, layout, rendering and the rules behind the editor's overlays. Loom already owns
that for a page (`?ui=loom` at the time; it is the page now). The rule from here on is:

> **A page's JavaScript finds a DOM element, mounts the runtime on it, and forwards the
> browser capabilities the runtime cannot reach itself. It contains nothing else.**

This note is the target API, the ownership boundary, the inventory that got us here, and
the stages that remove the rest.

> **Canonical model.** The host / Loom runtime / SSR shell / designer-builder split, the
> data paths of each surface, the wire's role, the single validation table and the
> adopt-and-listen contract are canonical in
> [`loom-wire-protocol.md`](loom-wire-protocol.md). The ownership table below is this
> note's JavaScript-line-budget view of the same boundary; when the two differ, the
> protocol note wins.

## 1. The target API

```js
// web/playground.js — the whole entry point
import { mount } from "./framework/mount.js";

mount(document.body, {
  module: () => import("./wiz-playground-ui.mjs"),   // the runtime
  transport: { engine, lsp },                        // what it cannot do itself
});
```

`mount(target, { module, transport })` is the only entry point. It:

1. **finds or creates the element** (`target` is an element or a selector; a missing
   `#id` is created);
2. **loads and instantiates the runtime module** (the dynamic import's factory, with
   `print`/`printErr`), checks the ABI before touching the page, and throws on failure
   (the page shows a text reason);
3. **decides adopt or replace** from the container's `data-wiz-*` island attributes
   and the SSR hash (canonical in `loom-wire-protocol.md`); on replace it mounts the SSR
   (`wiz_loom_html`) into the element, installs `js_patch`'s applier and the delegated
   event listeners;
4. **turns DOM events into steps** (`event "\n" index "\n" payload`, the existing
   driver ABI);
5. **publishes the host capabilities** a Wiz program cannot reach — `clipboard`,
   `download`, `storage.get/set`, `url`, `tick`, `onResize`, `edit` — as
   `globalThis.wizHost`, and `transport` as `globalThis.wizTransport`;
6. returns a handle whose `call(name, ...args)` is the **only** way the page invokes the
   runtime's own entry points (`wiz_loom_show`, …), and whose `ask(name, ...args)` is its
   read-only counterpart (the editor's pure rules). The page never sees the module
   object, allocates a string or touches the ABI.

The runtime interface is therefore small and stable:

```
wiz_loom_init : S
wiz_loom_html : S -> String                    -- SSR, first paint
wiz_loom_ssr_hash : S -> String                -- optional: the adopt hash (see the protocol note)
wiz_loom_step : S -> String -> IO S            -- one DOM event, patched via js_patch
wiz_loom_<effect> : S -> ... -> IO S           -- the page's effects, if it has any
```

`web/framework/mount.js` is that contract (the first slice); `web/playground.js` is its
first client. The current driver stays underneath as the DOM seam (event delegation,
patch application, the state-ownership rule of the C ABI); stages 2–3 fold it into
`mount.js` so there is one browser module, not two.

## 2. The ownership boundary

| belongs to the runtime (Wiz/Loom) | belongs to the host (JS) |
| --- | --- |
| the page's state and its transitions | the element's identity, creation, mount point |
| the tree, HTML/SSR and the patch list | applying a patch to the DOM |
| which nodes exist, their classes/ids/attrs | event capture and delegation |
| layout inside the page (header, panes, toolbar) | the browser's layout engine |
| the examples menu's data and selected id | `localStorage`, `history`, clipboard, files |
| output classification, `#count`, status text | the Wasm instances' lifecycle |
| completion lists: filter, order, selection, insert text | the popup's position on screen (font metrics) |
| squiggle geometry: ranges → segments/lines | drawing the underline over the textarea |
| the goals panel's markup and state | the socket / fetch that delivers it |
| keyboard *policy* (what Ctrl-Enter means) | the key event and `preventDefault` |
| URL fragment / draft *format* | `history.replaceState`, `localStorage` |

**What cannot move, and why.**

* **Text-input primitives.** A `<textarea>` value, selection, caret and undo stack are
  the browser's; an IME, spellcheck, accessibility and mobile keyboards are not
  reimplementable in Wiz without replacing the control with contenteditable (a
  dependency, a licence and a much worse failure mode — the reason `web/squiggles.js`
  chose a mirror in the first place). So the runtime owns the *text model* and the host
  owns the *control*: the runtime asks for an edit (`host.edit(insert)`) and receives the
  new value as the next `input` payload. The same applies to `preventDefault`: the host
  must not swallow typing because a runtime handled a keydown, so handler metadata (or a
  host policy) decides; see stage 4.
* **Browser APIs with no Wiz equivalent.** Clipboard, Blob/download, `localStorage`,
  History, `WebSocket`/`fetch`, `requestAnimationFrame`, `ResizeObserver`,
  `getComputedStyle`. Each is a named capability on `wizHost`; a capability that is not
  named is not available to the runtime.
* **Wasm instantiation and trapping.** The engine is a separate module (`web/playground-engine.js`)
  and the UI a separate instance; starting, replacing and guarding them is host work.
* **The LSP wire protocol** (`web/lsp-client.js`: framing, tokens, request ids) is
  transport, not layout. It stays JavaScript; the *view models* it feeds (goals,
  completions, squiggles, hover cards) move to the runtime.
* **Measurement.** Font metrics, scroll offsets and element boxes are the browser's;
  the runtime decides *what* to underline and *where in the text*, the host converts
  text positions to pixels.

## 3. Inventory (production JS, `integration/train6`)

Counts are lines; "net" is the proposed destination after the whole plan. Tests are
listed separately because they are the safety net, not the surface being shrunk.

| file | lines | owns | verdict |
| --- | ---: | --- | --- |
| `web/framework/driver.js` | 98 | event strings, delegation, SSR mount, state ownership | **host** (stays; folds into `mount.js`) |
| `web/framework/mount.js` | 180 | the mount contract + host capabilities | **host** (new, this slice) |
| `web/playground.js` | 543 → 153 | mount point + engine/goals effects | **done**: the page is the runtime; the old static page is deleted |
| `web/infoview.js` | 101 | endpoint mapping, follow flag, status text, wiring | endpoint/status → runtime; wiring → `mount`; ~30 |
| `web/squiggles.js` | 206 → 250 | mirror layer, geometry, computed-style copy | geometry is the runtime's (`Web.EditorModel`); paint/measure stays |
| `web/completions.js` | 361 → 370 | popup DOM, triggers, keys, positioning | filter/order/insert are the runtime's; paint/keys stay |
| `web/lsp-client.js` | 480 | JSON-RPC/WebSocket framing, tokens | **host** (stays; transport, not layout) |
| `web/editor-model.js` | 346 | pure position/squiggle/completion rules | **moved** → `lib/Web/EditorModel.wiz` (the editor remainder); `web/framework/editor-model.mjs` is the test oracle |
| `web/doc-live.js` | 311 | doc-page panel, Markdown, hover/definition | **moves** → runtime; fetch/socket host; ~80 |
| `web/playground-engine.js` | 170 | engine trampoline, restart, failure kinds | **host** (stays) |
| `web/playground-state.js` | 155 | URL fragment + draft encoding | **moved** → `Web.Draft` (stage 3); storage/history stay |
| `web/playground-presets.js` | 192 | the examples' data | **moved** → `Web.Examples`; `web/framework/examples.mjs` is the test oracle |
| `web/playground-values.js` | 120 | kernel value grammar | **moved** → `Web.Playground`; `web/framework/values.mjs` is the test oracle |
| `web/goals.js` | 444 | goals/tagged HTML, span geometry | **moves** → runtime |
| `web/playground-lsp.js` | 454 | pane orchestration, document sync, rendering | document sync/socket → host (~150); rest → runtime |
| `web/hover.js` | 388 | hover card DOM, when-to-ask rules | **moves** → runtime; ~40 |
| `web/selfhost-lsp-shim.js` | 669 | in-page LSP shim + `PositionIndex` | protocol/engine → host; pure index → runtime |
| `web/tagged.js` | 55 | tagged-text delegation | **moves/delete** (Wiz renders tagged text) |
| `web/scroll.js` | 68 | docs page DOM from JSON | **moves** → runtime |
| `web/scroll-search.js` | 72 | docs search DOM | **moves** → runtime |

Totals: **5,135 lines** of production page JS at the start (plus the 231-line framework
browser half), of which ~3.5k lines were layout/state/rendering/policy and ~1.6k genuine
host capability. After stages 1–4 it was **4,380** in `web/*.js` plus the 226-line mount
contract (4,606), with `framework/driver.js` (139) and `runtime.js` (140) the rest of the
browser half. After the editor remainder (`loom-edit`) it is **4,149** in `web/*.js` plus
the 318-line mount contract (**4,467**), `driver.js` (147), `runtime.js` (140) and
`framework/editor-text.js` (23) making **4,777** for the whole browser half. The stage-4
target was 3,733 (4,467 against it: +734); the difference is the mirror, the popup and
the computed-style copy, which are DOM/measurement, not rules, and so cannot move.

### Tests (the safety net; they stay, and move with the code they pin)

| test | lines | pins | verdict |
| --- | ---: | --- | --- |
| `framework/minidom.mjs` | 180 | the DOM double for every Node fixture | **keep** (test-only) |
| `framework/driver_test.mjs` | 100 | event strings, payloads, `onStep`, `js_patch` | **keep** |
| `playground_test.mjs` | 145 | the Wasm engine, every example, the check index | **keep** (CI; examples list moves to Wiz at stage 3) |
| `playground_lsp_test.mjs` | 689 | the LSP client and goals panel against a mock socket | **keep**; split when the pane moves (stage 5) |
| `selfhost_lsp_test.mjs` | 666 | the in-page shim, positions, goals, completions | **keep**; positions move with the shim (stage 7) |
| `infoview_page_test.mjs` | 55 | the infoview page's URL rule and status text | **keep**; the functions move to the runtime (stage 5) |
| `playground_ui_test.mjs` | 138 | the real Wasm UI module mounted with the driver | **keep** (CI; can call `mount` once the build is in the test job) |
| `playground_loom_test.mjs` | 89 | the output pane's SSR/patches and value corpus | **keep** |
| `playground_editor_test.mjs` | 69 | the editor component's LiveApp steps | **keep** |
| `playground-state_test.mjs` | 170 | URL fragment and draft encoding | **moved** to the runtime (`=loom`), with `playground-state.js` (stage 3) |
| `editor_test.mjs` | 215 | positions, squiggle ranges, completion rules | **kept as the oracle's test**; the runtime cases are `=loom` (the editor remainder) |
| `editor_dom_test.mjs` | 309 | the two overlays in the DOM double | **kept**, using the oracle's `rules` adapter for the widgets' paint/key assertions |
| `hover_test.mjs` | 286 | hover contents and when-to-ask | **move** with `hover.js` (stage 5) |
| `playground_engine_test.mjs` | 217 | exit/abort/trap handling of the engine guard | **keep** (host) |
| `scroll-search_test.mjs` | 33 | docs search markup | **move** (stage 6) |
| `doc_node_test.mjs` | 23 | docs page hooks | **move** (stage 6) |
| `doc_chrome_test.mjs` | 61 | a docs page in Chromium | **keep** (end-to-end) |
| `chrome_test.mjs` | 50 | the playground in Chromium | **keep** (end-to-end) |
| `node_test.mjs` | 37 | `web/Web.wiz`'s hooks with a real server | **keep** |

New in this branch: `framework/mount_test.mjs` (166), `playground_page_test.mjs` (110),
`playground_entry_test.mjs` (73), `playground_start_test.mjs` (44), with
`playground_page_gen.wiz` (52) as the fixture.

## 4. The first slice (this branch)

The smallest end-to-end piece that proves the shape is the `?ui=loom` page, because it
already has a Wiz runtime:

* **`web/framework/mount.js`** (new): the single entry point described above, with the
  host capabilities and `call`.
* **`web/playground.js`**: 543 → 153 lines in the first slice (225 after stage 3). It
  mounts `wiz-playground-ui.mjs` on the body, runs the engine, wires the goals island, and
  reports results through `mount`'s effect protocol — no DOM construction, no ABI, no
  marshalling. The static hand-written page is deleted and the `?ui` switch with it; when
  the runtime cannot start, `cannotStart` puts a plain-text reason in the mount point (no
  second UI).
* **`lib/Web/Examples.wiz`** (new): the seven examples as Wiz data (`id`, `title`,
  `code`). `web/framework/examples.mjs` is the oracle the Node test compares against.
* **`lib/Web/Playground.wiz`**: the page is now a runtime app (`Page`, `PageMsg`,
  `pageApp`): the header (brand, toolbar, status), the examples menu (`<select
  id="preset">`, options rendered from `Web.Examples`, the selected one marked), the
  editor pane (composed with `Loom.mapMsg`), the goals container, the output pane and
  the footer. Loading an example replaces the editor's text, empties the output and
  increments `Page.loads` — the page sees that counter as an effect request and runs the
  program.
* **`lib/Web/Loom.wiz`**: `Loom.mapMsg`, the composition primitive (Elm's `Html.map`) a
  page needs to embed a component with its own `Msg`; one new `=loom` case pins it.
* **`web/playground-ui.wiz`**: now only the C ABI wrapper (~70 lines), calling
  `Page`/`pageApp` from `Web.Playground`.

Tests added: `web/framework/mount_test.mjs` (the contract: one export, find/create the
element, ABI check, events, `call`, every host capability, refusal of a non-runtime);
`web/playground_page_gen.wiz` + `web/playground_page_test.mjs` (the page's SSR, the
menu's `change` step, patch/SSR equality, the examples against the JS oracle);
`web/playground_entry_test.mjs` (the entry has no ABI calls, no marshalling, no DOM
construction; `mount.js` exports exactly one function). `web/playground_ui_test.mjs`
(CI's Wasm path) gained the menu checks.

Not yet after stage 2: keyboard policy (it needed the `preventDefault` protocol below
before a keydown handler was safe on a textarea), draft/share/reset (they are host
effects with a state format that moves in stage 3). Both landed in stages 3–4 below. The
default is no longer a question: there is one page.

## 4a. Stages 3 and 4 (this branch)

* **Stage 3 — the state format and the effect protocol.**
  `lib/Web/Draft.wiz` owns the fragment and draft encoding (UTF-8, base64url,
  percent-encoded parameters, the versioned JSON draft) and the initial-state
  precedence (URL fragment, draft, default). `web/playground-state.js` and
  `web/playground-state_test.mjs` are deleted; the cases moved to `=loom`. The six
  `wiz_loom_show/fail/status/enable/engine/text` exports are one
  `wiz_loom_effect (state) kind a b`, and the runtime's effects are a JSON request list
  (`wiz_loom_requests`) that `mount` hands to the page's `onRequest(kind, payload)`; the
  page acknowledges each with `wiz_loom_effect "ack"`, so a request is never dropped or
  repeated. Share, Save, Reset and Clear are runtime toolbar buttons again: Reset and
  Clear are pure messages, Share and Save are requests whose payloads (the fragment, the
  source with the embedded Prelude) the runtime formats and the page writes with
  `host.clipboard`/`host.download`/`host.url`/`host.storage`.
* **Stage 4 — the keyboard and the overlays.**
  `Loom.onPrevent` marks a handler whose default action the runtime decides: the
  rendered element carries `data-wiz-prevent-EVENT`, and the driver asks
  `wiz_loom_consume` after the step, so the editor's `keydown` prevents only
  Ctrl/⌘+Enter (run) and Ctrl/⌘+S (save) — `Page.consume` is the policy, and typing is
  never swallowed. Both overlays are back on the page: `web/squiggles.js` no longer
  wraps the editor (the layer is the editor section's last child, so `Loom`'s
  child-index patch paths stay valid), the completion popup stays outside the rendered
  tree, and the overlay CSS moved to `web/overlays.css` (loaded by the playground).
  `web/loom_overlay_test.mjs` pins the two overlays against the patch paths. Editing the
  text recomputes the menu's selected id (`Draft.matchedPresetId`, with a disabled
  `Custom program` option, as the static page did), so the menu never lies about which
  example the editor holds.

## 4b. The editor remainder (`loom-edit`)

Stage 4 left `editor-model.js` in place because the standalone infoview still used it.
This branch finishes the editor side instead of waiting for stage 5:

* **`lib/Web/EditorModel.wiz`** owns the pure rules: UTF-16 positions (the LSP unit and
  a JavaScript string index; the module expands Wiz's code points at its one boundary),
  diagnostic ranges → merged, line-clipped spans, completion items/filter/score/order,
  the keyboard's index arithmetic, snippet stripping, the accepted edit, the popup
  state, and the Tab indentation. `web/framework/editor-model.mjs` is the test oracle
  (nothing in production imports it).
* **`host.edit`** is the missing text-input capability (`web/framework/mount.js`):
  `edit({ insert, from, to })` replaces `[from, to)` (the current selection when omitted)
  with `insert`, puts the caret after it, dispatches `input`, and returns
  `{ value, selectionStart, selectionEnd }`. It is a primitive, not a policy: the runtime
  decides what an indent is.
* **Tab-to-indent** is now the runtime's. The driver appends a text field's selection to
  a keydown payload (`@start@end`), `Page.key` asks `Web.EditorModel.indentJson` for the
  edit, and the page services the `edit` request with `host.edit` then reports the new
  text/selection through `wiz_loom_effect "edited"`. `Page.consume` consumes only
  Ctrl/⌘+Enter, Ctrl/⌘+S and Tab, so typing is still never swallowed.
* **The overlays ask the runtime.** `playground.js` builds a `rules` object from
  `mount`'s new `ask(name, ...args)` (a read-only string query over
  `wiz_loom_editor_*`); `squiggles.js` paints the returned spans and `completions.js`
  paints/keys the returned items. `framework/editor-text.js` keeps the two lines that
  genuinely read the control (`caretOffset`, `selectionOffsets`).
* **The desync regression test is on the real page now.** `web/playground_page_test.mjs`
  mounts the runtime's SSR, applies the menu patch, enables the squiggle layer, then
  applies a text patch at the editor's child-index path and requires the textarea's live
  value to change; `web/loom_overlay_test.mjs` keeps the smaller DOM-double version.

Production JS on `loom-edit` was **4,149** in `web/*.js` + **318** mount =
**4,467** (against the stage-4 target 3,733). The remaining 734 lines are the parts that
need the DOM: the mirror and its computed-style copy, the popup's rows/position, and the
widgets' event wiring. On `loom-edit`, `goals.js` still served the standalone pane's
geometry and `playground-lsp.js` asked `goals.positionAt` for the caret; stage 5 below
moves both.

## 4b. Stages 5 and 6 (this branch)

* **Stage 5 — the goals pane, the infoview and the hover card.**
  `lib/Web/Goals.wiz` renders the pane's status, hint, goals, expected type, term tree,
  diagnostics, selected subterm and widgets as `Loom.VNode`s; a click on a hypothesis,
  a goal or a tagged subterm is a message, and the pane asks the page for `reveal`,
  `subterm` or `reconnect` through `wiz_loom_requests` (the same request list the page
  already services). `lib/Web/Hover.wiz` owns the hover contents/Markdown lines and the
  definition label; `web/hover.js` is now only the timers, the caret and the card's
  position. The playground's `Page` embeds the pane (`lib/Web/Playground.wiz`) and its
  `wiz_loom_effect "panel"` feeds it. The standalone infoview is a Loom app
  (`lib/Web/InfoviewPage.wiz`, `web/infoview-ui.wiz`, `wiz-infoview-ui.mjs`): the page
  mounts it on the body and keeps the URL rule, the socket and the caret; it no longer
  imports `editor-model.js`. `web/goals.js` and the pure half of `web/hover.js` moved to
  `web/framework/{goals,hover}.mjs` as the Node test's oracles (as `values.mjs` and
  `examples.mjs` already are). `wiz_loom_effect "hover"` carries the server's answer and
  the runtime renders the card; the page positions `#wiz-hover`.
* **Stage 6 — the docs pages.**
  `lib/Web/Search.wiz` owns the search's ranking, snippets and hit markup; the new
  `wiz-docs-ui.mjs` is mounted on `#results`, and `web/scroll-search.js` keeps only the
  input, Enter/Escape and `location` (37 lines). `lib/Web/DocLive.wiz` owns the live
  panel's head, hover Markdown, goals, expected type and diagnostics; `wiz-doc-live-ui.mjs`
  is mounted on the panel, and `web/doc-live.js` keeps the source fetch, the socket and
  the pin. `web/tagged.js` is deleted (its loader/stepper/delegate are in `scroll.js`;
  the signatures are still `lib/Tagged.wiz`'s). `wiz doc` copies the two runtimes and
  `framework/` into the site.

Production JavaScript after both stages and the merged `loom-edit` remainder:
**3,278** in `web/*.js` plus the **628**-line browser half (`mount` 318, `driver` 147,
`runtime` 140, `editor-text` 23), **3,906** together. The test oracles
(`framework/goals.mjs` 481, `framework/hover.mjs` 150, `framework/editor-model.mjs` 396)
are not page code. That is still above the plan's 2,570/2,144 targets. The gap is not
the editor rules any more (`editor-model.js` is gone and the overlays paint runtime
segments/items): it is the irreducible host plus what stages 5–7 have left —
`selfhost-lsp-shim.js` (669, stage 7; `PositionIndex` is its next move),
`lsp-client.js` (480), the overlay paint/position modules (`completions.js` 361,
`squiggles.js` 235) and the pages' transport (`playground-lsp.js` 381,
`playground-engine.js` 170). The plan's stage-6 number assumed those would be gone by
then; they are not, so the target is not met rather than redefined.

## 4c. Stage 7 (`thin-js-7`)

`PositionIndex` and the editor rules already landed (`lib/Web/EditorModel.wiz`,
`loom-*`); this branch moves the rest of the in-page server's pure half and the last
paint-time rules:

* **`lib/Web/Selfhost.wiz`** (new) owns the engine's text output as diagnostics (the
  command splitter with doc comments/attributes/`mutual` blocks, the parse-error
  placement in UTF-16, severity and message un-prefixing), `parseCheck`'s shape check,
  `withPrelude`, the completion prefix/word scan/filter, and the completion, hover and
  definition answers decoded from the check's declaration index. `web/selfhost-lsp-shim.js`
  is now the server around them (314 lines, from 597): the JSON-RPC switch, the
  document map, the engine calls and the WebSocket stand-in. It receives the rules as
  `index`, the same adapter the overlays use; `createIndexer` in
  `web/playground-lsp.js` is the production adapter over `mount.ask`, and
  `web/framework/index-oracle.mjs` is the Node test oracle (test-only).
* **`Web.EditorModel`** gained the completion card's tooltip, the Ctrl/⌘-Space ask
  key, and the source-span ↔ offsets mapping, so `web/completions.js`,
  `web/squiggles.js` and `web/playground-lsp.js` only paint/measure/position.
  `playground-lsp.js` no longer carries `positionAt`/`parseSpan`/`offsetAt`; a span's
  offsets are `Web.EditorModel.spanJson` and the caret is the runtime's `position`.
* **What remains host.** `web/lsp-client.js` (480) is the transport the note already
  names as permanent: the socket, the promise/timer pending map, request ids, the token
  in the URL, and the boot-time endpoint rule (`web/infoview.js` needs `endpointOf`
  before it mounts). Its pure *shapes* could move, but every page would need the runtime
  before the socket exists and the docs page has no `createIndexer`; the layout gain is
  nil. `web/squiggles.js` (250) is the mirror, `getComputedStyle`, scroll and
  `ResizeObserver`; the ranges are the runtime's. `web/completions.js` (360) is the
  popup's rows, keyboard dispatch and the measured glyph; filter/order/insert/score are
  `Web.EditorModel`. `web/selfhost-lsp-shim.js`'s remaining 314 lines are the protocol
  and the engine boundary.

Production JS is now **3,470** in `web/*.js` before the framework's unchanged 628-line
browser half (the shim alone is 283 lines lighter; `playground-lsp.js` grew by the
adapter that marshals the runtime's answers). `=loom` has two new cases pinning
`Web.Selfhost`.

## 5. Stages, each landable on its own

Line targets are production JS (`web/*.js` outside tests and `framework/minidom.mjs`).
"today" is `integration/train6`; each row is cumulative.

| stage | what lands | production JS |
| --- | --- | ---: |
| today | — | 5,135 |
| **1. mount + examples** (this branch) | `mount.js`; entry split; examples menu/data in the runtime | 5,377 (entry 543→151; +190 contract, +444 fallback) |
| **2. drop the fallback** (this branch) | one page: `playground-static.js`, the static markup and the `?ui` switch deleted; a startup failure is a plain-text reason in the mount point | **4,937** (4,746 `web/*.js` + 191 `mount.js`) |
| **3. page effects + state format** (this branch) | the `wiz_loom_*` effect entry points become one `wiz_loom_effect` driven by the runtime's request counters; draft/fragment encoding into `Web.Draft`; `playground-state.js` deleted (its cases moved to `=loom`); share/save/reset/clear are runtime messages + `host` calls | **4,606** (target 4,470: 4,380 `web/*.js` + 226 `mount.js`) |
| **4. keyboard + overlays** (this branch) | `Loom.onPrevent` so a keydown handler prevents only what it consumed; the Enter/Save policy in the runtime; both overlays back on the page, the non-wrapping squiggle layer and `overlays.css` | **4,606** (target 3,733; the overlay rules waited for 4b) |
| **4b. editor remainder** (`loom-edit`) | `lib/Web/EditorModel.wiz`; `host.edit`; Tab-to-indent in the runtime; `ask` + `wiz_loom_editor_*`; the overlays paint runtime segments/items; the real-page desync test | **4,467** (4,149 `web/*.js` + 318 `mount.js`; target 3,733) |
| **5. goals pane** (merged) | `goals.js`, most of `playground-lsp.js`, `web/infoview.js`'s page logic into a Loom app (the infoview page becomes `mount`); `lsp-client.js` stays as the transport; `hover.js` into the same app | **3,906 after 5+6** (target 2,570) |
| **6. docs pages** (merged) | `scroll.js`, `scroll-search.js`, `doc-live.js` into the docs runtime; the docs page uses `mount`; `tagged.js` deleted | **3,906** (target 2,144; not met — see the breakdown above) |
| **7. the shim** | `PositionIndex` (`selfhost-lsp-shim.js:322`, with `editorOffset`/`range`) and its lookup/`termGoal`/`goal` rules into Wiz; the shim becomes the engine adapter (~250 lines); the engine's own LSP surface stays host | ~1,720 |

End state: ~1.7k lines of page JS plus the ~420-line framework browser half
(`driver`/`runtime`/`mount`); the irreducible host is most of it (`lsp-client`, the
engine adapter, the paint/measure adapters). Every page is 30–80 lines: an element, a
module import, a `transport`.

The order is chosen so that each stage deletes code the previous one made redundant and
none depends on a later stage: 1 introduces the contract, 2 removes the old page, 3–4
shrink the entry, 5–7 move the remaining pages/tools. Stage 4 needs the keydown protocol
and is the only one with a framework change; stage 5 needs the LSP transport to stay
where it is (it does).

## 6. What did not move, and open questions

**Known gap after stage 2 (closed by stage 3).** The static page's toolbar also had
Share, Save, Reset and Clear; the runtime page renders only the examples menu. Clear and
Reset are pure state changes, Share and Save are host effects plus the fragment format,
so they landed together with stage 3's effect protocol. `Web.Draft` owns the format and
`Page.requests` asks the page for the effect; the toolbar is the runtime's again.

* **`lsp-client.js` is a permanent host capability** unless a Wiz LSP client replaces it.
  It is a protocol state machine with a socket; moving it buys nothing for the page's
  layout and would duplicate a tested implementation.
* **The textarea stays.** An editor that owns its own caret/undo/IME is the one thing a
  plain `<textarea>` gets for free; the runtime can own everything around it.
* **`preventDefault` is per handler, and the runtime decides.** A keydown handler that
  always prevents the default swallows typing. `Loom.onPrevent` marks a handler whose
  default action the runtime owns; the driver asks `wiz_loom_consume` after the step and
  prevents only what the app consumed (`Page.consume`: Ctrl/⌘+Enter, Ctrl/⌘+S). This is
  the one framework change stage 4 needed.
* **`?squiggles=off` / `?completions=off`** stay the page's flags (`wantsSquiggles` /
  `wantsCompletions`). The widgets paint the runtime's spans/items; the standalone
  infoview still passes `squiggles: false`/`completions: false` until stage 5 gives it
  the runtime's `rules`, so the shared widget and CSS are ready for it.
* **Tab-to-indent is the runtime's, through `host.edit`.** The driver carries a text
  field's selection with the key, `Page.key` computes the indent with
  `Web.EditorModel.indentJson`, and the host applies the edit (value, selection, then
  `input`). The capability has no indentation policy in it; the keydown handler is on
  `<main>`, so a Ctrl+S with focus in the header (the examples menu) is still the
  browser's Save, not the page's.
* **There is no fallback page.** `wiz-playground-ui.mjs` is a build requirement, and a
  missing or foreign module produces a text reason in the mount point
  (`web/playground_start_test.mjs`), not a second UI. That is the rule this plan exists
  to enforce. The `.#wiz-playground` derivation builds both the engine and the page, so
  the site build gets both from one store path.
