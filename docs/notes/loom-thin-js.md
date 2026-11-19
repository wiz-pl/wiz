# Loom pages: the JavaScript is a mount point

**Status:** design + first slice (`loom-thin-js`, off `integration/train6`, 2026-11-19).
The migration is staged; each stage is independently landable.

The browser side of Wiz's pages has grown to about 5.1k lines of production JavaScript
(`web/*.js`, not counting tests), and most of it is not browser capability: it is page
state, layout, rendering and the rules behind the editor's overlays. Loom already owns
that for the `?ui=loom` page. The rule from here on is:

> **A page's JavaScript finds a DOM element, mounts the runtime on it, and forwards the
> browser capabilities the runtime cannot reach itself. It contains nothing else.**

This note is the target API, the ownership boundary, the inventory that got us here, and
the stages that remove the rest.

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
   `print`/`printErr`), checks the ABI before touching the page, and on failure leaves
   the fallback page intact;
3. **mounts the SSR** (`wiz_loom_html`) into the element, installs `js_patch`'s applier
   and the delegated event listeners;
4. **turns DOM events into steps** (`event "\n" index "\n" payload`, the existing
   driver ABI);
5. **publishes the host capabilities** a Wiz program cannot reach — `clipboard`,
   `download`, `storage.get/set`, `url`, `tick`, `onResize` — as `globalThis.wizHost`,
   and `transport` as `globalThis.wizTransport`;
6. returns a handle whose `call(name, ...args)` is the **only** way the page invokes the
   runtime's own entry points (`wiz_loom_show`, …). The page never sees the module
   object, allocates a string or touches the ABI.

The runtime interface is therefore small and stable:

```
wiz_loom_init : S
wiz_loom_html : S -> String                    -- SSR, first paint
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
| `web/playground.js` | 543 → 151 | static DOM, state, examples, draft/share, keyboard, engine effects | **split**: layout/state/data → runtime; engine/goals → host |
| `web/playground-static.js` | 444 | the old page, kept as the fallback | **delete** (stage 2) |
| `web/infoview.js` | 101 | endpoint mapping, follow flag, status text, wiring | endpoint/status → runtime; wiring → `mount`; ~30 |
| `web/squiggles.js` | 206 | mirror layer, geometry, computed-style copy | geometry → runtime; paint/measure → host; ~80 |
| `web/completions.js` | 361 | popup DOM, triggers, keys, positioning | policy → runtime; paint/keys → host; ~100 |
| `web/lsp-client.js` | 480 | JSON-RPC/WebSocket framing, tokens | **host** (stays; transport, not layout) |
| `web/editor-model.js` | 346 | pure position/squiggle/completion rules | **moves** → runtime (delete) |
| `web/doc-live.js` | 311 | doc-page panel, Markdown, hover/definition | **moves** → runtime; fetch/socket host; ~80 |
| `web/playground-engine.js` | 170 | engine trampoline, restart, failure kinds | **host** (stays) |
| `web/playground-state.js` | 155 | URL fragment + draft encoding | **moves** → runtime (format); storage/history stay |
| `web/playground-presets.js` | 192 | the examples' data | **moves** → runtime (done here); stays as test oracle |
| `web/playground-values.js` | 120 | kernel value grammar | **moves** (already ported to Wiz); stays as test oracle |
| `web/goals.js` | 444 | goals/tagged HTML, span geometry | **moves** → runtime |
| `web/playground-lsp.js` | 454 | pane orchestration, document sync, rendering | document sync/socket → host (~150); rest → runtime |
| `web/hover.js` | 388 | hover card DOM, when-to-ask rules | **moves** → runtime; ~40 |
| `web/selfhost-lsp-shim.js` | 669 | in-page LSP shim + `PositionIndex` | protocol/engine → host; pure index → runtime |
| `web/tagged.js` | 55 | tagged-text delegation | **moves/delete** (Wiz renders tagged text) |
| `web/scroll.js` | 68 | docs page DOM from JSON | **moves** → runtime |
| `web/scroll-search.js` | 72 | docs search DOM | **moves** → runtime |

Totals: **5,135 lines** of production page JS (plus the 231-line framework browser half),
of which ~3.5k lines are layout/state/rendering/policy and ~1.6k are genuine host
capability.

### Tests (the safety net; they stay, and move with the code they pin)

| test | lines | pins | verdict |
| --- | ---: | --- | --- |
| `framework/minidom.mjs` | 180 | the DOM double for every Node fixture | **keep** (test-only) |
| `framework/driver_test.mjs` | 100 | event strings, payloads, `onStep`, `js_patch` | **keep** |
| `playground_test.mjs` | 145 | the Wasm engine, every example, the check index | **keep** (CI; examples list moves to Wiz at stage 3) |
| `playground_lsp_test.mjs` | 689 | the LSP client and goals panel against a mock socket | **keep**; split when the pane moves (stage 5) |
| `selfhost_lsp_test.mjs` | 666 | the in-page shim, positions, goals, completions | **keep**; positions move with the shim (stage 7) |
| `infoview_page_test.mjs` | 55 | the infoview page's URL rule and status text | **keep**; the functions move to the runtime (stage 5) |
| `playground_ui_test.mjs` | 138 | the real Wasm UI module mounted with the driver | **keep** (CI); extends to `mount` at stage 2 |
| `playground_loom_test.mjs` | 89 | the output pane's SSR/patches and value corpus | **keep** |
| `playground_editor_test.mjs` | 69 | the editor component's LiveApp steps | **keep** |
| `playground-state_test.mjs` | 170 | URL fragment and draft encoding | **move** to the runtime with `playground-state.js` (stage 3) |
| `editor_test.mjs` | 215 | positions, squiggle ranges, completion rules | **move** to the runtime with `editor-model.js` (stage 4) |
| `editor_dom_test.mjs` | 309 | the two overlays in the DOM double | **keep**, rewritten against the runtime's items/segments (stage 4) |
| `hover_test.mjs` | 286 | hover contents and when-to-ask | **move** with `hover.js` (stage 5) |
| `playground_engine_test.mjs` | 217 | exit/abort/trap handling of the engine guard | **keep** (host) |
| `scroll-search_test.mjs` | 33 | docs search markup | **move** (stage 6) |
| `doc_node_test.mjs` | 23 | docs page hooks | **move** (stage 6) |
| `doc_chrome_test.mjs` | 61 | a docs page in Chromium | **keep** (end-to-end) |
| `chrome_test.mjs` | 50 | the playground in Chromium | **keep** (end-to-end) |
| `node_test.mjs` | 37 | `web/Web.wiz`'s hooks with a real server | **keep** |

New in this slice: `framework/mount_test.mjs` (166), `playground_page_test.mjs` (110),
`playground_entry_test.mjs` (55), with `playground_page_gen.wiz` (52) as the fixture.

## 4. The first slice (this branch)

The smallest end-to-end piece that proves the shape is the `?ui=loom` page, because it
already has a Wiz runtime:

* **`web/framework/mount.js`** (new): the single entry point described above, with the
  host capabilities and `call`.
* **`web/playground.js`**: 543 → 151 lines. It mounts `wiz-playground-ui.mjs` on
  `document.body`, runs the engine, wires the goals island, and reports results through
  `handle.call("wiz_loom_show", …)` — no DOM construction, no ABI, no marshalling. The
  static page is loaded dynamically as the fallback (`web/playground-static.js`, the
  deletion queue), so the default page still works when the module is not built.
* **`lib/Web/Examples.wiz`** (new): the seven examples as Wiz data (`id`, `title`,
  `code`). `web/playground-presets.js` stays as the oracle the Node test compares
  against.
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

Not in this slice: keyboard policy (it needs the `preventDefault` protocol below before a
keydown handler is safe on a textarea), draft/share/reset (they are host effects with a
state format that moves in stage 3), and flipping the default to the runtime.

## 5. Stages, each landable on its own

Line targets are production JS (`web/*.js` outside tests and `framework/minidom.mjs`).
"today" is `integration/train6`; each row is cumulative.

| stage | what lands | production JS |
| --- | --- | ---: |
| today | — | 5,135 |
| **1. mount + examples** (this branch) | `mount.js`; entry split; examples menu/data in the runtime | 5,377 (entry 543→151; +190 contract, +444 fallback) |
| **2. delete the fallback, flip the default** | `?ui=loom` becomes the page; `playground-static.js`, the static markup's controls and `initPageState` go; `?ui=static` removed with them | 4,933 |
| **3. page effects + state format** | the `wiz_loom_*` effect entry points become one `wiz_loom_effect` (or a typed message) driven by the runtime's request counters; draft/fragment encoding into `Web.Playground`; `playground-state.js`, `playground-presets.js`, `playground-values.js` deleted (their corpora move to the Wiz tests); share/save/reset/clear become runtime messages + `host` calls | 4,466 |
| **4. keyboard + overlays** | a handler's key metadata (`Loom.onPrevent`) so a keydown handler can prevent only what it consumed; Tab/Enter/Save policy in the runtime; `editor-model.js` deleted; `squiggles.js`/`completions.js` reduced to paint/measure/position host adapters over runtime segments/items | 3,733 |
| **5. goals pane** | `goals.js`, most of `playground-lsp.js`, `web/infoview.js`'s page logic into a Loom app (the infoview page becomes `mount`); `lsp-client.js` stays as the transport; `hover.js` into the same app | 2,566 |
| **6. docs pages** | `scroll.js`, `scroll-search.js`, `doc-live.js` into the docs runtime; the docs page uses `mount`; `tagged.js` deleted | 2,140 |
| **7. the shim** | `PositionIndex` (pure) into Wiz; `selfhost-lsp-shim.js` becomes the engine adapter (~250 lines); the engine's own LSP surface stays host | ~1,720 |

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

* **`lsp-client.js` is a permanent host capability** unless a Wiz LSP client replaces it.
  It is a protocol state machine with a socket; moving it buys nothing for the page's
  layout and would duplicate a tested implementation.
* **The textarea stays.** An editor that owns its own caret/undo/IME is the one thing a
  plain `<textarea>` gets for free; the runtime can own everything around it.
* **`preventDefault` needs a framework change.** A keydown handler that always prevents
  the default swallows typing. The fix is per-handler metadata (`Loom.onPrevent`) or a
  host policy; stage 4. Until then the Loom page's keyboard is the page's (a listener),
  not the runtime's.
* **`?squiggles=off` / `?completions=off`** stay the overlays branch's flags; this
  branch does not rewrite `web/squiggles.js` or `web/completions.js`. The only overlap is
  the entry split: `loom-overlays`' `wireGoals` change applies to
  `web/playground-static.js` now (and to the small Loom branch in `web/playground.js`).
* **The static page is a fallback, not a second implementation.** It exists only for a
  build without `wiz-playground-ui.mjs`; stage 2 makes the module a build requirement and
  deletes it.
