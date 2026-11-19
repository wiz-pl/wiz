# Loom pages: the JavaScript is a mount point

**Status:** design + stages 1–4 (`thin-js-34`, off `integration/train7`, 2026-11-19).
The migration is staged; each stage is independently landable. Stage 2 (one page, no
fallback), stage 3 (the state format and the effect protocol) and stage 4 (the keyboard
policy and the overlays) are on `thin-js-34`.

The browser side of Wiz's pages has grown to about 5.1k lines of production JavaScript
(`web/*.js`, not counting tests), and most of it is not browser capability: it is page
state, layout, rendering and the rules behind the editor's overlays. Loom already owns
that for a page (`?ui=loom` at the time; it is the page now). The rule from here on is:

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
   `print`/`printErr`), checks the ABI before touching the page, and throws on failure
   (the page shows a text reason);
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
| `web/playground.js` | 543 → 153 | mount point + engine/goals effects | **done**: the page is the runtime; the old static page is deleted |
| `web/infoview.js` | 101 | endpoint mapping, follow flag, status text, wiring | endpoint/status → runtime; wiring → `mount`; ~30 |
| `web/squiggles.js` | 206 | mirror layer, geometry, computed-style copy | geometry → runtime; paint/measure → host; ~80 |
| `web/completions.js` | 361 | popup DOM, triggers, keys, positioning | policy → runtime; paint/keys → host; ~100 |
| `web/lsp-client.js` | 480 | JSON-RPC/WebSocket framing, tokens | **host** (stays; transport, not layout) |
| `web/editor-model.js` | 346 | pure position/squiggle/completion rules | **stays until stage 5** (the standalone infoview still uses it); the playground's overlay layout is the runtime's |
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
host capability. After stages 1–4 it is **4,380** in `web/*.js` plus the 226-line mount
contract (4,606); `framework/driver.js` (139) and `runtime.js` (140) are the rest of the
browser half.

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
| `editor_test.mjs` | 215 | positions, squiggle ranges, completion rules | **move** to the runtime with `editor-model.js` (stage 4) |
| `editor_dom_test.mjs` | 309 | the two overlays in the DOM double | **keep**, rewritten against the runtime's items/segments (stage 4) |
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

`web/editor-model.js` is **not** deleted in stage 4: the standalone infoview page
(`web/infoview.js`, stage 5) still uses its position/squiggle/completion rules through
the same `web/playground-lsp.js`. The playground's overlay *layout* policy is the
runtime's (the layer is appended after the rendered children, the popup outside them);
moving the pure rules waits for stage 5, when the infoview is a Loom app too.

## 5. Stages, each landable on its own

Line targets are production JS (`web/*.js` outside tests and `framework/minidom.mjs`).
"today" is `integration/train6`; each row is cumulative.

| stage | what lands | production JS |
| --- | --- | ---: |
| today | — | 5,135 |
| **1. mount + examples** (this branch) | `mount.js`; entry split; examples menu/data in the runtime | 5,377 (entry 543→151; +190 contract, +444 fallback) |
| **2. drop the fallback** (this branch) | one page: `playground-static.js`, the static markup and the `?ui` switch deleted; a startup failure is a plain-text reason in the mount point | **4,937** (4,746 `web/*.js` + 191 `mount.js`) |
| **3. page effects + state format** (this branch) | the `wiz_loom_*` effect entry points become one `wiz_loom_effect` driven by the runtime's request counters; draft/fragment encoding into `Web.Draft`; `playground-state.js` deleted (its cases moved to `=loom`); share/save/reset/clear are runtime messages + `host` calls | **4,606** (target 4,470: 4,380 `web/*.js` + 226 `mount.js`) |
| **4. keyboard + overlays** (this branch) | `Loom.onPrevent` so a keydown handler prevents only what it consumed; the Enter/Save policy in the runtime; both overlays back on the page, the non-wrapping squiggle layer and `overlays.css` | **4,606** (target 3,733; `editor-model.js` and the overlay rules wait for stage 5) |
| **5. goals pane** | `goals.js`, most of `playground-lsp.js`, `web/infoview.js`'s page logic into a Loom app (the infoview page becomes `mount`); `lsp-client.js` stays as the transport; `hover.js` into the same app | 2,570 |
| **6. docs pages** | `scroll.js`, `scroll-search.js`, `doc-live.js` into the docs runtime; the docs page uses `mount`; `tagged.js` deleted | 2,144 |
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
  `wantsCompletions`). Stage 4 adopted `loom-overlays`' non-wrapping layer and the
  shared `web/overlays.css`; the completion *rules* (`web/editor-model.js`) still serve
  the standalone infoview until stage 5, so the playground and the infoview share the
  widget and differ only in whether the runtime or the module computes the segments.
* **Tab-to-indent is still the browser's.** The static page inserted two spaces on Tab;
  the runtime has no edit capability (`host.edit`), so Tab moves focus. Adding
  `host.edit` (set value, selection, then dispatch `input`) is the next host capability;
  Enter and Save do not need it. The keydown handler is on `<main>`, so a Ctrl+S with
  focus in the header (the examples menu) is the browser's Save, not the page's.
* **There is no fallback page.** `wiz-playground-ui.mjs` is a build requirement, and a
  missing or foreign module produces a text reason in the mount point
  (`web/playground_start_test.mjs`), not a second UI. That is the rule this plan exists
  to enforce. The `.#wiz-playground` derivation builds both the engine and the page, so
  the site build gets both from one store path.
