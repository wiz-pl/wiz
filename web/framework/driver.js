// The page half for an app built from lib/Web/Loom.wiz, mirroring web/tagged.js's
// `stepper`. There are two shapes of app:
//
//   1. `start`: a typed app with event handlers. The Wiz module exports
//
//        wiz_loom_init  : State
//        wiz_loom_html  : State -> String          (SSR of the current state)
//        wiz_loom_step  : State -> String -> State (the event string is "event\nindex")
//
//      and calls the FFI `js_patch` (web/js.c) with `Loom.patchesJson` on every step;
//      this file applies those patches and turns DOM events into step calls.
//
//   2. `startModel`: a `model -> tree` app whose model is a string the page holds (the
//      playground's `?ui=react` pane). The module exports `wiz_ui_html` and
//      `wiz_ui_patch`, and the page hands the driver the new model; see the function.
//
// Neither is exercised by the infoview's Wasm build; web/framework/test.mjs checks the
// same code path under Node with minidom.mjs, and web/playground_ui_test.mjs checks
// `startModel` against the playground UI module's fixture.
"use strict";
import { applyPatches, delegate, mount } from "./runtime.js";

const big = (x) => (typeof x === "bigint" ? x : BigInt(x));   // wasm64: pointers are i64

function takeString(wasm, p) {
  if (!p) return "";
  const s = wasm.UTF8ToString(Number(p));
  wasm._free(p);
  return s;
}

// Load `wasm` (Emscripten's MODULARIZE module), mount `wiz_loom_html`'s output into
// `root`, and wire events. `events` limits the delegated event types.
export function start(wasm, root, { events } = {}) {
  let state = wasm._wiz_loom_init();
  const html = () => takeString(wasm, wasm._wiz_loom_html(state));
  mount(root, html());
  globalThis.wizPatch = (json) => applyPatches(root, JSON.parse(json));
  delegate(root, (event, index) => {
    const p = wasm.stringToNewUTF8(event + "\n" + index);
    state = wasm._wiz_loom_step(state, big(p));
    wasm._free(p);
    return true;   // a handled event does not also submit a form or follow a link
  }, events);
  return { state: () => state, html };
}

// The other half of the integration: a page whose whole state is a string (the
// playground's `?ui=react` model). The Wiz module exports
//
//   wiz_ui_html  : Model -> String            (SSR of a model)
//   wiz_ui_patch : Old -> New -> String       (Loom.patchesJson between two models)
//
// and the page keeps the model; nothing round-trips through a Wiz value it cannot name.
// This is how a page with arbitrary text (output lines, a rendered goals panel) uses the
// framework: the framework's typed event dispatch needs static messages, but a pure
// `model -> tree` function does not. `patchExport` may be absent (an older module): the
// next render is then a full `mount`, which is correct, only less efficient.
//
// options: `model` (the initial model string), `document` (for parsing HTML),
// `parse` (a custom HTML→DocumentFragment, as the Node tests pass minidom's),
// `htmlExport`/`patchExport` (the Wasm function names).
export function startModel(wasm, root, options = {}) {
  const htmlExport = options.htmlExport || "_wiz_ui_html";
  const patchExport = options.patchExport || "_wiz_ui_patch";
  if (!wasm || typeof wasm[htmlExport] !== "function") return null;
  const doc = options.document || (typeof document !== "undefined" ? document : null);
  const parseFn = options.parse || (doc && typeof doc.createRange === "function"
    ? (html) => doc.createRange().createContextualFragment(html)
    : null);
  if (!parseFn) return null;   // no DOM to render into (and no parser passed)
  const call1 = (name, text) => {
    const p = wasm.stringToNewUTF8(String(text));
    const r = wasm[name](big(p));
    wasm._free(big(p));
    return takeString(wasm, r);
  };
  const call2 = (name, a, b) => {
    const pa = wasm.stringToNewUTF8(String(a));
    const pb = wasm.stringToNewUTF8(String(b));
    const r = wasm[name](big(pa), big(pb));
    wasm._free(big(pa));
    wasm._free(big(pb));
    return takeString(wasm, r);
  };
  let model = options.model === undefined ? "" : String(options.model);
  let html = call1(htmlExport, model);
  mount(root, html, parseFn);
  let renders = 1;
  return {
    model: () => model,
    html: () => html,
    renders: () => renders,
    // Move to `next` (a model string) and patch the DOM there.
    render(next) {
      const text = next === undefined || next === null ? "" : String(next);
      if (text === model) return html;
      const nextHtml = call1(htmlExport, text);
      if (typeof wasm[patchExport] === "function") {
        const patches = JSON.parse(call2(patchExport, model, text));
        applyPatches(root, patches, parseFn);
      } else {
        mount(root, nextHtml, parseFn);
      }
      model = text;
      html = nextHtml;
      renders += 1;
      return html;
    },
    dom: () => root,
  };
}
