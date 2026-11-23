// The page half for an app built from lib/Web/Loom.wiz, mirroring web/tagged.js's
// `stepper`: the Wiz module exports
//
//   wiz_loom_init  : State
//   wiz_loom_html  : State -> String          (SSR of the current state)
//   wiz_loom_step  : State -> String -> State (the event string is "event\nindex")
//
// and calls the FFI `js_patch` (web/js.c) with `Loom.patchesJson` on every step; this
// file applies those patches and turns DOM events into step calls. It is the intended
// integration, not yet exercised by a Wasm build (no Emscripten on the machine where
// the prototype was written); web/framework/test.mjs checks the same code path under
// Node with minidom.mjs.
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
