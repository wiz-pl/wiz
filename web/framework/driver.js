// The page half for an app built from lib/Web/Loom.wiz, mirroring web/tagged.js's
// `stepper`: the Wiz module exports
//
//   wiz_loom_init  : State
//   wiz_loom_html  : State -> String          (SSR of the current state)
//   wiz_loom_step  : State -> String -> State
//
// and calls the FFI `js_patch` (web/js.c) with `Loom.patchesJson` on every step; this
// file applies those patches and turns DOM events into step calls.
//
// **The event string.** A step's argument is
//
//   event "\n" index "\n" payload
//
// where `event` is the DOM type (`click`, `input`, `keydown`, …), `index` is the value of
// the element's `data-wiz-on-EVENT` attribute (a handler index from `Loom.render`), and
// `payload` is the rest of the string. The payload is how a pure `step` can see what a
// control holds: a form control's live `value` for `input`/`change`, the key for
// `keydown`/`keyup`, and nothing for the other events. It is the *rest* of the string,
// so a textarea's newlines arrive intact; Wiz parses it with `Loom.splitEvent` and an
// app that uses it is a `Loom.LiveApp` (`update msg payload state`).
//
// Nothing here reads a control's value except to report it: the patch applier still owns
// the DOM. A patch that sets a `value` attribute does not rewrite the property when it
// already holds that string (web/framework/runtime.js), so a re-render cannot move the
// caret of a control the user is typing in.
//
// **Ownership (stage 9g's C ABI).** An exported function consumes its arguments and
// returns an owned value, so `state` is transferred to every `wiz_loom_step` and the new
// one is kept. A read-only call (`wiz_loom_html` for the first paint) cannot take that
// one reference: the module must export `wiz_retain`, and the driver takes an extra
// reference first. A page that calls its own `wiz_loom_*` entry points must do the same:
// pass the state, keep the returned one.
//
// It is the intended integration, not yet exercised by a Wasm build (no Emscripten on
// the machine where the prototype was written); web/framework/driver_test.mjs checks the
// event strings and the mount under Node with minidom.mjs.
"use strict";
import { applyPatches, delegate, mount } from "./runtime.js";

const big = (x) => (typeof x === "bigint" ? x : BigInt(x));   // wasm64: pointers are i64

function takeString(wasm, p) {
  if (!p) return "";
  const s = wasm.UTF8ToString(Number(p));
  wasm._free(p);
  return s;
}

// What the step receives after the handler index: a form control's live value, a key,
// or nothing. (`value` is a string property on input/textarea/select; a test double may
// only have the attribute.)
export function payloadOf(type, e) {
  const target = e && e.target;
  if (type === "input" || type === "change") {
    if (target && typeof target.value === "string") return target.value;
    if (target && typeof target.getAttribute === "function") return target.getAttribute("value") || "";
    return "";
  }
  if (type === "keydown" || type === "keyup") {
    return e && typeof e.key === "string" ? e.key : "";
  }
  return "";
}

// Load `wasm` (Emscripten's MODULARIZE module), mount `wiz_loom_html`'s output into
// `root`, and wire events. `events` limits the delegated event types; `parse` is the
// HTML parser (the browser's by default, `minidom.mjs`'s in a test); `onStep(state,
// event, index, payload)` sees every step after it happened (a page's effect hook).
export function start(wasm, root, { events, parse, onStep } = {}) {
  let state = wasm._wiz_loom_init();
  // An exported function *consumes* its argument (the C ABI's ownership rule, stage 9g):
  // the SSR call only reads the state, so take an extra reference for it and keep ours.
  const html = () => {
    if (typeof wasm._wiz_retain === "function") {
      wasm._wiz_retain(typeof state === "bigint" ? state : big(state));
    }
    return takeString(wasm, wasm._wiz_loom_html(state));
  };
  mount(root, html(), parse);
  globalThis.wizPatch = (json) => applyPatches(root, JSON.parse(json), parse);
  delegate(root, (event, index, e) => {
    const payload = payloadOf(event, e);
    const p = wasm.stringToNewUTF8(event + "\n" + index + "\n" + payload);
    state = wasm._wiz_loom_step(state, big(p));
    wasm._free(p);
    if (typeof onStep === "function") onStep(state, event, index, payload);
    return true;   // a handled event does not also submit a form or follow a link
  }, events);
  return {
    state: () => state,
    // A page that changed the state through an entry point of its own (the playground's
    // `wiz_loom_show` and friends, which patch the DOM themselves) hands it back here, so
    // the next DOM event steps from it.
    setState: (next) => { state = next; },
    html,
  };
}
