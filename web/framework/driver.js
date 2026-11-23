// The page half for an app built from lib/Web/Loom.wiz, mirroring web/tagged.js's
// `stepper`: the Wiz module exports
//
//   wiz_loom_init     : State
//   wiz_loom_html     : State -> String          (SSR of the current state)
//   wiz_loom_step     : State -> String -> State
//   wiz_loom_effect   : State -> String -> String -> String -> State
//   wiz_loom_requests : State -> String          (pending effects, as JSON)
//   wiz_loom_consume  : State -> String -> Nat   (did a marked event consume its default?)
//
// and calls the FFI `js_patch` (web/js.c) with `Loom.patchesJson` on every step; this
// file applies those patches and turns DOM events into step calls. The last three are
// optional; a runtime with no effects or no `onPrevent` handler does not export them.
//
// The host/runtime/SSR-shell/designer-builder split, the data paths, the single
// validation table and the adopt contract are canonical in
// `docs/notes/loom-wire-protocol.md`; this file is only the DOM seam. `start` asks
// `adopt.js` whether an island's hash matches before it touches a node: a match attaches
// the listeners and keeps the static tree, a mismatch (or no island) replaces it exactly
// as before.
//
// **The event string.** A step's argument is
//
//   event "\n" index "\n" payload
//
// where `event` is the DOM type (`click`, `input`, `keydown`, …), `index` is the value of
// the element's `data-wiz-on-EVENT` attribute (a handler index from `Loom.render`), and
// `payload` is the rest of the string. The payload is how a pure `step` can see what a
// control holds: a form control's live `value` for `input`/`change`, the key for
// `keydown`/`keyup` (with its modifiers after a newline — `Enter\nc` — when there are
// any), and nothing for the other events. It is the *rest* of the string, so a
// textarea's newlines arrive intact; Wiz parses it with `Loom.splitEvent` and an app that
// uses it is a `Loom.LiveApp` (`update msg payload state`).
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
import { decideAdopt } from "./adopt.js";

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
//
// A keydown/keyup carries its modifiers after a newline — `Enter\nc` for Ctrl+Enter,
// `s\ncm` for ⌘+S — because the keyboard policy (`Page.consume`) must not run a program
// on a bare Enter or save on a bare `s`. When the event's target is a text field, the
// selection follows on another line as `@start@end` (UTF-16), so the runtime can indent
// a selection; a key is never a newline and `@` is not a modifier, so the format is
// unambiguous. With no modifier and no selection the payload is the key alone, as before.
const MOD_SEP = "\n";
export function payloadOf(type, e) {
  const target = e && e.target;
  if (type === "input" || type === "change") {
    if (target && typeof target.value === "string") return target.value;
    if (target && typeof target.getAttribute === "function") return target.getAttribute("value") || "";
    return "";
  }
  if (type === "keydown" || type === "keyup") {
    const key = e && typeof e.key === "string" ? e.key : "";
    const mods = (e && e.ctrlKey ? "c" : "") + (e && e.metaKey ? "m" : "") +
      (e && e.shiftKey ? "s" : "") + (e && e.altKey ? "a" : "");
    let selection = "";
    if (target && typeof target.selectionStart === "number") {
      const start = Math.max(0, Math.trunc(target.selectionStart));
      const end = typeof target.selectionEnd === "number" ? Math.max(start, Math.trunc(target.selectionEnd)) : start;
      selection = MOD_SEP + "@" + start + "@" + end;
    }
    if (!mods && !selection) return key;
    return key + MOD_SEP + mods + selection;
  }
  return "";
}

// Load `wasm` (Emscripten's MODULARIZE module), mount `wiz_loom_html`'s output into
// `root`, and wire events. `events` limits the delegated event types; `parse` is the
// HTML parser (the browser's by default, `minidom.mjs`'s in a test); `onStep(state,
// event, index, payload)` sees every step after it happened (a page's effect hook).
//
// `adopt` decides whether the container's `data-wiz-*` attributes describe a
// server-rendered island whose hash matches this runtime's first render. Equal -> adopt
// (keep every node, attach the listeners); unequal/absent -> replace through
// `runtime.js` (the pre-adopt behaviour). `warn` receives the one replace warning.
export function start(wasm, root, { events, parse, onStep, adopt = true, warn } = {}) {
  let state = wasm._wiz_loom_init();
  // An exported function *consumes* its argument (the C ABI's ownership rule, stage 9g):
  // the SSR call only reads the state, so take an extra reference for it and keep ours.
  const html = () => {
    if (typeof wasm._wiz_retain === "function") {
      wasm._wiz_retain(typeof state === "bigint" ? state : big(state));
    }
    return takeString(wasm, wasm._wiz_loom_html(state));
  };
  // The runtime may export its own SSR hash (`wiz_loom_ssr_hash`), so the client does
  // not have to hash `html` in JS. Read-only, the same extra reference as `html`; absent
  // -> the host hashes the string (`adopt.js`).
  const ssrHash = () => {
    if (typeof wasm._wiz_loom_ssr_hash !== "function") return null;
    if (typeof wasm._wiz_retain === "function") {
      wasm._wiz_retain(typeof state === "bigint" ? state : big(state));
    }
    return takeString(wasm, wasm._wiz_loom_ssr_hash(state));
  };
  // The pending effect requests, as the runtime serialized them (`wiz_loom_requests`,
  // an optional export: a runtime with no effects does not have it). Read-only, so the
  // same extra reference as `html`.
  const requests = () => {
    if (typeof wasm._wiz_loom_requests !== "function") return "";
    if (typeof wasm._wiz_retain === "function") {
      wasm._wiz_retain(typeof state === "bigint" ? state : big(state));
    }
    return takeString(wasm, wasm._wiz_loom_requests(state));
  };
  const first = html();
  const decision = adopt
    ? decideAdopt({ root, html: first, runtimeHash: ssrHash(),
      warn: typeof warn === "function" ? warn : (m) => console.warn(m) })
    : { mode: "replace", reason: "adopt-disabled", hash: null };
  if (decision.mode === "replace") mount(root, first, parse);
  globalThis.wizPatch = (json) => applyPatches(root, JSON.parse(json), parse);
  let lastPayload = "";
  // `Loom.onPrevent`: after a handled event, the runtime's `wiz_loom_consume` says
  // whether it consumed the default action. A runtime without the export keeps the old
  // rule (a handler that asked decides: prevent).
  const consume = (event, index) => {
    if (typeof wasm._wiz_loom_consume !== "function") return true;
    if (typeof wasm._wiz_retain === "function") {
      wasm._wiz_retain(typeof state === "bigint" ? state : big(state));
    }
    const p = wasm.stringToNewUTF8(event + "\n" + index + "\n" + lastPayload);
    const answer = Number(wasm._wiz_loom_consume(state, big(p)));
    wasm._free(p);
    return answer !== 0;
  };
  delegate(root, (event, index, e) => {
    const payload = payloadOf(event, e);
    lastPayload = payload;
    const p = wasm.stringToNewUTF8(event + "\n" + index + "\n" + payload);
    state = wasm._wiz_loom_step(state, big(p));
    wasm._free(p);
    if (typeof onStep === "function") onStep(state, event, index, payload);
    return true;   // a handled event does not also submit a form or follow a link
  }, events, consume);
  return {
    state: () => state,
    // A page that changed the state through an entry point of its own (the playground's
    // effects, which patch the DOM themselves) hands it back here, so the next DOM event
    // steps from it.
    setState: (next) => { state = next; },
    html,
    requests,
    // The adopt decision (see `adopt.js`): `mode` is "adopt" or "replace", `hash` is the
    // client's SSR hash and `reason` says why a replace happened.
    mode: decision.mode,
    adopted: decision.mode === "adopt",
    ssrHash: decision.hash,
    decision,
  };
}
