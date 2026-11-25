// The page half for an app built from lib/Web/Loom.wiz, mirroring web/tagged.js's
// `stepper`: the Wiz module exports
//
//   wiz_loom_init     : State
//   wiz_loom_html     : State -> String          (SSR of the current state)
//   wiz_loom_step     : State -> String -> State
//   wiz_step          : i32 -> i32 -> i32 -> i32 (the browser's step: state, payload ptr, len)
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
// **The step crosses as three 32-bit words (`wiz-web/1`).** A module built for the
// browser also exports
//
//   wiz_step : (state : i32, payload_ptr : i32, payload_len : i32) -> i32
//
// (`web/step.c`, linked beside the app's own `wiz_loom_step`), and that is the entry
// `start` calls: the state goes in and comes back as the low 32 bits of the same handle,
// and the payload as an address and a byte length. The JavaScript API has no `Number`
// path for an `i64` parameter or result — each one is a `BigInt` — so the word form is
// what keeps an opaque pointer from costing two BigInt allocations per DOM event. The
// `i64` entry stays for the Node tests and for a module built before this ABI: `start`
// uses it when `wiz_step` is absent, and every *other* call (`html`, `consume`, …) stays
// on `i64`, so the state is normalised through `bigState()` at each of those.
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
// returns an owned value, so `state` is transferred to every `wiz_loom_step` (or the
// `wiz_step` word entry) and the new one is kept. A read-only call (`wiz_loom_html` for
// the first paint) cannot take that one reference: the module must export `wiz_retain`,
// and the driver takes an extra reference first. A page that calls its own `wiz_loom_*`
// entry points must do the same: pass the state, keep the returned one.
//
// It is the intended integration, not yet exercised by a Wasm build (no Emscripten on
// the machine where the prototype was written); web/framework/driver_test.mjs checks the
// event strings and the mount under Node with minidom.mjs.
"use strict";
import { applyPatches, delegate, mount } from "./runtime.js";
import { decideAdopt } from "./adopt.js";

const big = (x) => (typeof x === "bigint" ? x : BigInt(x));   // wasm64: pointers are i64

// The UTF-8 byte length of `s`, as Emscripten's `stringToNewUTF8` encodes it (a lone
// surrogate is written as U+FFFD, three bytes). `wiz_step` takes the payload's length as
// the ABI's third word, so this is computed without a `TextEncoder` (and without
// allocating) on every event.
export function utf8Length(s) {
  let n = 0;
  for (let i = 0; i < s.length; i++) {
    const c = s.charCodeAt(i);
    if (c < 0x80) n += 1;
    else if (c < 0x800) n += 2;
    else if (c >= 0xd800 && c <= 0xdbff && i + 1 < s.length) {
      const d = s.charCodeAt(i + 1);
      if (d >= 0xdc00 && d <= 0xdfff) { n += 4; i++; } else n += 3;
    } else n += 3;
  }
  return n;
}

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
  // The state is a Wiz value: a `BigInt` from an i64 entry, or — once a step has gone
  // through `wiz_step` — the low 32 bits of the same handle as an unsigned Number.
  // `bigState()` is the one conversion the i64 entries need; `words` says which step
  // entry this module has.
  const bigState = () => (typeof state === "bigint" ? state : big(state));
  const words = typeof wasm._wiz_step === "function";
  // An exported function *consumes* its argument (the C ABI's ownership rule, stage 9g):
  // the SSR call only reads the state, so take an extra reference for it and keep ours.
  const html = () => {
    if (typeof wasm._wiz_retain === "function") wasm._wiz_retain(bigState());
    return takeString(wasm, wasm._wiz_loom_html(bigState()));
  };
  // The runtime may export its own SSR hash (`wiz_loom_ssr_hash`), so the client does
  // not have to hash `html` in JS. The Wiz side hashes the **normalised tree**
  // (`Loom.ssrHash`: sorted attributes, collapsed white space, keys included, plus a
  // length/node-count witness), so an HTML formatting difference cannot force a replace.
  // Read-only, the same extra reference as `html`; absent -> the host hashes the exact
  // string (`adopt.js`).
  const ssrHash = () => {
    if (typeof wasm._wiz_loom_ssr_hash !== "function") return null;
    if (typeof wasm._wiz_retain === "function") wasm._wiz_retain(bigState());
    return takeString(wasm, wasm._wiz_loom_ssr_hash(bigState()));
  };
  // The pending effect requests, as the runtime serialized them (`wiz_loom_requests`,
  // an optional export: a runtime with no effects does not have it). Read-only, so the
  // same extra reference as `html`.
  const requests = () => {
    if (typeof wasm._wiz_loom_requests !== "function") return "";
    if (typeof wasm._wiz_retain === "function") wasm._wiz_retain(bigState());
    return takeString(wasm, wasm._wiz_loom_requests(bigState()));
  };
  const first = html();
  const decision = adopt
    ? decideAdopt({ root, html: first, runtimeHash: ssrHash(),
      warn: typeof warn === "function" ? warn : (m) => console.warn(m) })
    : { mode: "replace", reason: "adopt-disabled", hash: null };
  if (decision.mode === "replace") mount(root, first, parse);
  globalThis.wizPatch = (json) => applyPatches(root, JSON.parse(json), parse);
  // The JS-on reload: re-render the current state and replace the container. It is the
  // recovery path behind the wire's `resync` (a dropped/gapped batch is one full
  // replace, never a partial adopt), and the same primitive the first mount uses.
  const resync = () => { mount(root, html(), parse); return root; };
  globalThis.wizResync = resync;
  globalThis.wizLoomMode = decision.mode;
  let lastPayload = "";
  // `Loom.onPrevent`: after a handled event, the runtime's `wiz_loom_consume` says
  // whether it consumed the default action. A runtime without the export keeps the old
  // rule (a handler that asked decides: prevent).
  const consume = (event, index) => {
    if (typeof wasm._wiz_loom_consume !== "function") return true;
    if (typeof wasm._wiz_retain === "function") wasm._wiz_retain(bigState());
    const p = wasm.stringToNewUTF8(event + "\n" + index + "\n" + lastPayload);
    const answer = Number(wasm._wiz_loom_consume(bigState(), big(p)));
    wasm._free(p);
    return answer !== 0;
  };
  delegate(root, (event, index, e) => {
    const payload = payloadOf(event, e);
    lastPayload = payload;
    // The event string is the same for both entries; only the marshalling differs. The
    // word form passes the payload's address and byte length as Numbers, and normalises
    // the result: a Wasm `i32` arrives in JavaScript sign-extended, and the handle is
    // unsigned. The i64 form passes the owned pointer as a BigInt, as before.
    const text = event + "\n" + index + "\n" + payload;
    const p = wasm.stringToNewUTF8(text);
    try {
      state = words
        ? wasm._wiz_step(Number(state) >>> 0, Number(p) >>> 0, utf8Length(text)) >>> 0
        : wasm._wiz_loom_step(bigState(), big(p));
    } finally {
      wasm._free(p);
    }
    if (typeof onStep === "function") onStep(state, event, index, payload);
    return true;   // a handled event does not also submit a form or follow a link
  }, events, consume);
  return {
    state: () => state,
    // Which step entry this module has: "i32" (`wiz_step`, the browser ABI) or "i64"
    // (`wiz_loom_step`, the Node tests' stubs and modules built before it).
    abi: words ? "i32" : "i64",
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
    resync,
  };
}
