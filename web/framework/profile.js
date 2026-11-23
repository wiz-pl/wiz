// The runtime seam: one interface over the two kinds of Loom runtime a page can mount.
//
// `mount` (mount.js) and the driver (driver.js) must not know which one they were given:
//
//   * a **Wasm** module — Emscripten's MODULARIZE instance of `wiz build --target wasm`,
//     with `_wiz_loom_init/_wiz_loom_html/_wiz_loom_step`, the state as an i64 `BigInt`,
//     strings as UTF-8 in linear memory, and ownership through `_wiz_retain`/`_free`;
//   * a **`--target js`** module — the ES module namespace `wiz build --target js` writes,
//     with `wiz_loom_init/_html/_step`, the state as a Wiz value (a JavaScript object the
//     host never inspects) and a string as a JavaScript string, because the module's
//     export wrapper marshals with the FFI table (`wizCallExport`). There is no memory, no
//     reference count and no i64 state here.
//
// `profile(module)` turns either into
//
//     { kind, module, present, init, html, step, requests, consume, ssrHash, call, ask,
//       stringOf }
//
// Every member is synchronous and speaks host values: `init`/`step`/`call` hand back the
// runtime's own state value (whatever it is), `html`/`requests`/`ssrHash`/`ask` hand back
// a JavaScript string, and `consume` a boolean. A page that needs to read a string out of
// a runtime value uses `stringOf` (a Wasm pointer or a Wiz `String` in, a JS string out).
//
// The Wasm branch is exactly the code `driver.js` ran before this file existed, moved and
// unchanged — the framework's Node tests (`driver_test.mjs`, `mount_test.mjs`) and the
// page tests are the regression oracle for it. A `profile` is a profile: calling
// `profile(p)` on one returns it, so `mount` can build it once and hand it to `start`.

"use strict";

const big = (x) => (typeof x === "bigint" ? x : BigInt(x));   // wasm64: pointers are i64

// Take an owned UTF-8 string out of the module (the module allocated it; free it after
// copying).
function takeString(wasm, p) {
  if (!p) return "";
  const s = wasm.UTF8ToString(Number(p));
  wasm._free(p);
  return s;
}

// The three exports every runtime must have (`wiz_loom_init` returns a state,
// `wiz_loom_html` its SSR, `wiz_loom_step` the state after one event string).
export const REQUIRED = ["wiz_loom_init", "wiz_loom_html", "wiz_loom_step"];

// Is this a Wasm instance (the shape an Emscripten module has)? A `--target js` module
// has no leading-underscore exports, so the two cannot be confused.
export function isWasm(m) {
  return !!m && typeof m._wiz_loom_init === "function";
}

// Is this a `--target js` module namespace (or anything else with the bare ABI names)?
export function isJs(m) {
  return !!m && typeof m.wiz_loom_init === "function";
}

// "wasm", "js", or null when this is neither.
export function kindOf(m) {
  if (isWasm(m)) return "wasm";
  if (isJs(m)) return "js";
  return null;
}

// Does `m` have the whole ABI for its kind? (A module with only some of it is refused
// before the page is touched, so it cannot half-render one.)
export function hasABI(m) {
  const kind = kindOf(m);
  if (kind === null) return false;
  const p = kind === "wasm" ? "_" : "";
  return REQUIRED.every((name) => typeof m[p + name] === "function");
}

// Is this already a profile (rather than a module)?
function isProfile(m) {
  return !!m && typeof m.kind === "string" && typeof m.init === "function" &&
    typeof m.step === "function" && typeof m.call === "function";
}

// A Wasm instance: `_` names, i64 state, linear-memory strings, retain/free ownership.
function wasmProfile(wasm) {
  const fn = (name) => wasm["_" + name];
  const present = (name) => typeof fn(name) === "function";
  // An exported function *consumes* its argument (the C ABI's ownership rule, stage 9g):
  // a call that only reads the state takes an extra reference and keeps ours.
  const retain = (state) => {
    if (typeof wasm._wiz_retain === "function") {
      wasm._wiz_retain(typeof state === "bigint" ? state : big(state));
    }
  };
  const readString = (name, state) => {
    retain(state);
    return takeString(wasm, fn(name)(state));
  };
  // The strings a call allocates in the module's memory, and the wasm64 arguments.
  const marshal = (args) => {
    const pointers = [];
    const rest = args.map((a) => {
      if (typeof a === "string") {
        const p = wasm.stringToNewUTF8(a);
        pointers.push(p);
        return big(p);
      }
      return typeof a === "number" ? big(a) : a;
    });
    return [rest, pointers];
  };
  return {
    kind: "wasm",
    module: wasm,
    present,
    init: () => wasm._wiz_loom_init(),
    html: (state) => readString("wiz_loom_html", state),
    // The runtime's own SSR hash (over the normalised tree) when it exports one; the
    // caller hashes the exact string otherwise.
    ssrHash: (state) => (present("wiz_loom_ssr_hash") ? readString("wiz_loom_ssr_hash", state) : null),
    requests: (state) => (present("wiz_loom_requests") ? readString("wiz_loom_requests", state) : ""),
    consume: (state, event) => {
      if (!present("wiz_loom_consume")) return true;   // the old rule: a handler that asked decides
      retain(state);
      const p = wasm.stringToNewUTF8(event);
      try {
        return Number(fn("wiz_loom_consume")(state, big(p))) !== 0;
      } finally {
        wasm._free(p);
      }
    },
    step: (state, event) => {
      const p = wasm.stringToNewUTF8(event);
      try {
        return fn("wiz_loom_step")(state, big(p));
      } finally {
        wasm._free(p);
      }
    },
    call: (state, name, args) => {
      if (!present(name)) throw new TypeError("mount: the runtime has no " + name);
      const [rest, pointers] = marshal(args);
      try {
        return fn(name)(state, ...rest);
      } finally {
        for (const p of pointers) wasm._free(p);
      }
    },
    ask: (name, args) => {
      if (!present(name)) throw new TypeError("mount: the runtime has no " + name);
      const [rest, pointers] = marshal(args);
      try {
        return takeString(wasm, fn(name)(...rest));
      } finally {
        for (const p of pointers) wasm._free(p);
      }
    },
    stringOf: (v) => String(v),
  };
}

// A `--target js` module namespace: bare names, the state is a Wiz value, a string is a
// JavaScript string (the export wrapper already marshalled it), and there is nothing to
// retain or free.
function jsProfile(ns) {
  const fn = (name) => ns[name];
  const present = (name) => typeof fn(name) === "function";
  // The module's export wrapper converts with the FFI table, so a `String` result is
  // already a JS string; a `w` result that is still a Wiz `String` is converted by the
  // module's own runtime. (No other case can reach here: an export's kinds are
  // `n u f s b v p w`.)
  const str = (v) => (typeof v === "string" ? v
    : (typeof ns.wizStringToJs === "function" ? ns.wizStringToJs(v) : String(v)));
  return {
    kind: "js",
    module: ns,
    present,
    init: () => ns.wiz_loom_init(),
    html: (state) => str(ns.wiz_loom_html(state)),
    ssrHash: (state) => (present("wiz_loom_ssr_hash") ? str(ns.wiz_loom_ssr_hash(state)) : null),
    requests: (state) => (present("wiz_loom_requests") ? str(ns.wiz_loom_requests(state)) : ""),
    consume: (state, event) => (present("wiz_loom_consume")
      ? Number(ns.wiz_loom_consume(state, event)) !== 0
      : true),
    step: (state, event) => ns.wiz_loom_step(state, event),
    call: (state, name, args) => {
      if (!present(name)) throw new TypeError("mount: the runtime has no " + name);
      return fn(name)(state, ...args);
    },
    ask: (name, args) => {
      if (!present(name)) throw new TypeError("mount: the runtime has no " + name);
      return str(fn(name)(...args));
    },
    stringOf: str,
  };
}

// Normalise a runtime module (or an existing profile) to the interface above. A module
// with the wrong shape is refused here, before anything is rendered.
export function profile(module) {
  if (isProfile(module)) return module;
  const kind = kindOf(module);
  if (kind === null) {
    throw new TypeError(
      "runtime: neither a Wasm instance (_wiz_loom_init) nor a JavaScript module (wiz_loom_init)");
  }
  if (!hasABI(module)) {
    throw new TypeError("runtime: does not export wiz_loom_init, wiz_loom_html and wiz_loom_step");
  }
  return kind === "wasm" ? wasmProfile(module) : jsProfile(module);
}
