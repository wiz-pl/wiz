// The page half for an app built from lib/Web/React.wiz: web/framework/app.wiz is the
// Wiz half and defines exactly these exports (build it with `--no-main`):
//
//   wiz_react_init  : State                       (the initial state, like WSt.empty)
//   wiz_react_html  : State → String              (SSR of the current state)
//   wiz_react_step  : State → String → IO State   (the event string is "event\nindex")
//
// and calls the FFI `js_patch` (web/js.c) with `React.patchesJson` on every step; this
// file applies those patches and turns DOM events into step calls. `js_patch` is one
// page-global function, so the hook applies a patch to the root of the app whose step is
// running (`stepping`), not to whichever app was mounted last.
"use strict";
import { applyPatches, delegate, mount } from "./runtime.js";

// The exports a React app's module must define (web/framework/app.wiz does).
export const REACT_EXPORTS = ["wiz_react_init", "wiz_react_html", "wiz_react_step"];

const big = (x) => (typeof x === "bigint" ? x : BigInt(x));   // wasm64: pointers are i64

// The root whose `wiz_react_step` is running. `js_patch` is called synchronously from
// inside it and carries no root, so this is how the patch finds its page.
let stepping = null;

// One hook for every mounted app: it applies a patch to the stepping root, and anything
// outside a step still reaches whatever hook the page installed before us.
let pageHook = null;
let hookInstalled = false;
function installHook() {
  if (hookInstalled) return;
  pageHook = globalThis.wizPatch;
  globalThis.wizPatch = (json) => {
    if (stepping) applyPatches(stepping, JSON.parse(json));
    else if (pageHook) pageHook(json);
  };
  hookInstalled = true;
}

function takeString(wasm, p) {
  if (!p) return "";
  try {
    return wasm.UTF8ToString(Number(p));
  } finally {
    wasm._free(p);
  }
}

// Load `wasm` (Emscripten's MODULARIZE module), mount `wiz_react_html`'s output into
// `root`, and wire events. `events` limits the delegated event types.
export function start(wasm, root, { events } = {}) {
  for (const name of REACT_EXPORTS) {
    if (typeof wasm["_" + name] !== "function") {
      throw new Error("the module does not export `" + name + "`: a React page's Wiz half " +
        "defines all of " + REACT_EXPORTS.join(", ") + " (see web/framework/app.wiz)");
    }
  }
  let state = wasm._wiz_react_init();
  const html = () => takeString(wasm, wasm._wiz_react_html(state));
  mount(root, html());
  installHook();
  delegate(root, (event, index) => {
    const p = wasm.stringToNewUTF8(event + "\n" + index);
    const outer = stepping;
    try {
      stepping = root;
      state = wasm._wiz_react_step(state, big(p));
    } finally {
      stepping = outer;
      wasm._free(big(p));
    }
    return true;   // a handled event does not also submit a form or follow a link
  }, events);
  return { state: () => state, html };
}
