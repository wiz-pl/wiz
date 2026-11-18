// (11ab) The static playground's page half: load the Wasm module web/build-playground.sh
// built (the self-hosted Wiz frontend), hand the editor's text to its export
// `wiz_playground_eval : String → String`, and show the lines it returns. There is no
// server and nothing to install: the module is the checker.
//
// `?ui=loom` renders the output pane and the status span from a second Wasm module
// (`wiz-playground-ui.mjs`, lib/Web/Playground.wiz as a Loom app). Each entry point
// takes the app's state by ownership and returns the next one; the page keeps the
// returned value and asks `wiz_loom_patches` for the DOM patches (the framework's
// `web/framework/runtime.js` applies them). The engine is a separate instance, so the
// guard in web/playground-engine.js can still drop and replace it after a trap, abort
// or out-of-memory without losing the page's state. The hand-written pane is the
// default and the fallback: with `?ui=loom` unset the page loads one module, as before.
"use strict";
import { isValue, renderValue } from "./playground-values.js";
import { startInfoview } from "./playground-lsp.js";
import { wantsSelfhost, selfhostEndpoint, withPrelude as preludeOf } from "./selfhost-lsp-shim.js";
import { createEngine, failureLines } from "./playground-engine.js";

const params = new URLSearchParams(typeof location !== "undefined" ? location.search : "");
const useLoom = params.get("ui") === "loom";

const editor = document.getElementById("editor");
const runButton = document.getElementById("run");
const output = document.getElementById("output");
const status = document.getElementById("status");
const count = document.getElementById("count");
const engine = document.getElementById("engine");

let wasm = null;   // web/playground-engine.js: every call guarded; replaced after a trap
let busy = false;

// The Loom UI (`?ui=loom`): its own module and instance, the app's state (owned by the
// page), the host element its tree is mounted into, and the patch applier.
let ui = null;
let uiState = null;
let uiRoot = null;
let applyLoom = null;

const big = (x) => (typeof x === "bigint" ? x : BigInt(x));   // wasm64: pointers are i64

function takeString(m, p) {
  if (!p) return "";
  const s = m.UTF8ToString(Number(p));
  m._free(p);
  return s;
}

const isErrLine = (l) => l.startsWith("error:") || l.startsWith("parse error");

// The page's `setStatus(text, kind)`.
function setStatus(text, kind) {
  if (ui) { uiStatus(text, kind || ""); return; }
  status.textContent = text;
  status.className = "status " + (kind || "");
}

// The engine has the self-hosted frontend's embedded Prelude; a source without an
// import gets it, so `Nat`, `Bool`, lists, … are in scope as in `wiz check`. (The rule
// lives in the shim, which moves diagnostics back across the added lines.)
function withPrelude(text) {
  return preludeOf(text).source;
}

// `wiz_playground_eval` on a source: the module's one call, shared by Run and the
// in-page language server. (stage 1) `wiz_playground_check`: the same check as JSON with
// each line's offset, for the in-page language server; null with a module built before
// it existed. Both reject with an `EngineFailure` when the module exits, aborts or traps.
const evalSource = (src) => wasm.evaluate(src);
const checkSource = (src) => wasm.check(src);

// ## The hand-written pane (the default; `?ui=loom` renders it from Wiz instead)

function line(text) {
  const el = document.createElement("div");
  el.className = "line";
  el.textContent = text;
  if (text.startsWith("error:") || text.startsWith("parse error")) {
    el.classList.add("err");
  } else if (isValue(text)) {
    el.classList.add("val");
    el.title = text;
    const shown = renderValue(text);
    if (shown !== null) el.textContent = shown;
    else el.classList.add("raw");
  }
  return el;
}

// The `#count` text (the page computes it from the text, as the app's state is opaque).
function countText(n, bad) {
  return n + (n === 1 ? " line" : " lines") + (bad ? ` · ${bad} error${bad === 1 ? "" : "s"}` : "");
}

// Show a run's output. Returns how many lines are errors (the status kind).
function show(text) {
  const lines = text.split("\n").filter((l) => l !== "");
  const bad = lines.filter(isErrLine).length;
  if (ui) uiShow(text);
  else {
    output.replaceChildren();
    for (const t of lines) output.appendChild(line(t));
  }
  count.textContent = countText(lines.length, bad);
  return bad;
}

// ## The Loom pane (`?ui=loom`)

// Call one of the UI module's `wiz_loom_*` entry points. The state is the first
// argument and is *consumed* (stage 9g's C ABI); strings are borrowed here and freed
// after the call, and a returned string must be freed by the caller.
function uiCall(name, ...args) {
  const pointers = [];
  const rest = args.map((a) => {
    if (typeof a === "string") { const p = ui.stringToNewUTF8(a); pointers.push(p); return big(p); }
    return typeof a === "number" ? big(a) : a;
  });
  try {
    return ui["_" + name](uiState, ...rest);
  } finally {
    for (const p of pointers) ui._free(big(p));
  }
}

// Before an entry point consumes the page's state, take the extra reference the diff
// needs: `wiz_loom_patches` consumes both of its arguments, and it needs the old state
// after the producing call has taken the page's one.
function loomHold() {
  ui._wiz_retain(big(uiState));
}

// Give the page the state `next` (one reference, from the entry point that made it) and
// patch the mounted tree from the old state (one reference, held by `loomHold`).
function loomAdvance(next) {
  ui._wiz_retain(big(next));   // the diff consumes it; the page keeps one
  const json = takeString(ui, ui._wiz_loom_patches(uiState, next));
  uiState = next;
  applyLoom(json);
}

function uiShow(text) {
  loomHold();
  loomAdvance(uiCall("wiz_loom_show", text));
}

function uiFail(text, countLabel) {
  loomHold();
  loomAdvance(uiCall("wiz_loom_fail", text, countLabel));
}

function uiStatus(text, kind) {
  loomHold();
  loomAdvance(uiCall("wiz_loom_status", text, kind));
}

// Mount the Loom app on a host in place of `#output`. Returns true, or leaves the
// hand-written page alone and returns false (the module is not built, or its ABI is not
// what this page expects). Nothing is removed from the page until the SSR has come
// back, so a missing module is a fallback and not a broken page.
async function mountLoom() {
  try {
    const createModule = (await import("./wiz-playground-ui.mjs")).default;
    const module = await createModule({
      print: (s) => console.log(s),
      printErr: (s) => console.warn(s),
    });
    // The first paint: `wiz_loom_html` only reads the state, so retain it first.
    let state = module._wiz_loom_init();
    module._wiz_retain(big(state));
    const html = takeString(module, module._wiz_loom_html(state));
    // (the SSR call consumed the extra reference; `state` is still the page's)
    if (typeof html !== "string" || !html.includes('id="output"')) {
      throw new Error("wiz_loom_html did not return the pane");
    }
    const { mount, applyPatches } = await import("./framework/runtime.js");
    uiRoot = document.createElement("div");
    uiRoot.className = "loom-ui";
    output.replaceWith(uiRoot);
    mount(uiRoot, html);
    // The app owns the status span now (the one it just rendered).
    status.remove();
    ui = module;
    uiState = state;
    applyLoom = (json) => applyPatches(uiRoot, JSON.parse(json));
    return true;
  } catch (e) {
    console.warn("wiz playground: using the hand-written pane: " +
      (e && e.message ? e.message : String(e)));
    ui = null;
    uiState = null;
    uiRoot = null;
    applyLoom = null;
    return false;
  }
}

function run() {
  if (!wasm || busy) return;
  busy = true;
  runButton.disabled = true;
  setStatus("running…", "running");
  // let the status paint before the (synchronous) Wasm call
  setTimeout(async () => {
    const started = performance.now();
    try {
      const text = await evalSource(withPrelude(editor.value));
      const ms = Math.max(0, performance.now() - started);
      const bad = show(text);
      setStatus(`done in ${ms < 10 ? "<10" : Math.round(ms)} ms`, bad ? "error" : "ready");
    } catch (e) {
      if (e && e.name === "EngineFailure") {
        const lines = failureLines(e);
        const label = e.kind === "exit" ? `exit code ${e.code}` : e.kind;
        if (ui) uiFail(lines.join("\n"), label);
        else {
          output.replaceChildren(...lines.map(line));
          count.textContent = label;
        }
      } else {
        const text = "error: " + (e && e.message ? e.message : String(e));
        if (ui) uiShow(text);
        else output.replaceChildren(line(text));
      }
      setStatus("failed", "error");
    } finally {
      busy = false;
      runButton.disabled = false;
    }
  }, 0);
}

runButton.addEventListener("click", run);
editor.addEventListener("keydown", (e) => {
  if (e.key === "Enter" && (e.ctrlKey || e.metaKey)) {
    e.preventDefault();
    run();
  }
});

// The goals pane is independent of the Wasm engine. By default it is the in-page server
// (web/selfhost-lsp-shim.js): the same Wasm engine answers the pane, so there is nothing
// to start, and it waits for the engine to load. `?lsp=ws://host:port` switches it to the
// external language client (web/playground-lsp.js), and `?lsp=off` (or none/0/false)
// leaves the pane with no server; a failed connection is the same as no server.
let engineReady;
const engineLoaded = new Promise((resolve, reject) => { engineReady = { resolve, reject }; });
engineLoaded.catch(() => { /* reported by start(); the shim reports it again */ });
const selfhost = typeof location !== "undefined" && wantsSelfhost(location.search)
  ? selfhostEndpoint({
    evaluate: (src) => engineLoaded.then(() => evalSource(src)),
    check: (src) => engineLoaded.then(() => checkSource(src)),
  })
  : undefined;
startInfoview({ editor, panel: document.getElementById("goals"), config: selfhost });

async function start() {
  // `?ui=loom`: the pane comes from the UI module; otherwise the static markup stays.
  if (useLoom) await mountLoom();
  setStatus("loading the engine…", "running");
  try {
    const createModule = (await import("./wiz-playground.mjs")).default;
    const engine = createEngine(createModule, {
      print: (s) => console.log(s),
      printErr: (s) => console.warn(s),
      onRestart: (f) => console.warn("wiz playground: restarting the engine: " + f.message),
    });
    await engine.ready;
    wasm = engine;
    engine.textContent = "engine: ready";
    engineReady.resolve();
    runButton.disabled = false;
    if (ui || !output.childElementCount) run();
    else setStatus("ready", "ready");
  } catch (e) {
    engine.textContent = "engine: failed";
    engineReady.reject(e);
    setStatus("the engine did not load: " + (e && e.message ? e.message : String(e)), "error");
    if (ui) uiShow("error: " + (e && e.message ? e.message : String(e)));
    else output.replaceChildren(line("error: " + (e && e.message ? e.message : String(e))));
  }
}

start();
