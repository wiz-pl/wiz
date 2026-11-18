// (11ab) The static playground's page half: load the Wasm module web/build-playground.sh
// built (the self-hosted Wiz frontend), hand the editor's text to its export
// `wiz_playground_eval : String → String`, and show the lines it returns. There is no
// server and nothing to install: the module is the checker.
//
// `?ui=loom` mounts the page itself from a second Wasm module
// (`web/build-playground-ui.wiz` → `wiz-playground-ui.mjs`): the whole page is one Loom
// app (`web/playground-ui.wiz`), and this file only loads the engine and turns its
// results into the app's states. The default is the static markup the page carries; the
// Loom path falls back to it when the module is not built, and it is the only path that
// can move the page's text into a Loom component.
"use strict";
import { isValue, renderValue } from "./playground-values.js";
import { startInfoview } from "./playground-lsp.js";
import { wantsSelfhost, selfhostEndpoint, withPrelude as preludeOf } from "./selfhost-lsp-shim.js";
import { createEngine, failureLines } from "./playground-engine.js";

const params = new URLSearchParams(typeof location !== "undefined" ? location.search : "");
const useLoom = params.get("ui") === "loom";

// The page's elements: the static markup's at load, or the Loom app's after it mounts.
let editor = null;
let runButton = null;
let output = null;
let status = null;
let count = null;
let engineEl = null;

// The Loom UI instance (`?ui=loom`), driver's handle and its state marshalling.
let ui = null;
let app = null;

let wasm = null;   // web/playground-engine.js: every call guarded; only a trap/OOM restarts it
let busy = false;

const big = (x) => (typeof x === "bigint" ? x : BigInt(x));   // wasm64: pointers are i64

// Call one of the UI module's `wiz_loom_*` entry points: the state first, then strings
// (allocated here and freed after) and numbers. The app patches the page itself
// (`js_patch`), so the page only keeps the returned state.
function uiCall(name, ...args) {
  if (!ui || !app) return null;
  const pointers = [];
  const rest = args.map((a) => {
    if (typeof a === "string") {
      const p = ui.stringToNewUTF8(a);
      pointers.push(p);
      return big(p);
    }
    return typeof a === "number" ? big(a) : a;
  });
  try {
    const next = ui["_" + name](app.state(), ...rest);
    app.setState(next);
    return next;
  } finally {
    for (const p of pointers) ui._free(p);
  }
}

// The UI's getters are not exported: an exported call consumes the state it is given
// (driver.js's ownership note), so the page computes what it needs from the text it
// already has (the error count for the status kind) and keeps the app's state.

function setStatus(text, kind) {
  if (ui) { uiCall("wiz_loom_status", text, kind || ""); return; }
  status.textContent = text;
  status.className = "status " + (kind || "");
}

function setEnabled(on) {
  if (ui) { uiCall("wiz_loom_enable", on ? 1 : 0); return; }
  runButton.disabled = !on;
}

function setEngine(text) {
  if (ui) { uiCall("wiz_loom_engine", text); return; }
  engineEl.textContent = text;
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
// it existed. Both reject with an `EngineFailure` when the program exits (the module is
// kept), aborts or traps (the module is replaced).
const evalSource = (src) => wasm.evaluate(src);
const checkSource = (src) => wasm.check(src);

// ## The static page's output pane (the Loom app renders its own)

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

// Show a run's output. Returns how many lines are errors (the status kind; the app owns
// the `#count` text and the classes).
function show(text) {
  if (ui) {
    uiCall("wiz_loom_show", text);
  } else {
    output.replaceChildren();
    const lines = text.split("\n").filter((l) => l !== "");
    for (const t of lines) output.appendChild(line(t));
    const bad = lines.filter((l) => l.startsWith("error:") || l.startsWith("parse error")).length;
    count.textContent = lines.length + (lines.length === 1 ? " line" : " lines") +
      (bad ? ` · ${bad} error${bad === 1 ? "" : "s"}` : "");
  }
  return text.split("\n").filter((l) => l !== "")
    .filter((l) => l.startsWith("error:") || l.startsWith("parse error")).length;
}

// An engine exit, abort or trap: the lines it printed, then what happened.
function showFailure(e) {
  const lines = failureLines(e);
  const countText = e.kind === "exit" ? `exit code ${e.code}` : e.kind;
  if (ui) { uiCall("wiz_loom_fail", lines.join("\n"), countText); return; }
  output.replaceChildren(...lines.map(line));
  count.textContent = countText;
}

function run() {
  if (!wasm || busy) return;
  busy = true;
  setEnabled(false);
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
      if (e && e.name === "EngineFailure") showFailure(e);
      else show("error: " + (e && e.message ? e.message : String(e)));
      setStatus("failed", "error");
    } finally {
      busy = false;
      setEnabled(true);
    }
  }, 0);
}

// ## The goals pane (independent of the Wasm engine)

// By default it is the in-page server (web/selfhost-lsp-shim.js): the same Wasm engine
// answers the pane, so there is nothing to start, and it waits for the engine to load.
// `?lsp=ws://host:port` switches it to the external language client
// (web/playground-lsp.js), and `?lsp=off` (or none/0/false) leaves the pane with no
// server; a failed connection is the same as no server.
let engineReady;
const engineLoaded = new Promise((resolve, reject) => { engineReady = { resolve, reject }; });
engineLoaded.catch(() => { /* reported by start(); the shim reports it again */ });
const selfhost = typeof location !== "undefined" && wantsSelfhost(location.search)
  ? selfhostEndpoint({
    evaluate: (src) => engineLoaded.then(() => evalSource(src)),
    check: (src) => engineLoaded.then(() => checkSource(src)),
  })
  : undefined;

function wireGoals() {
  startInfoview({ editor, panel: document.getElementById("goals"), config: selfhost });
}

// ## Mounting the page

// Mount the Loom app on `body` and return true, or leave the static markup in place and
// return false (the module is not built, or its ABI is not what the driver expects).
async function mountLoom() {
  try {
    const createModule = (await import("./wiz-playground-ui.mjs")).default;
    ui = await createModule({ print: (s) => console.log(s), printErr: (s) => console.warn(s) });
    // A cheap ABI probe before anything is removed from the page: the SSR has to come
    // back as a string, or the static page stays.
    const probe = ui._wiz_loom_init();
    ui._free(ui._wiz_loom_html(probe));
    const { start: startLoom } = await import("./framework/driver.js");
    app = startLoom(ui, document.body, { events: ["click", "input"] });
    return true;
  } catch (e) {
    console.warn("wiz playground: using the static page: " +
      (e && e.message ? e.message : String(e)));
    ui = null;
    app = null;
    return false;
  }
}

function wireEditor() {
  editor = document.getElementById("editor");
  runButton = document.getElementById("run");
  status = document.getElementById("status");
  output = document.getElementById("output");
  count = document.getElementById("count");
  engineEl = document.getElementById("engine");

  runButton.addEventListener("click", run);
  editor.addEventListener("keydown", (e) => {
    if (e.key === "Enter" && (e.ctrlKey || e.metaKey)) {
      e.preventDefault();
      run();
    }
  });
}

async function start() {
  // `?ui=loom`: the page is the Loom app; otherwise the static markup stays.
  if (useLoom) await mountLoom();
  wireEditor();
  wireGoals();

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
    setEngine("engine: ready");
    engineReady.resolve();
    setEnabled(true);
    if (!output.childElementCount) run();
    else setStatus("ready", "ready");
  } catch (e) {
    setEngine("engine: failed");
    engineReady.reject(e);
    setStatus("the engine did not load: " + (e && e.message ? e.message : String(e)), "error");
    show("error: " + (e && e.message ? e.message : String(e)));
  }
}

start();
