// (11ab) The static playground's page half: load the Wasm module web/build-playground.sh
// built (the self-hosted Wiz frontend), hand the editor's text to its export
// `wiz_playground_eval : String → String`, and show the lines it returns. There is no
// server and nothing to install: the module is the checker.
//
// `?ui=react` renders the right-hand pane with the repo's React-style framework
// (web/playground-react.js + web/framework/driver.js) instead of building its DOM nodes
// here. The textarea, its squiggles/completions, the header, the Run button and the
// footer stay imperative on both paths; without the flag nothing changes.
"use strict";
import { isValue, renderValue } from "./playground-values.js";
import { startInfoview } from "./playground-lsp.js";
import { wantsSelfhost, selfhostEndpoint, withPrelude as preludeOf } from "./selfhost-lsp-shim.js";
import { createEngine, failureLines } from "./playground-engine.js";
import { createPageUi } from "./playground-react.js";

const params = new URLSearchParams(typeof location !== "undefined" ? location.search : "");
const reactMode = params.get("ui") === "react";

const editor = document.getElementById("editor");
const runButton = document.getElementById("run");
const output = document.getElementById("output");
const status = document.getElementById("status");
const count = document.getElementById("count");
const engine = document.getElementById("engine");
const sideUi = document.getElementById("side-ui");
const sideDom = document.getElementById("side-dom");

// The Goals pane's element: the page's own div, or under `?ui=react` a detached one whose
// HTML the React model carries into the tree (the pane keeps web/goals.js's rendering).
const goalsPanel = reactMode ? document.createElement("div") : document.getElementById("goals");
let pageUi = null;        // the React pane's handle, once its module has loaded
let lastOutput = null;    // the last `show` text, re-applied when the React pane appears

let wasm = null;   // web/playground-engine.js: every call guarded; only a trap/OOM restarts it
let busy = false;

function setStatus(text, kind) {
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
// it existed. Both reject with an `EngineFailure` when the program exits (the module is
// kept), aborts or traps (the module is replaced).
const evalSource = (src) => wasm.evaluate(src);
const checkSource = (src) => wasm.check(src);

// An output line's class and the text to show. A value the page can render (a Nat, a
// Bool, a list) shows its rendered form; the raw text is in the DOM path's title.
function lineSpec(text) {
  if (text.startsWith("error:") || text.startsWith("parse error")) return { kind: "err", text };
  if (isValue(text)) {
    const shown = renderValue(text);
    return shown === null ? { kind: "raw", text } : { kind: "val", text: shown };
  }
  return { kind: "", text };
}

function line(text) {
  const el = document.createElement("div");
  el.className = "line";
  el.textContent = text;
  const spec = lineSpec(text);
  if (spec.kind === "err") el.classList.add("err");
  else if (spec.kind === "val" || spec.kind === "raw") {
    el.classList.add("val");
    el.title = text;
    if (spec.kind === "val") el.textContent = spec.text;
    else el.classList.add("raw");
  }
  return el;
}

function show(text) {
  lastOutput = text;
  const lines = text.split("\n").filter((l) => l !== "");
  const bad = lines.filter((l) => l.startsWith("error:") || l.startsWith("parse error")).length;
  const label = lines.length + (lines.length === 1 ? " line" : " lines") +
    (bad ? ` · ${bad} error${bad === 1 ? "" : "s"}` : "");
  // Under `?ui=react` the count is part of the React pane (its Output head) rather than
  // the line under the editor, so it is not drawn twice.
  if (!pageUi) count.textContent = label;
  if (pageUi) {
    // The React pane owns the output's nodes; the Wiz view escapes every line's text.
    pageUi.update({ count: label, lines: lines.map(lineSpec) });
    return bad;
  }
  output.replaceChildren();
  for (const t of lines) output.appendChild(line(t));
  return bad;
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
        // The failure's stderr lines are normal `error:` lines; `show` also keeps the
        // `?ui=react` pane in step with them.
        show(failureLines(e).join("\n"));
        if (!pageUi) count.textContent = e.kind === "exit" ? `exit code ${e.code}` : e.kind;
      } else show("error: " + (e && e.message ? e.message : String(e)));
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

// Under `?ui=react` the pane's HTML is mirrored into the React model after every render.
function syncGoals() {
  if (pageUi) pageUi.update({ goals: goalsPanel.innerHTML });
}

const selfhost = typeof location !== "undefined" && wantsSelfhost(location.search)
  ? selfhostEndpoint({
    evaluate: (src) => engineLoaded.then(() => evalSource(src)),
    check: (src) => engineLoaded.then(() => checkSource(src)),
  })
  : undefined;
startInfoview({
  editor,
  panel: goalsPanel,
  config: selfhost,
  onRender: syncGoals,
  // Under `?ui=react` the panel's markup lives in the live tree (#side-ui), so its
  // clicks and arrow keys are delegated to the pane, not to the detached panel. That
  // also keeps the DOM path working if the React module fails to load: #side-dom is
  // still inside `.side`.
  eventsFrom: reactMode ? document.querySelector(".side") : undefined,
});

// `?ui=react`: load the small UI module (web/playground-ui.wiz → wiz-playground-ui.mjs)
// and hand the pane to the React driver. A missing or broken module is not fatal: the
// page falls back to the DOM pane it always had.
async function startReactPane() {
  if (!reactMode || !sideUi || !sideDom) return;
  try {
    const createUi = (await import("./wiz-playground-ui.mjs")).default;
    const uiWasm = await createUi({ printErr: (s) => console.warn(s) });
    const page = createPageUi({
      wasm: uiWasm,
      root: sideUi,
      model: { count: "", lines: [], goals: goalsPanel.innerHTML },
    });
    if (!page) throw new Error("the UI module has no wiz_ui_html export");
    pageUi = page;
    // One pane at a time: removing the DOM copy also keeps the ids unique.
    if (sideDom.parentNode) sideDom.parentNode.removeChild(sideDom);
    sideUi.hidden = false;
    show(lastOutput === null ? "" : lastOutput);
    syncGoals();
  } catch (e) {
    pageUi = null;
    if (sideUi.parentNode) sideUi.parentNode.removeChild(sideUi);
    console.warn("?ui=react unavailable, using the DOM pane: " + (e && e.message ? e.message : String(e)));
  }
}

async function start() {
  setStatus("loading the engine…", "running");
  startReactPane();
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
    if (!output.childElementCount) run();
    else setStatus("ready", "ready");
  } catch (e) {
    engine.textContent = "engine: failed";
    engineReady.reject(e);
    setStatus("the engine did not load: " + (e && e.message ? e.message : String(e)), "error");
    show("error: " + (e && e.message ? e.message : String(e)));
  }
}

start();
