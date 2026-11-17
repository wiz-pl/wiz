// (11ab) The static playground's page half: load the Wasm module web/build-playground.sh
// built (the self-hosted Wiz frontend), hand the editor's text to its export
// `wiz_playground_eval : String → String`, and show the lines it returns. There is no
// server and nothing to install: the module is the checker.
"use strict";
import { isValue, renderValue } from "./playground-values.js";
import { startInfoview } from "./playground-lsp.js";
import { wantsSelfhost, selfhostEndpoint, withPrelude as preludeOf } from "./selfhost-lsp-shim.js";
import { evalSource, checkSource } from "./playground-wasm.js";

const editor = document.getElementById("editor");
const runButton = document.getElementById("run");
const output = document.getElementById("output");
const status = document.getElementById("status");
const count = document.getElementById("count");
const engine = document.getElementById("engine");

let wasm = null;
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

// (web/playground-wasm.js) `wiz_playground_eval`/`wiz_playground_check` on a source:
// the module's calls, shared by Run and the in-page language server. They free both
// strings on every path (a trap or a panic leaks nothing) and refuse a NUL in a source.

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

function show(text) {
  output.replaceChildren();
  const lines = text.split("\n").filter((l) => l !== "");
  for (const t of lines) output.appendChild(line(t));
  const bad = lines.filter((l) => l.startsWith("error:") || l.startsWith("parse error")).length;
  count.textContent = lines.length + (lines.length === 1 ? " line" : " lines") +
    (bad ? ` · ${bad} error${bad === 1 ? "" : "s"}` : "");
  return bad;
}

function run() {
  if (!wasm || busy) return;
  busy = true;
  runButton.disabled = true;
  setStatus("running…", "running");
  // let the status paint before the (synchronous) Wasm call
  setTimeout(() => {
    const started = performance.now();
    try {
      const text = evalSource(wasm, withPrelude(editor.value));
      const ms = Math.max(0, performance.now() - started);
      const bad = show(text);
      setStatus(`done in ${ms < 10 ? "<10" : Math.round(ms)} ms`, bad ? "error" : "ready");
    } catch (e) {
      output.replaceChildren(line("error: " + (e && e.message ? e.message : String(e))));
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
    evaluate: (src) => engineLoaded.then(() => evalSource(wasm, src)),
    check: (src) => engineLoaded.then(() => checkSource(wasm, src)),
  })
  : undefined;
startInfoview({ editor, panel: document.getElementById("goals"), config: selfhost });

async function start() {
  setStatus("loading the engine…", "running");
  try {
    const createModule = (await import("./wiz-playground.mjs")).default;
    wasm = await createModule({
      print: (s) => console.log(s),
      printErr: (s) => console.warn(s),
    });
    engine.textContent = "engine: ready";
    engineReady.resolve();
    runButton.disabled = false;
    if (!output.childElementCount) run();
    else setStatus("ready", "ready");
  } catch (e) {
    engine.textContent = "engine: failed";
    engineReady.reject(e);
    setStatus("the engine did not load: " + (e && e.message ? e.message : String(e)), "error");
    output.replaceChildren(line("error: " + (e && e.message ? e.message : String(e))));
  }
}

start();
