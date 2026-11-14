// (11ab) The static playground's page half: load the Wasm module web/build-playground.sh
// built (the self-hosted Wiz frontend), hand the editor's text to its export
// `wiz_playground_eval : String → String`, and show the lines it returns. There is no
// server and nothing to install: the module is the checker.
"use strict";
import { isValue, renderValue } from "./playground-values.js";

const editor = document.getElementById("editor");
const runButton = document.getElementById("run");
const output = document.getElementById("output");
const status = document.getElementById("status");
const count = document.getElementById("count");
const engine = document.getElementById("engine");

let wasm = null;
let busy = false;
const big = (x) => (typeof x === "bigint" ? x : BigInt(x));   // wasm64: pointers are i64

function setStatus(text, kind) {
  status.textContent = text;
  status.className = "status " + (kind || "");
}

// The engine has the self-hosted frontend's embedded Prelude; a source without an
// import gets it, so `Nat`, `Bool`, lists, … are in scope as in `wiz check`.
function withPrelude(text) {
  return /^\s*import\b/m.test(text) ? text : "import Prelude\n\n" + text;
}

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
      const src = withPrelude(editor.value);
      const p = wasm.stringToNewUTF8(src);
      const r = wasm._wiz_playground_eval(big(p));
      wasm._free(big(p));
      const text = r ? wasm.UTF8ToString(Number(r)) : "";
      if (r) wasm._free(r);
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

async function start() {
  setStatus("loading the engine…", "running");
  try {
    const createModule = (await import("./wiz-playground.mjs")).default;
    wasm = await createModule({
      print: (s) => console.log(s),
      printErr: (s) => console.warn(s),
    });
    engine.textContent = "engine: ready";
    runButton.disabled = false;
    if (!output.childElementCount) run();
    else setStatus("ready", "ready");
  } catch (e) {
    engine.textContent = "engine: failed";
    setStatus("the engine did not load: " + (e && e.message ? e.message : String(e)), "error");
    output.replaceChildren(line("error: " + (e && e.message ? e.message : String(e))));
  }
}

start();
