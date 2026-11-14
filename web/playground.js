// (11ab) The static playground's page half: load the Wasm module web/build-playground.sh
// built (the self-hosted Wiz frontend), hand the editor's text to its export
// `wiz_playground_eval : String → String`, and show the lines it returns. There is no
// server, no dependency and nothing to install: the module is the checker.
//
// The page's own state is deliberately small: the editor text, the example it came
// from, an optional draft in localStorage, and a URL fragment for sharing. The pure
// encoding lives in playground-state.js and is tested by playground-state_test.mjs.
"use strict";
import { isValue, renderValue } from "./playground-values.js";
import { findPreset, presets } from "./playground-presets.js";
import {
  defaultState,
  decodeFragment,
  encodeShareUrl,
  matchedPresetId,
  parseDraft,
  serializeDraft,
  stateFor,
  withPrelude,
} from "./playground-state.js";

const editor = document.getElementById("editor");
const runButton = document.getElementById("run");
const output = document.getElementById("output");
const status = document.getElementById("status");
const count = document.getElementById("count");
const engine = document.getElementById("engine");
const note = document.getElementById("note");
const presetSelect = document.getElementById("preset");
const shareButton = document.getElementById("share");
const saveButton = document.getElementById("save");
const resetButton = document.getElementById("reset");
const clearButton = document.getElementById("clear");

const DRAFT_KEY = "wiz-playground-draft-v1";
let wasm = null;
let busy = false;
let engineFailed = false;
let syncTimer = 0;
let noteTimer = 0;
const big = (x) => (typeof x === "bigint" ? x : BigInt(x));   // wasm64: pointers are i64

function setStatus(text, kind) {
  status.textContent = text;
  status.className = "status " + (kind || "");
}

function notify(text) {
  note.textContent = text;
  window.clearTimeout(noteTimer);
  noteTimer = window.setTimeout(() => { note.textContent = ""; }, 2600);
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
  output.scrollTop = 0;
  const lines = text.split("\n").filter((l) => l !== "");
  for (const t of lines) output.appendChild(line(t));
  const bad = lines.filter((l) => l.startsWith("error:") || l.startsWith("parse error")).length;
  count.textContent = lines.length + (lines.length === 1 ? " line" : " lines") +
    (bad ? ` · ${bad} error${bad === 1 ? "" : "s"}` : "");
  return bad;
}

function currentState() {
  return stateFor(editor.value);
}

function setEditor(code, preset) {
  editor.value = code;
  presetSelect.value = preset || "";
}

function buildPresetOptions() {
  presetSelect.replaceChildren();
  const custom = document.createElement("option");
  custom.value = "";
  custom.textContent = "Custom program";
  custom.disabled = true;
  presetSelect.appendChild(custom);
  for (const p of presets) {
    const option = document.createElement("option");
    option.value = p.id;
    option.textContent = p.title;
    presetSelect.appendChild(option);
  }
}

function syncPreset() {
  presetSelect.value = matchedPresetId(editor.value);
}

function readDraft() {
  try {
    return parseDraft(localStorage.getItem(DRAFT_KEY));
  } catch {
    return null;
  }
}

function writeDraft() {
  try {
    localStorage.setItem(DRAFT_KEY, serializeDraft(currentState()));
  } catch {
    // a private window or a full quota: the page still works, it just won't remember.
  }
}

function replaceUrl() {
  try {
    const href = encodeShareUrl(location.href, currentState());
    if (href !== location.href) history.replaceState(null, "", href);
  } catch {
    // `file://`, a blocked History API, or an over-long URL: sharing still copies the
    // fragment below even if the address bar cannot be updated.
  }
}

function scheduleSync() {
  window.clearTimeout(syncTimer);
  syncTimer = window.setTimeout(() => {
    writeDraft();
    replaceUrl();
  }, 250);
}

function syncNow() {
  window.clearTimeout(syncTimer);
  writeDraft();
  replaceUrl();
}

function clearOutput(quiet) {
  output.replaceChildren();
  output.scrollTop = 0;
  count.textContent = "0 lines";
  if (!busy) {
    if (wasm) setStatus("ready", "ready");
    else if (engineFailed) setStatus("the engine did not load", "error");
    else setStatus("loading the engine…", "running");
  }
  if (!quiet) notify("output cleared");
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
      count.textContent = "1 error";
      setStatus("failed", "error");
    } finally {
      busy = false;
      runButton.disabled = false;
    }
  }, 0);
}

function save() {
  const blob = new Blob([withPrelude(editor.value)], { type: "text/plain;charset=utf-8" });
  const href = URL.createObjectURL(blob);
  const link = document.createElement("a");
  link.href = href;
  link.download = "playground.wiz";
  document.body.appendChild(link);
  link.click();
  link.remove();
  window.setTimeout(() => URL.revokeObjectURL(href), 1000);
  writeDraft();
  notify("saved playground.wiz");
}

async function copyText(text) {
  try {
    if (navigator.clipboard && navigator.clipboard.writeText) {
      await navigator.clipboard.writeText(text);
      return true;
    }
  } catch {
    // fall through: plain HTTP pages often have no clipboard permission
  }
  let area = null;
  try {
    area = document.createElement("textarea");
    area.value = text;
    area.setAttribute("readonly", "");
    area.style.position = "fixed";
    area.style.opacity = "0";
    document.body.appendChild(area);
    area.select();
    return document.execCommand("copy");
  } catch {
    return false;
  } finally {
    if (area) area.remove();
  }
}

async function share() {
  syncNow();
  const url = encodeShareUrl(location.href, currentState());
  replaceUrl();
  if (await copyText(url)) {
    notify("link copied to the clipboard");
  } else {
    notify("link is in the address bar");
    window.prompt("Copy this playground link:", url);
  }
}

function reset() {
  const state = defaultState();
  setEditor(state.code, state.preset);
  clearOutput(true);
  syncNow();
  if (wasm) setStatus("ready", "ready");
  notify("reset to the default program");
}

function applyUrl(hash) {
  const state = decodeFragment(hash);
  if (!state) return false;
  setEditor(state.code, state.preset);
  clearOutput(true);
  if (!wasm) setStatus(engineFailed ? "the engine did not load" : "loading the engine…", engineFailed ? "error" : "running");
  else if (!busy && state.preset) run();
  else if (!busy) setStatus("ready — press Run", "ready");
  return true;
}

runButton.addEventListener("click", run);
clearButton.addEventListener("click", () => clearOutput(false));
shareButton.addEventListener("click", share);
saveButton.addEventListener("click", save);
resetButton.addEventListener("click", reset);

presetSelect.addEventListener("change", () => {
  const p = findPreset(presetSelect.value);
  if (!p) return;
  setEditor(p.code, p.id);
  clearOutput(true);
  syncNow();
  notify("loaded example: " + p.title);
  if (wasm && !busy) run();
  else if (!wasm) setStatus(engineFailed ? "the engine did not load" : "loading the engine…", engineFailed ? "error" : "running");
});

editor.addEventListener("input", () => {
  syncPreset();
  scheduleSync();
});

editor.addEventListener("keydown", (e) => {
  if (e.key !== "Tab" || e.ctrlKey || e.metaKey || e.altKey || e.shiftKey) return;
  e.preventDefault();
  const start = editor.selectionStart;
  const end = editor.selectionEnd;
  editor.setRangeText("  ", start, end, "end");
  syncPreset();
  scheduleSync();
});

document.addEventListener("keydown", (e) => {
  if (!(e.ctrlKey || e.metaKey)) return;
  if (e.key === "Enter") {
    e.preventDefault();
    run();
  } else if (e.key.toLowerCase() === "s") {
    e.preventDefault();
    save();
  }
});

window.addEventListener("hashchange", () => {
  applyUrl(location.hash);
});

window.addEventListener("pagehide", syncNow);

async function start() {
  buildPresetOptions();
  const fromUrl = decodeFragment(location.hash);
  const initial = fromUrl || readDraft() || defaultState();
  setEditor(initial.code, initial.preset);
  if (location.hash && !fromUrl) notify("ignored an invalid playground link");
  syncPreset();
  writeDraft();
  if (fromUrl) notify("loaded the program from the link");

  setStatus("loading the engine…", "running");
  try {
    const createModule = (await import("./wiz-playground.mjs")).default;
    wasm = await createModule({
      print: (s) => console.log(s),
      printErr: (s) => console.warn(s),
    });
    engine.textContent = "engine: ready";
    runButton.disabled = false;
    const current = currentState();
    if (!output.childElementCount && current.preset) run();
    else if (!output.childElementCount) setStatus("ready — press Run", "ready");
    else setStatus("ready", "ready");
  } catch (e) {
    engineFailed = true;
    engine.textContent = "engine: failed";
    setStatus("the engine did not load: " + (e && e.message ? e.message : String(e)), "error");
    output.replaceChildren(line("error: " + (e && e.message ? e.message : String(e))));
    count.textContent = "1 error";
  }
}

start();
