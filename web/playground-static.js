// The playground's static page: the markup in web/playground.html, driven by hand.
//
// This is the fallback web/playground.js loads when the runtime module
// (web/wiz-playground-ui.mjs, web/playground-ui.wiz) is not built. It is the page the
// JS-to-runtime migration is deleting: layout, state and rendering live here for now,
// and stages 2-4 of docs/notes/loom-thin-js.md move them to the runtime or delete them
// with the markup.
//
// The page's own state is deliberately small: the editor text, the example it came
// from, an optional draft in localStorage, and a URL fragment for sharing. The pure
// encoding lives in web/playground-state.js and is tested by playground-state_test.mjs.
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
} from "./playground-state.js";
import { startInfoview } from "./playground-lsp.js";
import { wantsSelfhost, selfhostEndpoint, withPrelude as preludeOf } from "./selfhost-lsp-shim.js";
import { createEngine, failureLines } from "./playground-engine.js";

// The page's elements (the static markup's).
let editor = null;
let runButton = null;
let output = null;
let status = null;
let count = null;
let engineEl = null;
let note = null;
let presetSelect = null;
let shareButton = null;
let saveButton = null;
let resetButton = null;
let clearButton = null;

const DRAFT_KEY = "wiz-playground-draft-v1";
let wasm = null;   // web/playground-engine.js: every call guarded; only a trap/OOM restarts it
let busy = false;
let engineFailed = false;
let syncTimer = 0;
let noteTimer = 0;

function setStatus(text, kind) {
  status.textContent = text;
  status.className = "status " + (kind || "");
}

function setEnabled(on) {
  runButton.disabled = !on;
}

function setEngine(text) {
  engineEl.textContent = text;
}

// A short-lived message beside the status line (the static page's `#note`).
function notify(text) {
  if (!note) return;
  note.textContent = text;
  window.clearTimeout(noteTimer);
  noteTimer = window.setTimeout(() => { note.textContent = ""; }, 2600);
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
  output.replaceChildren();
  output.scrollTop = 0;
  const lines = text.split("\n").filter((l) => l !== "");
  for (const t of lines) output.appendChild(line(t));
  const bad = lines.filter((l) => l.startsWith("error:") || l.startsWith("parse error")).length;
  count.textContent = lines.length + (lines.length === 1 ? " line" : " lines") +
    (bad ? ` · ${bad} error${bad === 1 ? "" : "s"}` : "");
  return text.split("\n").filter((l) => l !== "")
    .filter((l) => l.startsWith("error:") || l.startsWith("parse error")).length;
}

// An engine exit, abort or trap: the lines it printed, then what happened.
function showFailure(e) {
  const lines = failureLines(e);
  const countText = e.kind === "exit" ? `exit code ${e.code}` : e.kind;
  output.replaceChildren(...lines.map(line));
  output.scrollTop = 0;
  count.textContent = countText;
}

// ## The static page's program state (examples, the URL fragment, the draft)

function currentState() {
  return stateFor(editor ? editor.value : "");
}

function setEditor(code, preset) {
  if (editor) editor.value = code;
  if (presetSelect) presetSelect.value = preset || "";
}

function buildPresetOptions() {
  if (!presetSelect) return;
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
  if (!presetSelect) return;
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
  if (!editor) return;
  try {
    localStorage.setItem(DRAFT_KEY, serializeDraft(currentState()));
  } catch {
    // a private window or a full quota: the page still works, it just won't remember.
  }
}

function replaceUrl() {
  if (!editor) return;
  try {
    const href = encodeShareUrl(location.href, currentState());
    if (href !== location.href) history.replaceState(null, "", href);
  } catch {
    // `file://`, a blocked History API, or an over-long URL: sharing still copies the
    // fragment below even if the address bar cannot be updated.
  }
}

function scheduleSync() {
  if (!editor) return;
  window.clearTimeout(syncTimer);
  syncTimer = window.setTimeout(() => {
    writeDraft();
    replaceUrl();
  }, 250);
}

function syncNow() {
  if (!editor) return;
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

function save() {
  if (!editor) return;
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
  if (!editor) return;
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

// The page's state from the URL fragment, the draft, or the default example.
function initPageState() {
  buildPresetOptions();
  const fromUrl = decodeFragment(location.hash);
  const initial = fromUrl || readDraft() || defaultState();
  setEditor(initial.code, initial.preset);
  if (location.hash && !fromUrl) notify("ignored an invalid playground link");
  syncPreset();
  writeDraft();
  if (fromUrl) notify("loaded the program from the link");
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
  // The squiggle mirror is the static page's own layer (web/squiggles.js).
  startInfoview({
    editor, panel: document.getElementById("goals"), config: selfhost,
    squiggles: true,
  });
}

function wireEditor() {
  editor = document.getElementById("editor");
  runButton = document.getElementById("run");
  status = document.getElementById("status");
  output = document.getElementById("output");
  count = document.getElementById("count");
  engineEl = document.getElementById("engine");
  note = document.getElementById("note");
  presetSelect = document.getElementById("preset");
  shareButton = document.getElementById("share");
  saveButton = document.getElementById("save");
  resetButton = document.getElementById("reset");
  clearButton = document.getElementById("clear");

  if (runButton) runButton.addEventListener("click", run);
  if (clearButton) clearButton.addEventListener("click", () => clearOutput(false));
  if (shareButton) shareButton.addEventListener("click", share);
  if (saveButton) saveButton.addEventListener("click", save);
  if (resetButton) resetButton.addEventListener("click", reset);
  if (presetSelect) {
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
  }

  if (editor) {
    editor.addEventListener("input", () => {
      syncPreset();
      scheduleSync();
    });
    editor.addEventListener("keydown", (e) => {
      if (e.key === "Enter" && (e.ctrlKey || e.metaKey)) {
        e.preventDefault();
        run();
        return;
      }
      if (e.key !== "Tab" || e.ctrlKey || e.metaKey || e.altKey || e.shiftKey) return;
      e.preventDefault();
      const start = editor.selectionStart;
      const end = editor.selectionEnd;
      editor.setRangeText("  ", start, end, "end");
      syncPreset();
      scheduleSync();
    });
  }

  document.addEventListener("keydown", (e) => {
    if (!(e.ctrlKey || e.metaKey)) return;
    if (e.key.toLowerCase() === "s" && !e.shiftKey && !e.altKey) {
      e.preventDefault();
      save();
    }
  });

  window.addEventListener("hashchange", () => { applyUrl(location.hash); });
  window.addEventListener("pagehide", syncNow);
}

export async function startStatic() {
  wireEditor();
  initPageState();
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
    const current = currentState();
    if (!output.childElementCount && current.preset) run();
    else if (!output.childElementCount) setStatus("ready — press Run", "ready");
    else setStatus("ready", "ready");
  } catch (e) {
    engineFailed = true;
    setEngine("engine: failed");
    engineReady.reject(e);
    setStatus("the engine did not load: " + (e && e.message ? e.message : String(e)), "error");
    show("error: " + (e && e.message ? e.message : String(e)));
  }
}

