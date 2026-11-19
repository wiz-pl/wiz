// (11ab) The static playground's page half: load the Wasm module web/build-playground.sh
// built (the self-hosted Wiz frontend), hand the editor's text to its export
// `wiz_playground_eval : String → String`, and show the lines it returns. There is no
// server and nothing to install: the module is the checker.
//
// The page's own state is deliberately small: the editor text, the example it came
// from, an optional draft in localStorage, and a URL fragment for sharing. The pure
// encoding lives in web/playground-state.js and is tested by playground-state_test.mjs.
// Those controls belong to the static markup; `?ui=loom` replaces the page with the
// Loom app (`web/playground-ui.wiz`), which is the `web/` side's own UI.
//
// `?ui=loom` mounts the page itself from a second Wasm module
// (`web/build-playground-ui.wiz` → `wiz-playground-ui.mjs`): the whole page is one Loom
// app (`web/playground-ui.wiz`), and this file only loads the engine and turns its
// results into the app's states. The default is the static markup the page carries; the
// Loom path falls back to it when the module is not built, and it is the only path that
// can move the page's text into a Loom component.
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

const params = new URLSearchParams(typeof location !== "undefined" ? location.search : "");
const useLoom = params.get("ui") === "loom";

// The page's elements: the static markup's at load, or the Loom app's after it mounts.
// The UX controls (preset/share/save/reset/clear/note) exist only in the static
// markup, so they stay null under `?ui=loom`.
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

// The Loom UI instance (`?ui=loom`), driver's handle and its state marshalling.
let ui = null;
let app = null;
// Whether the Loom app actually mounted; a module that fails to load leaves the static
// page in place, which then needs its own state (examples, fragment, draft).
let loomMounted = false;

const DRAFT_KEY = "wiz-playground-draft-v1";
let wasm = null;   // web/playground-engine.js: every call guarded; only a trap/OOM restarts it
let busy = false;
let engineFailed = false;
let syncTimer = 0;
let noteTimer = 0;

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
  if (ui) {
    uiCall("wiz_loom_show", text);
  } else {
    output.replaceChildren();
    output.scrollTop = 0;
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
  output.scrollTop = 0;
  count.textContent = countText;
}

// ## The static page's program state (examples, the URL fragment, the draft)

function currentState() {
  return stateFor(editor ? editor.value : "");
}

function setEditor(code, preset) {
  if (ui) uiCall("wiz_loom_text", code);
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
  if (ui) {
    uiCall("wiz_loom_show", "");
  } else {
    output.replaceChildren();
    output.scrollTop = 0;
    count.textContent = "0 lines";
  }
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
  // The overlays work in both modes: the squiggle layer sits over the textarea without
  // wrapping it, so the Loom app's child-index patch paths stay stable (see
  // web/squiggles.js and web/loom_overlay_test.mjs). `?squiggles=off` and
  // `?completions=off` are still the page's flags.
  startInfoview({
    editor, panel: document.getElementById("goals"), config: selfhost,
  });
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
    loomMounted = true;
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

async function start() {
  // `?ui=loom`: the page is the Loom app; otherwise the static markup stays.
  if (useLoom) await mountLoom();
  wireEditor();
  // The examples, the URL fragment and the draft are the static page's state; the Loom
  // app owns its own, so do not overwrite it with a feature it does not render.
  if (!loomMounted) initPageState();
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
    if (!loomMounted) {
      const current = currentState();
      if (!output.childElementCount && current.preset) run();
      else if (!output.childElementCount) setStatus("ready — press Run", "ready");
      else setStatus("ready", "ready");
    } else if (!output || !output.childElementCount) {
      run();
    } else {
      setStatus("ready", "ready");
    }
  } catch (e) {
    engineFailed = true;
    setEngine("engine: failed");
    engineReady.reject(e);
    setStatus("the engine did not load: " + (e && e.message ? e.message : String(e)), "error");
    show("error: " + (e && e.message ? e.message : String(e)));
  }
}

start();
