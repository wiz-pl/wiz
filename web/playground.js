// The playground's entry point. It points at an element, loads the page's runtime
// (`web/playground-ui.wiz`, the whole page as one Loom app) and gives it the effects a
// Wiz runtime cannot do itself: the self-hosted engine in its own Wasm instance, the
// goals pane's language client (still a page island, `web/playground-lsp.js`), and the
// host capabilities `mount` publishes (`download`, `clipboard`, `storage`, `url`).
//
// Everything the page shows — the header and its toolbar (the examples menu, Share,
// Save, Reset, Clear), the editor pane, the output pane, the status line, the footer —
// is the runtime's. The page keeps no DOM structure of its own and never touches the
// module's ABI: `mount`'s `call` is the only way in, so the next page to migrate is this
// file with different effects.
//
// The runtime's effects come back as requests (`wiz_loom_requests`, a JSON list of
// `{kind, payload}`); the page does one and acknowledges it. That is why the page still
// knows about the engine and the language server but not about the fragment/draft
// format, the examples or the output's classification: those are the runtime's.
//
// There is one page and one runtime. If the runtime cannot start (the module was not
// built, the network failed, its ABI is not the Loom one), the mount point says so in
// plain text; it does not switch to a second, hand-written UI. `?lsp=ws://host:port`
// gives the goals pane an external language server; the default is the in-page one
// (`web/selfhost-lsp-shim.js`).
"use strict";
import { mount } from "./framework/mount.js";
import { startInfoview, createIndexer } from "./playground-lsp.js";
import { wantsSelfhost, selfhostEndpoint } from "./selfhost-lsp-shim.js";
import { createEngine, failureLines } from "./playground-engine.js";

const runtimeModule = () => import("./wiz-playground-ui.mjs");

// The draft's key in the host's storage (`host.storage.get/set`); the value's format is
// `Web.Draft`'s (the runtime serializes it in a `sync` request), so only the key is the
// page's.
const DRAFT_KEY = "wiz-playground-draft-v1";

let wasm = null;        // web/playground-engine.js: the self-hosted checker
let handle = null;      // mount's handle: the runtime's entry points
let busy = false;
let syncTimer = 0;
let noteTimer = 0;
let pendingSync = "";

// The runtime's one effect entry point.
function effect(kind, a = "", b = "") {
  if (handle) handle.call("wiz_loom_effect", kind, a, b);
}

function setStatus(text, kind) { effect("status", text, kind || ""); }
function setEngine(text) { effect("engine", text); }
function setEnabled(on) { effect("enable", on ? "1" : "0"); }

// A short-lived message beside the status line (`#note`, the runtime's field).
function note(text) {
  effect("note", text);
  if (noteTimer) clearTimeout(noteTimer);
  if (text) noteTimer = setTimeout(() => effect("note", ""), 2600);
}

// Run the editor's program: the effect behind the Run button, Ctrl/⌘+Enter, an
// example's load, and the engine becoming ready. The runtime holds the text and the
// state; the page calls the engine and reports the result.
function run() {
  const editor = document.getElementById("editor");
  if (!wasm || busy || !editor) return;
  busy = true;
  setEnabled(false);
  setStatus("running…", "running");
  // let the status paint before the (synchronous) Wasm call
  setTimeout(async () => {
    const started = performance.now();
    try {
      // The Prelude rule is the runtime's (`Web.Selfhost.preludeOf`, the same one the
      // in-page server applies) so a Run and a diagnostic agree on the checked source.
      const source = handle
        ? JSON.parse(handle.ask("wiz_loom_lsp_prelude", editor.value)).source
        : editor.value;
      const text = await wasm.evaluate(source);
      const ms = Math.max(0, performance.now() - started);
      effect("finished", text, `done in ${ms < 10 ? "<10" : Math.round(ms)} ms`);
    } catch (e) {
      if (e && e.name === "EngineFailure") {
        const countText = e.kind === "exit" ? `exit code ${e.code}` : e.kind;
        effect("failed", failureLines(e).join("\n"), countText);
      } else {
        effect("finished", "error: " + (e && e.message ? e.message : String(e)), "failed");
      }
    } finally {
      busy = false;
      setEnabled(true);
    }
  }, 0);
}

// The engine: a second Wasm instance (`web/build-playground.sh`), loaded after the page
// paints so the runtime's first frame is not waiting for it.
async function loadEngine() {
  setStatus("loading the engine…", "running");
  try {
    const createModule = (await import("./wiz-playground.mjs")).default;
    wasm = createEngine(createModule, {
      print: (s) => console.log(s),
      printErr: (s) => console.warn(s),
      onRestart: (f) => console.warn("wiz playground: restarting the engine: " + f.message),
    });
    await wasm.ready;
    setEngine("engine: ready");
    engineReady.resolve();
    setEnabled(true);
    setStatus("ready", "ready");
    run();
  } catch (e) {
    setEngine("engine: failed");
    engineReady.reject(e);
    const reason = e && e.message ? e.message : String(e);
    effect("finished", "error: " + reason, "the engine did not load: " + reason);
  }
}

// ## The runtime's editor rules

// The runtime owns the editor's pure rules (`lib/Web/EditorModel.wiz`); `createIndexer`
// is the one adapter that names the `wiz_loom_editor_*` queries, and the overlay widgets
// only paint and position. Nothing here decides what a diagnostic underlines, which item
// the popup selects, what a key does, or what a completion inserts.
function editorRules(handle, versionOf = null) {
  const index = createIndexer((name, ...args) => handle.ask(name, ...args), versionOf);
  return {
    segments: index.segments,
    items: index.items,
    popup: index.popup,
    key: index.key,
    accept: index.accept,
    trigger: index.trigger,
    itemTitle: index.itemTitle,
    askKey: index.askKey,
    position: index.position,
    target: index.target,
  };
}

// ## The effects the runtime asks for

// The URL fragment and the draft: the runtime hands over the *formatted* values (it
// owns the format); the page writes them, debounced, because a keystroke is not a
// reason to touch `history` and the storage capability twice. `flushSync` is also the
// `pagehide` path, so the last keystroke is not lost when the tab closes.
function flushSync() {
  if (!pendingSync || !handle) return;
  let value;
  try { value = JSON.parse(pendingSync); } catch { return; }
  try { handle.host.storage.set(DRAFT_KEY, value.draft); } catch { /* private window, full quota */ }
  if (typeof value.fragment === "string") handle.host.url(value.fragment);
}

function sync(payload) {
  pendingSync = payload;
  if (syncTimer) clearTimeout(syncTimer);
  syncTimer = setTimeout(() => { syncTimer = 0; flushSync(); }, 250);
}

async function share(fragment) {
  const base = typeof location !== "undefined" ? location.href.split("#")[0] : "";
  const url = base + fragment;
  handle.host.url(fragment);
  if (await handle.host.clipboard(url)) note("link copied to the clipboard");
  else note("link is in the address bar");
}

// `onRequest(kind, payload)` is mount's face of the runtime's request list. Acknowledge
// first: an effect that throws or is slow must not be requested again forever.
function onRequest(kind, payload) {
  if (!handle) return;
  effect("ack", kind);
  if (kind === "run") run();
  else if (kind === "save") {
    if (handle.host.download("playground.wiz", payload)) note("saved playground.wiz");
  } else if (kind === "share") share(payload);
  else if (kind === "sync") sync(payload);
  else if (kind === "edit") {
    // A Tab: the runtime formatted the edit (insert/indent at the selection); the host
    // applies it to the textarea and reports the value and the new selection back. The
    // `input` event the capability dispatches also reaches the runtime's normal path.
    let edit = null;
    try { edit = JSON.parse(payload); } catch { edit = null; }
    const result = edit ? handle.host.edit(edit) : null;
    if (result) effect("edited", result.value, result.selectionStart + "\n" + result.selectionEnd);
  }
  else if (goals) goals.request(kind, payload);
}

// ## The goals pane

// The goals pane is an island (`#goals`): the language client writes into it, and the
// runtime only renders the empty container, so a re-render never clobbers it. Both
// editor overlays are on: the squiggle layer no longer wraps the textarea (it is the
// last child of the editor's section, so the runtime's child-index patch paths stay
// stable), and the completion popup is appended to the body, outside the rendered tree.
let goals = null;

// The rules behind both overlays are the runtime's (`editorRules`); the pane is the
// runtime's too (`lib/Web/Goals.wiz`), so its answers go through the page's effect and a
// click's `reveal`/`subterm` request comes back through onRequest. Widget cards are not
// the pane's: `web/widgets.js` mounts them into the page's `#widget-list` and the pane
// never inserts a payload's markup.
function wireGoals(editor, rules) {
  const widgetPane = typeof document !== "undefined" ? document.getElementById("widget-list") : null;
  goals = startInfoview({
    editor,
    widgetPane,
    config: selfhost,
    rules,
    update: (kind, a, b) => effect("panel", kind, b === "" ? a : b),
  });
}

// The goals pane's server. The in-page one answers from the same engine, so it waits for
// the engine's promise; `?lsp=ws://host:port` uses the external client instead.
let engineReady;
const engineLoaded = new Promise((resolve, reject) => { engineReady = { resolve, reject }; });
engineLoaded.catch(() => { /* reported by loadEngine() */ });
const selfhost = typeof location !== "undefined" && wantsSelfhost(location.search)
  ? selfhostEndpoint({
    evaluate: (src) => engineLoaded.then(() => wasm.evaluate(src)),
    check: (src) => engineLoaded.then(() => wasm.check(src)),
    // Positions and the check's declaration index are the runtime's (`Web.EditorModel`);
    // the adapter closes over `handle`, which is set before the pane starts.
    index: createIndexer((name, ...args) => handle.ask(name, ...args)),
  })
  : undefined;

// There is no page to fall back to: if the runtime cannot start, the mount point says so
// in plain text, with the reason. This is the whole failure path — no DOM construction
// and no second UI, which is what keeps one page's behaviour in one place.
function cannotStart(root, e) {
  const reason = e && e.message ? e.message : String(e);
  console.error("wiz playground: the runtime could not start: " + reason);
  root.textContent =
    "The playground could not start: " + reason + "\n\n" +
    "This page runs the Wiz checker in WebAssembly. It needs the runtime module " +
    "(wiz-playground-ui.mjs) and the engine (wiz-playground.mjs); see docs/building.md, " +
    "\"The playground\".";
}

// Mount the runtime on `root` (the body by default) and give it its effects. Exported for
// the Node tests, which pass a stub module and a DOM double; `web/playground.html` calls
// it from a module script.
export async function startPage({ root, module = runtimeModule } = {}) {
  const target = root || document.body;
  try {
    handle = await mount(target, {
      module,
      transport: { engine: () => wasm },
      events: ["click", "input", "change", "keydown"],
      onRequest,
    });
  } catch (e) {
    cannotStart(target, e);
    return false;
  }
  // The initial state: the URL fragment wins, then the stored draft, then the default
  // example. `Web.Draft` owns the precedence and the format; the page only supplies the
  // two strings it can read.
  const hash = typeof location !== "undefined" ? location.hash : "";
  const draft = handle.host.storage.get(DRAFT_KEY) || "";
  handle.call("wiz_loom_effect", "load", hash, draft);
  const editor = document.getElementById("editor");
  if (editor) {
    // The editor's document version: one per `input`, so an arrow key on unchanged text
    // reuses the line table instead of keying the cache by the whole string.
    let editorVersion = 0;
    editor.addEventListener("input", () => { editorVersion++; });
    wireGoals(editor, editorRules(handle, () => editorVersion));
  }
  if (typeof addEventListener === "function") {
    addEventListener("pagehide", () => {
      if (syncTimer) { clearTimeout(syncTimer); syncTimer = 0; }
      flushSync();
    });
  }
  await loadEngine();
  return true;
}
