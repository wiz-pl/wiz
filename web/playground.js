// The playground's entry point. It points at an element, loads the page's runtime
// (`web/playground-ui.wiz`, the whole page as one Loom app) and gives it the effects a
// Wiz runtime cannot do itself: the self-hosted engine in its own Wasm instance, and the
// goals pane's language client (still a page island, `web/playground-lsp.js`).
//
// Everything the page shows — the header and its examples menu, the editor pane, the
// output pane, the status line, the footer — is the runtime's. The page keeps no DOM
// structure of its own and never touches the module's ABI: `mount`'s `call` is the only
// way in, so the next page to migrate is this file with different effects.
//
// `?ui=loom` selects this page (it is the one being migrated); without it, or when the
// runtime module is not built, the static markup's own script takes over
// (`web/playground-static.js`). `?lsp=ws://host:port` gives the goals pane an external
// language server; the default is the in-page one (`web/selfhost-lsp-shim.js`).
"use strict";
import { mount } from "./framework/mount.js";
import { startInfoview } from "./playground-lsp.js";
import { wantsSelfhost, selfhostEndpoint, withPrelude as preludeOf } from "./selfhost-lsp-shim.js";
import { createEngine, failureLines } from "./playground-engine.js";

const params = new URLSearchParams(typeof location !== "undefined" ? location.search : "");
const useLoom = params.get("ui") === "loom";

let wasm = null;        // web/playground-engine.js: the self-hosted checker
let handle = null;      // mount's handle: the runtime's entry points
let busy = false;

const withPrelude = (text) => preludeOf(text).source;
const isErrorLine = (l) => l.startsWith("error:") || l.startsWith("parse error");
const errorCount = (text) => text.split("\n").filter((l) => l !== "").filter(isErrorLine).length;

// The goals pane's server. The in-page one answers from the same engine, so it waits for
// the engine's promise; `?lsp=ws://host:port` uses the external client instead.
let engineReady;
const engineLoaded = new Promise((resolve, reject) => { engineReady = { resolve, reject }; });
engineLoaded.catch(() => { /* reported by loadEngine() */ });
const selfhost = typeof location !== "undefined" && wantsSelfhost(location.search)
  ? selfhostEndpoint({
    evaluate: (src) => engineLoaded.then(() => wasm.evaluate(src)),
    check: (src) => engineLoaded.then(() => wasm.check(src)),
  })
  : undefined;

function setStatus(text, kind) { handle.call("wiz_loom_status", text, kind || ""); }
function setEngine(text) { handle.call("wiz_loom_engine", text); }

// Run the editor's program: the one effect the editor's Run button (and an example's
// load) asks for. The runtime holds the text and the state; the page calls the engine
// and reports the result through the runtime's entry points.
function run() {
  const editor = document.getElementById("editor");
  if (!wasm || busy || !editor) return;
  busy = true;
  handle.call("wiz_loom_enable", 0);
  setStatus("running…", "running");
  // let the status paint before the (synchronous) Wasm call
  setTimeout(async () => {
    const started = performance.now();
    try {
      const text = await wasm.evaluate(withPrelude(editor.value));
      const ms = Math.max(0, performance.now() - started);
      handle.call("wiz_loom_show", text);
      const bad = errorCount(text);
      setStatus(`done in ${ms < 10 ? "<10" : Math.round(ms)} ms`, bad ? "error" : "ready");
    } catch (e) {
      if (e && e.name === "EngineFailure") {
        const countText = e.kind === "exit" ? `exit code ${e.code}` : e.kind;
        handle.call("wiz_loom_fail", failureLines(e).join("\n"), countText);
      } else {
        handle.call("wiz_loom_show", "error: " + (e && e.message ? e.message : String(e)));
      }
      setStatus("failed", "error");
    } finally {
      busy = false;
      handle.call("wiz_loom_enable", 1);
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
    handle.call("wiz_loom_enable", 1);
    setStatus("ready", "ready");
    run();
  } catch (e) {
    setEngine("engine: failed");
    engineReady.reject(e);
    setStatus("the engine did not load: " + (e && e.message ? e.message : String(e)), "error");
    handle.call("wiz_loom_show", "error: " + (e && e.message ? e.message : String(e)));
  }
}

// The goals pane is an island (`#goals`): the language client writes into it, and the
// runtime only renders the empty container, so a re-render never clobbers it. The
// squiggle mirror is off on this page for now (it wraps the textarea, and the driver's
// patch paths are child indices); `loom-overlays` relaxes that with a non-wrapping layer.
function wireGoals(editor) {
  startInfoview({
    editor,
    panel: document.getElementById("goals"),
    config: selfhost,
    squiggles: false,
  });
}

async function startLoom() {
  try {
    handle = await mount(document.body, {
      module: () => import("./wiz-playground-ui.mjs"),
      transport: { engine: () => wasm },
      events: ["click", "input", "change"],
      // An example's load is the page's cue to run it: the runtime is pure, so it
      // records the request (`Page.loads`) and the page does the effect.
      onStep: (_state, event) => { if (event === "change") run(); },
    });
  } catch (e) {
    console.warn("wiz playground: using the static page: " +
      (e && e.message ? e.message : String(e)));
    return false;
  }
  const editor = document.getElementById("editor");
  if (editor) wireGoals(editor);
  await loadEngine();
  return true;
}

async function start() {
  if (!useLoom) {
    const { startStatic } = await import("./playground-static.js");
    return startStatic();
  }
  if (await startLoom()) return;
  // The runtime module is not built (or its ABI is not what mount expects): the page's
  // own markup is still in the body, so the static script can take over untouched.
  const { startStatic } = await import("./playground-static.js");
  return startStatic();
}

start();
