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
// There is one page and one runtime. If the runtime cannot start (the module was not
// built, the network failed, its ABI is not the Loom one), the mount point says so in
// plain text; it does not switch to a second, hand-written UI. `?lsp=ws://host:port`
// gives the goals pane an external language server; the default is the in-page one
// (`web/selfhost-lsp-shim.js`).
"use strict";
import { mount } from "./framework/mount.js";
import { startInfoview } from "./playground-lsp.js";
import { wantsSelfhost, selfhostEndpoint, withPrelude as preludeOf } from "./selfhost-lsp-shim.js";
import { createEngine, failureLines } from "./playground-engine.js";

const runtimeModule = () => import("./wiz-playground-ui.mjs");

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
      events: ["click", "input", "change"],
      // An example's load is the page's cue to run it: the runtime is pure, so it
      // records the request (`Page.loads`) and the page does the effect.
      onStep: (_state, event) => { if (event === "change") run(); },
    });
  } catch (e) {
    cannotStart(target, e);
    return false;
  }
  const editor = document.getElementById("editor");
  if (editor) wireGoals(editor);
  await loadEngine();
  return true;
}
