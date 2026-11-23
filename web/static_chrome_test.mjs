// The playground's static-complete page in headless Chromium, over the DevTools
// protocol and a static server for the build directory. It checks the two halves the
// Node test cannot: a **real no-JavaScript load** (script execution disabled before
// navigation) still shows the whole shell, and a normal load **adopts** the static tree
// (the `#app` nodes are the same objects) instead of replacing it. It then focuses the
// editor and applies a `replace` of its `<main>` ancestor: the batch touches
// `document.activeElement`, so the morph path must preserve the textarea's node, focus,
// value and selection.
//
//   usage: node web/static_chrome_test.mjs CHROMIUM BUILD_DIR
//
// BUILD_DIR is what `web/test.sh` builds in OUT (playground.html, playground.js, the
// framework and the two Wasm modules). The test starts its own server on 127.0.0.1:0.
"use strict";
import { spawn } from "node:child_process";
import { createServer } from "node:http";
import { mkdtempSync, readFileSync } from "node:fs";
import { readFile, stat } from "node:fs/promises";
import { tmpdir } from "node:os";
import { extname, join, normalize, resolve, sep } from "node:path";

const [chrome, dirArg] = process.argv.slice(2);
if (!chrome || !dirArg) {
  console.error("usage: node web/static_chrome_test.mjs CHROMIUM BUILD_DIR");
  process.exit(2);
}
const root = resolve(dirArg);
const pageFile = join(root, "playground.html");

let failed = 0;
const ok = (cond, what, detail = "") => {
  if (cond) console.log("ok: " + what);
  else { failed++; console.log("FAIL: " + what + (detail ? "\n  " + detail : "")); }
};
const count = (html, re) => (html.match(re) || []).length;
const sleep = (ms) => new Promise((r) => setTimeout(r, ms));

// The JS-on load records the static nodes before the (deferred) module script runs. This
// is injected only into the served copy; the artifact is untouched.
const SNAPSHOT = "<script>window.__staticToolbar = document.querySelector('#app .toolbar');" +
  "window.__staticEditor = document.getElementById('editor');</script>";

const MIME = {
  ".html": "text/html; charset=utf-8",
  ".js": "text/javascript; charset=utf-8",
  ".mjs": "text/javascript; charset=utf-8",
  ".css": "text/css; charset=utf-8",
  ".json": "application/json; charset=utf-8",
  ".wasm": "application/wasm",
  ".txt": "text/plain; charset=utf-8",
};

function serve(dir) {
  const server = createServer(async (req, res) => {
    try {
      let pathname = decodeURIComponent(new URL(req.url, "http://127.0.0.1").pathname);
      if (pathname === "/") pathname = "/playground.html";
      let p = normalize(join(dir, pathname));
      if (!(p === dir || p.startsWith(dir + sep))) {
        res.writeHead(403).end("outside the build directory");
        return;
      }
      if ((await stat(p)).isDirectory()) p = join(p, "index.html");
      let body = await readFile(p);
      if (p === pageFile) {
        const html = body.toString("utf-8");
        const at = html.indexOf('<script type="module">');
        body = Buffer.from(at < 0 ? html : html.slice(0, at) + SNAPSHOT + html.slice(at));
      }
      res.writeHead(200, { "content-type": MIME[extname(p)] || "application/octet-stream" });
      res.end(body);
    } catch {
      res.writeHead(404).end("not found");
    }
  });
  return new Promise((done, fail) => {
    server.on("error", fail);
    server.listen(0, "127.0.0.1", () => {
      done({ server, url: `http://127.0.0.1:${server.address().port}/` });
    });
  });
}

async function connect(chromePath) {
  const port = 9300 + Math.floor(Math.random() * 500);
  const profile = mkdtempSync(join(tmpdir(), "wiz-static-chrome-"));
  const proc = spawn(chromePath, [
    "--headless", "--no-sandbox", "--disable-gpu", "--disable-dev-shm-usage",
    `--remote-debugging-port=${port}`, `--user-data-dir=${profile}`,
    "--window-size=1280,900", "about:blank",
  ], { stdio: "ignore" });
  let target = null;
  for (let i = 0; i < 100 && !target; i++) {
    await sleep(150);
    try {
      target = (await (await fetch(`http://127.0.0.1:${port}/json/list`)).json())
        .find((t) => t.type === "page");
    } catch { /* not listening yet */ }
  }
  if (!target) {
    proc.kill("SIGKILL");
    throw new Error("Chromium did not open a DevTools target");
  }
  const ws = new WebSocket(target.webSocketDebuggerUrl);
  await new Promise((r, j) => {
    ws.addEventListener("open", r);
    ws.addEventListener("error", j);
  });
  let id = 0;
  const pending = new Map();
  const errors = [];
  ws.addEventListener("message", (m) => {
    const msg = JSON.parse(m.data);
    if (msg.id && pending.has(msg.id)) {
      pending.get(msg.id)(msg.result);
      pending.delete(msg.id);
    }
    if (msg.method === "Runtime.exceptionThrown") {
      errors.push(msg.params.exceptionDetails.exception?.description ||
        msg.params.exceptionDetails.text || "exception");
    }
  });
  const call = (method, params = {}) => new Promise((r) => {
    pending.set(++id, r);
    ws.send(JSON.stringify({ id, method, params }));
  });
  return {
    call, errors,
    close: () => { try { ws.close(); } catch {} proc.kill("SIGKILL"); },
  };
}

// The no-JavaScript load: disable script execution before navigating and read the HTML
// the browser parsed, with no page script having run.
async function noScriptDom(chromePath, url) {
  const { call, close } = await connect(chromePath);
  try {
    await call("Page.enable");
    await call("DOM.enable");
    await call("Emulation.setScriptExecutionDisabled", { value: true });
    await call("Page.navigate", { url });
    let html = "";
    for (let i = 0; i < 100; i++) {
      await sleep(100);
      try {
        const rootNode = (await call("DOM.getDocument", { depth: 0 })).root;
        html = (await call("DOM.getOuterHTML", { nodeId: rootNode.nodeId })).outerHTML || "";
      } catch { /* the document is being replaced */ }
      if (html.includes('id="app"') && html.includes("</html>")) break;
    }
    return html;
  } finally {
    close();
  }
}

async function session(chromePath, url) {
  const { call, errors, close } = await connect(chromePath);
  const evaluate = async (expression) => {
    const r = await call("Runtime.evaluate", { expression, returnByValue: true, awaitPromise: true });
    if (r && r.exceptionDetails) {
      throw new Error(r.exceptionDetails.exception?.description || r.exceptionDetails.text);
    }
    return r && r.result ? r.result.value : undefined;
  };
  const waitFor = async (expression, ms = 25000) => {
    const end = Date.now() + ms;
    while (Date.now() < end) {
      try { if (await evaluate(expression)) return true; } catch { /* navigating */ }
      await sleep(100);
    }
    return false;
  };
  await call("Runtime.enable");
  await call("Page.enable");
  await call("Page.navigate", { url });
  const loaded = await waitFor(`typeof globalThis.wizPatch === "function" &&
    (globalThis.wizLoomMode === "adopt" || globalThis.wizLoomMode === "replace")`);
  return { call, evaluate, waitFor, errors, loaded, close };
}

const { server, url } = await serve(root);
try {
  // ## 1. The JS-off load is the page
  const dom = await noScriptDom(chrome, url);
  ok(dom.length > 0, "the no-JavaScript load produced a DOM");
  ok(/<div id="app" data-wiz-island="loom\/1" data-wiz-ssr="t1-[0-9a-f]{8}-\d+-\d+">/u.test(dom),
    "the no-JavaScript page has the island and its normalised hash");
  for (const want of ["<header", "<main", "<footer", 'id="editor"', 'id="preset"',
    'id="output"', 'id="goals"', 'id="status"']) {
    ok(dom.includes(want), "the no-JavaScript page has " + want);
  }
  ok(!dom.includes("data-wiz-error"), "the no-JavaScript page has no mount error");
  ok(count(dom, /<noscript>/g) === 1 && dom.includes("needs JavaScript"),
    "the page explains why it is inert without JavaScript");
  ok(/<textarea[^>]*id="editor"[^>]*>[\s\S]*?def /u.test(dom),
    "the no-JavaScript editor shows the default program");

  // ## 2. The JS-on load adopts the static tree and morphs without losing focus
  const page = await session(chrome, url);
  try {
    ok(page.loaded, "the runtime mounts (wizPatch and a mode are published)");
    const state = await page.evaluate(`({
      mode: globalThis.wizLoomMode,
      error: document.getElementById("app").hasAttribute("data-wiz-error"),
      toolbarSame: window.__staticToolbar === document.querySelector("#app .toolbar"),
      editorSame: window.__staticEditor === document.getElementById("editor"),
      headers: document.querySelectorAll("#app > header").length,
      mains: document.querySelectorAll("#app > main").length,
      footers: document.querySelectorAll("#app > footer").length,
    })`);
    ok(state.mode === "adopt", "the page adopts the static tree, not replaces it",
      String(state.mode));
    ok(state.toolbarSame, "adopt keeps the static toolbar node");
    ok(state.editorSame, "adopt keeps the static editor node");
    ok(!state.error, "the adopted page has no data-wiz-error");
    ok(state.headers === 1 && state.mains === 1 && state.footers === 1,
      "the adopted page still has one header, main and footer", JSON.stringify(state));

    const morphed = await page.evaluate(`(() => {
      const app = document.getElementById("app");
      const main = document.querySelector("#app > main");
      const index = [...app.childNodes].indexOf(main);
      const editor = document.getElementById("editor");
      editor.value = "hello\\nworld";
      editor.focus();
      editor.setSelectionRange(2, 7);
      const html = main.outerHTML.replace(">Output<", ">Output (morphed)<");
      globalThis.wizPatch(JSON.stringify([{ op: "replace", path: String(index), html }]));
      return {
        same: document.getElementById("editor") === editor,
        active: document.activeElement === editor,
        value: editor.value,
        start: editor.selectionStart,
        end: editor.selectionEnd,
        text: main.textContent.includes("Output (morphed)"),
      };
    })()`);
    ok(morphed.same, "a touching replace of <main> keeps the focused textarea node");
    ok(morphed.active, "the textarea is still document.activeElement");
    ok(morphed.value === "hello\nworld", "the live value survives the morph", morphed.value);
    ok(morphed.start === 2 && morphed.end === 7,
      "the selection survives the morph", morphed.start + "," + morphed.end);
    ok(morphed.text, "the replace's real change still lands");
    ok(page.errors.length === 0, "the browser console has no uncaught exception",
      page.errors.join("\n  "));
  } finally {
    page.close();
  }
} finally {
  server.close();
}

console.log(failed === 0 ? "static chrome: all checks passed"
  : `static chrome: ${failed} failure(s)`);
process.exit(failed === 0 ? 0 : 1);
