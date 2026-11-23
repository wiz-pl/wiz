// The landing page in headless Chromium, over the DevTools protocol: a real no-JavaScript
// load (scripts disabled before navigation), the carousel's keyboard and deep-link
// paths, and the Loom island's adoption and one-setAttr step.
//
//   usage: node web/landing_chrome_test.mjs CHROMIUM SITE
//
// SITE is an assembled tree: index.html at the root, landing.css beside it, and
// landing/ with app.js, carousel.js, the framework and wiz-landing-ui.mjs/.wasm.
"use strict";
import { spawn } from "node:child_process";
import { createServer } from "node:http";
import { mkdtempSync, readFileSync } from "node:fs";
import { readFile, stat } from "node:fs/promises";
import { tmpdir } from "node:os";
import { extname, join, normalize, resolve, sep } from "node:path";

const [chrome, dirArg] = process.argv.slice(2);
if (!chrome || !dirArg) {
  console.error("usage: node web/landing_chrome_test.mjs CHROMIUM SITE");
  process.exit(2);
}
const root = resolve(dirArg);
const pageFile = join(root, "index.html");
const sleep = (ms) => new Promise((r) => setTimeout(r, ms));

let failed = 0;
const ok = (cond, what, detail = "") => {
  if (cond) console.log("ok: " + what);
  else { failed++; console.log("FAIL: " + what + (detail ? "\n  " + detail : "")); }
};

const MIME = {
  ".html": "text/html; charset=utf-8",
  ".js": "text/javascript; charset=utf-8",
  ".mjs": "text/javascript; charset=utf-8",
  ".css": "text/css; charset=utf-8",
  ".json": "application/json; charset=utf-8",
  ".wasm": "application/wasm",
  ".txt": "text/plain; charset=utf-8",
};

// Record the pre-script nodes so adoption can prove it kept them (injected into the
// served copy only; the artifact is untouched).
const SNAPSHOT = "<script>window.__staticIsland = document.getElementById('quantity-widget');" +
  "window.__staticPanel = document.querySelector('.slide');</script>";

function serve(dir) {
  const server = createServer(async (req, res) => {
    try {
      let pathname = decodeURIComponent(new URL(req.url, "http://127.0.0.1").pathname);
      if (pathname === "/") pathname = "/index.html";
      let p = normalize(join(dir, pathname));
      if (!(p === dir || p.startsWith(dir + sep))) {
        res.writeHead(403).end("outside the site");
        return;
      }
      if ((await stat(p)).isDirectory()) p = join(p, "index.html");
      let body = await readFile(p);
      if (p === pageFile) {
        const html = body.toString("utf-8");
        const at = html.indexOf('<script type="module"');
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
  const port = 9800 + Math.floor(Math.random() * 190);
  const profile = mkdtempSync(join(tmpdir(), "wiz-landing-chrome-"));
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
  const logs = [];
  ws.addEventListener("message", (m) => {
    const msg = JSON.parse(m.data);
    if (msg.id && pending.has(msg.id)) { pending.get(msg.id)(msg.result); pending.delete(msg.id); }
    if (msg.method === "Runtime.exceptionThrown") {
      errors.push(msg.params.exceptionDetails.exception?.description ||
        msg.params.exceptionDetails.text || "exception");
    }
    if (msg.method === "Runtime.consoleAPICalled") {
      logs.push((msg.params.args || []).map((a) => a.value ?? a.description ?? "").join(" "));
    }
  });
  const call = (method, params = {}) => new Promise((r) => {
    pending.set(++id, r);
    ws.send(JSON.stringify({ id, method, params }));
  });
  return { call, errors, logs, close: () => { try { ws.close(); } catch {} proc.kill("SIGKILL"); } };
}

// A scripts-disabled navigation. Screen-reader-style evidence only: the DOM, the
// layout metrics (has the fragment scrolled?) and a computed style (does :target
// apply?), all read through the protocol with no page JavaScript.
async function noScriptPage(chromePath, url) {
  const { call, close } = await connect(chromePath);
  try {
    await call("Page.enable");
    await call("DOM.enable");
    await call("CSS.enable");
    await call("Emulation.setScriptExecutionDisabled", { value: true });
    await call("Page.navigate", { url });
    let html = "";
    for (let i = 0; i < 100; i++) {
      await sleep(100);
      try {
        const rootNode = (await call("DOM.getDocument", { depth: -1 })).root;
        html = (await call("DOM.getOuterHTML", { nodeId: rootNode.nodeId })).outerHTML || "";
        if (html.includes('id="carousel"') && html.includes("</html>")) break;
      } catch { /* the document is being replaced */ }
    }
    const metrics = await call("Page.getLayoutMetrics");
    const scrollY = metrics.cssLayoutViewport ? metrics.cssLayoutViewport.pageY : 0;
    // The vectors panel, by id, to ask for its computed style.
    const doc = (await call("DOM.getDocument", { depth: -1 })).root;
    const hit = await call("DOM.querySelector", { nodeId: doc.nodeId, selector: '[id="/s/vectors"]' });
    let outline = "";
    if (hit && hit.nodeId) {
      const style = await call("CSS.getComputedStyleForNode", { nodeId: hit.nodeId });
      const map = new Map((style.computedStyle || []).map((p) => [p.name, p.value]));
      outline = map.get("outline-style") || "";
    }
    return { html, scrollY, outline };
  } finally {
    close();
  }
}

async function session(chromePath, url) {
  const { call, errors, logs, close } = await connect(chromePath);
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
  const carousel = await waitFor(`document.getElementById("carousel") &&
    document.getElementById("carousel").getAttribute("data-carousel") === "on"`);
  const island = await waitFor(`typeof globalThis.wizLoomMode === "string" &&
    document.getElementById("quantity-app") &&
    document.getElementById("quantity-app").hasAttribute("data-live")`);
  return { call, evaluate, waitFor, errors, logs, carousel, island, close };
}

const { server, url } = await serve(root);
try {
  // ## 1. Without JavaScript the page is the whole page
  const off = await noScriptPage(chrome, url + "#/s/vectors");
  ok(off.html.length > 0, "the scripts-disabled load produced a DOM");
  for (const want of ['id="carousel"', 'id="/s/quantities"', 'id="/s/vectors"',
    'id="/s/equality"', 'id="/s/native"', "Vec.head", "funext", "IO.println"]) {
    ok(off.html.includes(want), "without JS the page has " + want);
  }
  ok(!off.html.includes('data-carousel="on"'), "without JS the carousel is not enhanced");
  ok(off.html.includes("data-wiz-island"), "without JS the island's static tree is there");
  ok(!off.html.includes("data-live"), "without JS the island's select is CSS-hidden");
  ok(off.scrollY > 0, "the #/s/vectors fragment scrolled the page to the panel",
    String(off.scrollY));
  ok(off.outline.includes("dashed"), "the deep-linked panel is :target (the no-JS marker)",
    off.outline);
  ok(!off.html.includes("data-wiz-error"), "without JS there is no mount error");

  // ## 2. With JavaScript: the deep link, the carousel and the island
  const page = await session(chrome, url + "#/s/equality");
  try {
    ok(page.carousel, "the carousel enhancer ran");
    ok(page.island, "the island mounted (wizLoomMode and data-live)");
    const state = await page.evaluate(`({
      mode: globalThis.wizLoomMode,
      hash: location.hash,
      active: [...document.querySelectorAll(".slide[data-active]")].map((p) => p.id),
      selected: [...document.querySelectorAll('[role="tab"][aria-selected="true"]')].map((t) => t.id),
      visible: [...document.querySelectorAll(".slide")].filter((p) => getComputedStyle(p).display !== "none").map((p) => p.id),
      island: window.__staticIsland === document.getElementById("quantity-widget"),
      panel: window.__staticPanel === document.querySelector(".slide"),
      selectShown: getComputedStyle(document.getElementById("q-select")).display !== "none",
      transition: getComputedStyle(document.querySelector(".slide")).transitionDuration,
    })`);
    ok(state.mode === "adopt", "the island adopts the static tree", String(state.mode));
    ok(state.island && state.panel, "adoption keeps the static nodes");
    ok(state.hash === "#/s/equality", "the deep link is the selection", state.hash);
    ok(state.active.length === 1 && state.active[0] === "/s/equality",
      "the equality panel is the one active panel", JSON.stringify(state.active));
    ok(state.selected.length === 1 && state.selected[0] === "tab-equality",
      "exactly one tab is aria-selected", JSON.stringify(state.selected));
    ok(state.visible.length === 1 && state.visible[0] === "/s/equality",
      "exactly one panel is visible", JSON.stringify(state.visible));
    ok(state.selectShown, "the island's select is shown once the runtime mounted");
    ok(state.transition === "0s", "the slide has no animation (reduced-motion safe)",
      state.transition);

    // ## Keyboard: ArrowRight, End, Home, with focus following the selection
    const keyboard = await page.evaluate(`(() => {
      const active = () => document.querySelector('[role="tab"][aria-selected="true"]');
      active().focus();
      const key = (k) => active().dispatchEvent(new KeyboardEvent("keydown", { key: k, bubbles: true }));
      key("ArrowRight");
      const right = { id: active().id, focus: document.activeElement === active(), hash: location.hash };
      key("End");
      const end = { id: active().id, focus: document.activeElement === active() };
      key("Home");
      const home = { id: active().id, focus: document.activeElement === active() };
      return { right, end, home,
        selected: document.querySelectorAll('[role="tab"][aria-selected="true"]').length,
        visible: [...document.querySelectorAll(".slide")].filter((p) => getComputedStyle(p).display !== "none").length };
    })()`);
    ok(keyboard.right.id === "tab-native" && keyboard.right.focus,
      "ArrowRight selects the next tab and moves focus", JSON.stringify(keyboard.right));
    ok(keyboard.right.hash === "#/s/native", "ArrowRight updates the deep link",
      keyboard.right.hash);
    ok(keyboard.end.id === "tab-native" && keyboard.end.focus, "End selects the last tab");
    ok(keyboard.home.id === "tab-quantities" && keyboard.home.focus, "Home selects the first tab");
    ok(keyboard.selected === 1 && keyboard.visible === 1,
      "the roving selection stays unique", JSON.stringify(keyboard));

    // A click navigates the hash and selects the clicked panel.
    const clicked = await page.evaluate(`(() => {
      document.getElementById("tab-vectors").click();
      return new Promise((r) => setTimeout(() => r({
        hash: location.hash,
        active: document.querySelector(".slide[data-active]").id,
        status: document.getElementById("carousel-status").textContent,
        copy: (() => { const b = document.querySelector(".copy"); return !b.hidden; })(),
        clipboard: !!(navigator.clipboard && navigator.clipboard.writeText),
      }), 50));
    })()`);
    ok(clicked.hash === "#/s/vectors" && clicked.active === "/s/vectors",
      "a tab click selects its panel", JSON.stringify(clicked));
    ok(/Vectors|A length|of 4/u.test(clicked.status),
      "the live region announces the selection", clicked.status);
    ok(clicked.copy === clicked.clipboard,
      "the copy button appears exactly when the clipboard API exists",
      JSON.stringify(clicked));

    // ## The island: one state attribute, and nothing else
    const stepped = await page.evaluate(`(() => {
      const real = globalThis.wizPatch;
      const patches = [];
      globalThis.wizPatch = (json) => { patches.push(...JSON.parse(json)); real(json); };
      const select = document.getElementById("q-select");
      select.value = "1";
      select.dispatchEvent(new Event("change", { bubbles: true }));
      const root = document.getElementById("quantity-widget");
      const shown = [...document.querySelectorAll(".q-panel")]
        .filter((p) => getComputedStyle(p).display !== "none").map((p) => p.getAttribute("data-for"));
      globalThis.wizPatch = real;
      return { patches, klass: root.getAttribute("class"), shown };
    })()`);
    ok(stepped.patches.length === 1, "a state change is one patch", JSON.stringify(stepped.patches));
    const p = stepped.patches[0] || {};
    ok(p.op === "setAttr" && p.name === "class" && p.value === "q-app q1",
      "it is setAttr class q-app q1", JSON.stringify(p));
    ok(stepped.klass === "q-app q1", "the DOM root has the new class", stepped.klass);
    ok(stepped.shown.length === 1 && stepped.shown[0] === "1",
      "one quantity panel is shown", JSON.stringify(stepped.shown));
    ok(page.errors.length === 0, "the console has no uncaught exception",
      page.errors.join("\n  "));
    ok(!page.logs.some((line) => /SSR hash|replacing it|hash-collision/u.test(line)),
      "adoption emitted no replace warning", page.logs.join("\n  "));
  } finally {
    page.close();
  }
} finally {
  server.close();
}

console.log(failed === 0 ? "landing chrome: all checks passed"
  : `landing chrome: ${failed} failure(s)`);
process.exit(failed === 0 ? 0 : 1);
