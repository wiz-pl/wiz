// The source reader in headless Chromium, over the DevTools protocol and the same
// static server the bundle is meant to be served from. This is the browser half of
// `web/source_static_test.mjs`: that test applies the Loom patches to the SSR with the
// minidom double; this one asks a real browser whether the module mounts, whether a
// `mouseover` on the sink reaches the runtime and returns the finding's rule, and whether
// `#/f/<id>` selects the row on a cold load.
//
// The page is also loaded with scripting disabled. The SSR is the product (WEB-1.3), so
// that load must already list the files and both findings, show the taint.c source and
// carry `data-finding`; JavaScript is only the hover/selection enhancement.
//
//   usage: node web/source_chrome_test.mjs CHROMIUM BUNDLE_DIR
//
// The bundle must be the packaged one (`web/source-bundle.sh`), which carries both the
// runtime's `.mjs` and its `.wasm`. The test starts its own server on 127.0.0.1:0; no
// port or URL argument is needed.
"use strict";
import { spawn } from "node:child_process";
import { createServer } from "node:http";
import { mkdtempSync, readFileSync } from "node:fs";
import { readFile, stat } from "node:fs/promises";
import { tmpdir } from "node:os";
import { extname, join, normalize, resolve, sep } from "node:path";

const [chrome, bundleArg] = process.argv.slice(2);
if (!chrome || !bundleArg) {
  console.error("usage: node web/source_chrome_test.mjs CHROMIUM BUNDLE_DIR");
  process.exit(2);
}
const bundle = resolve(bundleArg);

let failed = 0;
const ok = (cond, what, detail = "") => {
  if (cond) console.log("ok: " + what);
  else { failed++; console.log("FAIL: " + what + (detail ? "\n  " + detail : "")); }
};
const sleep = (ms) => new Promise((r) => setTimeout(r, ms));

// ## A static server for the bundle (relative `data/`, the page's own imports)

const MIME = {
  ".html": "text/html; charset=utf-8",
  ".js": "text/javascript; charset=utf-8",
  ".mjs": "text/javascript; charset=utf-8",
  ".css": "text/css; charset=utf-8",
  ".json": "application/json; charset=utf-8",
  ".wasm": "application/wasm",
  ".txt": "text/plain; charset=utf-8",
};

function serve(root) {
  const server = createServer(async (req, res) => {
    try {
      const pathname = decodeURIComponent(new URL(req.url, "http://127.0.0.1").pathname);
      let p = normalize(join(root, pathname));
      if (!(p === root || p.startsWith(root + sep))) {
        res.writeHead(403).end("outside the bundle");
        return;
      }
      if ((await stat(p)).isDirectory()) p = join(p, "index.html");
      const body = await readFile(p);
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

// ## The bundle's facts (the ids and text the assertions name)

const findingsJson = (() => {
  try {
    return JSON.parse(readFileSync(join(bundle, "data", "findings.json"), "utf-8"));
  } catch (e) {
    console.error("source smoke: cannot read " + join(bundle, "data", "findings.json") + ": " + e.message);
    process.exit(2);
  }
})();
const findings = findingsJson.findings || [];
const byPath = (suffix) => findings.find((f) => String(f.path).replace(/\\/g, "/").endsWith(suffix));
const taint = byPath("taint.c");
const xss = byPath("xss.c");
if (!taint || !xss) {
  console.error("source smoke: the bundle has no taint.c/xss.c finding (run web/source-bundle.sh)");
  process.exit(1);
}
const taintFile = JSON.parse(readFileSync(join(bundle, "data", "f", taint.fileId + ".json"), "utf-8"));
const taintLine = (String(taintFile.source || "").split("\n")[Math.max(0, (taint.line || 1) - 1)] || "").trim();
const count = (html, re) => (html.match(re) || []).length;

// ## The no-JavaScript load: a CDP session with script execution disabled

// `--blink-settings=scriptEnabled=false --dump-dom` prints nothing on the Chromium used
// here (157), so the no-JS load is a DevTools session that disables script execution
// before navigating and reads the parsed DOM through the DOM domain. That is still a
// real no-JavaScript load: no page script runs, and the HTML the browser parsed is what
// the assertions see.
async function noScriptDom(url) {
  const { call, close } = await connect(chrome);
  try {
    await call("Page.enable");
    await call("DOM.enable");
    await call("Emulation.setScriptExecutionDisabled", { value: true });
    await call("Page.navigate", { url });
    let html = "";
    for (let i = 0; i < 100; i++) {
      await sleep(100);
      try {
        const root = (await call("DOM.getDocument", { depth: 0 })).root;
        html = (await call("DOM.getOuterHTML", { nodeId: root.nodeId })).outerHTML || "";
      } catch { /* the document is being replaced */ }
      if (html.includes("source-reader")) break;
    }
    return html;
  } finally {
    close();
  }
}

// ## The JavaScript load: Chromium's DevTools protocol (the repo's existing browser tooling)

// Start Chromium and connect to its page target. `errors` collects uncaught exceptions
// and console errors; the no-script session does not use them.
async function connect(chrome) {
  const port = 9300 + Math.floor(Math.random() * 500);
  const profile = mkdtempSync(join(tmpdir(), "wiz-source-chrome-"));
  const proc = spawn(chrome, [
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
    if (msg.method === "Runtime.consoleAPICalled" && msg.params.type === "error") {
      errors.push(msg.params.args.map((a) => a.value ?? a.description ?? "").join(" "));
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

async function session(url) {
  const { call, errors, close } = await connect(chrome);
  const evaluate = async (expression) => {
    const r = await call("Runtime.evaluate", { expression, returnByValue: true, awaitPromise: true });
    if (r && r.exceptionDetails) {
      throw new Error(r.exceptionDetails.exception?.description || r.exceptionDetails.text);
    }
    return r && r.result ? r.result.value : undefined;
  };
  const has = (sel) => evaluate(`!!document.querySelector(${JSON.stringify(sel)})`);
  const waitFor = async (expression, ms = 25000) => {
    const end = Date.now() + ms;
    while (Date.now() < end) {
      try { if (await evaluate(expression)) return true; } catch { /* navigating */ }
      await sleep(100);
    }
    return false;
  };
  const goto = async (next) => {
    await call("Page.navigate", { url: next });
    return waitFor(`typeof globalThis.wizPatch === "function" &&
      document.querySelectorAll('li.file-row').length === 3`);
  };
  await call("Runtime.enable");
  await call("Page.enable");
  const loaded = await goto(url);
  return {
    call, evaluate, has, waitFor, goto, errors, loaded, close,
  };
}

const { server, url } = await serve(bundle);
try {
  // ## 1. The SSR is the page with JavaScript off

  const dom = await noScriptDom(url);
  ok(dom.length > 0, "the no-JavaScript load produced a DOM", "empty DOM");
  ok(count(dom, /class="source-reader"/g) === 1, "the SSR has one .source-reader");
  ok(count(dom, /<li class="file-row[^"]*"/g) === 3, "the SSR lists the three files",
    String(count(dom, /<li class="file-row[^"]*"/g)));
  ok(count(dom, /<li class="finding-row[^"]*"/g) === 2, "the SSR lists both findings",
    String(count(dom, /<li class="finding-row[^"]*"/g)));
  ok(dom.includes(`data-finding="${taint.id}"`), "the SSR carries the taint finding's data-finding");
  ok(dom.includes("system") && taintLine.includes("system"),
    "the SSR contains the taint.c source text", taintLine);
  ok(dom.includes("This page is complete without JavaScript"),
    "the page says the SSR is complete without JavaScript");
  ok(!dom.includes("This reader needs JavaScript"), "the page does not claim JavaScript is required");
  ok(!dom.includes("data-wiz-error"), "the no-JavaScript page has no data-wiz-error");

  // ## 2. The runtime mounts and answers a hover with its rule

  const page = await session(url);
  try {
    ok(page.loaded, "the Loom runtime mounts (wiz_loom_init/html/step ran)");
    const state = await page.evaluate(`({
      error: document.getElementById("app").hasAttribute("data-wiz-error"),
      readers: document.querySelectorAll(".source-reader").length,
      files: document.querySelectorAll("li.file-row").length,
      findings: document.querySelectorAll("li.finding-row").length,
      patch: typeof globalThis.wizPatch === "function",
    })`);
    ok(!state.error, "the mounted page has no data-wiz-error");
    ok(state.readers === 1, "the mounted page has one .source-reader", String(state.readers));
    ok(state.files === 3, "the mounted page keeps the three file rows", String(state.files));
    ok(state.findings === 2, "the mounted page keeps both finding rows", String(state.findings));
    ok(state.patch, "the driver installed the patch applier (the wiz_loom_* ABI ran)");

    // The source pane opens the first file with a finding (taint.c); click the row if a
    // different first-paint choice ever changes that.
    if (!(await page.has(`.src-mark[data-finding="${taint.id}"]`))) {
      await page.evaluate(`document.querySelector('li.file-row[data-file="${taint.fileId}"]')?.click()`);
      await page.waitFor(`!!document.querySelector('.src-mark[data-finding="${taint.id}"]')`, 5000);
    }
    const mark = await page.evaluate(`(() => {
      const el = document.querySelector('.src-mark[data-finding="${taint.id}"]');
      if (!el) return null;
      el.dispatchEvent(new MouseEvent("mouseover", { bubbles: true }));
      return el.getAttribute("data-span");
    })()`);
    ok(!!mark, "the source pane marks the taint finding", String(mark));
    const hovered = await page.waitFor(
      `(document.querySelector('.hover-host')?.getAttribute('data-rule') || '') === "command-injection"`,
      10000);
    const hover = await page.evaluate(`(() => {
      const host = document.querySelector(".hover-host");
      const card = document.querySelector(".wiz-hover");
      return host ? { rule: host.getAttribute("data-rule"),
        finding: host.getAttribute("data-finding"),
        text: host.textContent || "", card: !!card } : null;
    })()`);
    ok(hovered && hover && hover.rule === "command-injection",
      "hovering the sink returns the finding's rule", JSON.stringify(hover));
    ok(!!hover && hover.finding === taint.id,
      "the hover card names the taint finding", hover && hover.finding);
    ok(!!hover && hover.card && hover.text.includes(taint.spanText || "\u0000"),
      "the hover card shows the span", hover && hover.text.slice(0, 160));

    // ## 3. `#/f/<id>` selects the row after a full reload

    // about:blank first, so this is a document load with the fragment, not a
    // same-document `hashchange` (the router must handle a cold link).
    await page.call("Page.navigate", { url: "about:blank" });
    await sleep(200);
    const cold = await page.goto(url + "#/f/" + xss.id);
    ok(cold, "the #/f/<id> cold load mounts the runtime");
    const routed = await page.evaluate(`(() => {
      const row = document.querySelector('li.finding-row[data-finding="${xss.id}"]');
      return {
        selected: row ? row.getAttribute("aria-selected") : null,
        cls: row ? row.className : null,
        selection: !!document.querySelector('section.selection[data-finding="${xss.id}"]'),
        file: document.querySelector("section.source-pane")?.getAttribute("data-file") || null,
        error: document.getElementById("app").hasAttribute("data-wiz-error"),
      };
    })()`);
    ok(routed.selected === "true", "#/f/<id> selects the row (aria-selected)",
      JSON.stringify(routed));
    ok(String(routed.cls || "").includes("selected"), "#/f/<id> marks the row .selected");
    ok(routed.selection, "#/f/<id> opens the finding's selection card");
    ok(routed.file === xss.fileId, "#/f/<id> opens the finding's file", String(routed.file));
    ok(!routed.error, "the routed page has no data-wiz-error");

    ok(page.errors.length === 0, "the browser console has no error", page.errors.join("\n  "));
  } finally {
    page.close();
  }
} finally {
  server.close();
}

console.log(failed === 0 ? "source smoke: all checks passed"
  : `source smoke: ${failed} failure(s)`);
process.exit(failed === 0 ? 0 : 1);
