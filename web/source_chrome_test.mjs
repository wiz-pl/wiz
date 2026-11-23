// The source reader in headless Chromium, over the DevTools protocol and the same
// static server the bundle is meant to be served from. This is the browser half of
// `web/source_static_test.mjs`: that test applies the Loom patches to the SSR with the
// minidom double; this one asks a real browser whether the module mounts, whether a
// `mouseover` on the sink reaches the runtime and returns the finding's rule, whether
// `#/f/<id>` selects the row on a cold load, and — with `?lsp=` — whether a pointer over
// a Wiz source line asks a language server for hover and definition and the answer lands
// in the reader's own panels.
//
// The page is also loaded with scripting disabled. The SSR is the product (WEB-1.3), so
// that load must already list the files and both findings, show the taint.c source and
// carry `data-finding`; JavaScript is only the hover/selection enhancement.
//
//   usage: node web/source_chrome_test.mjs CHROMIUM BUNDLE_DIR [WIZ_BIN]
//
// Run it from the checkout root (the `?lspRoot=` the live page needs is the cwd). The
// bundle must be the packaged one (`web/source-bundle.sh`), which carries both the
// runtime's `.mjs` and its `.wasm`; a bundle with a Wiz `--source` file exercises the
// live section, a plain one skips it. `WIZ_BIN` is a built `wiz`; without it the test
// starts `web/mock_lsp_server.mjs` (the repo's stand-in, the same protocol), which is
// the fallback path, and says which one ran. The test starts its own static server on
// 127.0.0.1:0 and its own language server; no port argument is needed.
"use strict";
import { spawn } from "node:child_process";
import { createServer } from "node:http";
import { mkdtempSync, readFileSync } from "node:fs";
import { readFile, stat } from "node:fs/promises";
import { tmpdir } from "node:os";
import { extname, join, normalize, resolve, sep } from "node:path";
import { startMockServer } from "./mock_lsp_server.mjs";
import { startWizLsp } from "./source_lsp.mjs";

const [chrome, bundleArg, wizBin] = process.argv.slice(2);
if (!chrome || !bundleArg) {
  console.error("usage: node web/source_chrome_test.mjs CHROMIUM BUNDLE_DIR [WIZ_BIN]");
  process.exit(2);
}
const bundle = resolve(bundleArg);
const root = process.env.SCRY_WEB_ROOT ? resolve(process.env.SCRY_WEB_ROOT) : process.cwd();

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

function serve(dir) {
  const server = createServer(async (req, res) => {
    try {
      const pathname = decodeURIComponent(new URL(req.url, "http://127.0.0.1").pathname);
      let p = normalize(join(dir, pathname));
      if (!(p === dir || p.startsWith(dir + sep))) {
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

const readJson = (p) => JSON.parse(readFileSync(p, "utf-8"));
const findingsJson = (() => {
  try {
    return readJson(join(bundle, "data", "findings.json"));
  } catch (e) {
    console.error("source smoke: cannot read " + join(bundle, "data", "findings.json") + ": " + e.message);
    process.exit(2);
  }
})();
const filesJson = readJson(join(bundle, "data", "files.json"));
const findings = findingsJson.findings || [];
const fileCount = (filesJson.files || []).length;
const wizFiles = (filesJson.files || []).filter((f) => f.language === "wiz");
const byPath = (suffix) => findings.find((f) => String(f.path).replace(/\\/g, "/").endsWith(suffix));
const taint = byPath("taint.c");
const xss = byPath("xss.c");
if (!taint || !xss) {
  console.error("source smoke: the bundle has no taint.c/xss.c finding (run web/source-bundle.sh)");
  process.exit(1);
}
const taintFile = readJson(join(bundle, "data", "f", taint.fileId + ".json"));
const taintLine = (String(taintFile.source || "").split("\n")[Math.max(0, (taint.line || 1) - 1)] || "").trim();
const count = (html, re) => (html.match(re) || []).length;

// The Wiz file the live section reads: the reader's own model. A Wiz file under `lib/`
// matters: `wiz lsp` loads `lib/` as its module root, so the file's `import`s resolve
// (a file under `scry/` would need `-I scry/src`, which `wiz lsp` does not take).
const wiz = wizFiles.find((f) => String(f.path).replace(/\\/g, "/").endsWith("Web/Source/Model.wiz"))
  || wizFiles[0] || null;
const wizData = wiz ? readJson(join(bundle, "data", "f", wiz.id + ".json")) : null;

// ## A language server for the live section

// The real thing when the caller named a built wiz, else the repo's mock. Both are
// `textDocument/hover` + `textDocument/definition` over a WebSocket; nothing in the page
// knows which one is on the other end.
async function startLsp() {
  if (!wizBin) {
    const mock = await startMockServer();
    return {
      port: mock.port,
      kind: "mock",
      close: async () => { await mock.close(); },
    };
  }
  const srv = await startWizLsp(wizBin, root);
  return {
    port: srv.port,
    kind: "wiz",
    close: async () => { await srv.close(); },
  };
}

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
        const doc = (await call("DOM.getDocument", { depth: 0 })).root;
        html = (await call("DOM.getOuterHTML", { nodeId: doc.nodeId })).outerHTML || "";
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
async function connect(chromePath) {
  const port = 9300 + Math.floor(Math.random() * 500);
  const profile = mkdtempSync(join(tmpdir(), "wiz-source-chrome-"));
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
      document.querySelectorAll('li.file-row').length === ${fileCount}`);
  };
  await call("Runtime.enable");
  await call("Page.enable");
  const loaded = await goto(url);
  return {
    call, evaluate, has, waitFor, goto, errors, loaded, close,
  };
}

// ## Pointer → token, the way a person would: a Range around the token gives viewport
// coordinates, and a synthesised `mouseover`/`click` there is what the live host's
// `caretRangeFromPoint` reads. `line` is found by a substring of its text.
async function pointerAt(page, marker, needle, kind) {
  return page.evaluate(`(() => {
    const marker = ${JSON.stringify(marker)};
    const needle = ${JSON.stringify(needle)};
    const lines = [...document.querySelectorAll("div.src-line")];
    const line = lines.find((el) => (el.textContent || "").includes(marker));
    if (!line) return { error: "no line containing " + marker };
    line.scrollIntoView({ block: "center", inline: "nearest" });
    const code = line.querySelector("code.line");
    const text = code ? (code.textContent || "") : "";
    const idx = text.indexOf(needle);
    if (idx < 0) return { error: "no " + needle + " in the line" };
    const start = idx;
    const stop = idx + needle.replace(/[^A-Za-z0-9_]+$/, "").length;
    const walker = document.createTreeWalker(code, NodeFilter.SHOW_TEXT);
    let node, seen = 0, a = null, b = null;
    while ((node = walker.nextNode())) {
      const next = seen + node.data.length;
      if (a === null && start >= seen && start < next) a = [node, start - seen];
      if (b === null && stop > seen && stop <= next) b = [node, stop - seen];
      seen = next;
    }
    if (!a || !b) return { error: "no text node for the token" };
    const range = document.createRange();
    range.setStart(a[0], a[1]);
    range.setEnd(b[0], b[1]);
    const r = range.getBoundingClientRect();
    if (!r || r.width === 0 && r.height === 0) return { error: "no box for the token" };
    const at = { clientX: r.left + 2, clientY: r.top + Math.min(3, Math.max(1, r.height / 2)) };
    const ev = new MouseEvent(${JSON.stringify(kind)}, { bubbles: true, ...at });
    line.dispatchEvent(ev);
    return { text: line.textContent, x: at.clientX, y: at.clientY };
  })()`);
}

const { server, url } = await serve(bundle);
let lsp = null;
try {
  // ## 1. The SSR is the page with JavaScript off

  const dom = await noScriptDom(url);
  ok(dom.length > 0, "the no-JavaScript load produced a DOM", "empty DOM");
  ok(count(dom, /class="source-reader"/g) === 1, "the SSR has one .source-reader");
  ok(count(dom, /<li class="file-row[^"]*"/g) === fileCount,
    "the SSR lists every file (" + fileCount + ")",
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
  if (wiz) {
    ok(dom.includes(`data-file="${wiz.id}"`), "the SSR lists the Wiz source file",
      String(wiz.path));
  }

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
    ok(state.files === fileCount, "the mounted page keeps every file row", String(state.files));
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

    // ## 4. The live host: hover and definition on a Wiz source line
    //
    // `?lsp=` mounts the same `wiz-source-ui.mjs` through `source-live.js`; the pointer
    // over a line goes to `caretRangeFromPoint`, then the runtime's `hover-at`/
    // `definition-at` effects, then `textDocument/hover` / `textDocument/definition`.
    if (!wiz) {
      console.log("skip: the bundle has no Wiz --source file (live hover/definition)");
    } else {
      lsp = await startLsp();
      const liveUrl = url + "?lsp=" + lsp.port + "&lspRoot=" + encodeURIComponent(root);
      await page.call("Page.navigate", { url: "about:blank" });
      await sleep(200);
      const liveLoaded = await page.goto(liveUrl);
      ok(liveLoaded, "the ?lsp= page mounts the same runtime");
      const opened = await page.waitFor(`document.getElementById("app").getAttribute("data-lsp") === "open"`, 30000);
      ok(opened, "the live host connects to the language server (" + lsp.kind + ")",
        await page.evaluate(`document.getElementById("app").getAttribute("data-lsp")`));

      // Open the Wiz file in the pane.
      await page.evaluate(`document.querySelector('li.file-row[data-file="${wiz.id}"]')?.click()`);
      const onFile = await page.waitFor(
        `document.querySelector('section.source-pane')?.getAttribute('data-file') === "${wiz.id}"`, 5000);
      ok(onFile, "the Wiz file opens in the source pane", String(wiz.path));

      // Hover the `show` of `Source.Span.show` in the reader's own model.
      const over = await pointerAt(page, "Source.Span.show i span", "show i span", "mouseover");
      ok(!over || !over.error, "the pointer lands on a Wiz identifier",
        over && over.error ? over.error : "");
      const card = await page.waitFor(
        `!!document.querySelector(".hover-host .wiz-hover")`, 30000);
      const cardText = await page.evaluate(
        `document.querySelector(".hover-host")?.textContent || ""`);
      if (lsp.kind === "wiz") {
        ok(card && /show/.test(cardText), "hovering a Wiz name returns its LSP signature",
          cardText.slice(0, 200));
        ok(/LSP hover at/.test(cardText), "the card says it is a live LSP answer",
          cardText.slice(0, 120));
      } else {
        ok(card && /Nat\.add/.test(cardText), "hovering a Wiz name returns the mock's card",
          cardText.slice(0, 200));
      }

      // Click the same name: `textDocument/definition`, parsed by Web.Hover, mapped to a
      // bundle file and outlined there.
      const clicked = await pointerAt(page, "Source.Span.show i span", "show i span", "click");
      ok(!clicked || !clicked.error, "the click lands on a Wiz identifier",
        clicked && clicked.error ? clicked.error : "");
      const definition = await page.waitFor(
        `!!document.querySelector('section.info-pane .fact-row[data-kind="definition"]')`, 30000);
      const def = await page.evaluate(`(() => {
        const row = document.querySelector('section.info-pane .fact-row[data-kind="definition"]');
        if (!row) return null;
        const cells = [...row.querySelectorAll(".fact-cell")].map((c) => ({
          key: c.querySelector(".fact-key")?.textContent || "",
          value: c.querySelector(".fact-value")?.textContent || "",
        }));
        const pane = document.querySelector("section.source-pane");
        const focus = document.querySelector(".src-mark.src-focus");
        return {
          target: cells.find((c) => c.key === "target")?.value || "",
          uri: cells.find((c) => c.key === "uri")?.value || "",
          file: pane ? pane.getAttribute("data-file") : null,
          focus: focus ? focus.getAttribute("data-span") : null,
        };
      })()`);
      ok(definition && def, "the definition answer lands in the reader's info panel",
        JSON.stringify(def));
      if (lsp.kind === "wiz") {
        ok(def && /Span\.wiz/.test(def.target), "the definition names Span.wiz",
          def && def.target);
        const spanFile = (filesJson.files || []).find(
          (f) => String(f.path).replace(/\\/g, "/").endsWith("Web/Source/Span.wiz"));
        if (spanFile) {
          ok(def && def.file === spanFile.id,
            "the definition jumps to the bundled Span.wiz", def && def.file);
          ok(def && /^1[0-9]{2}:/.test(String(def.focus || "")),
            "the definition range is outlined in the source pane", def && def.focus);
        } else {
          console.log("skip: Span.wiz is not in the bundle (the jump cannot land)");
        }
      } else {
        ok(def && def.focus, "the mock definition outlines its range", def && def.focus);
      }

      // ## 5. A deliberate failure: the server goes away mid-session
      //
      // The page must stay a working reader: the note names the failure, the next hover
      // is "no answer" (or the bundle's own answer), and no error banner appears.
      // Re-open the Wiz model first: a successful definition may have jumped away.
      await page.evaluate(`document.querySelector('li.file-row[data-file="${wiz.id}"]')?.click()`);
      await page.waitFor(
        `document.querySelector('section.source-pane')?.getAttribute('data-file') === "${wiz.id}"`, 5000);
      await lsp.close();
      lsp = null;
      await sleep(300);
      await pointerAt(page, "Source.Span.show i span", "show i span", "mouseover");
      const survived = await page.waitFor(
        `(document.querySelector(".reader-foot .note")?.textContent || "").includes("live: hover failed")`,
        15000);
      const afterDeath = await page.evaluate(`({
        error: document.getElementById("app").hasAttribute("data-wiz-error"),
        files: document.querySelectorAll("li.file-row").length,
        findings: document.querySelectorAll("li.finding-row").length,
        none: !!document.querySelector(".hover-host.none"),
      })`);
      ok(survived, "a dead server is a note, not a silent failure", JSON.stringify(afterDeath));
      ok(afterDeath.files === fileCount && afterDeath.findings === 2,
        "the reader keeps its files and findings after the server dies",
        JSON.stringify(afterDeath));
      ok(!afterDeath.error, "a dead server writes no data-wiz-error");
    }

    ok(page.errors.length === 0, "the browser console has no error", page.errors.join("\n  "));
  } finally {
    page.close();
  }

  // ## 6. A deliberate failure at load: no server on the endpoint
  //
  // A closed port is the common case (the page outlives the server). The static reader
  // must be exactly as complete as the no-JS page.
  const dead = await session(url + "?lsp=1&lspRoot=" + encodeURIComponent(root));
  try {
    const off = await dead.waitFor(
      `document.getElementById("app").getAttribute("data-lsp") === "failed"`, 15000);
    const state = await dead.evaluate(`({
      error: document.getElementById("app").hasAttribute("data-wiz-error"),
      files: document.querySelectorAll("li.file-row").length,
      findings: document.querySelectorAll("li.finding-row").length,
      note: document.querySelector(".reader-foot .note")?.textContent || "",
    })`);
    ok(off, "a missing server leaves data-lsp=failed", JSON.stringify(state));
    ok(/live: off/.test(state.note), "the footer says the live reader is off", state.note);
    ok(state.files === fileCount && state.findings === 2,
      "the static reader is complete with no server", JSON.stringify(state));
    ok(!state.error, "a missing server writes no data-wiz-error");
    ok(dead.errors.length === 0, "the failed live load logs no browser error",
      dead.errors.join("\n  "));
  } finally {
    dead.close();
  }
} finally {
  if (lsp) await lsp.close();
  server.close();
}

console.log(failed === 0 ? "source smoke: all checks passed"
  : `source smoke: ${failed} failure(s)`);
process.exit(failed === 0 ? 0 : 1);
