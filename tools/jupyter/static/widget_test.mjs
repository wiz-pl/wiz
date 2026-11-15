#!/usr/bin/env node
// Headless-browser test of the Wiz notebook widget front end (tools/jupyter/static/
// widget.js), and the same scenario as a Node-only fallback.
//
//   node tools/jupyter/static/widget_test.mjs [--browser PATH] [--no-browser]
//                                             [--update] [--help]
//
// What runs:
//   1. the Node fallback, always: web/framework/minidom.mjs (a DOM test double) parses
//      the fixture's SSR, widget.js applies the patch the fake comm delivers, and the
//      serialised result is compared with the goldens.  No browser, no Python, no wiz.
//   2. the browser run, when Chrome/Chromium is installed: the same fixture and the
//      same assertions, but against a real DOM (the event objects, form-control value
//      properties and the browser's serialisation).  The page is served over HTTP by
//      this file, because ES modules do not load from file://.
//
// If no browser is found the browser run is skipped with a message and exit 0; the
// Node fallback still has to pass.  A found-but-broken browser is a failure.
//
// The goldens (`goldens/widget_initial.html`, `..._after_click.html`,
// `..._after_input.html`, `widget_comm.json`) are the serialised DOM after the first
// render and after each patch, plus the exact comm payloads.  A rendering regression is
// a diff; there is no screenshot.  Regenerate the fixture and goldens (needs a wiz
// binary, not needed to run the test) with:
//
//   WIZ=.lake/build/bin/wiz tools/jupyter/static/widget_gen.sh
//
//   WIZ_WIDGET_BROWSER=/path/to/chrome   pick a browser
//   WIZ_WIDGET_NO_BROWSER=1              force the Node fallback
//   WIZ_WIDGET_UPDATE=1                  rewrite the goldens from this run
"use strict";

import { spawn, spawnSync } from "node:child_process";
import { accessSync, constants, mkdtempSync, mkdirSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { createServer } from "node:http";
import { tmpdir } from "node:os";
import { dirname, extname, join, resolve, sep } from "node:path";
import { fileURLToPath } from "node:url";

import { runNodeScenario } from "./widget_checks.mjs";
import { parse } from "../../../web/framework/minidom.mjs";

const HERE = dirname(fileURLToPath(import.meta.url));
const ROOT = resolve(HERE, "../../..");
const GOLDEN_DIR = join(HERE, "goldens");
const FIXTURE = join(HERE, "widget_fixture.json");

const GOLDENS = {
  initial: "widget_initial.html",
  afterClick: "widget_after_click.html",
  afterInput: "widget_after_input.html",
};
const COMM_GOLDEN = "widget_comm.json";

const BROWSER_NAMES = ["chromium", "chromium-browser", "google-chrome",
  "google-chrome-stable", "chrome"];

const USAGE = `usage: node tools/jupyter/static/widget_test.mjs [options]

  --browser PATH    use this Chrome/Chromium (default: find one on PATH)
  --no-browser      skip the browser run (the Node fallback always runs)
  --update          rewrite the goldens from this run
  --help            this message

Environment: WIZ_WIDGET_BROWSER, WIZ_WIDGET_NO_BROWSER=1, WIZ_WIDGET_UPDATE=1.`;

async function main(port) {
  const args = process.argv.slice(2);
  if (args.includes("--help") || args.includes("-h")) { console.log(USAGE); return 0; }
  const noBrowser = args.includes("--no-browser") || envTrue("WIZ_WIDGET_NO_BROWSER");
  const update = args.includes("--update") || envTrue("WIZ_WIDGET_UPDATE");
  let browser = browserFromArgs(args) || process.env.WIZ_WIDGET_BROWSER || null;
  if (!browser && !noBrowser) browser = findBrowser();

  if (!exists(FIXTURE)) {
    console.error("FAIL: no fixture at " + FIXTURE);
    console.error("  regenerate it with: WIZ=.lake/build/bin/wiz tools/jupyter/static/widget_gen.sh");
    return 1;
  }
  const fixture = JSON.parse(readFileSync(FIXTURE, "utf8"));

  let failed = 0;

  // 1. The Node fallback: the pure patcher logic.
  let node;
  try {
    node = runNodeScenario(fixture, { parse });
    console.log("node fallback: " + node.checks.length + " checks passed");
  } catch (e) {
    console.error("FAIL: node fallback: " + (e && e.stack || e));
    return 1;
  }

  if (update) {
    writeGoldens(node);
    console.log("goldens: rewritten from the Node fallback");
  } else if (!checkGoldens("node", node)) {
    failed++;
  }

  // 2. The browser run, when there is a browser.
  let browserResult = null;
  if (noBrowser) {
    console.log("skip: browser (WIZ_WIDGET_NO_BROWSER); the Node fallback ran");
  } else if (!browser) {
    console.log("skip: browser (no Chrome/Chromium on PATH; set WIZ_WIDGET_BROWSER)");
    console.log("      the Node fallback ran; the goldens are still checked");
  } else {
    try {
      browserResult = await runBrowser(fixture, browser, port);
      console.log("browser (" + browser + "): " + browserResult.checks.length + " checks passed");
      if (!same(node.initial, browserResult.initial)
          || !same(node.afterClick, browserResult.afterClick)
          || !same(node.afterInput, browserResult.afterInput)) {
        console.error("FAIL: the browser and Node renderings differ");
        failed++;
      }
      if (!same(node.sent, browserResult.sent)) {
        console.error("FAIL: the browser and Node comm payloads differ");
        console.error("  node    " + JSON.stringify(node.sent));
        console.error("  browser " + JSON.stringify(browserResult.sent));
        failed++;
      }
      if (!update && !checkGoldens("browser", browserResult)) failed++;
    } catch (e) {
      console.error("FAIL: browser: " + (e && e.stack || e));
      failed++;
    }
  }

  if (failed) {
    console.error("\nwidget front end: " + failed + " failure(s)");
    return 1;
  }
  console.log("\nwidget front end: all checks passed"
    + (browserResult ? " (browser: " + browser + ")" : " (browser: skipped)"));
  return 0;
}

// -- goldens -------------------------------------------------------------

function writeGoldens(result) {
  mkdirSync(GOLDEN_DIR, { recursive: true });
  for (const [key, name] of Object.entries(GOLDENS)) {
    writeFileSync(join(GOLDEN_DIR, name), result[key] + "\n");
  }
  writeFileSync(join(GOLDEN_DIR, COMM_GOLDEN), JSON.stringify(result.sent, null, 2) + "\n");
}

function checkGoldens(label, result) {
  let ok = true;
  for (const [key, name] of Object.entries(GOLDENS)) {
    const want = read(join(GOLDEN_DIR, name));
    if (!same(want, result[key])) {
      ok = false;
      reportDiff(label + " " + name, want, result[key]);
    }
  }
  const wantComm = read(join(GOLDEN_DIR, COMM_GOLDEN));
  const gotComm = JSON.stringify(result.sent, null, 2);
  if (!same(wantComm, gotComm)) {
    ok = false;
    reportDiff(label + " " + COMM_GOLDEN, wantComm, gotComm);
  }
  console.log("goldens (" + label + "): " + (ok ? "match" : "FAIL"));
  return ok;
}

function read(path) {
  return readFileSync(path, "utf8").replace(/\n$/, "");
}

function reportDiff(what, want, got) {
  console.error("FAIL: golden " + what);
  const dir = mkdtempSync(join(tmpdir(), "wiz-widget-diff-"));
  const wantFile = join(dir, "expected");
  const gotFile = join(dir, "actual");
  writeFileSync(wantFile, want + "\n");
  writeFileSync(gotFile, got + "\n");
  const diff = spawnSync("diff", ["-u", "--label", "expected", "--label", "actual",
    wantFile, gotFile], { encoding: "utf8" });
  if (!diff.error && diff.stdout) {
    console.error(diff.stdout.replace(/\n$/, ""));
  } else {
    console.error("  expected: " + JSON.stringify(want));
    console.error("  actual:   " + JSON.stringify(got));
  }
  console.error("  (files kept in " + dir + ")");
}

// -- browser discovery ---------------------------------------------------

function browserFromArgs(args) {
  for (let i = 0; i < args.length; i++) {
    if (args[i] === "--browser") return args[++i] || null;
    if (args[i].startsWith("--browser=")) return args[i].slice("--browser=".length);
  }
  return null;
}

function findBrowser() {
  for (const name of BROWSER_NAMES) {
    for (const dir of (process.env.PATH || "").split(":")) {
      if (!dir) continue;
      const candidate = join(dir, name);
      try {
        accessSync(candidate, constants.X_OK);
        return candidate;
      } catch {}
    }
  }
  return null;
}

function exists(path) {
  try { accessSync(path, constants.R_OK); return true; } catch { return false; }
}

// -- the HTTP server (ES modules need an http origin) --------------------

function startServer() {
  const types = { ".html": "text/html; charset=utf-8", ".js": "text/javascript; charset=utf-8",
    ".mjs": "text/javascript; charset=utf-8", ".json": "application/json; charset=utf-8",
    ".css": "text/css; charset=utf-8", ".map": "application/json" };
  const server = createServer((req, res) => {
    let rel = "/tools/jupyter/static/widget_test.html";
    try {
      const url = new URL(req.url, "http://127.0.0.1");
      if (url.pathname && url.pathname !== "/") rel = decodeURIComponent(url.pathname);
    } catch {}
    const file = resolve(ROOT, "." + rel);
    if (file !== ROOT && !file.startsWith(ROOT + sep)) {
      res.statusCode = 403;
      res.end("outside the checkout");
      return;
    }
    try {
      const body = readFileSync(file);
      res.setHeader("Content-Type", types[extname(file)] || "application/octet-stream");
      res.end(body);
    } catch {
      res.statusCode = 404;
      res.end("not found: " + rel);
    }
  });
  return new Promise((accept, reject) => {
    server.on("error", reject);
    server.listen(0, "127.0.0.1", () => accept({ server, port: server.address().port }));
  });
}

// -- headless Chrome over the DevTools protocol --------------------------

async function runBrowser(fixture, browser, port) {
  const profile = mkdtempSync(join(tmpdir(), "wiz-widget-chrome-"));
  const proc = spawn(browser, [
    "--headless=new", "--no-sandbox", "--disable-gpu", "--disable-dev-shm-usage",
    "--disable-crash-reporter", "--disable-breakpad",
    "--remote-debugging-port=0", "--user-data-dir=" + profile, "about:blank",
  ], { stdio: "ignore", detached: true });
  try { proc.unref(); } catch {}

  const stop = () => {
    try { process.kill(-proc.pid, "SIGKILL"); } catch {}
    try { proc.kill("SIGKILL"); } catch {}
    // The Nix wrapper may have exec'd a browser that is no longer in the child's
    // process group; kill everything holding this unique profile.
    try { spawnSync("pkill", ["-9", "-f", profile], { stdio: "ignore" }); } catch {}
    try { rmSync(profile, { recursive: true, force: true }); } catch {}
  };
  const timer = setTimeout(stop, 45000);

  try {
    const debugPort = await waitForDebugPort(profile, proc);
    const target = await waitForTarget(debugPort, proc);
    const ws = new WebSocket(target.webSocketDebuggerUrl);
    await Promise.race([
      new Promise((accept, reject) => {
        ws.addEventListener("open", accept, { once: true });
        ws.addEventListener("error", () => reject(new Error("DevTools websocket failed")), { once: true });
      }),
      sleep(10000).then(() => { throw new Error("DevTools websocket did not open after 10s"); }),
    ]);
    let nextId = 0;
    const pending = new Map();
    const errors = [];
    ws.addEventListener("message", (m) => {
      const msg = JSON.parse(m.data);
      if (msg.id && pending.has(msg.id)) {
        const { accept, reject } = pending.get(msg.id);
        pending.delete(msg.id);
        if (msg.error) reject(new Error(msg.error.message || JSON.stringify(msg.error)));
        else accept(msg.result);
      } else if (msg.method === "Runtime.exceptionThrown") {
        errors.push(msg.params.exceptionDetails.exception?.description
          || msg.params.exceptionDetails.text);
      } else if (msg.method === "Runtime.consoleAPICalled" && msg.params.type === "error") {
        errors.push(msg.params.args.map((a) => a.value).join(" "));
      }
    });
    const call = (method, params = {}) => new Promise((accept, reject) => {
      const id = ++nextId;
      pending.set(id, { accept, reject });
      ws.send(JSON.stringify({ id, method, params }));
    });
    const evaluate = async (expression) => {
      const result = await call("Runtime.evaluate",
        { expression, returnByValue: true, awaitPromise: true });
      if (result.exceptionDetails) {
        throw new Error(result.exceptionDetails.exception?.description
          || result.exceptionDetails.text);
      }
      return result.result.value;
    };

    await call("Runtime.enable");
    await call("Page.enable");
    await call("Page.navigate", { url: `http://127.0.0.1:${port}/tools/jupyter/static/widget_test.html` });

    let payload = null;
    for (let i = 0; i < 150 && payload === null; i++) {
      await sleep(100);
      payload = await evaluate("globalThis.__widgetTest ? JSON.stringify(globalThis.__widgetTest) : null");
    }
    if (payload === null) {
      throw new Error("the page never filled globalThis.__widgetTest"
        + (errors.length ? "\nconsole errors:\n  " + errors.join("\n  ") : ""));
    }
    const result = JSON.parse(payload);
    if (!result.ok) throw new Error("page error:\n" + result.error);
    if (errors.length) throw new Error("console errors:\n  " + errors.join("\n  "));
    try { ws.close(); } catch {}
    return result.result;
  } finally {
    clearTimeout(timer);
    stop();
  }
}

async function waitForDebugPort(profile, proc) {
  const file = join(profile, "DevToolsActivePort");
  const deadline = Date.now() + 20000;
  while (Date.now() < deadline) {
    if (proc.exitCode !== null) {
      throw new Error("the browser exited (code " + proc.exitCode + ") before DevTools was ready");
    }
    try {
      const lines = readFileSync(file, "utf8").trim().split("\n");
      const port = Number(lines[0]);
      if (Number.isFinite(port) && port > 0) return port;
    } catch {}
    await sleep(100);
  }
  throw new Error("no DevToolsActivePort after 20s");
}

async function waitForTarget(port, proc) {
  for (let i = 0; i < 150; i++) {
    if (proc.exitCode !== null) {
      throw new Error("the browser exited (code " + proc.exitCode + ") before DevTools was ready");
    }
    try {
      const list = await (await fetch(`http://127.0.0.1:${port}/json/list`,
        { signal: AbortSignal.timeout(2000) })).json();
      const page = list.find((t) => t.type === "page");
      if (page && page.webSocketDebuggerUrl) return page;
    } catch {}
    await sleep(100);
  }
  throw new Error("no DevTools page after 15s");
}

function sleep(ms) {
  return new Promise((r) => setTimeout(r, ms));
}

function envTrue(name) {
  const v = process.env[name];
  return v !== undefined && v !== "" && v !== "0" && v.toLowerCase() !== "false";
}

function same(a, b) {
  return JSON.stringify(a) === JSON.stringify(b);
}

// -- entry point ---------------------------------------------------------

const handle = await startServer();
try {
  process.exitCode = await main(handle.port);
} finally {
  handle.server.close();
}
