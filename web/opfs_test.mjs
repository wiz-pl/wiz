// Exercise OPFS synchronous access handles in a worker, with a second tab open, over the
// DevTools protocol (the same hand-rolled CDP style as web/chrome_test.mjs: no npm).
//
//   usage: node web/opfs_test.mjs [CHROMIUM]
//
// What it proves, and what it falsifies:
//   * a worker that owns the "instance" can mount (async), pre-open, then write, seek and
//     read a file with FileSystemSyncAccessHandle methods only -- synchronously;
//   * a second tab is refused the exclusive lock (NoModificationAllowedError), and can
//     take it once the first closes it;
//   * a main-thread instance cannot have a sync handle, and cannot block on a worker
//     (Atomics.wait throws): the synchronous `open` the runtime needs does not exist on
//     the main thread.
import { spawn } from "node:child_process";
import { mkdtempSync, readFileSync } from "node:fs";
import { createServer } from "node:http";
import { tmpdir } from "node:os";
import { extname, join, normalize } from "node:path";

const chrome = process.argv[2] || "chromium";
const here = new URL(".", import.meta.url).pathname;
const root = normalize(join(here, "opfs"));

const types = { ".html": "text/html; charset=utf-8", ".mjs": "text/javascript; charset=utf-8",
  ".js": "text/javascript; charset=utf-8" };
const server = createServer((req, res) => {
  const path = normalize(join(root, decodeURIComponent(new URL(req.url, "http://x").pathname)));
  if (!path.startsWith(root)) { res.writeHead(403).end(); return; }
  const file = path.endsWith("/") ? join(path, "opfs.html") : path;
  try {
    const body = readFileSync(file);
    res.writeHead(200, {
      "content-type": types[extname(file)] || "application/octet-stream",
      // A shared-memory design needs cross-origin isolation; with it `Atomics.wait`
      // exists (and throws on the main thread). Without it, SharedArrayBuffer is absent.
      "cross-origin-opener-policy": "same-origin",
      "cross-origin-embedder-policy": "require-corp",
    });
    res.end(body);
  } catch {
    res.writeHead(404).end();
  }
});
await new Promise((r) => server.listen(0, "127.0.0.1", r));
const port = server.address().port;
const base = `http://127.0.0.1:${port}/opfs.html`;

const profile = mkdtempSync(join(tmpdir(), "wiz-opfs-"));
const proc = spawn(chrome, ["--headless", "--no-sandbox", "--disable-gpu",
  `--remote-debugging-port=0`, `--user-data-dir=${profile}`, "about:blank"], { stdio: "ignore" });
const sleep = (ms) => new Promise((r) => setTimeout(r, ms));

let browserWs = null;
let devtools = null;
// `--remote-debugging-port=0` writes the chosen port to DevToolsActivePort.
for (let i = 0; i < 150 && !browserWs; i++) {
  await sleep(200);
  try {
    devtools = readFileSync(join(profile, "DevToolsActivePort"), "utf8").split("\n")[0];
    const v = await (await fetch(`http://127.0.0.1:${devtools}/json/version`)).json();
    browserWs = v.webSocketDebuggerUrl;
  } catch { /* not up yet */ }
}
if (!browserWs) { console.error("chromium did not start"); proc.kill(); process.exit(1); }

const ws = new WebSocket(browserWs);
await new Promise((r) => ws.addEventListener("open", r));
let id = 0;
const pending = new Map();
const errors = [];
ws.addEventListener("message", (m) => {
  const msg = JSON.parse(m.data);
  if (msg.id && pending.has(msg.id)) { pending.get(msg.id)(msg); pending.delete(msg.id); }
  if (msg.method === "Runtime.exceptionThrown") {
    errors.push(msg.params.exceptionDetails.exception?.description || "exception");
  }
});
const send = (method, params = {}, sessionId) => new Promise((resolve) => {
  const n = ++id;
  pending.set(n, resolve);
  const payload = { id: n, method, params };
  if (sessionId) payload.sessionId = sessionId;
  ws.send(JSON.stringify(payload));
});

async function openTab(url) {
  const t = await send("Target.createTarget", { url });
  const targetId = t.result.targetId;
  const a = await send("Target.attachToTarget", { targetId, flatten: true });
  const sessionId = a.result.sessionId;
  await send("Runtime.enable", {}, sessionId);
  return { targetId, sessionId };
}

const evaluate = async (tab, expression, awaitPromise = false) => {
  const r = await send("Runtime.evaluate",
    { expression, returnByValue: true, awaitPromise }, tab.sessionId);
  if (r.result.exceptionDetails) throw new Error(JSON.stringify(r.result.exceptionDetails));
  return r.result.result.value;
};

async function waitDone(tab, label) {
  for (let i = 0; i < 150; i++) {
    await sleep(100);
    try { if (await evaluate(tab, "window.__opfsDone === true")) return; } catch { /* loading */ }
  }
  throw new Error(label + " did not finish");
}

const failures = [];
const check = (ok, what) => { if (!ok) failures.push(what); };

const timeout = setTimeout(() => { console.error("timeout"); proc.kill(); process.exit(1); }, 90000);

const primary = await openTab(base + "?role=primary");
await waitDone(primary, "primary");
const a = await evaluate(primary, "window.__opfsResult");
check(a.ok === true, "primary ok");
check(a.wrote === 11, "wrote 11");
check(a.a === "opfs" && a.b === "opfs", "read back 'opfs' after both seeks");
check(a.size === 11, "size 11");
check(a.atStart === 7 && a.atEnd === 7, "seek positions");
check(a.probes.createReturnsPromise === true || a.probes.createReturnsPromise === "absent", "createSyncAccessHandle is a promise or absent on the main thread");
check(a.probes.mainThreadHandle === "absent", "createSyncAccessHandle is absent on the main thread");
check(a.probes.crossOriginIsolated === true, "the probe page is cross-origin isolated");
check(a.probes.atomicsWait === "TypeError", "Atomics.wait throws on the main thread");

const locker = await openTab(base + "?role=locker");
await waitDone(locker, "locker (locked)");
const b1 = await evaluate(locker, "window.__opfsResult");
check(b1.ok === false, "second tab is refused the lock");
check(b1.error === "NoModificationAllowedError", "the refusal is NoModificationAllowedError");

const closed = await evaluate(primary, "window.__opfsClose()", true);
check(closed && closed.ok === true, "primary released the lock");

// a fresh tab, after the close: the lock is available again
const after = await openTab(base + "?role=locker");
await waitDone(after, "locker (free)");
const b2 = await evaluate(after, "window.__opfsResult");
check(b2.ok === true, "the lock is free once the first handle closes");

clearTimeout(timeout);
console.log(JSON.stringify({ primary: a, locked: b1, free: b2, errors }, null, 2));
if (failures.length) {
  console.error("opfs: FAILED: " + failures.join("; "));
  proc.kill(); server.close(); process.exit(1);
}
console.log("opfs: all checks passed");
proc.kill(); server.close(); process.exit(0);
