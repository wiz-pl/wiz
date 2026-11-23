// The Loom ABI from a `--target js` module, mounted by the real host in headless
// Chromium: `web/framework/mount.js` -> `driver.js` -> `profile.js` over a live `Document`,
// with `web/framework/dom-host.mjs` behind the module's `extern "js.wiz.dom.…"` calls.
// This is the half the Node tests cannot see: a real `Element`, a real event dispatch, a
// real `classList`/selection/focus implementation, and a patch list parsed by the
// browser's own HTML parser.
//
//   usage: node web/js_loom_chrome_test.mjs CHROMIUM BUILT.mjs
//
// BUILT.mjs is `wiz build examples/js-loom/boot.wiz --target js -o BUILT.mjs`. The test
// serves the framework files and that module from 127.0.0.1:0 and drives the page over
// the DevTools protocol (Node's built-in WebSocket). Exit code 0 means every assertion
// passed.
"use strict";
import { spawn } from "node:child_process";
import { createServer } from "node:http";
import { mkdtempSync } from "node:fs";
import { readFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import { dirname, extname, join, normalize, resolve, sep } from "node:path";
import { fileURLToPath } from "node:url";

const [chrome, bootArg] = process.argv.slice(2);
if (!chrome || !bootArg) {
  console.error("usage: node web/js_loom_chrome_test.mjs CHROMIUM BUILT.mjs");
  process.exit(2);
}
const frameworkDir = join(dirname(fileURLToPath(import.meta.url)), "framework");
const bootFile = resolve(bootArg);

let failed = 0;
const ok = (cond, what, detail = "") => {
  if (cond) console.log("ok: " + what);
  else { failed++; console.log("FAIL: " + what + (detail ? "\n  " + detail : "")); }
};
const eq = (what, want, got) => ok(Object.is(got, want), what,
  `want ${JSON.stringify(want)}\n  got  ${JSON.stringify(got)}`);
const sleep = (ms) => new Promise((r) => setTimeout(r, ms));

const PAGE = `<!doctype html>
<html><head><meta charset="utf-8"><title>js loom</title></head><body>
<div id="mount"></div>
<script type="module">
import { install } from "/framework/dom-host.mjs";
import { mount } from "/framework/mount.js";
globalThis.dom = install();
try {
  globalThis.app = await mount(document.getElementById("mount"), {
    module: () => import("/boot.mjs"),
    env: window,
  });
  globalThis.mounted = true;
} catch (e) {
  globalThis.mountError = String((e && e.message) || e);
}
</script>
</body></html>`;

const MIME = {
  ".js": "text/javascript; charset=utf-8",
  ".mjs": "text/javascript; charset=utf-8",
  ".html": "text/html; charset=utf-8",
};

function serve() {
  const server = createServer(async (req, res) => {
    try {
      const pathname = decodeURIComponent(new URL(req.url, "http://127.0.0.1").pathname);
      if (pathname === "/" || pathname === "/index.html") {
        res.writeHead(200, { "content-type": MIME[".html"] }).end(PAGE);
        return;
      }
      if (pathname === "/boot.mjs") {
        res.writeHead(200, { "content-type": MIME[".mjs"] }).end(await readFile(bootFile));
        return;
      }
      if (pathname.startsWith("/framework/")) {
        const name = normalize(pathname.slice("/framework/".length));
        const p = join(frameworkDir, name);
        if (!p.startsWith(frameworkDir + sep)) {
          res.writeHead(403).end("outside the framework directory");
          return;
        }
        res.writeHead(200, { "content-type": MIME[extname(p)] || "application/octet-stream" })
          .end(await readFile(p));
        return;
      }
      res.writeHead(404).end("not found");
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
  const profile = mkdtempSync(join(tmpdir(), "wiz-jsloom-chrome-"));
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
      errors.push(msg.params.args.map((a) => a.value).join(" "));
    }
  });
  const call = (method, params = {}) => new Promise((r) => {
    pending.set(++id, r);
    ws.send(JSON.stringify({ id, method, params }));
  });
  return { call, errors, close: () => { try { ws.close(); } catch {} proc.kill("SIGKILL"); } };
}

const { server, url } = await serve();
const { call, errors, close } = await connect(chrome);
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

try {
  await call("Runtime.enable");
  await call("Page.enable");
  await call("Page.navigate", { url });
  const mounted = await waitFor(`globalThis.mounted === true || !!globalThis.mountError`);
  ok(mounted, "the page mounted the JS-target runtime");
  eq("the mount did not fail", undefined, await evaluate(`globalThis.mountError`));
  if (await evaluate(`globalThis.mountError`)) {
    throw new Error("mount failed: " + await evaluate(`globalThis.mountError`));
  }

  // ## The ABI: the profile saw a JS module, the SSR is the first paint
  eq("the runtime is the js kind", "js", await evaluate(`globalThis.app.profile.kind`));
  eq("the SSR is mounted", "Home", await evaluate(`document.querySelector("#mount main").textContent`));
  eq("with its data-view", "home",
    await evaluate(`document.querySelector("#mount main").getAttribute("data-view")`));
  eq("the tree is the module's own html", true,
    await evaluate(`(() => { const html = document.getElementById("mount").innerHTML;
      return html === globalThis.app.html(); })()`));

  // ## A real click: delegation -> step -> wizPatch -> the browser's parser
  await evaluate(`document.querySelector('#mount a[data-wiz-on-click="1"]').click()`);
  eq("the title is the new route", "About",
    await evaluate(`document.querySelector("#mount main").textContent`));
  eq("and so is data-view", "about",
    await evaluate(`document.querySelector("#mount main").getAttribute("data-view")`));
  eq("the click was consumed (no navigation)", true,
    await evaluate(`location.hash === "" || location.hash === "#"`));

  // ## The effect round trip
  eq("the request is pending", true, await evaluate(`globalThis.app.requests().includes("#/about")`));
  await evaluate(`globalThis.app.call("wiz_loom_effect", "url", "ack", "")`);
  eq("the effect cleared it", "[]", await evaluate(`globalThis.app.requests()`));
  eq("and is counted", "1",
    await evaluate(`document.querySelector("#mount main").getAttribute("data-effects")`));

  // ## The DOM adapter: the module's own `wiz.dom` calls, on real elements
  await evaluate(`globalThis.app.module.wiz_loom_probe()`);
  eq("the probe appended its box", true, await evaluate(`!!document.getElementById("probe")`));
  // The box holds the probe's text node and then the button it appended (`setText` is
  // `textContent`, so the order matters and the text is the box's first child).
  eq("with its text", "ready", await evaluate(`document.getElementById("probe").firstChild.data`));
  eq("and a button", "probe",
    await evaluate(`document.querySelector("#probe button").textContent`));
  await evaluate(`document.querySelector("#probe button").click()`);
  eq("the Wiz closure ran", "clicked", await evaluate(`document.getElementById("probe").textContent`));
  eq("and set its attribute", "1",
    await evaluate(`document.getElementById("probe").getAttribute("data-clicked")`));
  // The adapter's other entries, directly: a class, the focus and the selection.
  eq("classList/classAdd/classHas", "on",
    await evaluate(`(() => { const d = globalThis.dom.api; const el = document.getElementById("probe");
      d.classAdd(el, "on"); return d.classList(el).join(","); })()`));
  eq("classHas sees it", true,
    await evaluate(`globalThis.dom.api.classHas(document.getElementById("probe"), "on")`));
  eq("classRemove removes it", "",
    await evaluate(`(() => { const d = globalThis.dom.api; const el = document.getElementById("probe");
      d.classRemove(el, "on"); return d.classList(el).join(","); })()`));
  eq("a 3-field selection round-trips", "1,4", await evaluate(`(() => {
      const d = globalThis.dom.api;
      const ta = document.createElement("textarea");
      document.body.appendChild(ta);
      ta.value = "hello";
      d.setSelection(ta, 1n, 4n);
      const s = d.selection(ta);
      ta.remove();
      return s.start + "," + s.end;
    })()`));
  eq("getAttribute is \"\" when absent", "",
    await evaluate(`globalThis.dom.api.getAttribute(document.getElementById("probe"), "nope")`));
  eq("focus takes the focus", "probe", await evaluate(`(() => {
      const d = globalThis.dom.api;
      const el = document.getElementById("probe");
      el.tabIndex = 0;
      d.focus(el);
      return document.activeElement && document.activeElement.id;
    })()`));

  ok(errors.length === 0, "no console errors or exceptions", errors.join("\n"));
} finally {
  close();
  server.close();
}

if (failed === 0) console.log("js loom chrome: all checks passed");
else { console.log(`js loom chrome: ${failed} failure(s)`); process.exitCode = 1; }
