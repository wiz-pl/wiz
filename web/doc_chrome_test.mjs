// (11s) A documentation page (`wiz doc`) in headless Chromium, over the DevTools
// protocol: wait until the Wasm module has rendered the signatures as tagged text, hover
// the first constant, select the first non-constant, and print what the page shows (and
// any console errors). With SHOT, also a screenshot (PNG) there.
//   usage: node web/doc_chrome_test.mjs CHROMIUM URL [SHOT]
import { spawn } from "node:child_process";
import { mkdtempSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
const [chrome, url, shot] = process.argv.slice(2);
const port = 9300 + Math.floor(Math.random() * 500);
const profile = mkdtempSync(join(tmpdir(), "wiz-chrome-"));
const proc = spawn(chrome, ["--headless", "--no-sandbox", "--disable-gpu", `--remote-debugging-port=${port}`,
  `--user-data-dir=${profile}`, "--window-size=1280,900", "about:blank"], { stdio: "ignore" });
const sleep = (ms) => new Promise((r) => setTimeout(r, ms));
const done = (code) => { proc.kill(); process.exit(code); };
setTimeout(() => { console.log("timeout"); done(1); }, 60000);
let target = null;
for (let i = 0; i < 100 && !target; i++) {
  await sleep(200);
  try { target = (await (await fetch(`http://127.0.0.1:${port}/json/list`)).json()).find((t) => t.type === "page"); } catch {}
}
const ws = new WebSocket(target.webSocketDebuggerUrl);
await new Promise((r) => ws.addEventListener("open", r));
let id = 0;
const pending = new Map();
const errors = [];
ws.addEventListener("message", (m) => {
  const msg = JSON.parse(m.data);
  if (msg.id && pending.has(msg.id)) { pending.get(msg.id)(msg.result); pending.delete(msg.id); }
  if (msg.method === "Runtime.exceptionThrown") errors.push(msg.params.exceptionDetails.exception?.description);
  if (msg.method === "Runtime.consoleAPICalled" && (msg.params.type === "error" || msg.params.type === "warning"))
    errors.push(msg.params.args.map((a) => a.value).join(" "));
});
const call = (method, params = {}) => new Promise((r) => { pending.set(++id, r); ws.send(JSON.stringify({ id, method, params })); });
const evaluate = async (expr) => (await call("Runtime.evaluate", { expression: expr, returnByValue: true })).result.value;
await call("Runtime.enable");
await call("Page.navigate", { url });
const has = (sel) => evaluate(`!!document.querySelector(${JSON.stringify(sel)})`);
for (let i = 0; i < 100 && !(await has(".sig-type .tt")); i++) await sleep(200);
console.log("interactive: " + await evaluate(`document.body.classList.contains("interactive")`));
console.log("rendered: " + await evaluate(`document.querySelectorAll(".sig-type .tt").length`));
await evaluate(`(() => { const t = document.querySelector(".sig-type .tt.k-const");
  t.dispatchEvent(new MouseEvent("mouseover", { bubbles: true })); })()`);
for (let i = 0; i < 50 && !(await has("#info .kind")); i++) await sleep(100);
console.log("hover: " + await evaluate(`document.getElementById("info").hidden ? "(hidden)" : document.getElementById("info").innerHTML`));
if (shot) {
  const r = await call("Page.captureScreenshot", { format: "png" });
  writeFileSync(shot, Buffer.from(r.data, "base64"));
}
await evaluate(`document.querySelector(".sig-type .tt:not(.k-const)").click()`);
await sleep(300);
console.log("selected: " + await evaluate(`document.querySelector(".tt.sel")?.outerHTML.slice(0, 120)`));
console.log("info: " + await evaluate(`document.getElementById("info").innerHTML`));
const searchCount = (q) => evaluate(`(() => { const b = document.getElementById("search"); b.value = ${JSON.stringify(q)};
  b.dispatchEvent(new Event("input")); return document.getElementById("results").querySelectorAll("a").length; })()`);
console.log("search name: " + await searchCount("pick"));
console.log("search docs: " + await searchCount("colour"));
console.log("search signature: " + await searchCount("Nat"));
for (const e of errors) console.log("error: " + e);
done(0);
