// The playground page in headless Chromium: web/playground.js fetches the default
// program (`playground-tour.wiz`, beside the page) and puts it in the textarea, and the
// page runs it once the Wasm engine loads. This checks both, and prints the editor's
// first line and the output's line count.
//   usage: node web/playground_chrome_test.mjs CHROMIUM URL
// (URL is the page over HTTP; a `file://` page cannot fetch the tour and keeps the
// textarea's inline fallback, which is the behaviour the page is built for but not what
// this test is about.)
import { spawn } from "node:child_process";
import { mkdtempSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
const [chrome, url] = process.argv.slice(2);
const port = 9800 + Math.floor(Math.random() * 500);
const profile = mkdtempSync(join(tmpdir(), "wiz-chrome-playground-"));
const proc = spawn(chrome, ["--headless", "--no-sandbox", "--disable-gpu", `--remote-debugging-port=${port}`,
  `--user-data-dir=${profile}`, "about:blank"], { stdio: "ignore" });
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
  if (msg.method === "Runtime.consoleAPICalled" && msg.params.type === "error")
    errors.push(msg.params.args.map((a) => a.value).join(" "));
});
const call = (method, params = {}) => new Promise((r) => { pending.set(++id, r); ws.send(JSON.stringify({ id, method, params })); });
const evaluate = async (expr) => (await call("Runtime.evaluate", { expression: expr, returnByValue: true })).result.value;
await call("Runtime.enable");
await call("Page.navigate", { url });
// The tour lands after a fetch; `tour: yes` is the textarea holding the file's first
// line, not the inline fallback (which starts with `import Prelude` too, so look for
// the tour's own header).
let tour = "no";
for (let i = 0; i < 100 && tour !== "yes"; i++) {
  await sleep(200);
  tour = await evaluate(`document.getElementById("editor").value.includes("Wiz in Y minutes") ? "yes" : "no"`);
}
let lines = 0;
for (let i = 0; i < 100 && lines === 0; i++) {
  await sleep(200);
  lines = await evaluate(`document.querySelectorAll("#output .line").length`);
}
console.log("tour: " + tour);
console.log("lines: " + lines);
console.log("first: " + await evaluate(`document.getElementById("output").querySelector(".line")?.textContent ?? ""`));
for (const e of errors) console.log("error: " + e);
done(tour === "yes" && lines > 0 ? 0 : 1);
