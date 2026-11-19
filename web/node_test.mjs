// The web module's Wiz half under Node, with a language server as a child process in
// place of the WebSocket: web/Web.wiz's `wiz_web_*` hooks, nothing else (the browser
// page itself is JavaScript now: web/infoview.js on top of web/playground-lsp.js, and
// web/chrome_test.mjs drives it). Prints the HTML Wiz sets, after opening a document,
// moving the cursor and clicking subterm 3.
//   usage: node web/node_test.mjs OUT_DIR SERVER_CMD...
import { spawn } from "node:child_process";
import { pathToFileURL } from "node:url";
const [outDir, ...server] = process.argv.slice(2);
let wasm = null;
let state = null;
const big = (x) => (typeof x === "bigint" ? x : BigInt(x));
const post = (kind, payload) => {
  const p = wasm.stringToNewUTF8(kind + "\n" + payload);
  state = wasm._wiz_web_step(state, big(p));
  wasm._free(p);
};
const lsp = spawn(server[0], server.slice(1), { stdio: ["pipe", "pipe", "inherit"] });
const decoder = new TextDecoder("utf-8");
const early = [];
lsp.stdout.on("data", (b) => { const t = decoder.decode(b, { stream: true }); if (wasm) post("net", t); else early.push(t); });
globalThis.wizSend = (text) => lsp.stdin.write(text);
const html = {};
globalThis.wizSetHtml = (id, h) => { html[id] = h; };
const createModule = (await import(pathToFileURL(outDir + "/wiz-infoview.mjs").href)).default;
wasm = await createModule({ printErr: (s) => console.error(s) });
state = wasm._wiz_web_init();
for (const t of early.splice(0)) post("net", t);
post("open", "file:///t.wiz\nimport Prelude\n");
post("cursor", "3 4");
setTimeout(() => post("click", "3"), 1500);
setTimeout(() => {
  console.log("goals: " + (html.goals || ""));
  console.log("info: " + (html.info || ""));
  lsp.kill();
  process.exit(0);
}, 3000);
