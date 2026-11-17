// web/framework/driver.js under Node, with web/framework/minidom.mjs as the DOM and a
// stub Wasm module: no browser, no Emscripten, no build. web/framework/test.sh runs it
// beside the SSR/patch test.
//
//   usage: node web/framework/driver_test.mjs
//
// Covers: the driver calls the exports web/framework/app.wiz defines (and refuses a
// module that lacks one); mount, event delegation and the patch hook; the hook applies a
// patch to the root whose step is running, not to the last app mounted (wasm-08); the
// previous page hook still receives patches from outside a step; and the event string's
// buffer is freed when the step throws.
"use strict";
import { readFileSync } from "node:fs";
import { document, serialize } from "./minidom.mjs";

globalThis.document = document();
const { start, REACT_EXPORTS } = await import("./driver.js");

let failed = 0;
function check(name, got, want) {
  const same = Object.is(got, want) || JSON.stringify(got) === JSON.stringify(want);
  if (same) console.log(`ok: ${name}`);
  else { failed++; console.log(`FAIL: ${name}\n  want: ${JSON.stringify(want)}\n  got:  ${JSON.stringify(got)}`); }
}
function checkThat(name, condition, detail) {
  if (condition) console.log(`ok: ${name}`);
  else { failed++; console.log(`FAIL: ${name}${detail ? "\n  " + detail : ""}`); }
}

// A stub Emscripten module: `_wiz_react_html` returns SSRing[state], and every step calls
// the page's `wizPatch` (as js_patch does) with one text patch before returning state+1.
function fake(ssr, textOfStep) {
  const log = [];
  const heap = new Map();
  let next = 100;
  let state = 1;
  const put = (s) => { const p = next++; heap.set(p, s); return p; };
  const wasm = {
    stringToNewUTF8(s) { log.push(["alloc", String(s)]); return put(String(s)); },
    UTF8ToString(p) { return heap.get(Number(p)); },
    _free(p) { log.push(["free", Number(p)]); heap.delete(Number(p)); },
    _wiz_react_init() { log.push(["init"]); return state; },
    _wiz_react_html(s) { log.push(["html", s]); return put(ssr[s] || ""); },
    _wiz_react_step(s, p) {
      const ev = heap.get(Number(p));
      log.push(["step", s, ev]);
      if (textOfStep === null) throw new Error("step failed");
      globalThis.wizPatch(JSON.stringify([{ op: "text", path: "0.1", text: textOfStep(ev) }]));
      state = s + 1;
      return state;
    },
  };
  return { wasm, log };
}

const SSR_A = '<div><button data-wiz-on-click="0">+</button><p>A</p></div>';
const SSR_B = '<div><button data-wiz-on-click="0">+</button><p>B</p></div>';

// ## app.wiz defines the exports the driver calls
{
  const wiz = readFileSync(new URL("./app.wiz", import.meta.url), "utf8");
  for (const name of REACT_EXPORTS) {
    checkThat(`app.wiz defines ${name}`, wiz.includes(`export "${name}"`), name);
  }
}

// ## Mount, step, patch (two apps; the global hook follows the stepping root)
const hooked = [];
globalThis.wizPatch = (json) => hooked.push(json);
const a = fake({ 1: SSR_A }, () => "A2");
const b = fake({ 1: SSR_B }, () => "B2");
const rootA = document().createElement("div");
const rootB = document().createElement("div");
const appA = start(a.wasm, rootA);
const appB = start(b.wasm, rootB);
check("mount: A's SSR", serialize(rootA), "<div>" + SSR_A + "</div>");
check("mount: B's SSR", serialize(rootB), "<div>" + SSR_B + "</div>");
check("mount: the initial state", [appA.state(), appB.state()], [1, 1]);
check("mount: html() is the current SSR", appA.html(), SSR_A);

// A is clicked while B is the last-mounted app: the patch must land on A.
const buttonA = rootA.childNodes[0].childNodes[0];
buttonA.dispatchEvent({ type: "click" });
check("step: A's event", a.log.filter((c) => c[0] === "step").map((c) => c[2]), ["click\n0"]);
check("step: A's new state", appA.state(), 2);
check("step: A's patch applied to A", serialize(rootA).includes("<p>A2</p>"), true);
check("step: B untouched", serialize(rootB), "<div>" + SSR_B + "</div>");
check("step: A's event buffer freed", a.log.filter((c) => c[0] === "free").map((c) => c[1]).includes(101), true);

// And B still patches B.
rootB.childNodes[0].childNodes[0].dispatchEvent({ type: "click" });
check("step: B's patch applied to B", serialize(rootB).includes("<p>B2</p>"), true);
check("step: A still A2", serialize(rootA).includes("<p>A2</p>"), true);

// Outside a step the previous page hook still sees the patch (no silent overwrite).
globalThis.wizPatch("outside");
check("hook: the previous handler still runs", hooked, ["outside"]);

// ## A step that throws: the input buffer is freed, and the next app is not confused
{
  const c = fake({ 1: SSR_A }, null);
  const root = document().createElement("div");
  start(c.wasm, root);
  let caught = null;
  try { root.childNodes[0].childNodes[0].dispatchEvent({ type: "click" }); } catch (e) { caught = e; }
  check("step: the error reaches the page", caught && caught.message, "step failed");
  check("step: the event buffer freed after the throw", c.log.filter((x) => x[0] === "free").map((x) => x[1]).includes(101), true);
  const before = a.log.filter((x) => x[0] === "step").length;
  rootA.childNodes[0].childNodes[0].dispatchEvent({ type: "click" });
  check("step: A still steps after another app's throw", a.log.filter((x) => x[0] === "step").length, before + 1);
  check("step: A's patch still lands on A", serialize(rootA).includes("<p>A2</p>"), true);
}

// ## A module without the exports is refused, with the missing name
{
  let caught = null;
  try { start({}, document().createElement("div")); } catch (e) { caught = e; }
  checkThat("start: a module without the exports says which one",
    caught && caught.message.includes("wiz_react_init"), caught && caught.message);
}

if (failed) { console.log(`\n${failed} failed`); process.exit(1); }
console.log("react framework driver: all checks passed");
