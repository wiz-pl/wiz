// The landing page's Loom island under Node, with the real Wasm module and the
// framework's minidom double: the SSR the build wrote is the app's first paint, `mount`
// adopts it (it does not replace a node), and a `change` step is exactly one
// `setAttr "class"` on the app's root.
//
//   usage: node web/landing_ui_test.mjs OUT   (OUT has landing/index.html and
//                                              landing/wiz-landing-ui.mjs)
"use strict";
import { readFileSync } from "node:fs";
import { join } from "node:path";
import { pathToFileURL } from "node:url";
import { mount } from "./framework/mount.js";
import { parse, serialize } from "./framework/minidom.mjs";

const out = process.argv[2] || new URL("./out/", import.meta.url).pathname;
const page = readFileSync(join(out, "landing/index.html"), "utf-8");
const createModule = (await import(pathToFileURL(join(out, "landing/wiz-landing-ui.mjs")).href)).default;

let failed = 0;
const ok = (cond, what, detail = "") => {
  if (cond) console.log("ok: " + what);
  else { failed++; console.log("FAIL: " + what + (detail ? "\n  " + detail : "")); }
};
const eq = (what, want, got) => ok(Object.is(got, want), what,
  `want ${JSON.stringify(want)}\n  got  ${JSON.stringify(got)}`);

function walk(node, pred, out = []) {
  if (pred(node)) out.push(node);
  for (const c of node.childNodes || []) walk(c, pred, out);
  return out;
}
const byTag = (root, tag) => walk(root, (n) => String(n.tagName || "").toLowerCase() === tag);
const byId = (root, id) => walk(root, (n) => n.getAttribute && n.getAttribute("id") === id)[0];

// ## The app's first paint, from its own module
const big = (x) => (typeof x === "bigint" ? x : BigInt(x));
const wasm = await createModule({ printErr: () => {} });
const init = wasm._wiz_loom_init();
const readState = (fn) => {
  if (typeof wasm._wiz_retain === "function") wasm._wiz_retain(big(init));
  const p = fn(init);
  return wasm.UTF8ToString(Number(p));
};
const ssrHtml = readState(wasm._wiz_loom_html);
const ssrHash = readState(wasm._wiz_loom_ssr_hash);
ok(/^t1-[0-9a-f]{8}-\d+-\d+$/u.test(ssrHash), "the module exports a normalised-tree hash", ssrHash);
ok(page.includes('data-wiz-ssr="' + ssrHash + '"'),
  "the built page carries that exact hash (the build and the runtime agree)", ssrHash);
const islandHtml = (() => {
  const at = page.indexOf('data-wiz-ssr="' + ssrHash + '">');
  if (at < 0) return "";
  const start = at + ('data-wiz-ssr="' + ssrHash + '">').length;
  const end = page.indexOf("\n</div>", start);
  return page.slice(start, end);
})();
eq("the built island is the module's SSR byte for byte", ssrHtml, islandHtml);
ok(ssrHtml.includes('id="q-select"'), "the first paint has the select");
ok((ssrHtml.match(/class="q-panel"/g) || []).length === 3,
  "the first paint has all three panels");
ok(ssrHtml.includes('class="q-app q0"'), "the first paint's root is quantity 0");
ok(!ssrHtml.includes("selected="), "the select carries no selected attribute (the browser owns it)");

// ## mount adopts the static tree
const doc = parse('<div id="quantity-app" data-wiz-island="loom/1" data-wiz-ssr="' +
  ssrHash + '">' + ssrHtml + "</div>");
const root = doc.childNodes[0];
const firstChild = root.childNodes[0];
const app = await mount(root, { module: createModule, parse });
eq("mount adopts the static island", "adopt", app.mode);
eq("the driver publishes the mode", "adopt", globalThis.wizLoomMode);
ok(root.childNodes[0] === firstChild, "adopt keeps the app's root node");
ok(byId(root, "q-select") != null, "the adopted tree has the select");
ok(byTag(root, "section").length === 3, "the adopted tree has the three panels");
ok(root.childNodes[0].getAttribute("class") === "q-app q0", "the adopted root's class");

// ## A step is one setAttr "class"; nothing else
const realPatch = globalThis.wizPatch;
const patches = [];
globalThis.wizPatch = (json) => { patches.push(JSON.parse(json)); realPatch(json); };
function choose(value) {
  patches.length = 0;
  const select = byId(root, "q-select");
  select.value = value;
  select.dispatchEvent({ type: "change" });
  return patches;
}
for (const [value, klass] of [["1", "q-app q1"], ["w", "q-app qw"], ["0", "q-app q0"]]) {
  const got = choose(value);
  eq(`change ${value}: exactly one patch`, 1, got.length);
  const p = got[0] || {};
  eq(`change ${value}: it is a setAttr`, "setAttr", p.op);
  eq(`change ${value}: on the app root`, "0", p.path);
  eq(`change ${value}: of the class`, "class", p.name);
  eq(`change ${value}: to ${klass}`, klass, p.value);
  eq(`change ${value}: the DOM has the new class`, klass,
    root.childNodes[0].getAttribute("class"));
  ok(byTag(root, "section").length === 3,
    `change ${value}: all three panels are still in the tree`);
}
eq("an unknown value changes nothing", 0, choose("nope").length);
ok(!serialize(root).includes("data-wiz-error"), "the adopted page has no mount error");

console.log(failed === 0 ? "landing ui: all checks passed"
  : `landing ui: ${failed} failure(s)`);
process.exit(failed === 0 ? 0 : 1);
