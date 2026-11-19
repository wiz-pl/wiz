// The whole playground page (lib/Web/Playground.wiz's `Page`/`pageApp`), end to end
// under Node: the fixture (web/playground_page_gen.wiz) is the runtime's answer; this
// test mounts its SSR with the framework's browser half (web/framework/{driver,runtime}.mjs),
// dispatches the same `change` event the examples menu does, and requires the patches to
// reproduce the next state's SSR exactly. It also keeps the examples honest: the Wiz list
// must equal web/playground-presets.js, which is still the oracle the Wasm test
// (web/playground_test.mjs) runs.
//
// No Wasm, no browser: the page is pure presentation plus a pure step, so its HTML, its
// event string and its patches are the whole contract.
//
//   node web/playground_page_test.mjs FIXTURE.json
"use strict";
import { readFileSync } from "node:fs";
import { applyPatches } from "./framework/runtime.js";
import { start } from "./framework/driver.js";
import { parse, serialize } from "./framework/minidom.mjs";
import { presets } from "./playground-presets.js";

const fixture = JSON.parse(readFileSync(process.argv[2], "utf-8"));
let failed = 0;
const ok = (cond, what, detail = "") => {
  if (cond) console.log("ok: " + what);
  else { failed++; console.log("FAIL: " + what + (detail ? "\n  " + detail : "")); }
};
const eq = (what, want, got) => ok(Object.is(got, want), what,
  `want ${JSON.stringify(want)}\n  got  ${JSON.stringify(got)}`);
const walk = (node, pred, out = []) => {
  if (pred(node)) out.push(node);
  for (const c of node.childNodes || []) walk(c, pred, out);
  return out;
};
const byId = (root, id) => walk(root, (n) => n.getAttribute && n.getAttribute("id") === id)[0];

// ## The examples are the runtime's data, and they are the page's data still
eq("seven examples", 7, (fixture.examples || []).length);
eq("the example ids", presets.map((p) => p.id).join(","),
  (fixture.examples || []).map((e) => e.id).join(","));
for (const p of presets) {
  const e = (fixture.examples || []).find((x) => x.id === p.id) || {};
  eq(`example ${p.id}: title`, p.title, e.title);
  eq(`example ${p.id}: code`, p.code, e.code);
}
eq("the default example", "basics", fixture.defaultExampleId);

// ## The first paint: the page's structure, rendered by the runtime
const initial = fixture.initial;
ok(initial.includes("<header>") && initial.includes("<main>") && initial.includes("<footer>"),
  "the whole page is the app: header, main and footer", initial.slice(0, 200));
ok(initial.includes('class="toolbar"') && initial.includes('id="preset"'),
  "the examples menu is in the header's toolbar");
ok(initial.includes('id="editor"') && initial.includes('id="run"') && initial.includes('id="count"'),
  "the editor pane is there (#editor, #run, #count)");
ok(initial.includes('id="goals"') && initial.includes('id="output"') && initial.includes('id="status"'),
  "the goals container, the output pane and the status are there");
ok(initial.includes('data-wiz-on-change="0"'), "the examples menu is handler 0 (document order)");
ok(initial.includes('<option value="basics" selected="selected">Basics</option>'),
  "the default example is selected in the menu");
ok(!initial.includes("<script"), "the app's text is escaped");

// ## The page's step: a preset load replaces the text, empties the output, counts
eq("the load carries the chosen id", "lists", fixture.loadedPreset);
eq("a load is one effect request", "1", fixture.loadedLoads);
eq("the editor holds the example's code", presets.find((p) => p.id === "lists").code,
  fixture.loadedText);
eq("a load empties the count", "0 lines", fixture.loadedCount);
eq("the first paint starts on the default", "basics", fixture.initialPreset);
eq("the first paint has no load", "0", fixture.initialLoads);

// An unknown id and a stale event change nothing: the page holds its state.
eq("an unknown id leaves the preset", "basics", fixture.unknownPreset);
eq("an unknown id leaves the text", presets.find((p) => p.id === "basics").code, fixture.unknownText);
eq("an unknown id is not a load", "0", fixture.unknownLoads);
eq("a stale handler index does nothing", presets.find((p) => p.id === "basics").code,
  fixture.staleIndexText);
eq("a stale handler index is not a load", "0", fixture.staleIndexLoads);
eq("a stale event name does nothing", presets.find((p) => p.id === "basics").code,
  fixture.staleEventText);

// ## The DOM path: mount the SSR, fire the menu's change event, apply the patches
const strings = new Map();
let next = 1;
const put = (s) => { const p = next++; strings.set(p, s); return p; };
const steps = [];
const wasm = {
  _wiz_loom_init: () => 0,
  _wiz_loom_html: () => put(initial),
  _wiz_loom_step: (state, p) => { steps.push(strings.get(Number(p))); return state; },
  stringToNewUTF8: (s) => put(s),
  UTF8ToString: (p) => strings.get(Number(p)) || "",
  _free: (p) => { strings.delete(Number(p)); },
};
const root = parse("");
const app = start(wasm, root, { parse, events: ["change"] });
eq("the driver receives the menu's change", "change\n0\nlists", (() => {
  const select = byId(root, "preset");
  select.value = "lists";
  select.dispatchEvent({ type: "change" });
  return steps[0];
})());
applyPatches(root, JSON.parse(fixture.initialToLoaded), parse);
eq("the patches reproduce the loaded SSR", fixture.loaded, serialize(root));
eq("the textarea's live value is the example", fixture.loadedText, byId(root, "editor").value);
eq("the menu's selection moved", "lists",
  walk(byId(root, "preset"), (n) => n.getAttribute && n.getAttribute("selected") != null)
    .map((n) => n.getAttribute("value")).join(","));
ok(app.state() === 0, "the driver keeps the state the runtime returned");

console.log(failed === 0 ? "playground page: all checks passed" : `playground page: ${failed} failure(s)`);
process.exit(failed === 0 ? 0 : 1);
