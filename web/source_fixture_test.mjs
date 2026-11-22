// The hand-written source-reader fixture (web/source_fixture_gen.wiz), replayed like
// web/playground_loom_test.mjs: parse the SSR with web/framework/minidom.mjs, apply each
// step's patch list with web/framework/runtime.js, and require the serialized result to
// equal the next state's SSR exactly. No Wasm, no browser, no scry.
//
//   node web/source_fixture_test.mjs FIXTURE.json
"use strict";
import { readFileSync } from "node:fs";
import { applyPatches } from "./framework/runtime.js";
import { parse, serialize } from "./framework/minidom.mjs";

const fixture = JSON.parse(readFileSync(process.argv[2], "utf-8"));
let failed = 0;
const ok = (cond, what, detail = "") => {
  if (cond) console.log("ok: " + what);
  else { failed++; console.log("FAIL: " + what + (detail ? "\n  " + detail : "")); }
};
const run = (oldHtml, patchesJson) => {
  const root = parse(oldHtml);
  applyPatches(root, JSON.parse(patchesJson), parse);
  return serialize(root);
};

const id = "f_00000000000000a1";
ok(fixture.schema === "scry.source.ui/1", "the fixture names the UI schema");
ok(fixture.initial.includes("demo.c"), "the first paint has the file tree");
ok(fixture.initial.includes('data-finding="' + id + '"'),
  "the first paint lists the finding by semantic id");
ok(fixture.initial.includes("system(p)"), "the first paint has the source");
ok(fixture.initial.includes("class=\"src-mark"), "the sink is marked in the source");

// Route steps are entry points from the initial page, not chained interactions.
const chained = (fixture.steps || []).filter((s) => !s.name.startsWith("route:"));
let current = fixture.initial;
for (const step of chained) {
  const next = run(current, step.patches);
  ok(next === step.html, "step " + step.name + " reproduces its SSR",
    next === step.html ? "" : "got  " + next.slice(0, 300) + "\nwant " + step.html.slice(0, 300));
  current = step.html;
}

const of = (prefix) => (fixture.steps || []).find((s) => s.name === prefix + id);
const selected = of("select:");
ok(!!selected, "the select step exists");
if (selected) {
  ok(selected.html.includes('aria-selected="true"'), "select marks the row selected");
  ok(selected.html.includes('class="finding-row selected"'),
    "select adds the selected class");
}
const hover = of("hover:");
ok(!!hover, "the hover step exists");
if (hover) {
  ok(hover.html.includes('class="wiz-hover"'), "the hover step draws the card");
  ok(hover.html.includes("command-injection"), "the card shows the rule");
  ok(hover.html.includes("3:3-3:12"), "the card shows the span");
}
const info = of("info:");
ok(!!info, "the info step exists");
if (info) {
  ok((info.html.match(/class="fact-row"/g) || []).length === 1,
    "the info view shows one fact row");
  ok((info.html.match(/class="fact-finding"/g) || []).length === 1,
    "the info view shows one finding");
}
const routed = (fixture.steps || []).find((s) => s.name === "route:#/f/" + id);
ok(!!routed && run(fixture.initial, routed.patches) === routed.html,
  "the route step is an entry point from the initial page");
ok(!!routed, "the #/f/<id> route step exists");
if (routed) {
  ok(routed.html.includes('aria-selected="true"'),
    "#/f/<id> selects the finding in the DOM");
}

console.log(failed === 0 ? "source fixture: all checks passed"
  : `source fixture: ${failed} failure(s)`);
process.exit(failed === 0 ? 0 : 1);
