// End-to-end test of the browser half of the Wiz Loom framework: take the JSON
// web/framework/gen.wiz printed (SSR HTML before and after a state change, and the
// patch list the Wiz diff produced), parse the "before" tree with minidom.mjs, apply
// the patches with runtime.js, and require the serialized result to equal the "after"
// HTML exactly. Also exercises keyed reorder, removal+insertion, escaping, and event
// delegation.
//
// This is a Node test double, not a browser: it cannot see form-control value
// properties or real DOM event objects.  tools/jupyter/static/widget_test.mjs runs the
// same patcher against headless Chrome (and minidom when no browser is installed).
//
//   node web/framework/test.mjs FIXTURE.json
"use strict";
import { readFileSync } from "node:fs";
import { applyPatches, delegate } from "./runtime.js";
import { parse, serialize } from "./minidom.mjs";

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

// 1. SSR + diff + patch: a text update.
ok(run(fixture.old, fixture.patches) === fixture.new, "a text patch reproduces the new SSR",
  "got  " + run(fixture.old, fixture.patches) + "\nwant " + fixture.new);
const textOps = JSON.parse(fixture.patches).map((p) => p.op);
ok(textOps.length === 1 && textOps[0] === "text", "a count change is one text patch", JSON.stringify(textOps));

// 2. Keyed reorder: one move (and handler renumbering), no replace.
ok(run(fixture.reorderOld, fixture.reorderPatches) === fixture.reorderNew,
  "a keyed reorder reproduces the new SSR");
const reorderOps = JSON.parse(fixture.reorderPatches).map((p) => p.op);
ok(reorderOps.includes("move"), "a keyed reorder emits a move", JSON.stringify(reorderOps));
ok(!reorderOps.includes("replace"), "a keyed reorder replaces nothing", JSON.stringify(reorderOps));

// 3. Rotation (a move earlier and a move later in one diff).
ok(run(fixture.rotateOld, fixture.rotatePatches) === fixture.rotateNew,
  "a keyed rotation reproduces the new SSR",
  "got  " + run(fixture.rotateOld, fixture.rotatePatches) + "\nwant " + fixture.rotateNew);
const rotateOps = JSON.parse(fixture.rotatePatches).map((p) => p.op);
ok(rotateOps.filter((op) => op === "move").length === 2 && !rotateOps.includes("insert"),
  "a rotation is two moves, no insert", JSON.stringify(rotateOps));

// 3b. A changed element tag is a replace at that node.
ok(run(fixture.tagOld, fixture.tagPatches) === fixture.tagNew,
  "a changed tag reproduces the new SSR", fixture.tagNew);
ok(JSON.parse(fixture.tagPatches).some((p) => p.op === "replace" && p.path === "0"),
  "a changed tag is one replace", fixture.tagPatches);

// 4. Removal and insertion in a keyed list.
ok(run(fixture.editOld, fixture.editPatches) === fixture.editNew,
  "a keyed removal+insertion reproduces the new SSR",
  "got  " + run(fixture.editOld, fixture.editPatches) + "\nwant " + fixture.editNew);
const editOps = JSON.parse(fixture.editPatches).map((p) => p.op);
ok(editOps.includes("remove") && editOps.includes("insert") && !editOps.includes("replace"),
  "removal+insertion uses remove and insert, not replace", JSON.stringify(editOps));

// 5. Conditional rendering: the list became a text node.
ok(fixture.hidden.includes("<p>count 0</p>") && fixture.hidden.endsWith("hidden</div>"),
  "conditional rendering drops the list", fixture.hidden);

// 6. Escaping: text round-trips, and no script element is created from text.
const escaped = parse(fixture.escape);
ok(serialize(escaped) === fixture.escape, "escaped text and attribute values round-trip");
ok(!fixture.escape.includes("<script>") && fixture.escape.includes("&lt;script&gt;"),
  "text is escaped, not markup", fixture.escape);
ok(!JSON.stringify(collectTags(escaped, [])).includes("script"), "the parser sees no script element");

function collectTags(n, out) {
  if (n.tagName) out.push(n.tagName);
  for (const c of n.childNodes || []) collectTags(c, out);
  return out;
}

// 7. Event delegation: the innermost element with data-wiz-on-click wins, and the event name
// must match. The fixture's item spans are handlers 1 and 2 (click).
{
  const root = parse(fixture.old);
  const calls = [];
  delegate(root, (event, index) => { calls.push([event, index]); return true; });
  const span = find(root, (n) => n.getAttribute && n.getAttribute("data-wiz-on-click") === "2");
  ok(span !== null, "the fixture has a click handler");
  if (span) {
    const inner = span.childNodes[0];
    inner.dispatchEvent({ type: "click" });
    ok(calls.length === 1 && calls[0][0] === "click" && calls[0][1] === 2,
      "clicking a child dispatches the enclosing handler", JSON.stringify(calls));
    inner.dispatchEvent({ type: "keydown" });
    ok(calls.length === 1, "an event with no handler is ignored", JSON.stringify(calls));
  }
}

function find(n, p) {
  if (p(n)) return n;
  for (const c of n.childNodes || []) { const r = find(c, p); if (r) return r; }
  return null;
}

// 8. Determinism flag from Wiz.
ok(fixture.deterministic === true, "SSR is deterministic (Wiz rendered it twice)");
ok(fixture.handlers === 3, "the fixture has three handlers", String(fixture.handlers));
ok(fixture.guard.includes('data-wiz-on-keydown="0"') &&
   fixture.guard.includes('data-wiz-prevent-keydown="1"'),
  "onPrevent renders the handler and the runtime-decides marker", fixture.guard);

if (failed) { console.log(`\n${failed} failed`); process.exit(1); }
console.log("\nloom framework: all checks passed");
