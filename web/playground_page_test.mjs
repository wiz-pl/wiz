// The whole playground page (lib/Web/Playground.wiz's `Page`/`pageApp`), end to end
// under Node: the fixture (web/playground_page_gen.wiz) is the runtime's answer; this
// test mounts its SSR with the framework's browser half (web/framework/{driver,runtime}.js),
// dispatches the same `change` event the examples menu does, and requires the patches to
// reproduce the next state's SSR exactly. It also checks the effect protocol: the JSON
// requests the page services (`run`, `save`, `share`, `sync`) and the results the page
// sends back (`finished`, `failed`, `load`, `ack`).
//
// No Wasm, no browser: the page is pure presentation plus a pure step, so its HTML, its
// event string, its patches, its requests and its effects are the whole contract.
//
//   node web/playground_page_test.mjs FIXTURE.json
"use strict";
import { readFileSync } from "node:fs";
import { applyPatches, nodeAt } from "./framework/runtime.js";
import { start } from "./framework/driver.js";
import { parse, serialize, document as minidoc } from "./framework/minidom.mjs";
import { presets } from "./framework/examples.mjs";
import { rules } from "./framework/editor-model.mjs";
import { mountSquiggles } from "./squiggles.js";

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
const requests = (page) => JSON.parse(page.requests || "[]");
const kinds = (page) => requests(page).map((r) => r.kind).join(",");
const byKind = (page, kind) => (requests(page).find((r) => r.kind === kind) || {}).payload;

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
ok(/<header[ >]/.test(initial) && /<main[ >]/.test(initial) && /<footer[ >]/.test(initial),
  "the whole page is the app: header, main and footer", initial.slice(0, 200));
ok(initial.includes('class="toolbar"') && initial.includes('id="preset"'),
  "the examples menu is in the header's toolbar");
for (const id of ["share", "save", "reset", "clear"]) {
  ok(initial.includes(`id="${id}"`), `the ${id} control is in the toolbar`);
}
ok(initial.includes('id="note"'), "the note is beside the status");
ok(initial.includes('id="editor"') && initial.includes('id="run"') && initial.includes('id="count"'),
  "the editor pane is there (#editor, #run, #count)");
ok(initial.includes('id="goals"') && initial.includes('id="output"') && initial.includes('id="status"'),
  "the goals container, the output pane and the status are there");
ok(initial.includes('data-wiz-on-change="0"'), "the examples menu is handler 0 (document order)");
ok(initial.includes('<option value="basics" selected="selected">Basics</option>'),
  "the default example is selected in the menu");
ok(!initial.includes("<script"), "the app's text is escaped");
eq("the first paint asks for no effect", "[]", fixture.initialPage.requests);

// ## The editor rules the page asks for (the runtime's, not the test oracle's)
const ruleSpans = JSON.parse(fixture.segments || "[]");
eq("one span for one diagnostic", 1, ruleSpans.length);
eq("the span's start", 13, ruleSpans[0].start);
eq("the span's stop", 17, ruleSpans[0].stop);
eq("the span's severity", 1, ruleSpans[0].severity);

// ## The page's step: a preset load replaces the text, empties the output, requests effects
eq("the load carries the chosen id", "lists", fixture.loadedPage.preset);
eq("a load is one run request", "1", fixture.loadedPage.loads);
eq("the editor holds the example's code", presets.find((p) => p.id === "lists").code,
  fixture.loadedPage.text);
eq("a load empties the count", "0 lines", fixture.loadedPage.count);
eq("the first paint starts on the default", "basics", fixture.initialPage.preset);
eq("the first paint has no load", "0", fixture.initialPage.loads);

// A load asks the page to run the program and to sync the draft/URL.
eq("a load requests run and sync", "run,sync", kinds(fixture.loadedPage));
eq("the run request has no payload", "", byKind(fixture.loadedPage, "run"));
const sync = JSON.parse(byKind(fixture.loadedPage, "sync") || "{}");
ok(typeof sync.draft === "string" && sync.draft.includes('"version":1'),
  "the sync payload carries the versioned draft", String(sync.draft).slice(0, 120));
eq("the sync payload's fragment is the example", fixture.listsFragment, sync.fragment);

// An unknown id and a stale event change nothing: the page holds its state.
eq("an unknown id leaves the preset", "basics", fixture.unknownPage.preset);
eq("an unknown id leaves the text", presets.find((p) => p.id === "basics").code,
  fixture.unknownPage.text);
eq("an unknown id is not a load", "0", fixture.unknownPage.loads);
eq("a stale handler index does nothing", presets.find((p) => p.id === "basics").code,
  fixture.staleIndexPage.text);
eq("a stale handler index is not a load", "0", fixture.staleIndexPage.loads);
eq("a stale event name does nothing", presets.find((p) => p.id === "basics").code,
  fixture.staleEventPage.text);

// ## The effects the page sends back
eq("a finished run counts its lines", "2 lines", fixture.finishedPage.count);
eq("a finished run shows the page's status", "done in 4 ms", fixture.finishedPage.status);
eq("a finished run's kind is the output's", "ready", fixture.finishedPage.statusKind);
eq("a failure shows its count text", "exit code 3", fixture.failedPage.count);
eq("a failure's status is failed", "failed", fixture.failedPage.status);
eq("a failure's kind is error", "error", fixture.failedPage.statusKind);
eq("acknowledging both requests leaves none", "[]", fixture.ackedPage.requests);

// ## The initial state: the fragment wins, then the draft, then the default
eq("a preset fragment loads its program", "lists", fixture.fromPresetPage.preset);
eq("a preset fragment loads its text", presets.find((p) => p.id === "lists").code,
  fixture.fromPresetPage.text);
eq("a loaded link is noted", "loaded the program from the link", fixture.fromPresetPage.note);
eq("a custom draft loads its text", "def one : Nat := 1\n", fixture.fromDraftPage.text);
eq("a custom draft has no preset", "", fixture.fromDraftPage.preset);
eq("the default example is the fallback", presets.find((p) => p.id === "basics").code,
  fixture.invalidPage.text);
eq("an invalid link is noted", "ignored an invalid playground link", fixture.invalidPage.note);

// ## The toolbar's requests
eq("share requests a link and a sync", "share,sync", kinds(fixture.sharedPage));
eq("the share payload is the fragment", "#preset=basics", byKind(fixture.sharedPage, "share"));
eq("save requests the file and a sync", "save,sync", kinds(fixture.savedPage));
eq("the save payload is the source", presets.find((p) => p.id === "basics").code,
  byKind(fixture.savedPage, "save"));
eq("reset restores the default program", presets.find((p) => p.id === "basics").code,
  fixture.resetPage.text);
eq("reset notes itself", "reset to the default program", fixture.resetPage.note);
eq("clear empties the count", "0 lines", fixture.clearedPage.count);
ok(!fixture.clearedPage.html.includes(">ok<"), "clear empties the output pane");

// ## Tab asks the host for one edit, at the selection the driver reported
eq("a Tab requests an edit", "edit", kinds(fixture.tabbedPage));
const tabEdit = JSON.parse(byKind(fixture.tabbedPage, "edit") || "{}");
eq("the edit's selection starts at the reported offset", 0, tabEdit.from);
ok(typeof tabEdit.to === "number" && tabEdit.to >= 3, "the edit replaces to the end of the selected line");
ok(String(tabEdit.insert).startsWith("  "), "the edit indents the selected lines", String(tabEdit.insert));

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

// ## The overlays on the real page, over its child-index patch paths
// The Loom page patches by child index (`web/framework/runtime.js`). Mount the page's
// own tree, apply its menu patch, then enable the squiggle layer the page enables
// (`wireGoals` -> `rules.segments`) and apply a text patch as typing would: the paths
// must still resolve to the same nodes. A wrapper (the old squiggle layer) would move the
// textarea one level deeper, and the text patch would reach the wrapper instead of the
// textarea's live value.
eq("the driver receives the menu's change", "change\n0\nlists", (() => {
  const select = byId(root, "preset");
  select.value = "lists";
  select.dispatchEvent({ type: "change" });
  return steps[0];
})());
applyPatches(root, JSON.parse(fixture.initialToLoaded), parse);
eq("the patches reproduce the loaded SSR", fixture.loaded, serialize(root));
eq("the textarea's live value is the example", fixture.loadedPage.text, byId(root, "editor").value);

const editor = byId(root, "editor");
const editorPath = (() => {
  const parts = [];
  for (let n = editor; n && n !== root; n = n.parentNode) parts.unshift(n.parentNode.childNodes.indexOf(n));
  return parts.join(".");
})();
eq("the real page puts the editor at its child-index path", "1.0.1", editorPath);
ok(nodeAt(root, editorPath) === editor, "and nodeAt resolves it");
const squiggles = mountSquiggles(editor, { document: minidoc(), segments: rules.segments });
ok(squiggles !== null, "squiggles mount on the Loom page");
ok(editor.parentNode === byId(root, "editor").parentNode,
  "the textarea is not wrapped (a wrapper breaks the patch paths)");
ok(nodeAt(root, editorPath) === editor, "the editor index is unchanged after mounting");

// The next keystroke's patch: the textarea's text node, at the path the app renders.
const typed = fixture.loadedPage.text + "\n-- typed\n";
applyPatches(root, [{ op: "text", path: editorPath + ".0", text: typed }], parse);
eq("a text patch after mounting reaches the textarea's live value", typed, editor.value);
ok(nodeAt(root, editorPath) === editor, "the text patch still resolves to the textarea");
eq("the textarea's text child still resolves", typed, nodeAt(root, editorPath + ".0").textContent);
const firstLine = typed.split("\n")[0];
squiggles.update([{
  range: { start: { line: 0, character: 0 }, end: { line: 0, character: firstLine.length } },
  severity: 1, message: "probe",
}]);
const layer = editor.parentNode.childNodes[editor.parentNode.childNodes.length - 1];
eq("the layer is the editor's last sibling", "squiggle-layer",
  layer.getAttribute && layer.getAttribute("class"));
eq("the underline follows the patched text", firstLine, layer.textContent.slice(0, firstLine.length));
applyPatches(root, [
  { op: "insert", path: "1.0", index: 3, html: '<div id="late"></div>' },
], parse);
eq("an insert at the section's end lands before the layer", "late", nodeAt(root, "1.0.3").getAttribute("id"));
ok(nodeAt(root, editorPath) === editor, "the editor path survives the insert");
eq("the layer stays last", "squiggle-layer",
  editor.parentNode.childNodes[editor.parentNode.childNodes.length - 1].getAttribute("class"));
eq("the menu's selection moved", "lists",
  walk(byId(root, "preset"), (n) => n.getAttribute && n.getAttribute("selected") != null)
    .map((n) => n.getAttribute("value")).join(","));
ok(app.state() === 0, "the driver keeps the state the runtime returned");

console.log(failed === 0 ? "playground page: all checks passed" : `playground page: ${failed} failure(s)`);
process.exit(failed === 0 ? 0 : 1);
