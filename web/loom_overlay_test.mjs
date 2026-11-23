// The playground page and its editor overlays, together: the page patches its DOM by
// child index (web/framework/runtime.js; `Loom.patchesJson` emits the paths), so the
// squiggle layer must not move the textarea in the tree. It used to wrap the editor in a
// positioned div, which put the textarea one level deeper: the patch that changes the
// editor text then resolved to the wrapper, and the textarea's *live* value kept the old
// text while the mirror drew underlines under the new one. This test mounts the page's
// own tree, turns both overlays on as the page now does, and applies the patches the Loom
// app emits — the text must reach the textarea and its squiggles.
//
// A Node DOM double (web/framework/minidom.mjs), no Wasm and no browser:
//
//   node web/loom_overlay_test.mjs
"use strict";
import { applyPatches, mount, nodeAt } from "./framework/runtime.js";
import { document as minidoc, parse, serialize } from "./framework/minidom.mjs";
import { mountSquiggles } from "./squiggles.js";
import { mountCompletions } from "./completions.js";
import { rules } from "./framework/editor-model.mjs";

let failed = 0;
function check(name, got, want) {
  const a = JSON.stringify(got), b = JSON.stringify(want);
  if (a === b) console.log(`ok: ${name}`);
  else { failed++; console.log(`FAIL: ${name}\n  want: ${b}\n  got:  ${a}`); }
}
function checkThat(name, condition, detail) {
  if (condition) console.log(`ok: ${name}`);
  else { failed++; console.log(`FAIL: ${name}${detail ? "\n  " + detail : ""}`); }
}

// A page double: minidom plus a body, the root the Loom driver mounts into.
function makeDoc() {
  const base = minidoc();
  const body = base.createElement("body");
  return {
    body,
    createElement: base.createElement,
    createTextNode: base.createTextNode,
    createRange: base.createRange,
    defaultView: { Event: class FakeEvent { constructor(type) { this.type = type; } } },
  };
}

// web/playground-ui.wiz's shape: body → header, main, footer; main → the editor's section
// and the goals/output section. In the editor section the textarea is child 1 (after the
// pane head, before the actions), so its text node is at "1.0.1.0" from the body.
const SSR =
  '<header><span id="status">loading the engine…</span></header>' +
  '<main>' +
    '<section class="pane">' +
      '<div class="pane-head"><label for="editor">Program</label></div>' +
      '<textarea id="editor" spellcheck="false" data-wiz-on-input="0">import Prelude\n</textarea>' +
      '<div class="actions"><button id="run" type="button" disabled>Run</button>' +
        '<span id="count" class="dim">0 lines</span></div>' +
    '</section>' +
    '<section class="pane side"><div id="goals" class="goals"></div>' +
      '<div id="output" class="output"></div></section>' +
  '</main>' +
  '<footer><span id="engine">engine: loading</span></footer>';

const doc = makeDoc();
const body = doc.body;
mount(body, SSR, parse);

const editor = nodeAt(body, "1.0.1");
const section = editor.parentNode;
check("the editor is where the Loom SSR puts it", editor.getAttribute("id"), "editor");
check("the editor's text node is the patch target", nodeAt(body, "1.0.1.0").textContent, "import Prelude\n");

// The page's `wireGoals`: both overlays are on, no Loom-specific flags.
const squiggles = mountSquiggles(editor, { document: doc, segments: rules.segments });
const completions = mountCompletions({
  editor, document: doc, rules, onRequest: async () => [],
});
checkThat("squiggles: mounted under the Loom page", !!squiggles);
checkThat("completions: mounted under the Loom page", !!completions);
checkThat("squiggles: the editor is not wrapped", editor.parentNode === section);
checkThat("squiggles: the editor keeps its index", nodeAt(body, "1.0.1") === editor);
check("squiggles: the layer is the section's last child",
  section.childNodes[section.childNodes.length - 1].getAttribute("data-squiggle-layer"), "1");
checkThat("completions: the popup is outside the editor's subtree",
  completions.element().parentNode === body);
checkThat("completions: the popup is the body's last child",
  body.childNodes[body.childNodes.length - 1] === completions.element());
// A Loom insert at the end of the root (body) goes before the popup, so the popup never
// takes a rendered child's index.
applyPatches(body, [
  { op: "insert", path: "", index: 3, html: '<div id="root-tail"></div>' },
], parse);
check("completions: a root insert lands before the popup", nodeAt(body, "3").getAttribute("id"), "root-tail");
checkThat("completions: the popup stays last",
  body.childNodes[body.childNodes.length - 1] === completions.element());

// The Loom app's text patch (the editor's `input` message): path "1.0.1.0" is the
// textarea's text node. With a wrapper it resolved to the wrapper, the runtime's
// textarea special case did not fire, and the live value stayed stale.
const typed = "import Prelude\ndef twice (n : Nat) : Nat := nope\n";
applyPatches(body, [
  { op: "text", path: "1.0.1.0", text: typed },
  { op: "text", path: "1.0.2.1.0", text: "1 line" },
], parse);
check("the text patch reaches the textarea's live value", editor.value, typed);
check("the text patch reaches the textarea's text", nodeAt(body, "1.0.1.0").textContent, typed);
check("the count patch reaches its node", nodeAt(body, "1.0.2.1.0").textContent, "1 line");
checkThat("the textarea is still at the same path", nodeAt(body, "1.0.1") === editor);

// The diagnostics arrive after the text: the mirror underlines the new text (the old
// wrapper also made `squiggles.update` read a stale `editor.value`).
const at = typed.indexOf("nope");
const before = typed.slice(0, at);
const line = (before.match(/\n/g) || []).length;
const character = at - (before.lastIndexOf("\n") + 1);
squiggles.update([{
  range: { start: { line, character }, end: { line, character: character + 4 } },
  severity: 1, message: "unknown identifier",
}]);
const underlines = [];
const walk = (n) => {
  if (n.getAttribute && (n.getAttribute("class") || "").split(/\s+/).includes("squiggle")) {
    underlines.push(n.textContent);
    return;
  }
  for (const c of n.childNodes || []) walk(c);
};
walk(section);
check("the squiggle is under the patched text", underlines, ["nope"]);
check("the underline is drawn over the textarea's box",
  section.childNodes[section.childNodes.length - 1].getAttribute("hidden"), null);

// An insert at the end of the section goes *before* the layer (the runtime's append
// index), so the textarea's path and the layer's "after all rendered children" place hold.
applyPatches(body, [
  { op: "insert", path: "1.0", index: 3, html: '<div id="late"></div>' },
], parse);
check("the inserted sibling is not the layer", nodeAt(body, "1.0.3").getAttribute("id"), "late");
checkThat("the editor is still at its path after an insert", nodeAt(body, "1.0.1") === editor);
check("the layer stays last",
  section.childNodes[section.childNodes.length - 1].getAttribute("data-squiggle-layer"), "1");

if (failed) {
  console.log(`loom overlay: ${failed} check(s) failed`);
  process.exit(1);
}
console.log("loom overlay: all checks passed");
