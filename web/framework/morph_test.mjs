// The patch applier's morph fallback (web/framework/runtime.js) under Node.
//
// A batch whose HTML-carrying `replace` removes the focused element (or an ancestor of
// it) is applied as a morph: children are matched by `id`/`data-key` first and by
// position otherwise, so a keyed child moves without being re-created and a focused
// control keeps its node, selection and live value. A batch that does not touch the
// focus stays on the fast keyed patch path, unchanged.
//
//   node web/framework/morph_test.mjs
"use strict";
import { applyPatches } from "./runtime.js";
import { parse, serialize, document as minidom } from "./minidom.mjs";

let failed = 0;
const ok = (cond, what, detail = "") => {
  if (cond) console.log("ok: " + what);
  else { failed++; console.log("FAIL: " + what + (detail ? "\n  " + detail : "")); }
};
const eq = (what, want, got) => ok(Object.is(got, want), what,
  `want ${JSON.stringify(want)}\n  got  ${JSON.stringify(got)}`);

const doc = minidom();
const rootWith = (html) => parse(html);
const patch = (root, ops) => applyPatches(root, ops, parse, { document: doc });
const byId = (root, id) => {
  const walk = (n) => {
    if (n.getAttribute && n.getAttribute("id") === id) return n;
    for (const c of n.childNodes || []) { const hit = walk(c); if (hit) return hit; }
    return null;
  };
  return walk(root);
};

// ## The fast path stays the fast path
{
  const root = rootWith('<section id="s"><p id="keep">old</p></section>');
  const oldSection = root.childNodes[0];
  const oldP = oldSection.childNodes[0];
  patch(root, [{ op: "replace", path: "0", html: '<section id="s"><p id="keep">new</p></section>' }]);
  ok(root.childNodes[0] !== oldSection && root.childNodes[0].childNodes[0] !== oldP,
    "a batch with no focused element replaces through the fast path");
  eq("the fast path still lands the new tree",
    '<section id="s"><p id="keep">new</p></section>', serialize(root));
}

// ## A touching batch morphs: identity, keyed move, focus, selection and live value
{
  const root = rootWith('<div id="form"><p id="a">a</p><input id="ed" value="default">' +
    '<textarea id="ta">x</textarea></div>');
  const form = root.childNodes[0];
  const p = byId(form, "a");
  const input = byId(form, "ed");
  const area = byId(form, "ta");
  input.value = "typed";
  input.setSelectionRange(2, 3);
  input.focus();
  ok(input === doc.activeElement, "the test double tracks the focused element");

  const next = '<div id="form"><input id="ed" value="default"><p id="a">changed</p>' +
    '<textarea id="ta">y</textarea><span id="new">n</span></div>';
  patch(root, [{ op: "replace", path: "0", html: next }]);

  ok(doc.activeElement === input, "the focused input keeps its node and the focus");
  eq("the live value survives", "typed", input.value);
  eq("the selection survives", "2,3", input.selectionStart + "," + input.selectionEnd);
  ok(byId(root, "a") === p, "a keyed sibling with an id keeps its node");
  eq("its text was updated in place", "changed", p.textContent);
  ok(byId(root, "ta") === area, "the textarea keeps its node");
  eq("its default text was updated", "y", area.childNodes[0].textContent);
  ok(byId(root, "new") !== null, "a new keyed child was inserted");
  eq("the keyed move and the text update produce the new SSR", next, serialize(root));
}

// ## A focused textarea's text is the user's; its text child is only the default
{
  const root = rootWith('<div><textarea id="ta">x</textarea></div>');
  const area = byId(root, "ta");
  area.value = "typed";
  area.setSelectionRange(1, 2);
  area.focus();
  patch(root, [{ op: "replace", path: "0",
    html: '<div><textarea id="ta">new default</textarea></div>' }]);
  eq("the focused textarea keeps its live value", "typed", area.value);
  eq("its selection survives", "1,2", area.selectionStart + "," + area.selectionEnd);
  ok(area.childNodes[0].textContent === "new default",
    "the text child (the default value) still updates");
}

// ## `move` by key: the key identifies the child, not an index
{
  const root = rootWith('<ul id="l"><li id="a">A</li><li id="b">B</li></ul>');
  patch(root, [{ op: "move", path: "0", key: "b", dst: 0 }]);
  eq("a keyed move puts b before a", '<ul id="l"><li id="b">B</li><li id="a">A</li></ul>',
    serialize(root));
  patch(root, [{ op: "move", path: "0", src: 0, dst: 1 }]);
  eq("an index move still works", '<ul id="l"><li id="a">A</li><li id="b">B</li></ul>',
    serialize(root));
}

// ## A batch that touches a sibling, not the focus, stays on the fast path
{
  const root = rootWith('<div><input id="ed"><section id="s"><p>old</p></section></div>');
  const input = byId(root, "ed");
  const section = byId(root, "s");
  input.focus();
  patch(root, [{ op: "replace", path: "0.1",
    html: '<section id="s"><p>new</p></section>' }]);
  ok(root.childNodes[0].childNodes[1] !== section,
    "an unrelated replace is still a fast replace (the morph is only for the focused subtree)");
  ok(doc.activeElement === input, "the untouched focused element keeps the focus");
  eq("the sibling's text still updates", "new",
    root.childNodes[0].childNodes[1].childNodes[0].textContent);
}

// ## A keyed node is not consumed by an earlier unkeyed sibling of the same tag
{
  const root = rootWith('<div><div id="a">a</div><span>s</span><input id="ed"></div>');
  const a = byId(root, "a");
  const input = byId(root, "ed");
  input.focus();
  patch(root, [{ op: "replace", path: "0",
    html: '<div><div>new</div><div id="a">a</div><input id="ed"></div>' }]);
  ok(byId(root, "a") === a, "the keyed node keeps its identity when an unkeyed sibling precedes it");
  ok(byId(root, "ed") === input && doc.activeElement === input,
    "the focused node still keeps its identity and focus");
  eq("the result is the new SSR",
    '<div><div>new</div><div id="a">a</div><input id="ed"></div>', serialize(root));
}

// ## An earlier op shifts the path: the morph decision is against the tree at apply time
{
  const root = rootWith('<div><p id="gone">x</p><section id="s"><input id="ed"></section></div>');
  const input = byId(root, "ed");
  input.value = "typed";
  input.focus();
  patch(root, [
    { op: "remove", path: "0", index: 0 },
    { op: "replace", path: "0.0", html: '<section id="s"><input id="ed"></section>' },
  ]);
  ok(byId(root, "ed") === input && doc.activeElement === input,
    "a replace whose path was shifted by an earlier remove still morphs");
  eq("the live value survives", "typed", input.value);
  eq("the batch lands", '<div><section id="s"><input id="ed"></section></div>', serialize(root));
}

// ## A batch that replaces the whole container in place
{
  const root = rootWith('<header>h</header><main><input id="ed" value="d"></main>');
  const input = byId(root, "ed");
  input.value = "typed";
  input.focus();
  patch(root, [{ op: "replace", path: "",
    html: '<header>h2</header><main><input id="ed" value="d"><b>new</b></main>' }]);
  ok(byId(root, "ed") === input, "a replace of the container morphs its children");
  eq("the focused input keeps its value", "typed", input.value);
  eq("the container is exactly the new SSR",
    '<header>h2</header><main><input id="ed" value="d"><b>new</b></main>', serialize(root));
}

console.log(failed === 0 ? "loom morph: all checks passed" : `loom morph: ${failed} failure(s)`);
process.exit(failed === 0 ? 0 : 1);
