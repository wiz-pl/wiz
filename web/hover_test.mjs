// The playground's hover card and go-to-definition under Node: the pure content and
// location rules, then the widget against `web/framework/minidom.mjs`. No browser, no
// server: this is what the page's editor does with a `textDocument/hover` or
// `textDocument/definition` answer.
//
//   usage: node web/hover_test.mjs
"use strict";
import { document as minidoc, Element } from "./framework/minidom.mjs";
import { wantsHover, mountHover } from "./hover.js";
import { hoverContents, hoverLines, definitionTarget, locationLabel } from "./framework/hover.mjs";

let failed = 0;
function check(name, got, want) {
  const a = JSON.stringify(got, null, 0), b = JSON.stringify(want, null, 0);
  if (a === b) console.log(`ok: ${name}`);
  else { failed++; console.log(`FAIL: ${name}\n  want: ${b}\n  got:  ${a}`); }
}
function checkThat(name, condition, detail) {
  if (condition) console.log(`ok: ${name}`);
  else { failed++; console.log(`FAIL: ${name}${detail ? "\n  " + detail : ""}`); }
}
const sleep = (ms) => new Promise((resolve) => setTimeout(resolve, ms));

// ## 1. The switch

check("hover: on by default", wantsHover(""), true);
check("hover: ?hover=off", wantsHover("?hover=off"), false);
check("hover: ?hover=0", wantsHover("?hover=0"), false);
check("hover: ?hover=none", wantsHover("?hover=none"), false);
check("hover: ?hover=on", wantsHover("?hover=on"), true);
check("hover: a bad query string", wantsHover("%%%"), true);

// ## 2. Contents: the three LSP shapes, and nothing for an empty answer

check("contents: a plain string",
  hoverContents({ contents: "Nat.add : Nat → Nat → Nat" }),
  { kind: "plaintext", text: "Nat.add : Nat → Nat → Nat" });
check("contents: a bare string",
  hoverContents("Nat.add"), { kind: "plaintext", text: "Nat.add" });
check("contents: MarkupContent markdown",
  hoverContents({ contents: { kind: "markdown", value: "```wiz\nNat.add : Nat → Nat → Nat\n```" } }),
  { kind: "markdown", text: "```wiz\nNat.add : Nat → Nat → Nat\n```" });
check("contents: MarkupContent plaintext",
  hoverContents({ contents: { kind: "plaintext", value: "x : Nat" } }),
  { kind: "plaintext", text: "x : Nat" });
check("contents: an array of strings",
  hoverContents({ contents: ["x : Nat", "a Nat"] }),
  { kind: "plaintext", text: "x : Nat\n\na Nat" });
check("contents: a MarkedString with a language is code",
  hoverContents({ contents: [{ language: "wiz", value: "Nat.add : Nat → Nat → Nat" }] }),
  { kind: "markdown", text: "```wiz\nNat.add : Nat → Nat → Nat\n```" });
check("contents: unknown parts are skipped",
  hoverContents({ contents: [null, { nope: 1 }, "x : Nat"] }),
  { kind: "plaintext", text: "x : Nat" });
check("contents: whitespace only is nothing", hoverContents({ contents: "  \n " }), null);
check("contents: missing is nothing", hoverContents(null), null);
check("contents: an empty object is nothing", hoverContents({}), null);

// ## 3. Lines: fences, a rule, and a limit

check("lines: the Wiz hover shape", hoverLines(hoverContents({
  contents: { kind: "markdown", value: "```wiz\nNat.add : Nat → Nat → Nat\n```\n\n---\n\nAdds two Nats." },
})), [
  { text: "Nat.add : Nat → Nat → Nat", code: true },
  { rule: true },
  { text: "Adds two Nats.", code: false },
]);
check("lines: plain text", hoverLines("x : Nat\ny : Bool"), [
  { text: "x : Nat", code: false },
  { text: "y : Bool", code: false },
]);
check("lines: a fence without a language", hoverLines("```\na\nb\n```"), [
  { text: "a", code: true },
  { text: "b", code: true },
]);
check("lines: a long answer is cut", hoverLines("a\nb\nc\nd\ne", 3), [
  { text: "a", code: false },
  { text: "b", code: false },
  { text: "…", ellipsis: true },
]);
check("lines: blank edges go", hoverLines("\n\na\n\n"), [{ text: "a", code: false }]);
check("lines: nothing", hoverLines(""), []);

// ## 4. Definitions: Location, LocationLink, arrays and junk

const prelude = {
  uri: "file:///lib/Prelude.wiz",
  range: { start: { line: 6, character: 0 }, end: { line: 6, character: 9 } },
};
check("definition: a Location", definitionTarget(prelude), prelude);
check("definition: an array takes the first", definitionTarget([null, prelude]), prelude);
check("definition: a LocationLink", definitionTarget({
  targetUri: "file:///a/B.wiz",
  targetSelectionRange: { start: { line: 2, character: 1 }, end: { line: 2, character: 4 } },
  targetRange: { start: { line: 2, character: 0 }, end: { line: 4, character: 0 } },
}), {
  uri: "file:///a/B.wiz",
  range: { start: { line: 2, character: 1 }, end: { line: 2, character: 4 } },
});
check("definition: null", definitionTarget(null), null);
check("definition: an empty array", definitionTarget([]), null);
check("definition: no range", definitionTarget({ uri: "file:///a.wiz" }), null);
check("definition: no uri", definitionTarget({ range: prelude.range }), null);
check("definition: junk", definitionTarget("nope"), null);

// The card's label is 1-based, and the last path segment is what a person recognises.
check("label: Prelude.wiz", locationLabel(prelude), "Prelude.wiz:7:1");
check("label: a query string is not part of the name",
  locationLabel({ uri: "file:///x/y.wiz?v=2#L3", range: { start: { line: 4, character: 8 } } }),
  "y.wiz:5:9");
check("label: an encoded name",
  locationLabel({ uri: "file:///a/My%20File.wiz", range: { start: { line: 0, character: 0 } } }),
  "My File.wiz:1:1");
check("label: nothing", locationLabel(null), "");

// ## 5. The widget: timers, the caret and the card the runtime renders

function makeDoc() {
  const base = minidoc();
  const body = base.createElement("body");
  const find = (node, id) => {
    if (node && node.getAttribute && node.getAttribute("id") === id) return node;
    for (const c of (node && node.childNodes) || []) {
      const hit = find(c, id);
      if (hit) return hit;
    }
    return null;
  };
  return {
    body, createElement: base.createElement, createTextNode: base.createTextNode,
    getElementById: (id) => find(body, id),
  };
}
function makeEditor(doc, value, selectionStart = value.length) {
  const editor = new Element("textarea");
  editor.value = value;
  editor.selectionStart = selectionStart;
  editor.selectionEnd = selectionStart;
  editor.scrollTop = 0;
  editor.scrollLeft = 0;
  editor.clientHeight = 200;
  editor.clientWidth = 400;
  editor.style = {};
  editor.getBoundingClientRect = () => ({ left: 10, top: 20, width: 400, height: 200 });
  editor.setSelectionRange = (start, end) => { editor.selectionStart = start; editor.selectionEnd = end; };
  editor.focus = () => {};
  return editor;
}
function keys(editor, type, event) {
  for (const fn of editor._ls.get(type) || []) fn(Object.assign({ target: editor }, event));
}
// The card is the runtime's; the test's `show` writes the oracle's lines into a double.
function makeCard(doc, sent) {
  let card = doc.getElementById("wiz-hover");
  if (!card) {
    card = doc.createElement("div");
    card.setAttribute("id", "wiz-hover");
    doc.body.appendChild(card);
  }
  card.textContent = "";
  if (!sent.raw && !sent.label) { card.setAttribute("hidden", ""); return; }
  card.removeAttribute("hidden");
  if (sent.label) card.appendChild(doc.createTextNode(sent.label));
  const lines = sent.raw ? hoverLines(hoverContents(JSON.parse(sent.raw))) : [];
  for (const line of lines) if (!line.rule) card.appendChild(doc.createTextNode(line.text + "\n"));
}
function mounts(doc, editor, options) {
  const card = doc.createElement("div");
  card.setAttribute("id", "wiz-hover");
  card.setAttribute("hidden", "");
  doc.body.appendChild(card);
  return mountHover({ editor, document: doc, show: (raw, label) => makeCard(doc, { raw, label }), ...options });
}
const HOVER = {
  contents: {
    kind: "markdown",
    value: "```wiz\nNat.add : Nat → Nat → Nat\n```\n\n---\n\nAdds two Nats.",
  },
};
const sameDoc = { uri: "file:///play.wiz", range: { start: { line: 1, character: 4 }, end: { line: 1, character: 9 } } };

{
  const doc = makeDoc();
  const editor = makeEditor(doc, "exact n\n", 5);
  const asked = [];
  const hover = mounts(doc, editor, {
    delay: 5,
    onHover: (position) => { asked.push(position); return HOVER; },
  });
  checkThat("widget: mounted", !!hover);
  checkThat("widget: not open", !hover.isOpen());

  await hover.inquire();
  check("widget: one request", asked.length, 1);
  check("widget: asked at the caret", asked[0], { line: 0, character: 5 });
  checkThat("widget: open", hover.isOpen());
  checkThat("widget: the signature", hover.content().includes("Nat.add : Nat → Nat → Nat"));
  checkThat("widget: the doc comment", hover.content().includes("Adds two Nats."));

  keys(editor, "keydown", { key: "Escape" });
  checkThat("widget: Escape closes", !hover.isOpen());
  check("widget: nothing to see", hover.content(), "");

  hover.close();
  const quiet = mounts(doc, editor, { onHover: () => null });
  await quiet.inquire();
  checkThat("widget: null is silence", !quiet.isOpen());

  const failing = mounts(doc, editor, { onHover: () => { throw new Error("MethodNotFound"); } });
  await failing.inquire();
  checkThat("widget: an error is silence", !failing.isOpen());

  await hover.inquire();
  keys(editor, "input", {});
  checkThat("widget: typing closes", !hover.isOpen());
  await hover.inquire();
  keys(editor, "scroll", {});
  checkThat("widget: scrolling closes", !hover.isOpen());

  hover.close();
  let resolveHover;
  const slow = mounts(doc, editor, {
    onHover: () => new Promise((resolve) => { resolveHover = resolve; }),
  });
  const answer = slow.inquire();
  editor.selectionStart = 1;
  resolveHover(HOVER);
  await answer;
  checkThat("widget: a stale answer is dropped", !slow.isOpen());

  const debounce = [];
  const timed = mounts(doc, editor, {
    delay: 5,
    onHover: (position) => { debounce.push(position.character); return HOVER; },
  });
  editor.selectionStart = 3;
  keys(editor, "keyup", { key: "ArrowLeft" });
  keys(editor, "keyup", { key: "ArrowLeft" });
  await sleep(25);
  check("widget: one request after the rest", debounce, [3]);
  checkThat("widget: the card is up", timed.isOpen());
  timed.destroy();
  checkThat("widget: destroy closes it", !timed.isOpen());
}

// ## 6. Go to definition: F12, Ctrl-click and a library definition

{
  const doc = makeDoc();
  const editor = makeEditor(doc, "def x := Nat.add 1 2\n", 12);
  const jumps = [];
  const asked = [];
  const hover = mounts(doc, editor, {
    onHover: () => null,
    onDefinition: (position) => { asked.push(position); return sameDoc; },
    onJump: (target) => { jumps.push(target); return true; },
  });
  await hover.goToDefinition();
  check("definition: asked at the caret", asked[0], { line: 0, character: 12 });
  check("definition: the page jumps", jumps, [sameDoc]);
  checkThat("definition: the card stays closed after a jump", !hover.isOpen());

  keys(editor, "keydown", { key: "F12" });
  await sleep(5);
  check("definition: F12 asks", asked.length, 2);

  editor.selectionStart = 19;
  keys(editor, "click", { ctrlKey: true });
  await sleep(5);
  check("definition: Ctrl-click asks", asked.length, 3);
  check("definition: Ctrl-click's caret", asked[2], { line: 0, character: 19 });

  hover.close();
  const elsewhere = mounts(doc, editor, { onDefinition: () => prelude });
  const target = await elsewhere.goToDefinition();
  check("definition: the library target", target, prelude);
  checkThat("definition: the card is up", elsewhere.isOpen());
  checkThat("definition: the library is named", elsewhere.content().includes("Prelude.wiz:7:1"));
  check("definition: no jump without onJump", elsewhere.content(), "Prelude.wiz:7:1");
  elsewhere.close();

  const empty = mounts(doc, editor, { onDefinition: () => null });
  check("definition: null", await empty.goToDefinition(), null);
  checkThat("definition: null is silence", !empty.isOpen());
}

// ## 7. Without a document (or without a request function) there is no widget

check("widget: no editor", mountHover({ document: minidoc(), onHover: () => null }), null);
check("widget: no document", mountHover({ editor: { value: "" }, onHover: () => null }), null);
check("widget: no request", mountHover({ editor: { value: "" }, document: minidoc() }), null);

if (failed) {
  console.log(`hover: ${failed} check(s) failed`);
  process.exit(1);
}
console.log("hover: all checks passed");
