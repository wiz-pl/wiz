// The playground editor's two DOM widgets under Node, against `web/framework/minidom.mjs`
// (the same DOM double the React framework's browser half is tested with). No browser:
// this checks what the widgets put in the tree and what keys do, not how they look.
//
//   usage: node web/editor_dom_test.mjs
"use strict";
import { readFileSync } from "node:fs";
import { document as minidoc, Element } from "./framework/minidom.mjs";
import { mountSquiggles, wantsSquiggles } from "./squiggles.js";
import { mountCompletions, wantsCompletions } from "./completions.js";
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
const sleep = (ms) => new Promise((resolve) => setTimeout(resolve, ms));

// A page double: minidom's elements, plus the pieces the widgets reach for. The `Event`
// class is a plain one: minidom assigns `target` and `preventDefault` to the event object
// (a real DOM forbids that, so a real `Event` would throw here).
function makeDoc() {
  const base = minidoc();
  const body = base.createElement("body");
  return {
    body,
    createElement: base.createElement,
    createTextNode: base.createTextNode,
    createRange: base.createRange,
    defaultView: {
      Event: class FakeEvent {
        constructor(type) { this.type = type; }
      },
    },
  };
}

// A textarea double. It is an Element (so the widgets can listen and dispatch), with the
// text-field properties and the two methods a widget calls.
function makeEditor(doc, value, selectionStart = value.length) {
  const editor = new Element("textarea");
  editor.value = value;
  editor.selectionStart = selectionStart;
  editor.selectionEnd = selectionStart;
  editor.scrollTop = 0;
  editor.scrollLeft = 0;
  editor.clientHeight = 200;
  editor.clientWidth = 400;
  editor.setSelectionRange = (start, end) => { editor.selectionStart = start; editor.selectionEnd = end; };
  editor.getBoundingClientRect = () => ({ left: 10, top: 20, width: 400, height: 200 });
  return editor;
}

// The first `<span class="squiggle">` in a tree.
function firstSquiggle(n) {
  if (n.getAttribute && (n.getAttribute("class") || "").split(/\s+/).includes("squiggle")) return n;
  for (const c of n.childNodes || []) {
    const found = firstSquiggle(c);
    if (found) return found;
  }
  return null;
}

// The text under each `<span class="squiggle">`, in document order.
function squiggleTexts(layer) {
  const out = [];
  const walk = (n) => {
    if (n.getAttribute) {
      const cls = n.getAttribute("class") || "";
      if (cls.split(/\s+/).includes("squiggle")) { out.push(n.textContent); return; }
    }
    for (const c of n.childNodes || []) walk(c);
  };
  walk(layer);
  return out;
}

// ## 1. Squiggles: diagnostics become underlines under the offending text

{
  const doc = makeDoc();
  const editor = makeEditor(doc, "def f : Nat := nope\n");
  const pane = doc.createElement("div");
  pane.appendChild(editor);
  doc.body.appendChild(pane);
  const squiggles = mountSquiggles(editor, { document: doc, segments: rules.segments });
  checkThat("squiggles: a layer beside the editor", !!squiggles);
  // The editor is not wrapped: it stays where it was and the layer is appended after it,
  // so a child-index patch applier still finds the textarea at its original path.
  checkThat("squiggles: the editor is not wrapped", editor.parentNode === pane);
  check("squiggles: the layer is the parent's last child", pane.childNodes.length, 2);
  check("squiggles: the layer is beside the editor", pane.childNodes[1].getAttribute("class"), "squiggle-layer");

  squiggles.update([{
    range: { start: { line: 0, character: 15 }, end: { line: 0, character: 19 } },
    severity: 1, message: "unknown identifier",
  }]);
  check("squiggles: one underline", squiggleTexts(pane).length, 1);
  check("squiggles: under the offending text", squiggleTexts(pane), ["nope"]);
  check("squiggles: the message is the tooltip", firstSquiggle(pane).getAttribute("title"), "unknown identifier");
  check("squiggles: the severity class", firstSquiggle(pane).getAttribute("class"), "squiggle sev-error");

  check("squiggles: the count is on the parent", pane.getAttribute("data-squiggles"), "1");

  // Diagnostics clear: nothing is drawn.
  squiggles.update([]);
  check("squiggles: cleared", squiggleTexts(pane).length, 0);
  checkThat("squiggles: the layer is hidden", pane.childNodes[1].getAttribute("hidden") === "");

  // A missing end underlines the token, and a multi-line range is one span per line.
  squiggles.update([{ range: { start: { line: 0, character: 15 } }, message: "m" }]);
  check("squiggles: a range with no end", squiggleTexts(pane), ["nope"]);
  squiggles.update([{
    range: { start: { line: 0, character: 4 }, end: { line: 1, character: 2 } }, severity: 2,
  }]);
  check("squiggles: a multi-line range underlines each line", squiggleTexts(pane), ["f : Nat := nope"]);

  // Typing re-renders the same spans against the new text (the offsets are stale until
  // the server answers, and must not throw).
  editor.value = "def g : Nat := nope\n";
  for (const fn of editor._ls.get("input") || []) fn({ type: "input" });
  checkThat("squiggles: re-rendered after typing", squiggleTexts(pane).length === 1);

  squiggles.destroy();
  check("squiggles: destroyed, the layer is gone", pane.childNodes.length, 1);
  checkThat("squiggles: destroyed, the editor stays", editor.parentNode === pane);
}

// The class suffix is the runtime's `severityName`, not a numeric map in the widget: a
// name the page does not know is still the one painted (`sev-hint` for a severity-1
// span). The oracle's `rules.segments` would re-derive the name, so this uses a rule
// that returns a runtime-shaped span directly.
{
  const doc = makeDoc();
  const editor = makeEditor(doc, "def f : Nat := nope\n");
  const pane = doc.createElement("div");
  pane.appendChild(editor);
  doc.body.appendChild(pane);
  const squiggles = mountSquiggles(editor, {
    document: doc,
    segments: () => [{ start: 15, stop: 19, severity: 1, severityName: "hint", message: "m" }],
  });
  squiggles.update([]);
  check("squiggles: the runtime's severity name is painted verbatim",
    firstSquiggle(pane).getAttribute("class"), "squiggle sev-hint");
  squiggles.destroy();
}

check("squiggles: on by default", wantsSquiggles(""), true);
check("squiggles: ?squiggles=off", wantsSquiggles("?squiggles=off"), false);
check("squiggles: ?squiggles=0", wantsSquiggles("?squiggles=0"), false);
check("squiggles: ?squiggles=on", wantsSquiggles("?squiggles=on"), true);

// ## 2. Completions: the popup, the keys and the insertion

const NAT_ITEMS = [
  { label: "Nat.add", detail: "Nat → Nat → Nat" },
  { label: "Nat.sub", detail: "Nat → Nat → Nat" },
  { label: "Nat.succ", detail: "Nat → Nat" },
];

function completionPage(options = {}) {
  const doc = makeDoc();
  const editor = makeEditor(doc, options.value || "", options.caret);
  doc.body.appendChild(editor);
  const calls = [];
  const popup = mountCompletions({
    editor, document: doc, rules: options.rules || rules,
    debounce: options.debounce === undefined ? 5 : options.debounce,
    autoTrigger: options.autoTrigger,
    onRequest: options.onRequest || (async (position) => { calls.push(position); return options.items || NAT_ITEMS; }),
  });
  return { doc, editor, popup, calls };
}

{
  const { editor, popup, calls } = completionPage({ value: "def x := Nat.a", caret: 14 });
  const shown = await popup.request({ line: 0, character: 14 });
  check("completions: the request's position", calls, [{ line: 0, character: 14 }]);
  check("completions: opened", popup.isOpen(), true);
  check("completions: filtered by the typed prefix", shown.map((i) => i.label), ["Nat.add"]);
  check("completions: the first is selected", popup.selectedIndex(), 0);
  const rows = popup.element().childNodes;
  check("completions: one row", rows.length, 1);
  check("completions: the row's label", rows[0].childNodes[0].textContent, "Nat.add");
  check("completions: the row's detail", rows[0].childNodes[1].textContent, "Nat → Nat → Nat");
  check("completions: aria-selected", rows[0].getAttribute("aria-selected"), "true");
  check("completions: the list is visible", popup.element().getAttribute("hidden"), null);

  // Down/Up move with wrapping; Escape closes.
  popup.handleKey({ key: "ArrowDown", preventDefault() {} });
  check("completions: down", popup.selectedIndex(), 0);   // one item: wraps to itself
  popup.handleKey({ key: "Escape", preventDefault() {} });
  check("completions: escape closes", popup.isOpen(), false);
  checkThat("completions: the list is hidden", popup.element().getAttribute("hidden") === "");
}

{
  const { editor, popup } = completionPage({ value: "Nat.", caret: 4 });
  await popup.request({ line: 0, character: 4 });
  check("completions: all three match", popup.items().map((i) => i.label), ["Nat.add", "Nat.sub", "Nat.succ"]);
  popup.handleKey({ key: "ArrowDown", preventDefault() {} });
  popup.handleKey({ key: "ArrowDown", preventDefault() {} });
  check("completions: down twice", popup.selectedIndex(), 2);
  popup.handleKey({ key: "ArrowDown", preventDefault() {} });
  check("completions: down wraps to the first", popup.selectedIndex(), 0);
  popup.handleKey({ key: "ArrowUp", preventDefault() {} });
  check("completions: up wraps to the last", popup.selectedIndex(), 2);
  popup.handleKey({ key: "PageUp", preventDefault() {} });
  check("completions: page up wraps through the list", popup.selectedIndex(), 1);

  // Enter accepts the selected item over the typed prefix.
  let prevented = false;
  let inputs = 0;
  editor.addEventListener("input", () => { inputs++; });
  popup.handleKey({ key: "Enter", preventDefault() { prevented = true; }, stopPropagation() {} });
  check("completions: Enter is the popup's", prevented, true);
  check("completions: the text", editor.value, "Nat.sub");
  check("completions: the caret", editor.selectionStart, 7);
  check("completions: one input event", inputs, 1);
  check("completions: closed after accepting", popup.isOpen(), false);
}

{
  // The host has no key table: it carries out whichever command the runtime names, even
  // when the key is not one a real popup binds (here ArrowDown means "close").
  const command = { action: "close" };
  const { popup } = completionPage({
    value: "Nat.", caret: 4, rules: { ...rules, key: () => command },
  });
  await popup.request({ line: 0, character: 4 });
  let prevented = false;
  popup.handleKey({ key: "ArrowDown", preventDefault() { prevented = true; } });
  check("completions: the runtime's key command is carried out", popup.isOpen(), false);
  check("completions: a handled key is prevented", prevented, true);
}

{
  // A move command carries the index itself; the host sets it, it does not add a delta.
  const { popup } = completionPage({
    value: "Nat.", caret: 4, rules: { ...rules, key: () => ({ action: "move", index: 2 }) },
  });
  await popup.request({ line: 0, character: 4 });
  popup.handleKey({ key: "x", preventDefault() {} });
  check("completions: the runtime's index is the selection", popup.selectedIndex(), 2);
}

{
  // Tab accepts too, and a `textEdit` replaces the range the server named.
  const editItems = [{
    label: "twice",
    textEdit: { range: { start: { line: 0, character: 9 }, end: { line: 0, character: 11 } }, newText: "twice" },
  }];
  const { editor, popup } = completionPage({ value: "def y := tw", caret: 11, items: editItems });
  await popup.request({ line: 0, character: 11 });
  popup.handleKey({ key: "Tab", preventDefault() {}, stopPropagation() {} });
  check("completions: Tab accepts", editor.value, "def y := twice");
  check("completions: the caret after a textEdit", editor.selectionStart, 14);
}

{
  // Typing an identifier character asks on its own after the debounce.
  const { editor, popup, calls } = completionPage({ value: "Nat", caret: 3 });
  for (const fn of editor._ls.get("input") || []) fn({ type: "input" });
  check("completions: not asked synchronously", calls.length, 0);
  await sleep(30);
  check("completions: asked after the debounce", calls.length, 1);
  check("completions: at the caret", calls[0], { line: 0, character: 3 });
  check("completions: open after typing", popup.isOpen(), true);

  // A non-identifier key closes; a space is not a completion context.
  editor.value = "Nat ";
  editor.selectionStart = 4;
  for (const fn of editor._ls.get("input") || []) fn({ type: "input" });
  check("completions: a space closes", popup.isOpen(), false);
  await sleep(30);
  check("completions: no request after a space", calls.length, 1);
}

{
  // Ctrl-Space asks even with no prefix; blur closes.
  const { editor, popup, calls } = completionPage({ value: "", caret: 0 });
  popup.handleKey({ key: " ", ctrlKey: true, code: "Space", preventDefault() {} });
  await sleep(10);
  check("completions: ctrl-space asks", calls.length, 1);
  check("completions: ctrl-space opens", popup.isOpen(), true);
  for (const fn of editor._ls.get("blur") || []) fn({ type: "blur" });
  check("completions: blur closes", popup.isOpen(), false);
}

{
  // A server without completion: the request rejects and the page is silent.
  const { popup } = completionPage({ value: "x", caret: 1, onRequest: async () => { throw new Error("no completion"); } });
  const shown = await popup.request({ line: 0, character: 1 });
  check("completions: an error shows nothing", shown, []);
  check("completions: an error leaves it closed", popup.isOpen(), false);
  // An empty result is the same.
  const empty = completionPage({ value: "x", caret: 1, items: [] });
  await empty.popup.request({ line: 0, character: 1 });
  check("completions: an empty result is closed", empty.popup.isOpen(), false);
}

{
  // A stale answer does not reopen a popup the user closed.
  let release;
  const gate = new Promise((resolve) => { release = resolve; });
  const { popup } = completionPage({ value: "N", caret: 1, onRequest: async () => { await gate; return NAT_ITEMS; } });
  const pending = popup.request({ line: 0, character: 1 });
  popup.close();
  release();
  await pending;
  check("completions: a stale answer is dropped", popup.isOpen(), false);
}

{
  // The answer was computed for "N", but the user typed "at" while it was in flight:
  // its textEdit range ends at the old caret, so applying it to the new text would
  // duplicate the typed suffix (`def x := Nat.addat`). The accept re-anchors the edit
  // on the identifier prefix at the current caret.
  let release;
  const gate = new Promise((resolve) => { release = resolve; });
  const stale = [{
    label: "Nat.add",
    textEdit: {
      range: { start: { line: 0, character: 9 }, end: { line: 0, character: 10 } },
      newText: "Nat.add",
    },
  }];
  const { editor, popup } = completionPage({
    value: "def x := N", caret: 10, autoTrigger: false,
    onRequest: async () => { await gate; return stale; },
  });
  const pending = popup.request({ line: 0, character: 10 });
  editor.value = "def x := Nat";
  editor.selectionStart = 12;
  editor.selectionEnd = 12;
  for (const fn of editor._ls.get("input") || []) fn({ type: "input" });
  release();
  await pending;
  check("completions: the stale answer opens over the new prefix", popup.isOpen(), true);
  popup.handleKey({ key: "Enter", preventDefault() {}, stopPropagation() {} });
  check("completions: a textEdit from older text is not applied", editor.value, "def x := Nat.add");
  check("completions: the caret after a re-anchored edit", editor.selectionStart, 16);
}

// The popup may not bring back the policy the runtime owns: a local key table, a page
// size, or scoring/filtering/acceptance arithmetic is the regression this pins.
{
  const source = readFileSync(new URL("./completions.js", import.meta.url), "utf-8");
  checkThat("source: no local key table",
    !/case\s+"(?:Arrow|Page|Enter|Tab|Escape)/.test(source));
  checkThat("source: no local page size", !/\bPAGE\b/.test(source));
  checkThat("source: no local completion scoring, filtering or acceptance",
    !/completionScore|filterCompletions|acceptCompletion|completionPopupState/.test(source));
}

check("completions: on by default", wantsCompletions(""), true);
check("completions: ?completions=off", wantsCompletions("?completions=off"), false);
check("completions: ?completions=0", wantsCompletions("?completions=0"), false);

if (failed) {
  console.log(`editor dom: ${failed} check(s) failed`);
  process.exit(1);
}
console.log("editor dom: all checks passed");
