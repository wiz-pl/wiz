// Hover at the caret and go-to-definition for the playground editor.
//
// Two server features the page never used: `textDocument/hover` (the type of the
// identifier under the caret and, for a global, its doc comment) and
// `textDocument/definition` (where it is declared, including inside the library). The
// client advertises both in `initialize` (`web/lsp-client.js`), and the server
// implements them (`Wiz/LSP.lean`, the `hover`/`definition` branch); this module is the
// page's half: a small card over the editor and the rules for when to ask.
//
// **What the card shows, and its safety.** Hover contents are Markdown by contract
// (`docs/playground-lsp.md`), but the card is not a Markdown viewer and does not
// interpret HTML: `hoverContents` normalises the three LSP shapes, `hoverLines` turns
// them into text lines (a fenced block stays code, `---` is a rule), and the widget
// writes each line with `textContent`. A server therefore cannot inject markup into the
// page. A definition in another document (a library file) has no page to open, so the
// card shows `Prelude.wiz:7:1` and leaves the editor alone.
//
// **When it asks.** Hover is asked when the caret *rests* after a mouse click or
// selection, or after an arrow/Home/End/Page key — not after typing, where a popup on
// every keystroke is noise — and after `delay` ms. F12 and Ctrl/⌘-click ask for the
// definition at the caret. Escape, typing, scrolling or leaving the field close the
// card. A server that answers `null` or `MethodNotFound` is silent: the playground keeps
// working exactly as before.
//
// The decisions are pure functions (tested in `web/hover_test.mjs`); `mountHover` is the
// DOM and the timers, tested against `web/framework/minidom.mjs`.
"use strict";
import { positionAt } from "./goals.js";

// `?hover=off` (also `0`, `none`, `false`) turns the feature off. On by default.
export function wantsHover(search) {
  try {
    const value = new URLSearchParams(search || "").get("hover");
    return value === null || !/^\s*(off|none|no|0|false)\s*$/i.test(value);
  } catch (_) {
    return true;
  }
}

// ## Hover contents

// One LSP `MarkedString`/`MarkupContent`/plain string as `{kind, text, language}`.
function contentPart(part) {
  if (typeof part === "string") return { kind: "plaintext", text: part, language: null };
  if (!part || typeof part !== "object") return null;
  if (typeof part.value !== "string") return null;
  const kind = part.kind === "plaintext" ? "plaintext" : "markdown";
  const language = typeof part.language === "string" && part.language !== "" ? part.language : null;
  return { kind, text: part.value, language };
}

// A `textDocument/hover` result as `{kind: "markdown"|"plaintext", text}` or null.
// Accepts LSP's three forms:
//
//   * a string,
//   * `{kind, value}` (MarkupContent),
//   * an array of strings / `{language, value}` (MarkedString) / MarkupContent.
//
// A `{language, value}` part becomes a fenced code block, so `hoverLines` keeps it
// code. Unknown parts are skipped rather than shown as `[object Object]`; empty contents
// are null ("nothing at this character"), which is what the widget treats as silence.
export function hoverContents(result) {
  const raw = result && typeof result === "object" && "contents" in result ? result.contents : result;
  const parts = Array.isArray(raw) ? raw.map(contentPart) : [contentPart(raw)];
  const kept = parts.filter((p) => p && p.text.trim() !== "");
  if (kept.length === 0) return null;
  const markdown = kept.some((p) => p.kind === "markdown" || p.language !== null);
  const text = kept.map((p) => (p.language === null ? p.text.trim()
    : "```" + p.language + "\n" + p.text.replace(/\s+$/, "") + "\n```")).join("\n\n");
  return { kind: markdown ? "markdown" : "plaintext", text };
}

// The lines the card draws from `hoverContents`'s answer (or a plain string): `{text,
// code}` per line, `{rule: true}` for a Markdown thematic break, and `{text: "…",
// ellipsis: true}` when the answer is longer than `limit`. Fence markers are dropped and
// the language tag with them; a separator line is not drawn as a line of text.
export function hoverLines(contents, limit = 24) {
  const text = typeof contents === "string" ? contents
    : (contents && typeof contents.text === "string" ? contents.text : "");
  const out = [];
  let fence = null;             // the open fence's marker ("```" or "~~~"), if any
  for (const raw of text.split(/\r\n?|\n/)) {
    const line = raw.replace(/\s+$/, "");
    const open = /^\s*(```+|~~~+)/.exec(line);
    if (open) {
      if (fence === null) { fence = open[1][0]; continue; }
      if (open[1][0] === fence) { fence = null; continue; }
    }
    if (fence === null && /^\s*(-{3,}|\*{3,}|_{3,})\s*$/.test(line)) {
      out.push({ rule: true });
      continue;
    }
    out.push({ text: line, code: fence !== null });
  }
  // A blank line is spacing, which the card gets from its own line height: outside code
  // it is not a line of its own, and the trailing/leading ones of an answer are noise.
  const lines = out.filter((line) => line.rule || line.code || line.text !== "");
  const max = typeof limit === "number" && limit > 0 ? Math.trunc(limit) : 24;
  if (lines.length > max) {
    lines.length = Math.max(0, max - 1);
    lines.push({ text: "…", ellipsis: true });
  }
  return lines;
}

// ## Definitions

function oneTarget(value) {
  if (!value || typeof value !== "object") return null;
  const uri = typeof value.uri === "string" ? value.uri
    : (typeof value.targetUri === "string" ? value.targetUri : null);
  if (uri === null || uri === "") return null;
  const range = value.range || value.targetSelectionRange || value.targetRange;
  if (!range || typeof range !== "object") return null;
  return { uri, range };
}

// A `textDocument/definition` result as `{uri, range}` or null. Accepts a `Location`,
// the `LocationLink` shape (a server with `linkSupport`), and an array of either (the
// Wiz server sends one location, or several macro rules). The first usable one wins:
// the server ordered them, and the page has only one editor to jump in.
export function definitionTarget(result) {
  if (Array.isArray(result)) {
    for (const value of result) {
      const target = oneTarget(value);
      if (target) return target;
    }
    return null;
  }
  return oneTarget(result);
}

// The last path segment of a URI, for people: `file:///lib/Prelude.wiz` → `Prelude.wiz`.
function documentName(uri) {
  let text = String(uri || "").replace(/[?#].*$/, "");
  let name = text.slice(text.lastIndexOf("/") + 1);
  try { name = decodeURIComponent(name); } catch (_) { /* keep it encoded */ }
  return name || text || "?";
}

// `file:line:col` of a target, 1-based as an editor shows it: `Prelude.wiz:7:1`.
export function locationLabel(target) {
  if (!target) return "";
  const start = (target.range && target.range.start) || {};
  const line = typeof start.line === "number" && start.line >= 0 ? start.line + 1 : 1;
  const character = typeof start.character === "number" && start.character >= 0 ? start.character + 1 : 1;
  return documentName(target.uri) + ":" + line + ":" + character;
}

// ## The card

const NAVIGATION = new Set(["ArrowUp", "ArrowDown", "ArrowLeft", "ArrowRight",
  "Home", "End", "PageUp", "PageDown"]);

// `mountHover({editor, onHover, onDefinition, onJump, document, delay, limit})`:
//
//   * `onHover(position)` returns a `textDocument/hover` result (or a promise); the
//     widget shows its contents, or stays closed for null/empty/`MethodNotFound`.
//   * `onDefinition(position)` returns a `textDocument/definition` result.
//   * `onJump(target)` is the page's jump: return true if it moved the caret (a
//     definition in the editor's own document), false to have the card show the
//     location (a library file, which this page cannot open).
//   * `document` defaults to the editor's `ownerDocument` (the tests pass a double).
//
// Returns null without an editor and a document, or without either request function.
// The returned API is `{card, inquire, schedule, close, goToDefinition, isOpen,
// content}`; `inquire` asks now (the tests' entry point), `schedule` (re)starts the
// delay, and `close` hides and forgets an in-flight answer.
export function mountHover(options = {}) {
  const editor = options.editor;
  const onHover = options.onHover;
  const onDefinition = options.onDefinition;
  const onJump = options.onJump;
  const doc = options.document || (editor && editor.ownerDocument) ||
    (typeof document !== "undefined" ? document : null);
  if (!editor || !doc || typeof doc.createElement !== "function") return null;
  if (typeof onHover !== "function" && typeof onDefinition !== "function") return null;
  const delay = typeof options.delay === "number" && options.delay >= 0 ? options.delay : 350;
  const limit = typeof options.limit === "number" && options.limit > 0 ? options.limit : 24;

  const card = doc.createElement("div");
  card.setAttribute("class", "wiz-hover");
  card.setAttribute("role", "tooltip");
  card.setAttribute("hidden", "");
  const host = doc.body || doc.documentElement || doc;
  if (typeof host.appendChild === "function") host.appendChild(card);

  let timer = null;
  let seq = 0;                 // a request generation: a stale answer is dropped
  let open = false;
  let shownAt = -1;            // the caret the card describes

  const value = () => (typeof editor.value === "string" ? editor.value : "");
  function caret() {
    const text = value();
    const at = typeof editor.selectionStart === "number" ? editor.selectionStart : 0;
    return Math.max(0, Math.min(text.length, Math.trunc(at)));
  }
  const position = () => positionAt(value(), caret());

  function cancel() {
    if (timer !== null) {
      clearTimeout(timer);
      timer = null;
    }
  }

  // Hide the card and drop an answer still in flight.
  function close() {
    cancel();
    seq++;
    card.setAttribute("hidden", "");
    card.textContent = "";
    open = false;
    shownAt = -1;
  }

  function draw(lines, label) {
    card.textContent = "";
    if (typeof label === "string" && label !== "") {
      const head = doc.createElement("div");
      head.setAttribute("class", "hover-head");
      head.textContent = label;
      card.appendChild(head);
    }
    for (const line of lines) {
      if (line.rule) {
        card.appendChild(doc.createElement("hr"));
        continue;
      }
      const element = doc.createElement("div");
      element.setAttribute("class", "hover-line" + (line.code ? " code" : "") +
        (line.ellipsis ? " more" : ""));
      element.textContent = line.text;
      card.appendChild(element);
    }
    card.removeAttribute("hidden");
    open = true;
    place();
  }

  // Put the card just under the caret. The editor is monospace, so a line's height and
  // the textarea's padding are enough; there is no horizontal measurement to get wrong.
  // Without layout (a Node test, a hidden pane) the defaults keep it on the page.
  function place() {
    if (!card.style || typeof card.style !== "object") return;
    let lineHeight = 21;
    let paddingLeft = 0;
    let paddingTop = 0;
    try {
      const style = typeof getComputedStyle === "function" ? getComputedStyle(editor) : null;
      if (style) {
        const height = parseFloat(style.lineHeight);
        if (isFinite(height) && height > 0) lineHeight = height;
        const left = parseFloat(style.paddingLeft);
        if (isFinite(left)) paddingLeft = left;
        const top = parseFloat(style.paddingTop);
        if (isFinite(top)) paddingTop = top;
      }
    } catch (_) { /* no layout: the defaults */ }
    const rect = typeof editor.getBoundingClientRect === "function"
      ? editor.getBoundingClientRect() : { left: 0, top: 0 };
    const scrollTop = typeof editor.scrollTop === "number" ? editor.scrollTop : 0;
    const at = position();
    let left = (rect.left || 0) + paddingLeft + 8;
    let top = (rect.top || 0) + paddingTop + (at.line + 1) * lineHeight - scrollTop;
    const width = typeof card.offsetWidth === "number" && card.offsetWidth > 0 ? card.offsetWidth : 320;
    const height = typeof card.offsetHeight === "number" && card.offsetHeight > 0 ? card.offsetHeight : 60;
    const viewWidth = typeof innerWidth === "number" ? innerWidth : 1024;
    const viewHeight = typeof innerHeight === "number" ? innerHeight : 768;
    if (left + width > viewWidth - 8) left = Math.max(8, viewWidth - width - 8);
    if (top + height > viewHeight - 8) {
      top = (rect.top || 0) + paddingTop + at.line * lineHeight - scrollTop - height;
      if (top < 8) top = 8;
    }
    card.style.position = "fixed";
    card.style.left = Math.round(left) + "px";
    card.style.top = Math.round(top) + "px";
    card.style.zIndex = "40";
  }

  // Ask for the hover at the caret now. Returns the contents shown, or null (nothing at
  // the character, no server, an error, or the caret moved while the answer was out).
  async function inquire() {
    cancel();
    if (typeof onHover !== "function") return null;
    const at = caret();
    const mine = ++seq;
    let result;
    try {
      result = await onHover(position());
    } catch (_) {
      result = null;             // MethodNotFound, not connected, a timeout: silence
    }
    if (mine !== seq || caret() !== at) return null;
    const contents = hoverContents(result);
    if (!contents) return null;
    draw(hoverLines(contents, limit));
    shownAt = at;
    return contents;
  }

  function schedule() {
    cancel();
    timer = setTimeout(() => { timer = null; inquire(); }, delay);
  }

  // F12 / Ctrl-⌘-click: where is the identifier at the caret declared?
  async function goToDefinition() {
    if (typeof onDefinition !== "function") return null;
    cancel();
    const mine = ++seq;
    let result;
    try {
      result = await onDefinition(position());
    } catch (_) {
      result = null;
    }
    if (mine !== seq) return null;
    const target = definitionTarget(result);
    if (!target) return null;
    let jumped = false;
    if (typeof onJump === "function") {
      try { jumped = onJump(target) === true; } catch (_) { jumped = false; }
    }
    if (jumped) {
      close();
      return target;
    }
    draw([], locationLabel(target));
    return target;
  }

  function onKeydown(event) {
    if (!event) return;
    if (event.key === "Escape") {
      if (open) {
        close();
        if (typeof event.preventDefault === "function") event.preventDefault();
      }
      return;
    }
    if (event.key === "F12") {
      if (typeof event.preventDefault === "function") event.preventDefault();
      goToDefinition();
      return;
    }
    if (NAVIGATION.has(event.key)) close();   // the card describes the old caret
  }

  function onKeyup(event) {
    if (event && NAVIGATION.has(event.key)) schedule();
  }

  function onClick(event) {
    if (event && (event.ctrlKey === true || event.metaKey === true)) {
      if (typeof event.preventDefault === "function") event.preventDefault();
      goToDefinition();
      return;
    }
    schedule();               // the browser has moved the caret by the click
  }

  if (typeof editor.addEventListener === "function") {
    editor.addEventListener("keydown", onKeydown);
    editor.addEventListener("keyup", onKeyup);
    editor.addEventListener("click", onClick);
    editor.addEventListener("select", schedule);
    editor.addEventListener("input", close);
    editor.addEventListener("scroll", close);
    editor.addEventListener("blur", close);
  }

  return {
    card,
    inquire,
    schedule,
    close,
    goToDefinition,
    isOpen: () => open,
    content: () => card.textContent,
    describedAt: () => shownAt,
    destroy() {
      close();
      if (card.parentNode) card.parentNode.removeChild(card);
    },
  };
}
