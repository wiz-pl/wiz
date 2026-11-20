// Hover contents and location rules (test oracle): the pure half of the hover card.
// The card itself is a Loom view in lib/Web/Hover.wiz; this file is what the Node test
// compares the runtime against.
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

