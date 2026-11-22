// The playground editor's model, **kept as the test oracle**: the pure functions the
// page used to import. The runtime now owns these rules (`lib/Web/EditorModel.wiz`,
// reached through `wiz_loom_editor_*`); this module is not served and nothing in
// production imports it. The Node tests use it for the DOM widgets (`web/editor_dom_test.mjs`,
// `web/loom_overlay_test.mjs`) and as the reference the Wiz cases are compared with.
//
//   * **Positions.** LSP counts UTF-16 code units (docs/playground-lsp.md, "Position
//     encoding"), and a JavaScript string index is one, so the page sends the textarea's
//     `selectionStart` unchanged. The code-point helpers exist for the other convention
//     (the self-hosted frontend's `String.codes` counts Unicode scalar values) and to
//     pin in a test that the two differ only for characters outside the BMP.
//   * **Squiggles.** A diagnostic's `range` as the text offsets to underline, with the
//     repairs a real server's ranges need: a missing end, an empty range, a range that
//     runs past the text, a multi-line range, and two ranges that overlap.
//   * **Completions.** The `textDocument/completion` result (an array or a
//     `CompletionList`), the identifier prefix of the caret, filtering and ordering, the
//     keyboard's command table and index arithmetic, and the text an accepted item
//     inserts.
//
// The offset arithmetic is here, not in a second module: `web/goals.js` is the test
// oracle for the runtime's `lib/Web/Goals.wiz` now.
"use strict";

import { definitionTarget, locationLabel } from "./hover.mjs";

const clampNat = (n, lo, hi) => (n < lo ? lo : n > hi ? hi : n);
const num = (x) => (typeof x === "number" && isFinite(x) ? Math.trunc(x) : 0);

function positionOfOffset(text, offset) {
  const at = Math.max(0, Math.min(text ? text.length : 0, num(offset)));
  const before = text ? text.slice(0, at) : "";
  const line = (before.match(/\n/g) || []).length;
  return { line, character: at - (before.lastIndexOf("\n") + 1) };
}

function offsetOfPosition(text, position) {
  if (!text || !position) return 0;
  const line = Math.max(0, num(position.line));
  const character = Math.max(0, num(position.character));
  let offset = 0;
  for (let l = 0; l < line; l++) {
    const newline = text.indexOf("\n", offset);
    if (newline < 0) return text.length;
    offset = newline + 1;
  }
  const newline = text.indexOf("\n", offset);
  const lineEnd = newline < 0 ? text.length : newline;
  return Math.min(lineEnd, offset + character);
}

// ## Positions

// A LSP position for a JavaScript string index (`null`/`undefined` → 0).
export const positionFromOffset = (text, offset) => positionOfOffset(text || "", offset);

// The JavaScript string index of a LSP position, clamped to the text.
export const offsetFromPosition = (text, position) => offsetOfPosition(text || "", position || {});

// The caret: `selectionStart`, which is a UTF-16 index. A textarea with a selection has
// the caret at its start; the goals are asked about the start of the selection, as the
// infoview does. A stub editor without `selectionStart` counts as 0.
export function caretOffset(editor) {
  const value = (editor && typeof editor.value === "string") ? editor.value : "";
  const at = editor && typeof editor.selectionStart === "number" ? editor.selectionStart : 0;
  return clampNat(num(at), 0, value.length);
}

// The caret as `{line, character}` (UTF-16), the position params every `wiz/*` request
// takes.
export function caretPosition(editor) {
  const value = (editor && typeof editor.value === "string") ? editor.value : "";
  return positionFromOffset(value, caretOffset(editor));
}

// The same position counted in Unicode scalar values (code points), for a server that
// counts code points instead of UTF-16 units. `character` is then an index into
// `Array.from(line)`.
export function codePointPositionFromOffset(text, offset) {
  const value = text || "";
  const at = clampNat(num(offset), 0, value.length);
  const before = value.slice(0, at);
  const line = (before.match(/\n/g) || []).length;
  const lineStart = before.lastIndexOf("\n") + 1;
  return { line, character: Array.from(before.slice(lineStart)).length };
}

// A UTF-16 index for a code-point index into `text`, and the inverse. Astral characters
// (outside the BMP) are two UTF-16 units and one code point; everything in the BMP is
// one of each.
export function utf16OffsetFromCodePoints(text, codePoints) {
  const value = text || "";
  let i = 0;
  for (let n = 0; n < codePoints && i < value.length; n++) {
    const c = value.charCodeAt(i);
    i += c >= 0xd800 && c <= 0xdbff && i + 1 < value.length ? 2 : 1;
  }
  return i;
}

export function codePointOffsetFromUtf16(text, offset) {
  const value = text || "";
  const at = clampNat(num(offset), 0, value.length);
  let n = 0;
  for (let i = 0; i < at; ) {
    const c = value.charCodeAt(i);
    i += c >= 0xd800 && c <= 0xdbff && i + 1 < value.length ? 2 : 1;
    n++;
  }
  return n;
}

// ## Squiggles (a diagnostic's range, as something an editor can underline)

export const SEVERITY_NAME = { 1: "error", 2: "warning", 3: "info", 4: "hint" };

// LSP's default when a server omits `severity`; the goals panel makes the same choice.
export function severityOf(diagnostic) {
  const s = diagnostic && typeof diagnostic.severity === "number" ? Math.trunc(diagnostic.severity) : 0;
  return s >= 1 && s <= 4 ? s : 3;
}

const isSpace = (c) => c === " " || c === "\t" || c === "\n" || c === "\r" || c === "\f" || c === "\v";

// The offset just past the token at `offset`: to the next whitespace, or to the end of
// the text; at least one character, so a diagnostic with no end still underlines
// something. On whitespace or past the end it is one character (or the text's end).
export function tokenEnd(text, offset) {
  const value = text || "";
  const at = clampNat(num(offset), 0, value.length);
  if (at >= value.length) return value.length;
  if (isSpace(value[at])) return at + 1;
  let to = at;
  while (to < value.length && !isSpace(value[to])) to++;
  return to;
}

// `[start, end)` cut at line breaks, so no segment contains a `\n`: a multi-line
// diagnostic underlines the rest of each line, not the newline.
export function splitAtLines(text, start, end) {
  const value = text || "";
  const from = clampNat(num(start), 0, value.length);
  const to = clampNat(num(end), from, value.length);
  const out = [];
  let at = from;
  while (at < to) {
    const nl = value.indexOf("\n", at);
    const pieceEnd = nl < 0 || nl > to ? to : nl;
    if (pieceEnd > at) out.push({ start: at, end: pieceEnd });
    if (nl < 0 || nl >= to) break;
    at = nl + 1;
  }
  return out;
}

// Two segments that overlap (or touch) become one: the stricter severity, and both
// messages when they differ. Editors draw one underline, not two on top of each other.
export function mergeSegments(segments) {
  const list = (Array.isArray(segments) ? segments : [])
    .filter((s) => s && s.end > s.start)
    .sort((a, b) => a.start - b.start || a.end - b.end || a.severity - b.severity);
  const out = [];
  for (const seg of list) {
    const last = out[out.length - 1];
    if (last && seg.start < last.end) {
      last.end = Math.max(last.end, seg.end);
      if (seg.severity < last.severity) {
        last.severity = seg.severity;
        last.message = joinMessages(seg.message, last.message);
      } else {
        last.message = joinMessages(last.message, seg.message);
      }
      continue;
    }
    out.push({ start: seg.start, end: seg.end, severity: seg.severity, message: seg.message });
  }
  return out;
}

function joinMessages(a, b) {
  const left = a === undefined || a === null ? "" : String(a);
  const right = b === undefined || b === null ? "" : String(b);
  if (left === "") return right;
  if (right === "" || right === left) return left;
  return left + " · " + right;
}

// The spans to underline for `diagnostics`, in text offsets and in `{line, character}`
// (UTF-16), clamped to `text` and non-overlapping. A diagnostic with no `range.start` is
// dropped (there is nowhere to put it); one with no end, an empty end, or an end before
// its start underlines the token at its start (`tokenEnd`).
export function squiggleSegments(text, diagnostics, options = {}) {
  const value = text || "";
  const list = Array.isArray(diagnostics) ? diagnostics : [];
  const out = [];
  for (const d of list) {
    if (!d || !d.range || !d.range.start) continue;
    const start = offsetFromPosition(value, d.range.start);
    const hasEnd = !!(d.range.end && typeof d.range.end.line === "number");
    let end = hasEnd ? offsetFromPosition(value, d.range.end) : tokenEnd(value, start);
    if (!(end > start)) end = tokenEnd(value, start);
    if (!(end > start)) continue;                       // the caret is past the last char
    const severity = severityOf(d);
    const message = d.message === undefined || d.message === null ? "" : String(d.message);
    for (const piece of splitAtLines(value, start, end)) {
      out.push({ start: piece.start, end: piece.end, severity, message });
    }
  }
  const merged = mergeSegments(out);
  const limit = options.maxSegments === undefined ? Infinity : options.maxSegments;
  // `line`/`character` describe where each merged span starts and ends (the merge can
  // widen a span across a line, so they are recomputed rather than carried over).
  return merged.slice(0, limit).map((s) => Object.assign({}, s, {
    line: positionFromOffset(value, s.start).line,
    startCharacter: positionFromOffset(value, s.start).character,
    endCharacter: positionFromOffset(value, s.end).character,
  }));
}

// ## Completions

// Characters that continue a Wiz identifier (or a qualified name: `Nat.add`). A quote is
// part of an identifier, a dot joins a namespace to a name.
const IDENT = /[A-Za-z0-9_'.]/;

export function isIdentifierChar(c) { return typeof c === "string" && c.length > 0 && IDENT.test(c); }

// The identifier being typed before `offset`: `{start, word}`. `word` is everything from
// the last non-identifier character to the caret, so a server can filter by it.
export function identifierPrefix(text, offset) {
  const value = text || "";
  const at = clampNat(num(offset), 0, value.length);
  let start = at;
  while (start > 0 && IDENT.test(value[start - 1])) start--;
  return { start, word: value.slice(start, at) };
}

// `--` starts a line comment in Wiz; a completion popup in one is noise. (A `--` inside a
// string literal is not detected: this is a heuristic, not a lexer.)
export function inLineComment(text, offset) {
  const value = text || "";
  const at = clampNat(num(offset), 0, value.length);
  const lineStart = value.lastIndexOf("\n", at - 1) + 1;
  return value.slice(lineStart, at).includes("--");
}

// Whether typing `c` at `offset` should ask for completions: an identifier character,
// outside a line comment.
export function completionTrigger(text, offset, c) {
  if (!isIdentifierChar(c)) return false;
  return !inLineComment(text, offset);
}

// The items of a `textDocument/completion` result: an array, a `CompletionList`
// (`{items}`), a single item object, or null. Items without a string `label` are dropped
// (there is nothing to show); the rest are copied, so the caller's objects stay as they
// came from the client.
export function completionItems(result) {
  if (result === null || result === undefined) return [];
  const raw = Array.isArray(result) ? result
    : (Array.isArray(result.items) ? result.items : (typeof result.label === "string" ? [result] : []));
  const out = [];
  for (const item of raw) {
    if (!item || typeof item.label !== "string" || item.label === "") continue;
    out.push(Object.assign({}, item));
  }
  return out;
}

// How well `item` matches the typed prefix: lower is better, -1 is no match. An exact
// prefix wins; then the last segment of a qualified name (`ad` matching `Nat.add`, and
// `Nat.a` matching `Nat.add`); then a substring. Case-insensitive, as most servers and
// editors are.
export function completionScore(item, prefix) {
  const p = String(prefix || "").toLowerCase();
  if (p === "") return 0;
  const label = String((item && (item.filterText || item.label)) || "");
  const h = label.toLowerCase();
  if (h.startsWith(p)) return 0;
  const pTail = p.slice(p.lastIndexOf(".") + 1);
  const hTail = h.slice(h.lastIndexOf(".") + 1);
  if (pTail !== "" && hTail.startsWith(pTail)) return 1;
  if (h.includes(p)) return 2;
  return -1;
}

// The matching items, best first. `sortText` (LSP) orders equal scores; the label breaks
// the remaining ties, so the list is deterministic.
export function filterCompletions(items, prefix, options = {}) {
  const scored = [];
  for (const item of Array.isArray(items) ? items : []) {
    const score = completionScore(item, prefix);
    if (score < 0) continue;
    scored.push({ item, score });
  }
  scored.sort((a, b) => a.score - b.score ||
    String(a.item.sortText || a.item.label).localeCompare(String(b.item.sortText || b.item.label)) ||
    String(a.item.label).localeCompare(String(b.item.label)));
  const limit = options.limit === undefined ? Infinity : options.limit;
  return scored.slice(0, limit).map((s) => s.item);
}

// The selected index after moving `delta` in a list of `count` items, wrapping at both
// ends (Up from the first is the last, as in a menu).
export function moveSelection(index, delta, count) {
  const n = Math.max(0, Math.trunc(num(count)));
  if (n === 0) return -1;
  const from = index < 0 ? (delta > 0 ? -1 : 0) : clampNat(Math.trunc(num(index)), 0, n - 1);
  return ((from + Math.trunc(num(delta))) % n + n) % n;
}

// A snippet's text without its placeholders: `${1:name}` → `name`, `${0}`/`$1` → "",
// `\$` → `$`. The playground asks for `snippetSupport: false`, so this is only a safety
// net for a server that sends one anyway.
export function stripSnippet(text) {
  return String(text === undefined || text === null ? "" : text)
    .replace(/\$\{\d+:([^}]*)\}/g, "$1")
    .replace(/\$\{\d+\}/g, "")
    .replace(/\$\d+/g, "")
    .replace(/\\\$/g, "$");
}

// What an accepted item inserts and where: `{text, start, end, caret, insert}`. A
// `textEdit` is authoritative (its range replaces the prefix, or more, as the server
// says) *when its end is the caret*: an answer requested for an older caret can arrive
// after more typing, and applying its range to the newer text would duplicate the typed
// suffix (`Nat.add` over `N`, then `at` → `Nat.addat`). A range that does not end at the
// current caret is re-anchored on the identifier prefix at the caret. Otherwise
// `insertText` — or the label — replaces that prefix.
export function acceptCompletion(item, text, offset) {
  const value = text || "";
  const at = clampNat(num(offset), 0, value.length);
  const prefix = identifierPrefix(value, at);
  let start = prefix.start;
  let end = at;
  let insert;
  const edit = item && item.textEdit;
  const anchored = (from, to) => to === at && from <= at;
  if (edit && edit.range) {
    const from = offsetFromPosition(value, edit.range.start || {});
    const to = edit.range.end ? offsetFromPosition(value, edit.range.end) : at;
    insert = edit.newText !== undefined ? String(edit.newText) : String(edit.insertText || item.label || "");
    if (anchored(from, to)) { start = from; end = to; }
  } else if (edit && (edit.insert || edit.replace)) {
    // InsertReplaceEdit: the narrower range is the one an accept replaces.
    const range = edit.replace || edit.insert;
    const from = offsetFromPosition(value, range.start || {});
    const to = range.end ? offsetFromPosition(value, range.end) : at;
    insert = String(edit.newText || item.label || "");
    if (anchored(from, to)) { start = from; end = to; }
  } else {
    insert = item && item.insertText !== undefined ? String(item.insertText) : String(item && item.label || "");
    if (item && item.insertTextFormat === 2) insert = stripSnippet(insert);
  }
  if (end < start) end = start;
  const next = value.slice(0, start) + insert + value.slice(end);
  return { text: next, start, end, caret: start + insert.length, insert };
}

// How many items the popup draws: enough to browse, bounded so a server cannot make the
// page janky with 10,000 suggestions.
export const COMPLETION_LIMIT = 100;

// The popup's whole state transition, as a function: the text, the caret and a list of
// items in, the visible items and the selected index out. `index` is clamped; `prefix`
// is the word the items were filtered by.
export function completionPopupState(text, offset, items, index = 0) {
  const prefix = identifierPrefix(text, offset);
  const filtered = filterCompletions(items, prefix.word, { limit: COMPLETION_LIMIT });
  const selected = filtered.length === 0 ? -1 : moveSelection(index, 0, filtered.length);
  return { items: filtered, index: selected, prefix };
}

// How many rows a page key moves: enough to browse, small enough that a PageDown is not
// the whole list.
export const COMPLETION_PAGE = 10;

// The popup's response to a keydown, as the runtime computes it: a move carries the
// selected index after `moveSelection`; Enter/Tab accept, Escape closes, everything else
// is ignored. `index` and `count` are the popup's current state. The host has no key
// table of its own.
export function completionKey(key, index, count) {
  const delta = key === "ArrowDown" ? 1
    : key === "ArrowUp" ? -1
      : key === "PageDown" ? COMPLETION_PAGE
        : key === "PageUp" ? -COMPLETION_PAGE : 0;
  if (delta !== 0) return { action: "move", index: moveSelection(index, delta, count) };
  if (key === "Enter" || key === "Tab") return { action: "accept" };
  if (key === "Escape") return { action: "close" };
  return { action: "ignore" };
}

// The same surface the page gets from the runtime (`wiz_loom_editor_*`, see
// `web/framework/mount.js`'s `ask`). The DOM tests pass this so they still exercise the
// widgets with the real rules; production passes the runtime's.
export const rules = {
  segments: (text, diagnostics) => squiggleSegments(text, diagnostics).map((s) => ({
    start: s.start, stop: s.end, severity: s.severity,
    severityName: SEVERITY_NAME[s.severity] || "info", message: s.message,
    line: s.line, startCharacter: s.startCharacter, endCharacter: s.endCharacter,
  })),
  items: (result) => completionItems(result),
  popup(text, offset, items, index) {
    const state = completionPopupState(text, offset, items, index);
    return {
      items: state.items,
      index: state.index,
      prefixStart: state.prefix.start,
      prefixWord: state.prefix.word,
    };
  },
  move: (index, delta, count) => moveSelection(index, delta, count),
  key: (key, index, count) => completionKey(key, index, count),
  accept: (item, text, offset) => {
    const a = acceptCompletion(item, text, offset);
    return { text: a.text, start: a.start, stop: a.end, caret: a.caret, insert: a.insert };
  },
  trigger: (text, offset, c) => completionTrigger(text, offset, c),
  position: (text, offset) => positionFromOffset(text, offset),
  // A `textDocument/definition` answer's target, range and label (`Web.Hover`); the
  // production page gets this from `wiz_loom_hover_target`.
  target(result) {
    const t = definitionTarget(result);
    return t ? { uri: t.uri, range: t.range, label: locationLabel(t) } : null;
  },
  // The popup's tooltip and ask key, and the goals pane's source spans (the runtime's
  // `Web.EditorModel` rules; these are the test oracle's).
  itemTitle(item) {
    const docs = item && item.documentation;
    if (typeof docs === "string") return docs;
    if (docs && typeof docs.value === "string") return docs.value;
    return item && item.detail !== undefined && item.detail !== null ? String(item.detail) : "";
  },
  askKey: (key, code, ctrl, meta) =>
    (key === " " || key === "Spacebar" || code === "Space") && (!!ctrl || !!meta),
  span(text, span) {
    const m = /^(\d+):(\d+)-(\d+):(\d+)$/.exec(String(span || ""));
    if (!m) return null;
    const start = offsetFromPosition(text, { line: Number(m[1]), character: Number(m[2]) });
    const end = offsetFromPosition(text, { line: Number(m[3]), character: Number(m[4]) });
    return [start, Math.max(start, end)];
  },
  rangeText(range) {
    if (!range || typeof range !== "object") return "";
    const start = range.start || {};
    const stop = range.end || start;
    return `${start.line || 0}:${start.character || 0}-${stop.line || 0}:${stop.character || 0}`;
  },
};
