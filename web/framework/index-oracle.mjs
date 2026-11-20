// The Node test oracle for `lib/Web/EditorModel.wiz`'s `PositionIndex` and the
// selfhost shim's index adapter. It is the implementation the shim used to carry (the
// UTF-16 positions, the innermost-entry lookup, `termGoal`/`goal`/declarations); the
// production shim receives the Wiz one through `createIndexer` (`web/playground-lsp.js`),
// and this file is only imported by tests. Keep the values in step with the Wiz tests
// (`Tests/Groups/Loom.lean`); the shim's behaviour is pinned against the same fixtures.
"use strict";
import { withPrelude } from "../selfhost-lsp-shim.js";

export function positionOf(text, offset) {
  const end = Math.max(0, Math.min(offset, text.length));
  let line = 0;
  let lineStart = 0;
  for (let i = 0; i < end; i++) {
    if (text.charCodeAt(i) === 10) { line++; lineStart = i + 1; }
  }
  return { line, character: end - lineStart };
}

// A code-point offset (what the self-hosted frontend counts: `String.codes`) as a UTF-16
// offset into the same text.
export function utf16OfCodePoints(text, codePoints) {
  let i = 0;
  for (let n = 0; n < codePoints && i < text.length; n++) {
    const c = text.charCodeAt(i);
    i += c >= 0xd800 && c <= 0xdbff && i + 1 < text.length ? 2 : 1;
  }
  return i;
}

export function lineEnd(text, offset) {
  const nl = text.indexOf("\n", offset);
  return nl < 0 ? text.length : nl;
}

export function range(text, from, to) {
  return { start: positionOf(text, from), end: positionOf(text, to) };
}

export function editorOffset(text, prefix, codePoints) {
  return Math.max(0, Math.min(text.length, utf16OfCodePoints(prefix + text, codePoints) - prefix.length));
}

// A position (`{line, character}`, UTF-16) as an offset into `text`.
export function offsetOf(text, position) {
  let offset = 0;
  for (let line = 0; line < position.line; line++) {
    const nl = text.indexOf("\n", offset);
    if (nl < 0) return text.length;
    offset = nl + 1;
  }
  return Math.min(text.length, lineEnd(text, offset), offset + position.character);
}

// `tacGoalsShow`'s text as the goals it lists: one per blank-line-separated block,
// `"no goals"` (a finished proof) and an empty text as none.
export function splitGoals(text) {
  const s = String(text === null || text === undefined ? "" : text).trim();
  if (s === "" || s === "no goals") return [];
  return s.split(/\n\s*\n/).map((g) => g.trim()).filter((g) => g !== "");
}

// Positions → what the pane asks for, from a check answer's `index`. An entry is
// `{s, e, kind: "term"|"goal", expected?: string, goals?: [string]}`, `s`/`e` code-point
// offsets into the checked source (end-exclusive). A lookup is the innermost entry of
// that kind containing the caret (a caret at an entry's end counts); ties go to the
// later entry.
export class PositionIndex {
  constructor(text, entries) {
    const { prefix } = withPrelude(text);
    this.text = text;
    this.entries = (Array.isArray(entries) ? entries : [])
      .filter((x) => x && typeof x.s === "number" && typeof x.e === "number" && x.e >= x.s)
      .map((x) => Object.assign({}, x, {
        start: editorOffset(text, prefix, x.s),
        end: editorOffset(text, prefix, x.e),
      }));
  }

  get size() { return this.entries.length; }

  lookup(offset, kind) {
    let best = null;
    for (const x of this.entries) {
      if (x.kind !== kind || offset < x.start || offset > x.end) continue;
      if (best === null || x.end - x.start <= best.end - best.start) best = x;
    }
    return best;
  }

  rangeOf(entry) { return range(this.text, entry.start, entry.end); }

  // `wiz/plainTermGoal`: `{goal, range}` or null
  termGoal(offset) {
    const x = this.lookup(offset, "term");
    return x && typeof x.expected === "string" ? { goal: x.expected, range: this.rangeOf(x) } : null;
  }

  // The declarations the checked module added, in source order: `{label, kind, detail,
  // range}` (kind is an LSP `CompletionItemKind`).
  declarations() {
    return this.entries
      .filter((x) => x.kind === "decl" && typeof x.name === "string" && x.name !== "")
      .map((x) => ({
        label: x.name,
        kind: typeof x.ckind === "number" ? x.ckind : 6,
        detail: typeof x.detail === "string" ? x.detail : "",
        range: this.rangeOf(x),
      }));
  }

  // The declaration a source name denotes: an exact label, else a unique suffix match
  // (`mk` for `T.mk`, as a constructor is used after a dot).
  declarationNamed(name) {
    const n = String(name === undefined || name === null ? "" : name);
    if (n === "") return null;
    const all = this.declarations();
    const exact = all.find((d) => d.label === n);
    if (exact) return exact;
    const suffix = all.filter((d) => d.label.endsWith("." + n));
    return suffix.length === 1 ? suffix[0] : null;
  }

  // `wiz/plainGoal`: `{goals, rendered}` or null (`goals: []` is a finished proof)
  goal(offset) {
    const x = this.lookup(offset, "goal");
    if (!x || !Array.isArray(x.goals)) return null;
    const goals = [];
    for (const g of x.goals) {
      for (const one of splitGoals(g)) goals.push(one);
    }
    const rendered = goals.length ? "```wiz\n" + goals.join("\n\n") + "\n```" : "no goals";
    return { goals, rendered, range: this.rangeOf(x) };
  }
}

// The adapter the shim takes as `index` (web/selfhost-lsp-shim.js): positions and the
// check's entry index. Tests pass this; the page passes `createIndexer`.
export const index = {
  position: positionOf,
  offset: offsetOf,
  lineEnd,
  range,
  utf16: utf16OfCodePoints,
  editorOffset,
  build: (text, entries) => new PositionIndex(text, entries),
  size: (ix) => ix.size,
  term: (_text, ix, offset) => ix.termGoal(offset),
  goal: (_text, ix, offset) => ix.goal(offset),
  declarations: (_text, ix) => ix.declarations(),
  declarationNamed: (_text, ix, name) => ix.declarationNamed(name),
};
