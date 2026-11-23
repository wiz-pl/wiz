// The Node test oracle for `lib/Web/EditorModel.wiz`'s `PositionIndex`,
// `lib/Web/Selfhost.wiz`'s command/diagnostic/completion rules, and the selfhost shim's
// index adapter. It is the implementation the shim used to carry (the UTF-16 positions,
// the innermost-entry lookup, `termGoal`/`goal`/declarations, the command splitter and
// the engine lines as diagnostics); the production shim receives the Wiz ones through
// `createIndexer` (`web/playground-lsp.js`), and this file is only imported by tests.
// Keep the values in step with the Wiz tests (`Tests/Groups/Loom.lean`); the shim's
// behaviour is pinned against the same fixtures.
"use strict";

// The page's rule (web/playground.js): a source without an `import` gets the embedded
// Prelude. `prefix` is what was added, so offsets can be moved back into the editor.
export function withPrelude(text) {
  if (/^\s*import\b/m.test(text)) return { source: text, prefix: "" };
  const prefix = "import Prelude\n\n";
  return { source: prefix + text, prefix };
}

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

// ## The selfhost shim's pure rules (the oracle for `Web.Selfhost.wiz`)

const SILENT = /^(import|syntax|notation|infixl|infixr|infix|prefix|postfix|macro_rules|macro|declare_syntax_cat|deriving\s+instance)\b/;
const CONTINUES = /^(\||where\b|deriving\b|with\b|\)|\]|\}|,|:=)/;
const RESULT = /^#(check|eval|reduce|print)\b/;

function blockDepth(line, depth) {
  for (let i = 0; i + 1 < line.length; i++) {
    if (line[i] === "/" && line[i + 1] === "-") { depth++; i++; }
    else if (line[i] === "-" && line[i + 1] === "/") { depth = Math.max(0, depth - 1); i++; }
  }
  return depth;
}

// The top-level commands of `text`: a command starts at column 0 (after any doc comment
// or attribute lines, which belong to it), and runs to the next one. Comments, blank
// lines and the body of a `mutual … end` block do not start a command.
export function splitCommands(text) {
  const commands = [];
  const lines = text.split("\n");
  let offset = 0;
  let inBlock = 0;
  let inMutual = false;
  let pending = null;
  for (const line of lines) {
    const here = offset;
    offset += line.length + 1;
    if (inBlock > 0) { inBlock = blockDepth(line, inBlock); continue; }
    if (line.trim() === "" || /^\s*--/.test(line)) continue;
    if (/^\s/.test(line)) continue;
    if (line.startsWith("/-")) {
      const depth = blockDepth(line, 0);
      if (line.startsWith("/--") && pending === null) pending = here;
      inBlock = depth;
      continue;
    }
    if (inMutual) { if (/^end\b/.test(line)) inMutual = false; continue; }
    if (CONTINUES.test(line)) continue;
    if (line.startsWith("@[") && !/\]\s*\S/.test(line)) {
      if (pending === null) pending = here;
      continue;
    }
    const keyword = line.replace(/^@\[[^\]]*\]\s*/, "")
      .replace(/^((private|protected|noncomputable|partial|unsafe)\s+)*/, "");
    const command = {
      start: pending === null ? here : pending,
      head: here,
      end: text.length,
      keyword: (keyword.match(/^\S+/) || [""])[0],
      silent: SILENT.test(keyword),
      result: RESULT.test(keyword),
    };
    pending = null;
    if (commands.length) commands[commands.length - 1].end = command.start;
    commands.push(command);
    if (/^mutual\b/.test(keyword)) inMutual = true;
  }
  return commands;
}

export function outputLines(output) {
  const lines = String(output || "").split("\n");
  if (lines.length && lines[lines.length - 1] === "") lines.pop();
  return lines;
}

export function parseErrorOffset(line) {
  const m = /^parse error (\d+):/.exec(line);
  return m ? Number(m[1]) : null;
}

function severityOf(line) {
  if (line.startsWith("error:") || line.startsWith("parse error")) return 1;
  if (line.startsWith("warning:")) return 2;
  return 3;
}

function messageOf(line) {
  if (line.startsWith("error: ")) return line.slice(7);
  if (line.startsWith("warning: ")) return line.slice(9);
  const m = /^parse error (\d+): ?(.*)$/.exec(line);
  if (m) return "parse error: " + m[2];
  return line;
}

function tokenStop(text, at) {
  let to = at;
  while (to < text.length && !/\s/.test(text[to])) to++;
  return to;
}

export function diagnosticsFromOutput(text, output) {
  const { prefix } = withPrelude(text);
  const lines = outputLines(output);
  const commands = splitCommands(text).filter((c) => !c.silent);
  const last = lines.length ? lines[lines.length - 1] : null;
  const parseAt = last === null ? null : parseErrorOffset(last);
  const placed = parseAt === null ? lines.length : lines.length - 1;
  const aligned = parseAt === null ? placed === commands.length : placed <= commands.length;
  const diagnostics = [];
  for (let i = 0; i < placed; i++) {
    const line = lines[i];
    const severity = severityOf(line);
    const command = aligned ? commands[i] : null;
    if (severity === 3 && !(command && command.result)) continue;
    if (severity === 3 && line === "") continue;
    const diagnostic = { severity, source: "wiz-selfhost", message: messageOf(line) };
    if (command) {
      diagnostic.range = range(text, command.head, lineEnd(text, command.head));
    } else {
      diagnostic.range = range(text, 0, 0);
      diagnostic.message += " (position unknown: the output did not line up with the commands)";
    }
    diagnostics.push(diagnostic);
  }
  if (parseAt !== null) {
    const at = editorOffset(text, prefix, parseAt);
    const to = tokenStop(text, at);
    diagnostics.push({
      severity: 1, source: "wiz-selfhost", code: "parse-error",
      message: messageOf(last), range: range(text, at, Math.max(to, Math.min(at + 1, text.length))),
    });
  }
  return diagnostics;
}

export function parseCheck(json) {
  if (json === null || json === undefined) return null;
  let answer;
  try { answer = typeof json === "string" ? JSON.parse(json) : json; } catch (_) { return null; }
  if (!answer || !Array.isArray(answer.lines)) return null;
  return answer;
}

export function diagnosticsFromCheck(text, answer) {
  const { prefix } = withPrelude(text);
  const diagnostics = [];
  for (const line of answer.lines) {
    const raw = String(line.text === undefined ? "" : line.text);
    const severity = line.sev === 1 || line.sev === 2 ? line.sev : severityOf(raw);
    const parseAt = parseErrorOffset(raw);
    if (parseAt !== null) {
      const at = editorOffset(text, prefix, parseAt);
      const to = tokenStop(text, at);
      diagnostics.push({
        severity: 1, source: "wiz-selfhost", code: "parse-error",
        message: messageOf(raw), range: range(text, at, Math.max(to, Math.min(at + 1, text.length))),
      });
      continue;
    }
    const known = typeof line.off === "number";
    const at = known ? editorOffset(text, prefix, line.off) : 0;
    if (severity === 3 && (raw === "" || !known || !RESULT.test(text.slice(at)))) continue;
    const diagnostic = { severity, source: "wiz-selfhost", message: messageOf(raw) };
    diagnostic.range = known ? range(text, at, lineEnd(text, at)) : range(text, 0, 0);
    if (!known) diagnostic.message += " (position unknown)";
    diagnostics.push(diagnostic);
  }
  return diagnostics;
}

export function completionPrefix(text, offset) {
  const at = Math.max(0, Math.min(offset, String(text || "").length));
  let start = at;
  while (start > 0) {
    const c = text[start - 1];
    if (!/[A-Za-z0-9_'.]/.test(c)) break;
    start--;
  }
  return { start, prefix: text.slice(start, at) };
}

export function wordAt(text, offset) {
  const s = String(text === undefined || text === null ? "" : text);
  const at = Math.max(0, Math.min(offset, s.length));
  let start = at;
  let end = at;
  while (start > 0 && /[A-Za-z0-9_'.]/.test(s[start - 1])) start--;
  while (end < s.length && /[A-Za-z0-9_'.]/.test(s[end])) end++;
  return { start, end, word: s.slice(start, end) };
}

export function filterCompletions(names, prefix, limit = 200) {
  const want = String(prefix || "").toLowerCase();
  const items = [];
  for (const name of Array.isArray(names) ? names : []) {
    if (!name || typeof name.label !== "string") continue;
    if (want !== "" && !name.label.toLowerCase().startsWith(want)) continue;
    items.push(Object.assign({ label: name.label, kind: name.kind }, name.detail ? { detail: name.detail } : {}));
    if (items.length >= limit) break;
  }
  return items;
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

// The adapter the shim takes as `index` (web/selfhost-lsp-shim.js): positions, the
// check's entry index, and the pure request/response rules `Web.Selfhost.wiz` owns.
// Tests pass this; the page passes `createIndexer`.
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
  initializeCapabilities: () => ({
    positionEncoding: "utf-16",
    textDocumentSync: 1,
    hoverProvider: true,
    definitionProvider: true,
    completionProvider: { triggerCharacters: ["."], resolveProvider: false },
    experimental: { wizInfoview: { version: 1, methods: ["wiz/plainGoal", "wiz/plainTermGoal"] } },
  }),
  withPrelude,
  splitCommands,
  outputLines,
  parseErrorOffset,
  diagnosticsFromOutput: (text, output) => diagnosticsFromOutput(text, output),
  parseCheck,
  diagnosticsFromCheck,
  completionPrefix,
  wordAt,
  filterCompletions,
  // `textDocument/completion`: the declaration index's items with a `textEdit` over the
  // identifier prefix at the caret.
  completion: (text, ix, position) => {
    const offset = offsetOf(text, position || { line: 0, character: 0 });
    const { start, prefix } = completionPrefix(text, offset);
    const decls = ix ? ix.declarations() : [];
    const items = filterCompletions(decls, prefix).map((item) =>
      Object.assign({}, item, { textEdit: { range: range(text, start, offset), newText: item.label } }));
    return { isIncomplete: false, items };
  },
  // `textDocument/hover`: Markdown with the declaration's signature.
  hover: (text, ix, position) => {
    const offset = offsetOf(text, position || { line: 0, character: 0 });
    const found = wordAt(text, offset);
    const decl = !ix || found.word === "" ? null : ix.declarationNamed(found.word);
    if (!decl) return null;
    const signature = decl.detail === "" ? decl.label : decl.label + " : " + decl.detail;
    return { contents: { kind: "markdown", value: "```wiz\n" + signature + "\n```" }, range: decl.range };
  },
  // `textDocument/definition`: a `Location` in this document.
  definition: (text, ix, position, uri) => {
    const offset = offsetOf(text, position || { line: 0, character: 0 });
    const found = wordAt(text, offset);
    const decl = !ix || found.word === "" ? null : ix.declarationNamed(found.word);
    return decl ? { uri, range: decl.range } : null;
  },
};
