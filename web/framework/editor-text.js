// The editor's text-input primitives: the parts of a text field that are the browser's,
// kept in one named place. The *rules* (positions, diagnostics, completions) are
// `lib/Web/EditorModel.wiz`; this file only reads what the control holds.
//
// A textarea's `selectionStart` is a UTF-16 index, which is also a JavaScript string
// index and the LSP's unit. A selection's caret is its start.
"use strict";

// The caret: `selectionStart`, clamped to the value. A stub editor without one counts
// as 0.
export function caretOffset(editor) {
  const value = editor && typeof editor.value === "string" ? editor.value : "";
  const at = editor && typeof editor.selectionStart === "number" ? editor.selectionStart : 0;
  return Math.max(0, Math.min(value.length, Number.isFinite(at) ? Math.trunc(at) : 0));
}

// The selection, in UTF-16 offsets (`end` is never before `start`).
export function selectionOffsets(editor) {
  const value = editor && typeof editor.value === "string" ? editor.value : "";
  const start = caretOffset(editor);
  const end = editor && typeof editor.selectionEnd === "number" ? editor.selectionEnd : start;
  return { start, end: Math.max(start, Math.min(value.length, Math.trunc(end))) };
}
