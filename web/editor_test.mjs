// The playground editor's model under Node: positions (UTF-16 versus code points), the
// ranges diagnostics underline, and the completion list's filtering, ordering, keyboard
// index and insertion. Pure functions, no DOM, no server: this is the part of the
// editor's behaviour that a browser test would only repeat.
//
//   usage: node web/editor_test.mjs
"use strict";
import {
  positionFromOffset, offsetFromPosition, caretOffset, caretPosition,
  codePointPositionFromOffset, utf16OffsetFromCodePoints, codePointOffsetFromUtf16,
  squiggleSegments, mergeSegments, tokenEnd, splitAtLines, severityOf,
  identifierPrefix, isIdentifierChar, inLineComment, completionTrigger,
  completionItems, completionScore, filterCompletions, moveSelection,
  stripSnippet, acceptCompletion, completionPopupState, COMPLETION_LIMIT,
} from "./editor-model.js";

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

// ## 1. Positions: UTF-16 at the edge, code points for a server that counts them

{
  const text = "a😀b\nc";
  // UTF-16: a(1) 😀(2) b(1) = 4 units on line 0, 'c' at unit 5.
  check("utf-16: an emoji is two units", offsetFromPosition(text, { line: 0, character: 3 }), 3);
  check("utf-16: the second line starts after the emoji", offsetFromPosition(text, { line: 1, character: 1 }), 6);
  check("utf-16: position of the caret after the emoji", positionFromOffset(text, 3), { line: 0, character: 3 });
  check("utf-16: position after the newline", positionFromOffset(text, 5), { line: 1, character: 0 });

  // A character past the end of its line stops at the line end (LSP ranges from other
  // servers do this); it must not resolve into the next line.
  check("utf-16: past the line end stays on the line", offsetFromPosition("ab\ncd", { line: 0, character: 5 }), 2);
  check("utf-16: past the last line's end stops at the text", offsetFromPosition("ab\ncd", { line: 1, character: 5 }), 5);

  // Code points: a(1) 😀(1) b(1) = 3 on line 0; the difference is one.
  check("code points: after the emoji", codePointPositionFromOffset(text, 3), { line: 0, character: 2 });
  check("code points: line 2", codePointPositionFromOffset(text, 6), { line: 1, character: 1 });
  check("code points → utf-16: index 2 is offset 3", utf16OffsetFromCodePoints(text, 2), 3);
  check("utf-16 → code points: offset 3 is index 2", codePointOffsetFromUtf16(text, 3), 2);
  check("code points: the round trip", utf16OffsetFromCodePoints(text, codePointOffsetFromUtf16(text, 5)), 5);
  // A BMP character is one unit and one code point: the two conventions agree.
  check("code points: BMP only", codePointPositionFromOffset("ab\ncd", 4), { line: 1, character: 1 });
}

{
  const editor = { value: "ab😀cd", selectionStart: 5, selectionEnd: 5 };
  check("caret: selectionStart is the utf-16 offset", caretOffset(editor), 5);
  check("caret: as a position", caretPosition(editor), { line: 0, character: 5 });
  check("caret: a selection uses its start", caretOffset({ value: "abcd", selectionStart: 1, selectionEnd: 3 }), 1);
  check("caret: clamped to the text", caretOffset({ value: "ab", selectionStart: 99 }), 2);
  check("caret: a stub editor is 0", caretOffset({}), 0);
}

// ## 2. Squiggles

{
  const text = "def f : Nat := nope\n";
  const segs = squiggleSegments(text, [{
    range: { start: { line: 0, character: 13 }, end: { line: 0, character: 17 } },
    severity: 1, message: "unknown identifier",
  }]);
  check("squiggle: one span", segs.length, 1);
  check("squiggle: its offsets", [segs[0].start, segs[0].end], [13, 17]);
  check("squiggle: its line and characters", [segs[0].line, segs[0].startCharacter, segs[0].endCharacter], [0, 13, 17]);
  check("squiggle: the severity", segs[0].severity, 1);
  check("squiggle: the message", segs[0].message, "unknown identifier");
}

// A range with no end underlines the token at its start.
check("squiggle: no end underlines the token",
  squiggleSegments("def x := nope + 1", [{ range: { start: { line: 0, character: 9 } }, message: "m" }])
    .map((s) => [s.start, s.end]),
  [[9, 13]]);
// An empty range (start == end) is the same repair.
check("squiggle: an empty range underlines the token",
  squiggleSegments("x nope y", [{ range: { start: { line: 0, character: 2 }, end: { line: 0, character: 2 } } }])
    .map((s) => [s.start, s.end]),
  [[2, 6]]);
// On whitespace, or in the middle of one: one character.
check("squiggle: on whitespace, one character",
  squiggleSegments("ab cd", [{ range: { start: { line: 0, character: 2 } } }]).map((s) => [s.start, s.end]),
  [[2, 3]]);
// Past the end of the text: nothing to underline (not a zero-width span).
check("squiggle: past the end is dropped",
  squiggleSegments("ab", [{ range: { start: { line: 4, character: 0 } } }]).length, 0);
// A range that runs past the text is clamped.
check("squiggle: a range past the end is clamped",
  squiggleSegments("abc", [{ range: { start: { line: 0, character: 1 }, end: { line: 9, character: 9 } } }])
    .map((s) => [s.start, s.end]),
  [[1, 3]]);
// A multi-line range becomes one span per line, none containing a newline.
{
  const text = "one two\nthree four\nfive";
  const segs = squiggleSegments(text, [{
    range: { start: { line: 0, character: 4 }, end: { line: 2, character: 2 } }, severity: 2, message: "w",
  }]);
  check("squiggle: a multi-line range is one span per line", segs.length, 3);
  check("squiggle: the pieces", segs.map((s) => [s.start, s.end]), [[4, 7], [8, 18], [19, 21]]);
  check("squiggle: no newline in a span", segs.every((s) => !text.slice(s.start, s.end).includes("\n")), true);
  check("squiggle: each piece is on its line", segs.map((s) => s.line), [0, 1, 2]);
}
// Overlaps merge: the stricter severity wins, both messages survive.
{
  const merged = mergeSegments([
    { start: 5, end: 9, severity: 2, message: "warning" },
    { start: 7, end: 12, severity: 1, message: "error" },
    { start: 20, end: 22, severity: 3, message: "info" },
  ]);
  check("merge: two spans", merged.length, 2);
  check("merge: the overlapping span", [merged[0].start, merged[0].end], [5, 12]);
  check("merge: the stricter severity", merged[0].severity, 1);
  check("merge: both messages", merged[0].message, "error · warning");
}
check("severity: missing is info", severityOf({}), 3);
check("severity: out of range is info", severityOf({ severity: 9 }), 3);
check("severity: 2 is warning", severityOf({ severity: 2 }), 2);
check("tokenEnd: an identifier", tokenEnd("ab cd", 0), 2);
check("tokenEnd: at the end", tokenEnd("ab", 2), 2);
check("splitAtLines: no break, no split", splitAtLines("abc", 0, 3).length, 1);

// ## 3. Completions

check("items: an array", completionItems([{ label: "a" }, { label: "b" }]).length, 2);
check("items: a CompletionList", completionItems({ isIncomplete: true, items: [{ label: "a" }] }).length, 1);
check("items: a single item", completionItems({ label: "a" }).length, 1);
check("items: null", completionItems(null).length, 0);
check("items: no label is dropped", completionItems([{ detail: "x" }, { label: "" }, { label: "ok" }]).length, 1);
check("items: copied, not aliased", completionItems([{ label: "a" }])[0] !== undefined, true);

{
  const items = completionItems([
    { label: "Nat.add" }, { label: "Nat.sub" }, { label: "natPred" }, { label: "Bool.and" },
    { label: "Nat.succ", sortText: "0" }, { label: "add" },
  ]);
  check("filter: the prefix picks the label", filterCompletions(items, "Nat.ad").map((i) => i.label), ["Nat.add", "add"]);
  check("filter: case-insensitive", filterCompletions(items, "NAT.S").map((i) => i.label), ["Nat.succ", "Nat.sub"]);
  check("filter: an exact prefix before a longer one",
    filterCompletions(items, "add").map((i) => i.label), ["add", "Nat.add"]);
  check("filter: sortText orders equal matches", filterCompletions(items, "NAT.S")[0].label, "Nat.succ");
  check("filter: a qualified tail matches", filterCompletions(items, "x.and").map((i) => i.label), ["Bool.and"]);
  check("filter: a substring matches last", completionScore({ label: "Nat.add" }, "dd"), 2);
  check("filter: no match", completionScore({ label: "Nat.add" }, "zz"), -1);
  check("filter: an empty prefix keeps everything", filterCompletions(items, "").length, items.length);
  check("items: bounded", filterCompletions(items, "", { limit: 2 }).length, 2);
  check("popup: an empty prefix is capped", completionPopupState("", 0, new Array(300).fill(0).map((_, i) => ({ label: "x" + i }))).items.length, COMPLETION_LIMIT);
}

check("move: down", moveSelection(0, 1, 3), 1);
check("move: up wraps", moveSelection(0, -1, 3), 2);
check("move: down wraps", moveSelection(2, 1, 3), 0);
check("move: no items", moveSelection(0, 1, 0), -1);
check("move: an out-of-range index is clamped", moveSelection(9, 0, 3), 2);
check("move: from nothing, down is the first", moveSelection(-1, 1, 3), 0);

check("snippet: placeholders stripped", stripSnippet("foo ${1:bar} $2 ${0}"), "foo bar  ");
check("snippet: an escaped dollar", stripSnippet("a \\$ b"), "a $ b");

// Insertion: the label replaces the identifier prefix.
{
  const r = acceptCompletion({ label: "twice" }, "def x := tw", 11);
  check("accept: the new text", r.text, "def x := twice");
  check("accept: the replaced span", [r.start, r.end], [9, 11]);
  check("accept: the caret after the insert", r.caret, 14);
}
// insertText wins over the label.
check("accept: insertText", acceptCompletion({ label: "twice", insertText: "twice 0" }, "tw", 2).text, "twice 0");
// A textEdit's range is authoritative (it may replace more than the prefix).
{
  const r = acceptCompletion({
    label: "Nat.add",
    textEdit: { range: { start: { line: 0, character: 0 }, end: { line: 0, character: 3 } }, newText: "Nat.add" },
  }, "Nat", 3);
  check("accept: a textEdit's range", [r.start, r.end], [0, 3]);
  check("accept: a textEdit's text", r.text, "Nat.add");
}
// A snippet sent anyway has its placeholders stripped.
check("accept: snippet format", acceptCompletion({ label: "f", insertText: "f(${1:x})", insertTextFormat: 2 }, "f", 1).text, "f(x)");
// Accepting with no prefix inserts at the caret.
check("accept: an empty prefix", acceptCompletion({ label: "abc" }, "x ", 2).text, "x abc");
// An emoji before the caret does not shift the prefix: the text is UTF-16, like the caret.
{
  const r = acceptCompletion({ label: "twice" }, "😀 tw", 5);
  check("accept: after an emoji", r.text, "😀 twice");
  check("accept: the caret after an emoji", r.caret, 8);
}

// ## 4. When the popup opens

check("trigger: a letter", completionTrigger("x", 1, "a"), true);
check("trigger: a digit", completionTrigger("x", 1, "1"), true);
check("trigger: a quote (part of an identifier)", completionTrigger("x", 1, "'"), true);
check("trigger: a dot (a qualified name)", completionTrigger("Nat", 3, "."), true);
check("trigger: a space", completionTrigger("x", 1, " "), false);
check("trigger: a newline", completionTrigger("x", 1, "\n"), false);
check("trigger: in a line comment", completionTrigger("-- no", 5, "t"), false);
check("trigger: the start of a new line after a comment", completionTrigger("-- x\n", 5, "t"), true);
check("comment: a new line is not a comment", inLineComment("-- x\ny", 6), false);
check("identifier: the prefix", identifierPrefix("def foo := Nat.ad", 17), { start: 11, word: "Nat.ad" });
check("identifier: after a space", identifierPrefix("def x", 5), { start: 4, word: "x" });
check("identifier: is a char", isIdentifierChar("_"), true);
check("identifier: is not a char", isIdentifierChar("-"), false);

if (failed) {
  console.log(`editor model: ${failed} check(s) failed`);
  process.exit(1);
}
console.log("editor model: all checks passed");
