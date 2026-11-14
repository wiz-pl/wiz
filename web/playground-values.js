// (11ab) Reading the self-hosted checker's `#eval` output: `#eval` prints the kernel's
// normal form, which is the runtime's tagged values, e.g.
//
//   con((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt))))   -- 2
//
// That is exact but not friendly. This module parses the shape and shows a Nat, a Bool
// or a list when the shape says unambiguously what it is; anything else is left as the
// raw line (and the page always keeps the raw text in the line's `title`).
"use strict";

// A value is `con(pair(tag, fields))`, a pair `(a, b)`, a tag `#n` or `tt`.
function parse(s, i = 0) {
  i = skip(s, i);
  if (s.startsWith("con(", i)) {
    const [v, j] = parse(s, i + 4);
    if (v === null) return [null, i];
    const k = skip(s, j);
    return s[k] === ")" ? [v, k + 1] : [null, i];
  }
  if (s.startsWith("tt", i)) return [{ k: "tt" }, i + 2];
  if (s[i] === "#") {
    let j = i + 1;
    while (j < s.length && s[j] >= "0" && s[j] <= "9") j++;
    return j > i + 1 ? [{ k: "tag", n: Number(s.slice(i + 1, j)) }, j] : [null, i];
  }
  if (s[i] === "(") {
    const [a, j] = parse(s, i + 1);
    if (a === null) return [null, i];
    let k = skip(s, j);
    if (s[k] !== ",") return [null, i];
    const [b, l] = parse(s, k + 1);
    if (b === null) return [null, i];
    k = skip(s, l);
    return s[k] === ")" ? [{ k: "pair", a, b }, k + 1] : [null, i];
  }
  return [null, i];
}

function skip(s, i) {
  while (i < s.length && (s[i] === " " || s[i] === "\n" || s[i] === "\t")) i++;
  return i;
}

function whole(s) {
  const [v, j] = parse(s, 0);
  return v !== null && skip(s, j) === s.length ? v : null;
}

const isTt = (v) => v !== null && v.k === "tt";

// The fields of a constructor: `(f1, (f2, ... (tt, tt)))`; `(tt, tt)` is none.
function fields(v) {
  const out = [];
  while (v !== null && v.k === "pair") {
    if (isTt(v.a) && isTt(v.b)) return out;
    out.push(v.a);
    v = v.b;
  }
  return null;
}

// `con((#tag, payload))` → { tag, fields }.
function con(v) {
  if (v === null || v.k !== "pair") return null;
  if (v.a === null || v.a.k !== "tag") return null;
  const fs = fields(v.b);
  return fs === null ? null : { tag: v.a.n, fields: fs };
}

// A Nat is a chain of `succ` (tag 1, one field) to `zero` (tag 0, no fields).
function nat(v) {
  const c = con(v);
  if (c === null) return null;
  if (c.tag === 0 && c.fields.length === 0) return 0;
  if (c.tag === 1 && c.fields.length === 1) {
    const n = nat(c.fields[0]);
    return n === null ? null : n + 1;
  }
  return null;
}

// A list is `nil` (tag 0, no fields) or `cons` (tag 1, two fields); `nested` allows
// nil (at the top, `nil` looks like `false` and `0`, so it stays raw).
function list(v, nested) {
  const c = con(v);
  if (c === null) return null;
  if (c.tag === 0 && c.fields.length === 0) return nested ? [] : null;
  if (c.tag === 1 && c.fields.length === 2) {
    const head = elem(c.fields[0]);
    const tail = list(c.fields[1], true);
    return head === null || tail === null ? null : [head, ...tail];
  }
  return null;
}

function elem(v) {
  const n = nat(v);
  if (n !== null && n > 0) return String(n);
  const c = con(v);
  if (c !== null && c.tag === 1 && c.fields.length === 0) return "true";
  const l = list(v, true);
  return l === null ? null : `[${l.join(", ")}]`;
}

// The display text for one output line, or null to show it as it came.
export function renderValue(line) {
  const v = whole(line);
  if (v === null) return null;
  const n = nat(v);
  if (n !== null && n > 0) return String(n);
  const c = con(v);
  if (c !== null && c.tag === 1 && c.fields.length === 0) return "true";
  const l = list(v, false);
  return l === null ? null : `[${l.join(", ")}]`;
}

// Lines that are a kernel value rather than a definition or an error.
export function isValue(line) {
  return /^con\(/.test(line);
}
