// The playground's Wasm boundary (web/playground-wasm.js) under Node: a stub module
// records every allocation and free, so the ownership rules are testable without a Wiz
// build or Emscripten.
//
//   usage: node web/playground-wasm_test.mjs
//
// Covers: the happy path frees the input and the output once; a trap from either export
// frees the input (and the output, when it was returned); a decode that throws frees
// both; a missing `wiz_playground_check` allocates nothing; a source with U+0000 is
// refused before anything is allocated.
"use strict";
import { evalSource, checkSource, NUL_MESSAGE } from "./playground-wasm.js";

let failed = 0;
function check(name, got, want) {
  const same = Object.is(got, want) || JSON.stringify(got) === JSON.stringify(want);
  if (same) console.log(`ok: ${name}`);
  else { failed++; console.log(`FAIL: ${name}\n  want: ${JSON.stringify(want)}\n  got:  ${JSON.stringify(got)}`); }
}

// A stub module: pointers are integers into a map, and every export is configurable.
function stub({ evalResult = 7, evalThrows = false, checkResult = null, checkThrows = false,
                decodeThrows = false } = {}) {
  const wasm = {
    next: 100,
    strings: new Map(),
    allocated: [],
    freed: [],
    calls: [],
    stringToNewUTF8(s) {
      const p = wasm.next++;
      wasm.strings.set(p, s);
      wasm.allocated.push(p);
      return p;
    },
    UTF8ToString(p) {
      wasm.calls.push(["decode", p]);
      if (decodeThrows) throw new Error("decode failed");
      return wasm.strings.get(p);
    },
    _free(p) {
      const n = Number(p);
      wasm.calls.push(["free", n]);
      wasm.freed.push(n);
    },
  };
  wasm._wiz_playground_eval = (p) => {
    wasm.calls.push(["eval", Number(p), wasm.strings.get(Number(p))]);
    if (evalThrows) throw new Error("wasm trap");
    return evalResult;
  };
  if (checkResult !== null || checkThrows) {
    wasm._wiz_playground_check = (p) => {
      wasm.calls.push(["check", Number(p), wasm.strings.get(Number(p))]);
      if (checkThrows) throw new Error("wasm trap");
      return checkResult;
    };
  }
  return wasm;
}

// ## The happy path: both strings are freed exactly once
{
  const wasm = stub({ evalResult: 7 });
  wasm.strings.set(7, "a : Nat\n");
  check("eval: the text", evalSource(wasm, "def a : Nat := 1"), "a : Nat\n");
  check("eval: the input reaches the export", wasm.calls.find((c) => c[0] === "eval")[2], "def a : Nat := 1");
  check("eval: input and output freed once", wasm.freed.slice().sort((x, y) => x - y), [7, 100]);
}
{
  const wasm = stub({ checkResult: 8 });
  wasm.strings.set(8, '{"v":1,"lines":[]}');
  check("check: the JSON", checkSource(wasm, "def a : Nat := 1"), '{"v":1,"lines":[]}');
  check("check: input and output freed once", wasm.freed.slice().sort((x, y) => x - y), [8, 100]);
}

// ## A trap: the input is still freed (the leak wasm-01)
for (const [what, make, call] of [
  ["eval", () => stub({ evalThrows: true }), (w) => evalSource(w, "def a : Nat := 1")],
  ["check", () => stub({ checkThrows: true }), (w) => checkSource(w, "def a : Nat := 1")],
]) {
  const wasm = make();
  let caught = null;
  try { call(wasm); } catch (e) { caught = e; }
  check(`${what}: the trap reaches the page`, caught && caught.message, "wasm trap");
  check(`${what}: the input is freed after a trap`, wasm.freed, [100]);
}

// ## The output decode throws: both pointers are freed
{
  const wasm = stub({ decodeThrows: true, evalResult: 7 });
  wasm.strings.set(7, "x");
  let caught = null;
  try { evalSource(wasm, "def a : Nat := 1"); } catch (e) { caught = e; }
  check("decode: the error reaches the page", caught && caught.message, "decode failed");
  check("decode: input and output freed", wasm.freed.slice().sort((x, y) => x - y), [7, 100]);
}

// ## A module built before the check export: null, and nothing allocated
{
  const wasm = stub();
  check("check: an old module answers null", checkSource(wasm, "def a : Nat := 1"), null);
  check("check: an old module allocates nothing", wasm.allocated, []);
}

// ## U+0000: refused with a message, before the boundary can truncate the program
for (const [what, call] of [
  ["eval", (w) => evalSource(w, "def a : Nat := 1\u0000def b : Nat := 2")],
  ["check", (w) => checkSource(w, "def a : Nat := 1\u0000def b : Nat := 2")],
]) {
  const wasm = stub({ checkResult: 8 });
  let caught = null;
  try { call(wasm); } catch (e) { caught = e; }
  check(`${what}: U+0000 is refused`, caught && caught.message, NUL_MESSAGE);
  check(`${what}: U+0000 allocates nothing`, wasm.allocated, []);
}

if (failed) { console.log(`\n${failed} failed`); process.exit(1); }
console.log("playground wasm boundary: all checks passed");
