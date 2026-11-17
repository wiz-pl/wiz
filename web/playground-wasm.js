// (11ab) The playground's two Wasm exports (web/playground-exports.wiz) and the
// ownership rules of their strings. It lives beside web/playground.js, not in it, so
// Node can test the boundary without a page (web/playground-wasm_test.mjs).
//
// Both directions are NUL-terminated UTF-8 (`String` in, `String` out:
// runtime/rt_data.inc's `wiz_out_string`/`wiz_in_string`), so a source cannot carry
// U+0000: it would silently truncate the program at the first NUL. The page refuses such
// a source with a message instead (`checkSource` would escape it in JSON, but the eval
// export would still cut the program short, and a result containing NUL would truncate
// too). The input pointer and the returned pointer are freed on every path, including a
// Wasm trap or a panic, which Emscripten throws into JavaScript.
"use strict";

const big = (x) => (typeof x === "bigint" ? x : BigInt(x));   // wasm64: pointers are i64

export const NUL_MESSAGE =
  "the source contains U+0000, which the Wasm string boundary cannot carry " +
  "(its strings are NUL-terminated UTF-8, so the program would be cut off there)";

function rejectNul(src) {
  if (String(src).includes("\u0000")) throw new Error(NUL_MESSAGE);
}

// The string `r` (a malloc'ed UTF-8 pointer, or 0) as text; the pointer is freed even
// when the decode throws.
function takeString(wasm, r) {
  try {
    return r ? wasm.UTF8ToString(Number(r)) : "";
  } finally {
    if (r) wasm._free(r);
  }
}

// `wiz_playground_eval(src)`: the engine's output lines. The input is copied by
// `wiz_out_string`, so it is freed as soon as the call returns (or throws).
export function evalSource(wasm, src) {
  rejectNul(src);
  const p = wasm.stringToNewUTF8(src);
  try {
    return takeString(wasm, wasm._wiz_playground_eval(big(p)));
  } finally {
    wasm._free(big(p));
  }
}

// (stage 1) `wiz_playground_check(src)`: the same check as JSON, or null with a module
// built before the export existed.
export function checkSource(wasm, src) {
  if (typeof wasm._wiz_playground_check !== "function") return null;
  rejectNul(src);
  const p = wasm.stringToNewUTF8(src);
  try {
    const r = wasm._wiz_playground_check(big(p));
    try {
      return r ? wasm.UTF8ToString(Number(r)) : null;
    } finally {
      if (r) wasm._free(r);
    }
  } finally {
    wasm._free(big(p));
  }
}
