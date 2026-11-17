// web/playground-values.js under Node: the kernel normal forms `#eval` prints, and the
// depth cap that keeps a big value from exhausting the JavaScript stack.
//
//   usage: node web/playground_values_test.mjs
//
// Covers: Nat, Bool and list rendering; 0 and nil stay raw (they look like false); a
// 10,000-successor Nat and a 3,000-element list render the truncation marker instead of
// throwing (wasm-06); and a deep malformed line does not throw either.
"use strict";
import { renderValue, isValue, TOO_DEEP_MARKER } from "./playground-values.js";

let failed = 0;
function check(name, got, want) {
  if (Object.is(got, want)) console.log(`ok: ${name}`);
  else { failed++; console.log(`FAIL: ${name}\n  want: ${JSON.stringify(want)}\n  got:  ${JSON.stringify(got)}`); }
}

// The runtime's printed constructor: `con((#tag, (fields…, (tt, tt))))`.
const ZERO = "con((#0, (tt, tt)))";
const ONE = "con((#1, (con((#0, (tt, tt))), (tt, tt))))";
function succ(s) { return `con((#1, (${s}, (tt, tt))))`; }
function nat(n) { let s = ZERO; for (let i = 0; i < n; i++) s = succ(s); return s; }
function nil() { return ZERO; }
function cons(head, tail) { return `con((#1, (${head}, (${tail}, (tt, tt)))))`; }
function list(values) { let s = nil(); for (let i = values.length - 1; i >= 0; i--) s = cons(values[i], s); return s; }

// ## Small values
check("Nat 1", renderValue(ONE), "1");
check("Nat 42", renderValue(nat(42)), "42");
check("a 500-successor Nat", renderValue(nat(500)), "500");
check("true", renderValue("con((#1, (tt, tt)))"), "true");
check("a list", renderValue(list([nat(1), nat(2), nat(3)])), "[1, 2, 3]");
check("a nested list", renderValue(list([list([nat(1)]), list([nat(2), nat(3)])])), "[[1], [2, 3]]");
check("zero stays raw (it also looks like false and nil)", renderValue(ZERO), null);
check("nil stays raw at the top", renderValue(nil()), null);
check("a non-value stays raw", renderValue("a : Nat"), null);
check("isValue: a constructor line", isValue(nat(3)), true);

// ## wasm-06: the depth cap
{
  let value = null;
  let error = null;
  try { value = renderValue(nat(10000)); } catch (e) { error = e; }
  check("a 10,000-successor Nat does not throw", error, null);
  check("a 10,000-successor Nat shows the marker", value, TOO_DEEP_MARKER);
}
{
  let value = null;
  let error = null;
  try { value = renderValue(list(Array.from({ length: 3000 }, (_, i) => nat(1 + (i % 2))))); }
  catch (e) { error = e; }
  check("a 3,000-element list does not throw", error, null);
  check("a 3,000-element list shows the marker", value, TOO_DEEP_MARKER);
}
{
  let value = null;
  let error = null;
  try { value = renderValue("(".repeat(5000)); } catch (e) { error = e; }
  check("a deep malformed line does not throw", error, null);
  check("a deep malformed line shows the marker", value, TOO_DEEP_MARKER);
}

if (failed) { console.log(`\n${failed} failed`); process.exit(1); }
console.log("playground values: all checks passed");
