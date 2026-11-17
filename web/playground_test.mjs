// (11ab) The playground's Wasm module under Node: no page, no server. Calls the exported
// `wiz_playground_eval` on a small program, reads the string back, and checks a
// definition, one `#eval` (42, whose kernel normal form web/playground-values.js turns
// into `42`), a Bool and an error; then on the playground's default program,
// web/playground-tour.wiz (the file web/playground.js fetches and the page shows), whose
// whole output is checked against the expectation below.
//   usage: node web/playground_test.mjs OUT_DIR
import { readFileSync } from "node:fs";
import { pathToFileURL } from "node:url";
import { renderValue } from "./playground-values.js";

const outDir = process.argv[2] || new URL("./out/", import.meta.url).pathname;
const createModule = (await import(pathToFileURL(outDir + "/wiz-playground.mjs").href)).default;
const wasm = await createModule({ printErr: (s) => console.error(s) });
const big = (x) => (typeof x === "bigint" ? x : BigInt(x));   // wasm64: pointers are i64

function run(source) {
  const p = wasm.stringToNewUTF8(source);
  const r = wasm._wiz_playground_eval(big(p));
  wasm._free(big(p));
  const text = r ? wasm.UTF8ToString(Number(r)) : "";
  if (r) wasm._free(r);
  return text.split("\n").filter((l) => l !== "");
}

let failed = 0;
function check(name, got, want) {
  if (got === want) console.log(`ok: ${name}`);
  else { failed++; console.log(`FAIL: ${name}\n  want: ${JSON.stringify(want)}\n  got:  ${JSON.stringify(got)}`); }
}

const out = run(`import Prelude

def twice (n : Nat) : Nat := n + n

#check twice
#eval twice 21
#eval Nat.beq (7 + 7) 14
#eval nope
`);
check("a definition's signature", out[0], "twice : (x0 : Nat) → Nat");
check("#check", out[1], "(x0 : Nat) → Nat");
const fortyTwo = out.find((l) => l.startsWith("con("));
check("one evaluation (42)", renderValue(fortyTwo), "42");
check("a Bool evaluation", renderValue(out[3]), "true");
check("an error", out[4], "error: unknown identifier nope");

// A source without an import is what the page sends (`withPrelude` prepends it); the
// engine itself needs the import, so this is the page's contract, checked here once.
const bare = run("import Prelude\ndef one : Nat := 1\n#eval one\n");
check("a bare definition's own output", bare[0], "one : Nat");
check("a bare evaluation", renderValue(bare[1]), "1");

// The playground's default program is a Wiz file, not the textarea's inline text: the
// page fetches `playground-tour.wiz` and shows it (the inline text is only the fallback
// when the fetch fails). Check the checked-in file itself, so the tour cannot rot, and
// compare its whole output at the display the page renders (renderValue, else raw).
const tour = readFileSync(new URL("./playground-tour.wiz", import.meta.url), "utf8");
check("the tour starts with import Prelude", tour.startsWith("import Prelude\n"), true);
const tourLines = tour.replace(/\n$/, "").split("\n").length;
check("the tour's length (40-70 lines)", tourLines >= 40 && tourLines <= 70, true);
const shown = (lines) => lines.map((l) => {
  const value = renderValue(l);
  return value === null ? l : value;
});
check("the tour's output", shown(run(tour)).join("\n"), [
  "Nat",
  "42",
  "add3 : (x0 : Nat) → (x1 : Nat) → (x2 : Nat) → Nat",
  "6",
  "parity : (x0 : Nat) → Nat",
  "1",
  "Shape : U0",
  "area : (x0 : Shape) → Nat",
  "total : (x0 : (List Nat)) → Nat",
  "6",
  "[2, 3]",
  "Point : U0",
  "Point.x : (x0 : Point) → Nat",
  "Point.y : (x0 : Point) → Nat",
  "2",
  "Describe : (x0 : U0) → U0",
  "Describe.describe : (x0 :0 U0) → (x1 : (Describe x0)) → (x2 : x0) → Nat",
  "instDescribeNat : (Describe Nat)",
  "42",
  "Vec : (x0 : U0) → (x1 : Nat) → U0",
  "head : (x0 :0 U0) → (x1 :0 Nat) → (x2 : x0) → (x3 : ((Vec x0) x1)) → x0",
  "7",
  "twoPlusTwo : Eq(Nat, ((Nat.add (Nat.succ (Nat.succ Nat.zero))) (Nat.succ (Nat.succ Nat.zero))), (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))",
  "3",
  "7",
  "25",
].join("\n"));

if (failed) process.exit(1);
console.log("playground: all checks passed");
