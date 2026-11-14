// (11ab) The playground's Wasm module under Node: no page, no server. Calls the exported
// `wiz_playground_eval` on a small program, reads the string back, and checks a
// definition, one `#eval` (42, whose kernel normal form web/playground-values.js turns
// into `42`), a Bool and an error.
//   usage: node web/playground_test.mjs OUT_DIR
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

if (failed) process.exit(1);
console.log("playground: all checks passed");
