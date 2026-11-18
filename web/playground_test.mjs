// (11ab) The playground's Wasm module under Node: no page, no server. Calls the exported
// `wiz_playground_eval` on a small program, reads the string back, and checks a
// definition, one `#eval` (42, whose kernel normal form web/playground-values.js turns
// into `42`), a Bool and an error.
//   usage: node web/playground_test.mjs OUT_DIR
import { pathToFileURL } from "node:url";
import { renderValue } from "./playground-values.js";
import { PositionIndex } from "./selfhost-lsp-shim.js";

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

// (stage 2/3) the check's position index and the names export. The page adds the Prelude
// line itself (`withPrelude`), so the checked text is that source.
function call(name, source) {
  const p = wasm.stringToNewUTF8(source);
  const r = wasm[name](big(p));
  wasm._free(big(p));
  const text = r ? wasm.UTF8ToString(Number(r)) : "";
  if (r) wasm._free(r);
  return text;
}
function checkThat(name, condition, detail) {
  if (condition) console.log(`ok: ${name}`);
  else { failed++; console.log(`FAIL: ${name}${detail ? "\n  " + detail : ""}`); }
}
{
  const body = "def twice (n : Nat) : Nat := n + n\n";
  const answer = JSON.parse(call("_wiz_playground_check", "import Prelude\n\n" + body));
  checkThat("check: an index", Array.isArray(answer.index) && answer.index.length > 0,
    JSON.stringify(answer).slice(0, 400));
  const index = new PositionIndex(body, answer.index);
  const at = body.indexOf("n + n");
  const last = body.lastIndexOf("n");
  check("index: the body's expected type", (index.termGoal(at + 2) || {}).goal, "Nat");
  check("index: at the body's end", (index.termGoal(at + 4) || {}).goal, "Nat");
  // `n + n` is an infix macro: the rewritten node keeps its range but not its children
  check("index: the rewrite's span is the whole body",
    (index.termGoal(last) || { range: { start: {} } }).range.start.character, at);
  check("index: nothing before it", index.termGoal(0), null);
}
{
  // a plain application is not rewritten: its arguments keep their spans
  const src = "def ap (f : Nat → Nat) (x : Nat) : Nat := f x\n";
  const answer = JSON.parse(call("_wiz_playground_check", "import Prelude\n\n" + src));
  const index = new PositionIndex(src, answer.index);
  const body = src.indexOf("f x");
  const arg = src.lastIndexOf("x");
  check("app: the body's expected type", (index.termGoal(body) || {}).goal, "Nat");
  check("app: the argument's expected type", (index.termGoal(arg) || {}).goal, "Nat");
  check("app: the argument's own span", (index.termGoal(arg) || { range: { start: {} } }).range.start.character, arg);
}
{
  // a tactic block: the state before `exact a` is the initial goal
  const src = "import Prelude\n\ndef idA (A : Type) (a : A) : A := by\n  exact a\n";
  const answer = JSON.parse(call("_wiz_playground_check", src));
  const errors = answer.lines.filter((l) => l.sev === 1 || l.sev === 2);
  check("by: the block checks", errors.map((l) => l.text), []);
  const doc = "def idA (A : Type) (a : A) : A := by\n  exact a\n";
  const index = new PositionIndex(doc, answer.index);
  const step = doc.indexOf("exact");
  const goal = index.goal(step);
  checkThat("by: a goal before the step", goal !== null && goal.goals.length === 1,
    JSON.stringify(answer.index));
  checkThat("by: its target", goal !== null && goal.rendered.includes("⊢ A"), goal && goal.rendered);
  const end = doc.indexOf("exact a") + "exact a".length;   // the block's stop
  checkThat("by: the end of the block has a state", index.goal(end) !== null, JSON.stringify(goal));
}
{
  // the names export is not wired into the build yet (it enumerated the environment and
  // overflowed the wasm stack); the page's server treats that as an empty completion list
  check("names: the export is not wired yet", typeof wasm._wiz_playground_names, "undefined");
}

if (failed) process.exit(1);
console.log("playground: all checks passed");
