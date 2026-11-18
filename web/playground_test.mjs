// (11ab) The playground's Wasm module under Node: no page, no server. Calls the exported
// `wiz_playground_eval` on a small program, reads the string back, and checks a
// definition, one `#eval` (42, whose kernel normal form the value grammar turns into
// `42`), a Bool and an error.
//
// It then runs the same output through both UI paths and compares them: the page's
// hand-written pane (the `line()`/`show()` logic in web/playground.js, reproduced here
// with web/playground-values.js) and the Loom pane's module
// (`wiz-playground-ui.mjs`, lib/Web/Playground.wiz), mounted with
// web/framework/{runtime,minidom}.mjs. The two must agree on every line's text, class,
// tooltip and the status span -- that is the check that retires the hand-written pane.
//
//   usage: node web/playground_test.mjs OUT_DIR
import { pathToFileURL } from "node:url";
import { isValue, renderValue } from "./playground-values.js";
import { applyPatches, mount } from "./framework/runtime.js";
import { parse, serialize } from "./framework/minidom.mjs";

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

// ## The two panes, side by side

// The hand-written pane's `line()` and `show()` (web/playground.js), on the string the
// engine returned. The page builds DOM nodes; here the description is enough.
const domLine = (text) => {
  if (text.startsWith("error:") || text.startsWith("parse error")) {
    return { text, cls: "line err", title: null };
  }
  if (isValue(text)) {
    const shown = renderValue(text);
    return shown === null
      ? { text, cls: "line val raw", title: text }
      : { text: shown, cls: "line val", title: text };
  }
  return { text, cls: "line", title: null };
};
const domShow = (text) => text.split("\n").filter((l) => l !== "").map(domLine);

// The Loom pane: the UI module's `wiz_loom_show` + `wiz_loom_patches`, applied to a
// minidom tree by the same applier the page uses. The ownership dance is the page's
// (`web/playground.js`, `loomHold`/`loomAdvance`): an entry point consumes the state,
// the diff consumes both of its arguments.
const uiModule = await import(pathToFileURL(outDir + "/wiz-playground-ui.mjs").href)
  .then((m) => m.default({ printErr: (s) => console.error(s) }))
  .catch(() => null);
if (!uiModule) {
  failed++;
  console.log("FAIL: no " + outDir + "/wiz-playground-ui.mjs (run web/build-playground.sh)");
} else {
  const root = parse("");
  let state = uiModule._wiz_loom_init();
  uiModule._wiz_retain(big(state));
  const firstPaint = uiModule._wiz_loom_html(state);
  mount(root, uiModule.UTF8ToString(Number(firstPaint)), parse);
  uiModule._free(firstPaint);
  const uiCall = (name, ...args) => {
    const pointers = [];
    const rest = args.map((a) => {
      if (typeof a === "string") { const p = uiModule.stringToNewUTF8(a); pointers.push(p); return big(p); }
      return typeof a === "number" ? big(a) : a;
    });
    try { return uiModule["_" + name](state, ...rest); }
    finally { for (const p of pointers) uiModule._free(big(p)); }
  };
  const hold = () => uiModule._wiz_retain(big(state));
  const advance = (next) => {
    uiModule._wiz_retain(big(next));
    const p = uiModule._wiz_loom_patches(state, next);
    const json = uiModule.UTF8ToString(Number(p));
    uiModule._free(p);
    state = next;
    applyPatches(root, JSON.parse(json), parse);
  };
  const uiShow = (text) => { hold(); advance(uiCall("wiz_loom_show", text)); };
  const uiFail = (text, label) => { hold(); advance(uiCall("wiz_loom_fail", text, label)); };
  const uiStatus = (text, kind) => { hold(); advance(uiCall("wiz_loom_status", text, kind)); };

  const walk = (n, pred, acc = []) => {
    if (pred(n)) acc.push(n);
    for (const c of n.childNodes || []) walk(c, pred, acc);
    return acc;
  };
  const linesIn = () => walk(root, (n) => n.getAttribute &&
    /\bline\b/.test(n.getAttribute("class") || "")).map((n) => ({
      text: n.textContent,
      cls: n.getAttribute("class"),
      title: n.getAttribute("title"),
    }));
  const statusIn = () => {
    const s = walk(root, (n) => n.getAttribute && n.getAttribute("id") === "status")[0];
    return s && { text: s.textContent, cls: s.getAttribute("class") };
  };

  const same = (what, got, want) => {
    check(what, JSON.stringify(got), JSON.stringify(want));
  };

  // The engine's own output, and a few shapes the engine only produces for other
  // programs (a first-class list, a raw value, a failure).
  for (const text of [out.join("\n"), bare.join("\n"),
    "con((#1, (con((#0, (tt, tt))), (tt, tt))))",
    "con((#1, (tt, tt)))\ncon((#2, (tt, tt)))",
    "", "error: unknown identifier nope\nparse error at 2:1"]) {
    uiShow(text);
    same("the Loom pane matches the hand-written one: " + JSON.stringify(text.slice(0, 30)),
      linesIn(), domShow(text));
  }

  // The status span: the app owns the page's `#status`.
  uiStatus("done in 4 ms", "ready");
  check("status: text", (statusIn() || {}).text, "done in 4 ms");
  check("status: class", (statusIn() || {}).cls, "status ready");
  uiStatus("running…", "running");
  check("status: running", (statusIn() || {}).cls, "status running");

  // A failure: the page's own count label is passed in (`exit code 3`), the lines are
  // the guard's.
  uiStatus("failed", "error");
  const failure = "error: the program exited with code 3";
  uiFail(failure, "exit code 3");
  same("a failure's lines", linesIn(), domShow(failure));
  check("a failure keeps the status", (statusIn() || {}).text, "failed");

  // The count. The pane's model has it (`#count` stays the page's text), so the page's
  // `countText` is what the tests pin; the app's state is opaque.
  const countText = (raw) => {
    const lines = raw.split("\n").filter((l) => l !== "");
    const bad = lines.filter((l) => l.startsWith("error:") || l.startsWith("parse error")).length;
    return lines.length + (lines.length === 1 ? " line" : " lines") +
      (bad ? ` · ${bad} error${bad === 1 ? "" : "s"}` : "");
  };
  check("a five-line run's count", countText(out.join("\n")), "5 lines · 1 error");
  check("a single line's count", countText(bare.join("\n")), "2 lines");

  // Many state changes: a wrong reference count would corrupt the heap (or trap) here.
  for (let i = 0; i < 50; i++) {
    uiShow("ok\n" + i);
    uiStatus("done", "ready");
  }
  same("fifty runs keep the pane correct", linesIn(), domShow("ok\n49"));
  check("fifty runs keep the status", (statusIn() || {}).text, "done");
  check("the mount serializes", serialize(root).includes('id="output"'), true);
}

if (failed) process.exit(1);
console.log("playground: all checks passed");
