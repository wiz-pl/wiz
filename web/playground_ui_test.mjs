// The playground's Loom pane under Node: load the UI module web/build-playground.sh
// built (`wiz-playground-ui.mjs`, lib/Web/Playground.wiz behind
// web/playground-ui-exports.wiz), mount its first paint with
// web/framework/{runtime,minidom}.mjs, and drive it through the entry points exactly as
// web/playground.js does -- including the ownership dance (an entry point consumes the
// state it is given; the diff consumes both of its arguments; a read-only call takes
// `_wiz_retain` first).
//
// It is also the comparison: for every input the hand-written pane's `line()` (with
// web/playground-values.js) is the oracle, and the Loom pane must agree line by line on
// the text, the class and the tooltip, and on the status span. No engine and no browser:
// the engine is the page's other module (web/playground_test.mjs compares the two on the
// engine's own output).
//
//   usage: node web/playground_ui_test.mjs OUT_DIR
import { pathToFileURL } from "node:url";
import { isValue, renderValue } from "./playground-values.js";
import { applyPatches, mount } from "./framework/runtime.js";
import { parse, serialize } from "./framework/minidom.mjs";

const outDir = process.argv[2] || new URL("./out/", import.meta.url).pathname;
const createModule = (await import(pathToFileURL(outDir + "/wiz-playground-ui.mjs").href)).default;
const wasm = await createModule({ printErr: (s) => console.error(s) });
const big = (x) => (typeof x === "bigint" ? x : BigInt(x));   // wasm64: pointers are i64

let failed = 0;
function check(what, got, want) {
  if (JSON.stringify(got) === JSON.stringify(want)) console.log("ok: " + what);
  else { failed++; console.log(`FAIL: ${what}\n  want: ${JSON.stringify(want)}\n  got:  ${JSON.stringify(got)}`); }
}

// ## The hand-written pane's description of a run (web/playground.js, `line`)

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

// ## The Loom pane, driven the way the page drives it

const root = parse("");
let state = wasm._wiz_loom_init();

// The first paint is a read-only call: take an extra reference for it.
wasm._wiz_retain(big(state));
const firstPaint = wasm._wiz_loom_html(state);
mount(root, wasm.UTF8ToString(Number(firstPaint)), parse);
wasm._free(firstPaint);

function take(p) {
  if (!p) return "";
  const s = wasm.UTF8ToString(Number(p));
  wasm._free(p);
  return s;
}

// `uiCall` is the page's: the state first (consumed), strings borrowed and freed after.
function uiCall(name, ...args) {
  const pointers = [];
  const rest = args.map((a) => {
    if (typeof a === "string") { const p = wasm.stringToNewUTF8(a); pointers.push(p); return big(p); }
    return typeof a === "number" ? big(a) : a;
  });
  try { return wasm["_" + name](state, ...rest); }
  finally { for (const p of pointers) wasm._free(big(p)); }
}

// `loomHold` + `loomAdvance` are the page's: the producing call consumes the page's
// reference, so the old state is retained for the diff; the diff consumes both, so the
// new one is retained too (the page keeps one).
const hold = () => wasm._wiz_retain(big(state));
function advance(next) {
  wasm._wiz_retain(big(next));
  const json = take(wasm._wiz_loom_patches(state, next));
  state = next;
  applyPatches(root, JSON.parse(json), parse);
}
const uiShow = (text) => { hold(); advance(uiCall("wiz_loom_show", text)); };
const uiFail = (text, label) => { hold(); advance(uiCall("wiz_loom_fail", text, label)); };
const uiStatus = (text, kind) => { hold(); advance(uiCall("wiz_loom_status", text, kind)); };

// ## Reading the mounted tree

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
const byId = (id) => walk(root, (n) => n.getAttribute && n.getAttribute("id") === id)[0];
const statusIn = () => {
  const s = byId("status");
  return s && { text: s.textContent, cls: s.getAttribute("class") };
};

// The first paint is the page's static state: an empty pane and the header's line.
check("the first paint's pane", linesIn(), []);
check("the first paint's status", statusIn(),
  { text: "loading the engine…", cls: "status running" });
check("the pane keeps the page's id and aria-live",
  [byId("output").getAttribute("aria-live"), byId("output").getAttribute("class")],
  ["polite", "output"]);

// ## Every kind of line, against the hand-written pane's description

const corpus = [
  "twice : (x0 : Nat) → Nat",
  "(x0 : Nat) → Nat",
  "con((#1, (con((#0, (tt, tt))), (tt, tt))))",
  "con((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (tt, tt))))",
  "con((#1, (tt, tt)))",
  "con((#1, (con((#1, (con((#0, (tt, tt))), (tt, tt)))), (con((#0, (tt, tt))), (tt, tt)))))",
  "con((#0, (tt, tt)))",
  "con((#2, (tt, tt)))",
  "con(",
  "error: unknown identifier nope",
  "parse error at 2:1",
  "",
];
for (const text of corpus) {
  uiShow(text);
  check("the Loom pane matches the hand-written one: " + JSON.stringify(text).slice(0, 50),
    linesIn(), domShow(text));
}
uiShow("<script>alert('x')</script>");
check("output text is escaped",
  [serialize(root).includes("&lt;script&gt;"), serialize(root).includes("<script>")],
  [true, false]);

// A whole run, several lines at once (the page always shows one).
const runText = corpus.slice(0, 6).join("\n");
uiShow(runText);
check("a run's lines", linesIn(), domShow(runText));

// ## The status span, a failure, and the page's own count text

uiStatus("done in 4 ms", "ready");
check("status: done", statusIn(), { text: "done in 4 ms", cls: "status ready" });
uiStatus("running…", "running");
check("status: running", statusIn(), { text: "running…", cls: "status running" });
uiStatus("failed", "error");
const failure = "error: the program exited with code 3";
uiFail(failure, "exit code 3");
check("a failure's lines", linesIn(), domShow(failure));
check("a failure keeps the status's text", (statusIn() || {}).text, "failed");

// The `#count` text stays the page's (the state is opaque, and a getter export would
// free the caller's state): pin the rule the page uses.
const countText = (raw) => {
  const lines = raw.split("\n").filter((l) => l !== "");
  const bad = lines.filter((l) => l.startsWith("error:") || l.startsWith("parse error")).length;
  return lines.length + (lines.length === 1 ? " line" : " lines") +
    (bad ? ` · ${bad} error${bad === 1 ? "" : "s"}` : "");
};
check("a two-line run's count", countText("ok\n3 : Nat"), "2 lines");
check("a run with errors counts them", countText("ok\nerror: x\nparse error at 1:1"), "3 lines · 2 errors");
check("an empty run's count", countText(""), "0 lines");

// ## Many transitions: a wrong reference count would corrupt the heap or trap here

for (let i = 0; i < 100; i++) {
  uiShow("ok\n" + i);
  uiStatus("done", "ready");
}
check("a hundred runs keep the pane right", linesIn(), domShow("ok\n99"));
check("a hundred runs keep the status right", (statusIn() || {}).text, "done");
check("the tree still serializes", serialize(root).includes('id="output"'), true);

console.log(failed === 0 ? "playground ui: all checks passed" : `playground ui: ${failed} failure(s)`);
process.exit(failed === 0 ? 0 : 1);
