// The whole playground page as a Loom app (web/playground-ui.wiz) — the page, not an
// option — mounted for real under Node: the module web/build-playground-ui.sh built is Emscripten's, web/framework/
// driver.js mounts its SSR into minidom and delegates events, and its `wiz_loom_*` entry
// points are the page's calls (a run's output, a failure, the status pair, Run's state,
// the footer, the editor's text). No browser and no engine: the engine is the page's
// other module.
//
//   node web/playground_ui_test.mjs OUT_DIR
"use strict";
import { pathToFileURL } from "node:url";
import { start } from "./framework/driver.js";
import { parse, serialize } from "./framework/minidom.mjs";
import { findPreset } from "./framework/examples.mjs";

const outDir = process.argv[2] || new URL("./out/", import.meta.url).pathname;
const createModule = (await import(pathToFileURL(outDir + "/wiz-playground-ui.mjs").href)).default;
const wasm = await createModule({ printErr: (s) => console.error(s) });
const big = (x) => (typeof x === "bigint" ? x : BigInt(x));   // wasm64: pointers are i64

let failed = 0;
const ok = (cond, what, detail = "") => {
  if (cond) console.log("ok: " + what);
  else { failed++; console.log("FAIL: " + what + (detail ? "\n  " + detail : "")); }
};
const check = (what, want, got) => ok(Object.is(got, want), what,
  `want ${JSON.stringify(want)}\n  got  ${JSON.stringify(got)}`);

// Call an entry point the way web/playground.js does: the state, then strings (allocated
// and freed here) and numbers; the module patches the DOM itself.
function call(name, ...args) {
  const pointers = [];
  const rest = args.map((a) => {
    if (typeof a === "string") { const p = wasm.stringToNewUTF8(a); pointers.push(p); return big(p); }
    return typeof a === "number" ? big(a) : a;
  });
  try {
    const next = wasm["_" + name](app.state(), ...rest);
    app.setState(next);
    return next;
  } finally {
    for (const p of pointers) wasm._free(p);
  }
}

function walk(node, pred, out = []) {
  if (pred(node)) out.push(node);
  for (const c of node.childNodes || []) walk(c, pred, out);
  return out;
}
const byId = (root, id) => walk(root, (n) => n.getAttribute && n.getAttribute("id") === id)[0];

// ## The mount
const root = parse("");
const app = start(wasm, root, { parse });
let html = serialize(root);
ok(html.includes("<header") && html.includes("<main") && html.includes("<footer"),
  "the whole page is the app: header, main and footer", html.slice(0, 200));
ok(byId(root, "editor") && byId(root, "run") && byId(root, "count"),
  "the editor pane is there (#editor, #run, #count)");
ok(byId(root, "goals") && byId(root, "output") && byId(root, "status") && byId(root, "engine"),
  "the goals container, the output pane, the status and the engine line are there");
ok(byId(root, "goals").getAttribute("aria-live") === "polite" &&
   byId(root, "output").getAttribute("aria-live") === "polite",
  "both panes keep aria-live");
ok(html.includes('class="goals"') && html.includes('class="output"'),
  "the panes keep their classes (web/playground.css)");
ok(html.includes("Ctrl/⌘+Enter runs"), "the editor's hint text is unchanged");
ok(byId(root, "preset") && byId(root, "preset").getAttribute("data-wiz-on-change") === "0",
  "the examples menu is in the page and is handler 0", html.slice(0, 300));
ok(walk(byId(root, "preset"), (n) => n.tagName === "option").length === 8,
  "the examples menu has the custom option and every example");
ok(html.includes("from <code>?lsp=ws://host:port</code>"),
  "the goals pane's hint text is unchanged", html);
ok(byId(root, "status").textContent === "loading the engine…", "the first paint's status");
ok(byId(root, "engine").textContent === "engine: loading", "the first paint's engine line");
ok(byId(root, "run").getAttribute("disabled") != null, "Run starts disabled");
ok(!html.includes("<script"), "the app's text is escaped");

// ## The editor's pure rules are read-only exports (`mount`'s `ask`)
function ask(name, ...args) {
  const pointers = [];
  const rest = args.map((a) => {
    const p = wasm.stringToNewUTF8(a);
    pointers.push(p);
    return big(p);
  });
  let result = 0;
  try {
    result = wasm["_" + name](...rest);
    return wasm.UTF8ToString(result);
  } finally {
    if (result) wasm._free(result);
    for (const p of pointers) wasm._free(p);
  }
}
const spans = JSON.parse(ask("wiz_loom_editor_segments", "def f : Nat := nope\n",
  '[{"range":{"start":{"line":0,"character":13},"end":{"line":0,"character":17}},"severity":1,"message":"m"}]', "0"));
ok(spans.length === 1 && spans[0].start === 13 && spans[0].stop === 17,
  "the runtime returns the squiggle spans", JSON.stringify(spans));
const position = JSON.parse(ask("wiz_loom_editor_position", "a😀b", "3"));
ok(position.line === 0 && position.character === 3, "the runtime returns a UTF-16 position",
  JSON.stringify(position));

// ## Tab: the key carries the selection, and the runtime asks for a host edit
const editorField = byId(root, "editor");
editorField.selectionStart = 1;
editorField.selectionEnd = 3;
editorField.dispatchEvent({ type: "keydown", key: "Tab" });
ok(JSON.parse(app.requests() || "[]").some((r) => r.kind === "edit"),
  "Tab asks the page for an edit", app.requests());
call("wiz_loom_effect", "ack", "edit", "");

// ## The editor: the driver's input payload reaches the app
const textarea = byId(root, "editor");
ok(textarea.getAttribute("data-wiz-on-input") === "6",
  "the textarea's input handler follows the toolbar's five handlers and keydown",
  textarea.getAttribute("data-wiz-on-input"));
textarea.value = "def one : Nat := 1";
textarea.dispatchEvent({ type: "input" });
ok(serialize(root).includes(">def one : Nat := 1</textarea>"),
  "an input event updates the textarea from its payload", serialize(root).slice(0, 400));

// ## A run: the output pane and the count
call("wiz_loom_effect", "finished", "ok\n3 : Nat", "done in 2 ms");
let out = byId(root, "output");
ok(out.textContent === "ok3 : Nat", "the output pane has the run's lines", out.textContent);
ok(byId(root, "count").textContent === "2 lines", "the count text is the page's",
  byId(root, "count").textContent);
ok(walk(out, (n) => n.getAttribute && (n.getAttribute("class") || "") === "line").length === 2,
  "one .line div per line");

// A value line: the friendly form, the raw text as its tooltip, and the class.
call("wiz_loom_effect", "finished", "con((#1, (con((#0, (tt, tt))), (tt, tt))))", "done in 2 ms");
out = byId(root, "output");
const valueLine = out.childNodes[0];
check("value: shown", "1", out.textContent);
check("value: class", "line val", valueLine.getAttribute("class"));
check("value: tooltip", "con((#1, (con((#0, (tt, tt))), (tt, tt))))", valueLine.getAttribute("title"));
ok(byId(root, "count").textContent === "1 line", "one value line counts as 1 line");

// ## A failure: the page's count text, and errors
call("wiz_loom_effect", "failed", "error: the engine exited with code 3", "exit code 3");
check("failure: count", "exit code 3", byId(root, "count").textContent);
ok(walk(byId(root, "output"), (n) => n.getAttribute &&
  (n.getAttribute("class") || "") === "line err").length === 1, "the failure line is `err`");

// ## The examples menu: a `change` step loads the runtime's example
const select = byId(root, "preset");
select.value = "lists";
select.dispatchEvent({ type: "change" });
check("the menu loads an example", findPreset("lists").code, byId(root, "editor").value);
check("the menu's selection moved", "lists",
  walk(select, (n) => n.getAttribute && n.getAttribute("selected") != null)
    .map((n) => n.getAttribute("value")).join(","));

// ## The request protocol: a step asks for effects; the page acks what it serviced
const pending = () => JSON.parse(app.requests() || "[]").map((r) => r.kind).join(",");
check("an input and a load request a sync and a run", "run,sync", pending());
call("wiz_loom_effect", "ack", "run", "");
check("acking run leaves the sync", "sync", pending());
call("wiz_loom_effect", "ack", "sync", "");
check("acking both leaves no request", "", pending());

// ## The status pair, Run's state, the footer, the text
call("wiz_loom_effect", "status", "done in 4 ms", "ready");
check("status: text", "done in 4 ms", byId(root, "status").textContent);
check("status: kind", "status ready", byId(root, "status").getAttribute("class"));
call("wiz_loom_effect", "status", "running…", "running");
check("status: running", "status running", byId(root, "status").getAttribute("class"));
call("wiz_loom_effect", "enable", "1", "");
ok(byId(root, "run").getAttribute("disabled") == null, "the page enables Run");
call("wiz_loom_effect", "enable", "0", "");
ok(byId(root, "run").getAttribute("disabled") != null, "and disables it again");
call("wiz_loom_effect", "engine", "engine: ready", "");
check("engine: the footer", "engine: ready", byId(root, "engine").textContent);
call("wiz_loom_effect", "text", "sample", "");
ok(serialize(root).includes(">sample</textarea>"), "the page can replace the editor's text");
ok(byId(root, "editor").value === "sample",
  "a textarea's text patch sets its live value too (the runtime's text op)", byId(root, "editor").value);

console.log(failed === 0 ? "playground ui: all checks passed" : `playground ui: ${failed} failure(s)`);
process.exit(failed === 0 ? 0 : 1);
