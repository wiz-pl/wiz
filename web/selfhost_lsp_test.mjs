// `?lsp=selfhost`: the playground's in-page language server (web/selfhost-lsp-shim.js)
// under Node, with a stub engine in place of the Wasm module, so the test needs no Wiz
// build, no browser and no socket.
//
//   usage: node web/selfhost_lsp_test.mjs
//
// Covers: selecting the server from the query string, splitting a source into
// commands, the engine's lines as diagnostics (one per command, a parse error at its
// offset in UTF-16, the added Prelude line, output that does not line up), the
// handshake through `LspClient`, didOpen/didChange → publishDiagnostics (and
// `wiz/elaborated`), the plain fallback answering "nothing at the cursor", completion,
// hover and definition from the check's declaration index (with their `textEdit`, Markdown
// and `Location` shapes), an engine that loads late or fails, the page's wiring
// (`startInfoview` with a stub textarea), and no unhandled rejection anywhere.
"use strict";
import {
  isSelfhostSearch, wantsSelfhost, withPrelude, splitCommands, diagnosticsFromOutput, outputLines,
  parseErrorOffset, utf16OfCodePoints, positionOf, selfhostSocketClass, selfhostEndpoint,
  SelfhostServer, SELFHOST_URL, parseCheck, diagnosticsFromCheck, PositionIndex, offsetOf,
  completionPrefix, filterCompletions, splitGoals, wordAt,
} from "./selfhost-lsp-shim.js";
import { LspClient, LspError } from "./lsp-client.js";
import { readGoalState, renderPanel } from "./goals.js";
import { startInfoview } from "./playground-lsp.js";
import { document as minidoc } from "./framework/minidom.mjs";

let failed = 0;
function check(name, got, want) {
  const same = typeof want === "object" ? JSON.stringify(got) === JSON.stringify(want) : Object.is(got, want);
  if (same) {
    console.log(`ok: ${name}`);
  } else {
    failed++;
    console.log(`FAIL: ${name}\n  want: ${JSON.stringify(want)}\n  got:  ${JSON.stringify(got)}`);
  }
}
function checkThat(name, condition, detail) {
  if (condition) {
    console.log(`ok: ${name}`);
  } else {
    failed++;
    console.log(`FAIL: ${name}${detail ? "\n  " + detail : ""}`);
  }
}
const sleep = (ms) => new Promise((resolve) => setTimeout(resolve, ms));
const rejections = [];
process.on("unhandledRejection", (reason) => rejections.push(reason));

function waitFor(client, type, predicate = () => true, ms = 3000) {
  return new Promise((resolve, reject) => {
    let off = null;
    const timer = setTimeout(() => { if (off) off(); reject(new Error(`timed out waiting for ${type}`)); }, ms);
    off = client.on(type, (payload) => {
      let ok = false;
      try { ok = predicate(payload); } catch (_) { ok = false; }
      if (!ok) return;
      clearTimeout(timer);
      off();
      resolve(payload);
    });
  });
}

// ## The stub engine: `wiz_playground_eval`'s output shape, written independently of the
// shim's splitter. One line per column-0 `def`/`theorem`/`#check`/`#eval` (`error: …`
// when the line says BAD), none for `import`/`notation`, and `parse error N: …` at the
// first `@@` (N in code points, as `String.codes` counts), after which nothing runs.
function stubEval(source) {
  const out = [];
  let offset = 0;   // UTF-16
  for (const line of source.split("\n")) {
    const at = line.indexOf("@@");
    if (at >= 0) {
      const cp = Array.from(source.slice(0, offset + at)).length;
      out.push(`parse error ${cp}: unexpected token '@@'`);
      break;
    }
    const m = /^(def|theorem) (\S+)/.exec(line);
    if (m) out.push(line.includes("BAD") ? "error: unknown identifier 'BAD'" : `${m[2]} : Nat`);
    else if (/^#check /.test(line)) out.push(line.includes("BAD") ? "error: unknown identifier 'BAD'" : "twice : Nat → Nat");
    else if (/^#eval /.test(line)) out.push("42");
    offset += line.length + 1;
  }
  return out.map((l) => l + "\n").join("");
}
let evaluated = 0;
const countingEval = (src) => { evaluated++; return stubEval(src); };

// ## 1. Selecting the server

check("search: ?lsp=selfhost", isSelfhostSearch("?lsp=selfhost"), true);
check("search: any case, with a token", isSelfhostSearch("?lsp=SelfHost&token=x"), true);
check("search: a ws endpoint is not it", isSelfhostSearch("?lsp=ws://127.0.0.1:8765"), false);
check("default: no lsp parameter is the in-page server", wantsSelfhost(""), true);
check("default: an unrelated parameter is still the in-page server", wantsSelfhost("?token=x"), true);
check("default: ?lsp=selfhost names it", wantsSelfhost("?lsp=SelfHost"), true);
check("default: ?lsp=off disables it", wantsSelfhost("?lsp=off"), false);
check("default: ?lsp=none disables it", wantsSelfhost("?lsp=none"), false);
check("default: a port keeps the external client", wantsSelfhost("?lsp=8765"), false);
check("default: a ws url keeps the external client", wantsSelfhost("?lsp=ws://127.0.0.1:8765"), false);
check("search: nothing", isSelfhostSearch(""), false);
check("endpoint: the url", selfhostEndpoint({ evaluate: stubEval }).url, SELFHOST_URL);
check("endpoint: a WebSocketImpl", typeof selfhostEndpoint({ evaluate: stubEval }).WebSocketImpl, "function");

// ## 2. Positions and the Prelude

check("prelude: added without an import", withPrelude("def a : Nat := 1").prefix, "import Prelude\n\n");
check("prelude: kept with one", withPrelude("import Prelude\ndef a : Nat := 1").prefix, "");
check("position: line and character", positionOf("ab\ncd", 4), { line: 1, character: 1 });
check("code points: an emoji is two UTF-16 units", utf16OfCodePoints("a😀b", 2), 3);
check("parse error offset", parseErrorOffset("parse error 57: unexpected"), 57);
check("output: an empty line is a line", outputLines("a\n\nb\n"), ["a", "", "b"]);

// ## 3. Commands

const SOURCE = `import Prelude
-- a comment
/-- doc -/
def twice (n : Nat) : Nat := n + n

@[simp]
theorem t : Nat := 0
def f : Nat → Nat
| 0 => 1
| _ => 2
/- a block
def notACommand : Nat := 0
-/
notation "⊕" => Nat.add
mutual
def even : Nat → Bool := fun _ => .true
def odd : Nat → Bool := fun _ => .false
end
#check twice
#eval twice 21
`;
const commands = splitCommands(SOURCE);
check("split: keywords", commands.map((c) => c.keyword), ["import", "def", "theorem", "def", "notation", "mutual", "#check", "#eval"]);
check("split: silent ones", commands.filter((c) => c.silent).map((c) => c.keyword), ["import", "notation"]);
check("split: a doc comment belongs to its command", SOURCE.slice(commands[1].start, commands[1].start + 3), "/--");
check("split: the head is the keyword line", SOURCE.slice(commands[1].head, commands[1].head + 3), "def");
check("split: an attribute belongs to its command", SOURCE.slice(commands[2].start, commands[2].start + 2), "@[");
check("split: results", commands.filter((c) => c.result).map((c) => c.keyword), ["#check", "#eval"]);

// ## 4. Lines as diagnostics

{
  // aligned: def, theorem, def, mutual, #check, #eval → six lines
  const out = ["twice : Nat → Nat", "t : Nat", "error: unknown identifier 'g'", "", "twice : Nat → Nat", "42"]
    .map((l) => l + "\n").join("");
  const ds = diagnosticsFromOutput(SOURCE, out);
  check("diagnostics: one error and two results", ds.map((d) => d.severity), [1, 3, 3]);
  check("diagnostics: the error's message", ds[0].message, "unknown identifier 'g'");
  check("diagnostics: on its command's line", ds[0].range, { start: { line: 7, character: 0 }, end: { line: 7, character: 17 } });
  check("diagnostics: #eval's value", ds[2].message, "42");
  check("diagnostics: #eval's line", ds[2].range.start.line, 19);
}
{
  // the playground adds the Prelude line: a parse error's offset is moved back, and an
  // astral character before it counts one code point but two UTF-16 units
  const text = "def a : Nat := 1\n-- 😀\ndef b : Nat := @@ 2\n";
  const ds = diagnosticsFromOutput(text, stubEval(withPrelude(text).source));
  check("parse error: one diagnostic (the def before it prints a signature)", ds.length, 1);
  check("parse error: the code", ds[0].code, "parse-error");
  check("parse error: at the token", ds[0].range, { start: { line: 2, character: 15 }, end: { line: 2, character: 17 } });
  check("parse error: the message", ds[0].message, "parse error: unexpected token '@@'");
}
{
  const ds = diagnosticsFromOutput("def a : Nat := 1\n", "error: one\nerror: two\n");
  check("misaligned: both reported", ds.length, 2);
  check("misaligned: at the top", ds[0].range.start, { line: 0, character: 0 });
  checkThat("misaligned: says so", ds[0].message.includes("position unknown"), ds[0].message);
}
check("clean: no diagnostics", diagnosticsFromOutput("def a : Nat := 1\n", "a : Nat\n").length, 0);

// ## 5. The server through the real client

const uri = "file:///playground-test.wiz";
const client = new LspClient({ url: SELFHOST_URL, WebSocketImpl: selfhostSocketClass({ evaluate: countingEval }), requestTimeout: 2000 });
const elaborated = [];
client.on("wiz/elaborated", (p) => elaborated.push(p));
await client.connect();
check("handshake: open", client.state, "open");
check("handshake: serverInfo", client.serverInfo && client.serverInfo.name, "wiz-selfhost");
check("handshake: the infoview tag", client.infoview && client.infoview.version, 1);
check("handshake: the methods", client.infoview && client.infoview.methods, ["wiz/plainGoal", "wiz/plainTermGoal"]);
check("handshake: full sync", client.capabilities.textDocumentSync, 1);
check("handshake: utf-16", client.capabilities.positionEncoding, "utf-16");

const firstText = "def twice (n : Nat) : Nat := n + n\n#eval twice 21\n";
const first = waitFor(client, "diagnostics", (p) => p.uri === uri);
client.openDocument(uri, firstText);
const opened = await first;
check("didOpen: diagnostics published", opened.diagnostics.map((d) => [d.severity, d.message]), [[3, "42"]]);
check("didOpen: one evaluation", evaluated, 1);
await sleep(10);
check("didOpen: wiz/elaborated", elaborated.length, 1);

const second = waitFor(client, "diagnostics", (p) => p.uri === uri);
client.changeDocument(uri, "def twice (n : Nat) : Nat := n + n\n#check BAD\n");
const changed = await second;
check("didChange: the error", changed.diagnostics.map((d) => d.message), ["unknown identifier 'BAD'"]);
check("didChange: its range", changed.diagnostics[0].range.start, { line: 1, character: 0 });
check("didChange: the version", changed.version, 2);
await sleep(10);
check("didChange: a new session", elaborated.length === 2 && elaborated[1].session > elaborated[0].session, true);

let notFound = null;
try { await client.interactiveGoals(uri, { line: 0, character: 4 }); } catch (e) { notFound = e; }
check("interactiveGoals: MethodNotFound", notFound instanceof LspError ? notFound.code : String(notFound), -32601);
check("plainGoal: nothing at the cursor", await client.plainGoal(uri, { line: 0, character: 4 }), null);
check("plainTermGoal: nothing at the cursor", await client.plainTermGoal(uri, { line: 0, character: 4 }), null);
let notOpen = null;
try { await client.plainGoal("file:///other.wiz", { line: 0, character: 0 }); } catch (e) { notOpen = e; }
check("plainGoal: an unopened document", notOpen instanceof LspError ? notOpen.code : String(notOpen), -32602);
check("hover: null", await client.request("textDocument/hover", { textDocument: { uri }, position: { line: 0, character: 0 } }), null);
check("definition: null", await client.request("textDocument/definition", { textDocument: { uri }, position: { line: 0, character: 0 } }), null);
let unknown = null;
try { await client.request("wiz/frobnicate", {}); } catch (e) { unknown = e; }
check("an unknown request: MethodNotFound", unknown && unknown.code, -32601);

const state = await readGoalState(client, uri, { line: 0, character: 4 });
check("readGoalState: the plain path", [state.goalsKind, state.termKind], ["plain", "plain"]);
const panel = { innerHTML: "" };
renderPanel(panel, {
  state: "open", endpoint: SELFHOST_URL, serverInfo: client.serverInfo, infoview: client.infoview,
  diagnostics: changed.diagnostics, goals: state.goals, goalsKind: state.goalsKind,
  term: state.term, termKind: state.termKind, info: null,
});
checkThat("panel: the server's name", panel.innerHTML.includes("wiz-selfhost"));
checkThat("panel: the diagnostic", panel.innerHTML.includes("unknown identifier"));
checkThat("panel: nothing at the cursor", panel.innerHTML.includes("nothing at the cursor"), panel.innerHTML.slice(0, 400));

client.closeDocument(uri);
client.close();
check("close: closed", client.state, "closed");
let afterClose = null;
try { await client.plainGoal(uri, { line: 0, character: 0 }); } catch (e) { afterClose = e; }
check("close: a request rejects", afterClose instanceof LspError, true);
const reopened = waitFor(client, "diagnostics", (p) => p.uri === uri);
client.openDocument(uri, firstText);
await client.reconnect();
check("reconnect: open", client.state, "open");
check("reconnect: the document again", (await reopened).diagnostics.length, 1);
client.close();

// ## 6. An engine that loads late, and one that fails

{
  let release;
  const loaded = new Promise((resolve) => { release = resolve; });
  const late = new LspClient({ url: SELFHOST_URL, WebSocketImpl: selfhostSocketClass({ evaluate: (s) => loaded.then(() => stubEval(s)) }) });
  const t0 = Date.now();
  await late.connect();
  checkThat("late engine: the handshake does not wait for it", Date.now() - t0 < 500);
  const got = waitFor(late, "diagnostics");
  late.openDocument(uri, "def a : Nat := BAD\n");
  await sleep(30);
  check("late engine: no diagnostics before it loads", late.diagnostics.has(uri), false);
  release();
  check("late engine: then the error", (await got).diagnostics.map((d) => d.message), ["unknown identifier 'BAD'"]);
  late.close();
}
{
  const broken = new LspClient({ url: SELFHOST_URL, WebSocketImpl: selfhostSocketClass({ evaluate: () => Promise.reject(new Error("no wasm")) }) });
  await broken.connect();
  const got = waitFor(broken, "diagnostics");
  broken.openDocument(uri, "def a : Nat := 1\n");
  const ds = (await got).diagnostics;
  checkThat("failed engine: one error that says why", ds.length === 1 && ds[0].message.includes("no wasm"), JSON.stringify(ds));
  broken.close();
}
{
  // the handler shape of the planned `wiz_lsp_handle`: text in, messages out
  const server = new SelfhostServer({ evaluate: stubEval });
  const out = await server.handle('[{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}},' +
    '{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"u","version":1,"text":"def a : Nat := BAD\\n"}}}]');
  check("handle: a batch answers in order", out.map((m) => m.id !== undefined ? "result" : m.method), ["result", "textDocument/publishDiagnostics"]);
  check("handle: not JSON", (await server.handle("{"))[0].error.code, -32700);
}

// ## 7. The page's wiring (`startInfoview` with the endpoint, as playground.js does)

function fakeEditor(value) {
  return {
    value, selectionStart: 0, selectionEnd: 0, scrollTop: 0, clientHeight: 200, listeners: {},
    addEventListener(type, fn) { (this.listeners[type] || (this.listeners[type] = [])).push(fn); },
    focus() {},
    setSelectionRange(start, end) { this.selectionStart = start; this.selectionEnd = end; },
  };
}
function fakePanel() {
  return {
    innerHTML: "", scrollTop: 0, listeners: {},
    addEventListener(type, fn) { (this.listeners[type] || (this.listeners[type] = [])).push(fn); },
    querySelectorAll() { return []; },
  };
}
// The DOM the squiggle overlay needs (minidom's elements plus a body).
function fakeDocument() {
  const base = minidoc();
  return {
    body: base.createElement("body"),
    createElement: base.createElement,
    createTextNode: base.createTextNode,
    createRange: base.createRange,
    defaultView: { Event: class FakeEvent { constructor(type) { this.type = type; } } },
  };
}
async function waitUntil(predicate, ms = 3000) {
  const deadline = Date.now() + ms;
  while (Date.now() < deadline) {
    if (predicate()) return true;
    await sleep(20);
  }
  return false;
}
{
  const editor = fakeEditor("def twice (n : Nat) : Nat := n + n\n#eval twice 21\n");
  const wire = fakePanel();
  const app = startInfoview({
    editor, panel: wire, config: selfhostEndpoint({ evaluate: stubEval }), uri: "file:///wire.wiz",
    document: fakeDocument(),
  });
  checkThat("wiring: connected", await waitUntil(() => wire.innerHTML.includes("connected")), wire.innerHTML.slice(0, 300));
  checkThat("wiring: the #eval result", await waitUntil(() => wire.innerHTML.includes("42")));
  editor.value = "def twice (n : Nat) : Nat := BAD\n";
  for (const fn of editor.listeners.input || []) fn();
  checkThat("wiring: an edit's error", await waitUntil(() => wire.innerHTML.includes("unknown identifier")), wire.innerHTML.slice(0, 600));
  checkThat("wiring: on line 1", wire.innerHTML.includes('data-span="0:0-0:'));
  // The in-page server's diagnostics reach the editor's squiggle layer too.
  checkThat("wiring: the error is underlined", !!app.squiggles() && app.squiggles().segments().length === 1,
    JSON.stringify(app.squiggles() && app.squiggles().segments()));
  app.stop();
}

// ## 8. Stage 1: `wiz_playground_check`'s JSON, and the position index

// The stub of the export (web/playground-exports.wiz): stubEval's lines, each tagged with
// its command's code-point offset, as `{"v":1,"lines":[{"off","sev","text"}]}`; `extra`
// is merged in (an `index`, say).
function stubCheck(source, extra = {}) {
  const lines = [];
  let offset = 0;   // UTF-16
  const cp = (o) => Array.from(source.slice(0, o)).length;
  for (const line of source.split("\n")) {
    const at = line.indexOf("@@");
    if (at >= 0) {
      lines.push({ off: cp(offset), sev: 1, text: `parse error ${cp(offset + at)}: unexpected token '@@'` });
      break;
    }
    const one = stubEval(line + "\n").replace(/\n$/, "");
    if (/^(def|theorem|#check|#eval) /.test(line)) {
      lines.push({ off: cp(offset), sev: one.startsWith("error:") ? 1 : 3, text: one });
    }
    offset += line.length + 1;
  }
  return JSON.stringify(Object.assign({ v: 1, lines }, extra));
}

check("check: garbage is not an answer", parseCheck("{"), null);
check("check: an old module's null", parseCheck(null), null);
check("check: no lines", parseCheck('{"v":1}'), null);
{
  const text = "-- 😀\ndef a : Nat := BAD\n#eval a\ndef b : Nat := @@\n";
  const ds = diagnosticsFromCheck(text, parseCheck(stubCheck(withPrelude(text).source)));
  check("check: error, result, parse error", ds.map((d) => d.severity), [1, 3, 1]);
  check("check: the error on its command (after an astral character)", ds[0].range,
    { start: { line: 1, character: 0 }, end: { line: 1, character: 18 } });
  check("check: the result's line", ds[1].range.start.line, 2);
  check("check: the parse error at its token", ds[2].range.start, { line: 3, character: 15 });
  check("check: the parse error's code", ds[2].code, "parse-error");
}
{
  // a tactic error spans lines; a line without a tag still reports
  const answer = parseCheck(JSON.stringify({ v: 1, lines: [
    { off: 16, sev: 1, text: "error: unsolved goals:\nn : Nat\n⊢ Nat" },
    { off: null, sev: 1, text: "error: cannot find module X" },
  ] }));
  const ds = diagnosticsFromCheck("def k : Nat → Nat := by\n  intro n\n", answer);
  check("check: a multi-line message is one diagnostic", ds[0].message, "unsolved goals:\nn : Nat\n⊢ Nat");
  check("check: at its command (the Prelude line subtracted)", ds[0].range.start, { line: 0, character: 0 });
  checkThat("check: an untagged line says so", ds[1].message.includes("position unknown"));
}
{
  // offsets are into the checked source: the Prelude line (16 code points) comes first
  const text = "def f (n : Nat) : Nat := g n\n";
  const p = withPrelude(text).prefix.length;
  const index = new PositionIndex(text, [
    { s: p + 0, e: p + 28, kind: "term", expected: "Nat → Nat" },
    { s: p + 25, e: p + 28, kind: "term", expected: "Nat" },
    { s: p + 27, e: p + 28, kind: "term", expected: "Nat (n)" },
    { s: p + 25, e: p + 28, kind: "goal", goals: ["n : Nat\n⊢ Nat"] },
    { s: p + 0, e: p + 3, kind: "goal", goals: [] },
    { s: 5, e: 2, kind: "term", expected: "bad: ends before it starts" },
  ]);
  check("index: well-formed entries kept", index.size, 5);
  check("index: the innermost term", index.termGoal(27).goal, "Nat (n)");
  check("index: the enclosing one", index.termGoal(26).goal, "Nat");
  check("index: its range", index.termGoal(26).range, { start: { line: 0, character: 25 }, end: { line: 0, character: 28 } });
  check("index: the caret at an end counts", index.termGoal(28).goal, "Nat (n)");
  check("index: outside everything", index.termGoal(29), null);
  check("index: goals", index.goal(26).goals, ["n : Nat\n⊢ Nat"]);
  check("index: goals rendered as a fence", index.goal(26).rendered, "```wiz\nn : Nat\n⊢ Nat\n```");
  check("index: a finished proof", index.goal(1).rendered, "no goals");
  check("offsetOf: line and character", offsetOf("ab\ncd\n", { line: 1, character: 1 }), 4);
  check("offsetOf: clamped to the line", offsetOf("ab\ncd\n", { line: 0, character: 9 }), 2);
}
{
  // a module without the export: check answers null and the text path is used
  let evals = 0;
  const server = new SelfhostServer({ evaluate: (s) => { evals++; return stubEval(s); }, check: () => null });
  await server.handle('{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}');
  const out = await server.handle(JSON.stringify({ jsonrpc: "2.0", method: "textDocument/didOpen",
    params: { textDocument: { uri: "u", version: 1, text: "def a : Nat := BAD\n" } } }));
  check("fallback: evaluate was used", evals, 1);
  check("fallback: its diagnostic", out[0].params.diagnostics.map((d) => d.message), ["unknown identifier 'BAD'"]);
}
{
  // the export with an index, through the client and the panel
  const text = "def k (n : Nat) : Nat := n\n#eval k 2\n";
  const p = withPrelude(text).prefix.length;
  let evals = 0;
  const index = [
    { s: p + 25, e: p + 26, kind: "term", expected: "Nat" },
    { s: p + 25, e: p + 26, kind: "goal", goals: ["n : Nat\n⊢ Nat"] },
  ];
  const c2 = new LspClient({ url: SELFHOST_URL, WebSocketImpl: selfhostSocketClass({
    evaluate: (s) => { evals++; return stubEval(s); },
    // the index belongs to the first text only; a new text's check has none
    check: (s) => Promise.resolve(stubCheck(s, s.includes(":= n\n") ? { index } : {})),
  }) });
  await c2.connect();
  const got = waitFor(c2, "diagnostics");
  c2.openDocument(uri, text);
  check("export: the result diagnostic", (await got).diagnostics.map((d) => [d.severity, d.message, d.range.start.line]), [[3, "42", 1]]);
  check("export: evaluate not called", evals, 0);
  check("export: plainTermGoal from the index", await c2.plainTermGoal(uri, { line: 0, character: 25 }),
    { goal: "Nat", range: { start: { line: 0, character: 25 }, end: { line: 0, character: 26 } } });
  check("export: nothing elsewhere", await c2.plainTermGoal(uri, { line: 1, character: 2 }), null);
  const st = await readGoalState(c2, uri, { line: 0, character: 25 });
  const p2 = { innerHTML: "" };
  renderPanel(p2, { state: "open", endpoint: SELFHOST_URL, diagnostics: [], goals: st.goals, goalsKind: st.goalsKind,
    term: st.term, termKind: st.termKind, info: null });
  checkThat("export: the panel shows the goal", p2.innerHTML.includes("⊢ Nat") && p2.innerHTML.includes("n : Nat"), p2.innerHTML.slice(0, 500));
  checkThat("export: and the expected type's span", p2.innerHTML.includes('data-span="0:25-0:26"'));
  const changed2 = waitFor(c2, "diagnostics");
  c2.changeDocument(uri, "def k (n : Nat) : Nat := BAD\n");
  await changed2;
  check("export: a new check replaces the index", await c2.plainTermGoal(uri, { line: 0, character: 25 }), null);
  c2.close();
}

// ## 9. Completion, hover and definition (`textDocument/*` from the declaration index)

// The index of a module's declarations: `{s,e,kind:"decl",name,detail,ckind}` in the
// checked source (the Prelude line included), as `wiz_playground_check` emits them.
function declCheck(source, decls, extra = {}) {
  // the client passes the checked source, so the added Prelude is already in it
  const p = source.startsWith("import Prelude\n\n") ? "import Prelude\n\n".length : 0;
  const index = decls.map((d) => ({
    s: p + d.s, e: p + d.e, kind: "decl", name: d.name, detail: d.detail, ckind: d.kind,
  }));
  return stubCheck(source, Object.assign({ index }, extra));
}

const DECLS = [
  { name: "twice", detail: "(n : Nat) → Nat", kind: 3, s: 4, e: 9 },
  { name: "pred", detail: "Nat → Nat", kind: 3, s: 39, e: 43 },
  { name: "MyType", detail: "Type", kind: 7, s: 75, e: 81 },
];
const DECL_TEXT = "def twice (n : Nat) : Nat := n + n\n" +
  "def pred (n : Nat) : Nat := n\n" +
  "inductive MyType where\n" +
  "  | mk\n" +
  "#eval twice";

const declarations = [
  { label: "twice", kind: 3, detail: "(n : Nat) → Nat", range: { start: { line: 0, character: 4 }, end: { line: 0, character: 9 } } },
  { label: "pred", kind: 3, detail: "Nat → Nat", range: { start: { line: 0, character: 39 }, end: { line: 0, character: 43 } } },
  { label: "MyType", kind: 7, detail: "Type", range: { start: { line: 0, character: 75 }, end: { line: 0, character: 81 } } },
];

check("prefix: after an identifier", completionPrefix("x := tw", 7), { start: 5, prefix: "tw" });
check("prefix: a dotted name", completionPrefix("Nat.ad", 6).prefix, "Nat.ad");
check("prefix: after a space", completionPrefix("= ", 2), { start: 2, prefix: "" });
check("prefix: at the start", completionPrefix("twice", 0).prefix, "");
check("word: at a name", wordAt("def twice (n : Nat)", 6), { start: 4, end: 9, word: "twice" });
check("word: just after it", wordAt("def twice (n : Nat)", 9).word, "twice");
check("word: a dotted name", wordAt("Nat.add", 4).word, "Nat.add");
check("word: on a space", wordAt("   ", 1).word, "");
check("filter: the prefix", filterCompletions(declarations, "tw").map((n) => n.label), ["twice"]);
check("filter: case-insensitive", filterCompletions(declarations, "MY").map((n) => n.label), ["MyType"]);
check("filter: dotted", filterCompletions(declarations, "Nat.").map((n) => n.label), []);
check("filter: no match", filterCompletions(declarations, "zz"), []);
check("filter: an empty prefix keeps the order", filterCompletions(declarations, "").map((n) => n.label),
  ["twice", "pred", "MyType"]);
check("filter: the detail survives", filterCompletions(declarations, "tw")[0].detail, "(n : Nat) → Nat");
check("filter: a cap", filterCompletions(declarations, "", 2).length, 2);
{
  // the handshake advertises all three, and the answers come from the index
  const c3 = new LspClient({ url: SELFHOST_URL, WebSocketImpl: selfhostSocketClass({
    evaluate: stubEval, check: (s) => declCheck(s, DECLS)
  }) });
  await c3.connect();
  const caps = c3.capabilities || {};
  checkThat("completion: advertised", (caps.completionProvider || {}).triggerCharacters !== undefined,
    JSON.stringify(caps));
  check("hover: advertised", caps.hoverProvider, true);
  check("definition: advertised", caps.definitionProvider, true);
  const got = waitFor(c3, "diagnostics");
  c3.openDocument(uri, DECL_TEXT);
  await got;

  const answer = await c3.completion(uri, { line: 4, character: 8 });
  check("completion: isIncomplete", answer.isIncomplete, false);
  check("completion: the prefix", answer.items.map((i) => i.label), ["twice"]);
  check("completion: the kind and detail", [answer.items[0].kind, answer.items[0].detail], [3, "(n : Nat) → Nat"]);
  check("completion: a textEdit over the prefix", answer.items[0].textEdit,
    { range: { start: { line: 4, character: 6 }, end: { line: 4, character: 8 } }, newText: "twice" });
  const empty = await c3.completion(uri, { line: 4, character: 6 });
  check("completion: an empty prefix lists them all", empty.items.map((i) => i.label),
    ["twice", "pred", "MyType"]);
  check("completion: none for an unknown prefix", (await c3.completion(uri, { line: 4, character: 3 })).items, []);

  check("hover: a declaration's signature", await c3.request("textDocument/hover", { textDocument: { uri }, position: { line: 4, character: 10 } }), {
    contents: { kind: "markdown", value: "```wiz\ntwice : (n : Nat) → Nat\n```" },
    range: { start: { line: 0, character: 4 }, end: { line: 0, character: 9 } },
  });
  check("hover: on the declaration itself", (await c3.request("textDocument/hover", { textDocument: { uri }, position: { line: 0, character: 6 } })).contents.value,
    "```wiz\ntwice : (n : Nat) → Nat\n```");
  check("hover: an unknown name is null", await c3.request("textDocument/hover", { textDocument: { uri }, position: { line: 4, character: 4 } }), null);
  check("definition: the declaration's Location", await c3.request("textDocument/definition", { textDocument: { uri }, position: { line: 4, character: 10 } }), {
    uri, range: { start: { line: 0, character: 4 }, end: { line: 0, character: 9 } },
  });
  check("definition: another declaration's Location", (await c3.request("textDocument/definition", { textDocument: { uri }, position: { line: 1, character: 6 } })).range,
    { start: { line: 1, character: 4 }, end: { line: 1, character: 8 } });
  check("definition: an unknown name is null", await c3.request("textDocument/definition", { textDocument: { uri }, position: { line: 4, character: 4 } }), null);
  c3.close();
}
{
  // a constructor is used after a dot; the index has its full name
  const text = "inductive Box where\n  | mk\ndef b : Box := Box.mk\n";
  const decls = [
    { name: "Box", detail: "Type", kind: 7, s: 10, e: 13 },
    { name: "Box.mk", detail: "Box", kind: 3, s: 24, e: 26 },
  ];
  const c4 = new LspClient({ url: SELFHOST_URL, WebSocketImpl: selfhostSocketClass({
    evaluate: stubEval, check: (s) => declCheck(s, decls),
  }) });
  await c4.connect();
  const got4 = waitFor(c4, "diagnostics");
  c4.openDocument(uri, text);
  await got4;
  check("definition: a constructor's suffix", (await c4.request("textDocument/definition", { textDocument: { uri }, position: { line: 2, character: 20 } })).range,
    { start: { line: 1, character: 4 }, end: { line: 1, character: 6 } });
  check("completion: a constructor's full name", (await c4.completion(uri, { line: 2, character: 21 })).items.map((i) => i.label),
    ["Box.mk"]);
  c4.close();
}
{
  // a module without the export: empty lists and nulls, never an error
  const server = new SelfhostServer({ evaluate: stubEval });
  check("completion: no check is an empty list",
    (await server.handle('{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}'))[0].result
      .capabilities.completionProvider !== undefined, true);
  await server.handle(JSON.stringify({ jsonrpc: "2.0", method: "textDocument/didOpen",
    params: { textDocument: { uri: "u", version: 1, text: "def a : Nat := 1\n" } } }));
  const out = await server.handle('{"jsonrpc":"2.0","id":2,"method":"textDocument/completion",' +
    '"params":{"textDocument":{"uri":"u"},"position":{"line":0,"character":4}}}');
  check("completion: no index, no items", [out[0].result.isIncomplete, out[0].result.items], [false, []]);
  const hov = await server.handle('{"jsonrpc":"2.0","id":3,"method":"textDocument/hover",' +
    '"params":{"textDocument":{"uri":"u"},"position":{"line":0,"character":4}}}');
  check("hover: no index is null", hov[0].result, null);
  const def = await server.handle('{"jsonrpc":"2.0","id":4,"method":"textDocument/definition",' +
    '"params":{"textDocument":{"uri":"u"},"position":{"line":0,"character":4}}}');
  check("definition: no index is null", def[0].result, null);
  // before the handshake an unknown method is still refused, and an unopened document is
  // an invalid parameter (not a crash)
  const fresh = new SelfhostServer({ evaluate: stubEval });
  const unknown = await fresh.handle('{"jsonrpc":"2.0","id":5,"method":"wiz/frobnicate","params":{}}');
  check("before initialize: an unknown method", unknown[0].error.code, -32601);
  const closed = await fresh.handle('{"jsonrpc":"2.0","id":6,"method":"textDocument/completion",' +
    '"params":{"textDocument":{"uri":"nope"},"position":{"line":0,"character":0}}}');
  check("before initialize: an unopened document", closed[0].error.code, -32602);
}
// ## 10. Stage 3: tactic states in the index (`wiz/plainGoal`)

check("goals: two blocks", splitGoals("a : Nat\n⊢ Nat\n\nb : Bool\n⊢ Bool"),
  ["a : Nat\n⊢ Nat", "b : Bool\n⊢ Bool"]);
check("goals: a finished proof", splitGoals("no goals"), []);
check("goals: nothing", splitGoals(""), []);
{
  // an index with the states a `by` block records: one per step, the block's end, and
  // the expected types beside them (the shapes `wiz_playground_check` emits)
  const text = "def f (n : Nat) : Nat := n + n\n";
  const p = withPrelude(text).prefix.length;
  const body = text.indexOf("n + n");               // 24
  const second = text.lastIndexOf("n");             // 28
  const index = [
    { s: p + body, e: p + body + 5, kind: "term", expected: "Nat" },
    { s: p + body, e: p + body + 1, kind: "term", expected: "Nat" },
    { s: p + second, e: p + second + 1, kind: "term", expected: "Nat" },
    { s: p + body, e: p + body + 5, kind: "goal", goals: ["n : Nat\n⊢ Nat"] },
    { s: p + body, e: p + second + 1, kind: "goal", goals: ["n : Nat\n⊢ Nat\n\nm : Nat\n⊢ Nat"] },
    { s: p + second + 1, e: p + second + 1, kind: "goal", goals: [] },
  ];
  const c5 = new LspClient({ url: SELFHOST_URL, WebSocketImpl: selfhostSocketClass({
    evaluate: stubEval, check: (src) => Promise.resolve(stubCheck(src, { index })),
  }) });
  await c5.connect();
  const got5 = waitFor(c5, "diagnostics");
  c5.openDocument(uri, text);
  await got5;
  check("goals: the innermost step", await c5.plainGoal(uri, { line: 0, character: body + 1 }),
    { goals: ["n : Nat\n⊢ Nat", "m : Nat\n⊢ Nat"], rendered: "```wiz\nn : Nat\n⊢ Nat\n\nm : Nat\n⊢ Nat\n```",
      range: { start: { line: 0, character: body }, end: { line: 0, character: second + 1 } } });
  check("goals: at the body's end, the finished proof", (await c5.plainGoal(uri, { line: 0, character: second + 1 })).goals, []);
  check("goals: outside it is null", await c5.plainGoal(uri, { line: 0, character: 0 }), null);
  // the expected type at the same carets
  check("term: the second n", (await c5.plainTermGoal(uri, { line: 0, character: second })).goal, "Nat");
  check("term: the whole body", (await c5.plainTermGoal(uri, { line: 0, character: body + 3 })).range,
    { start: { line: 0, character: body }, end: { line: 0, character: body + 5 } });
  // the panel shows both
  const st5 = await readGoalState(c5, uri, { line: 0, character: 28 });
  const p5 = { innerHTML: "" };
  renderPanel(p5, { state: "open", endpoint: SELFHOST_URL, diagnostics: [], goals: st5.goals,
    goalsKind: st5.goalsKind, term: st5.term, termKind: st5.termKind, info: null });
  checkThat("panel: the tactic goals", p5.innerHTML.includes("n : Nat") && p5.innerHTML.includes("m : Nat"),
    p5.innerHTML.slice(0, 500));
  c5.close();
}
{
  // a code-point offset after an astral character: the entry is inside the checked text,
  // the caret is a UTF-16 position
  const text = "-- 😀\ndef f (n : Nat) : Nat := n\n";
  const p = withPrelude(text).prefix.length;
  const caret = text.length - 2;                    // the last `n`
  const cp = Array.from(text.slice(0, caret)).length;
  const index = [{ s: p + cp, e: p + cp + 1, kind: "term", expected: "Nat" }];
  const c6 = new LspClient({ url: SELFHOST_URL, WebSocketImpl: selfhostSocketClass({
    evaluate: stubEval, check: (src) => Promise.resolve(stubCheck(src, { index })),
  }) });
  await c6.connect();
  const got6 = waitFor(c6, "diagnostics");
  c6.openDocument(uri, text);
  await got6;
  const at = positionOf(text, caret);
  check("astral: the expected type", (await c6.plainTermGoal(uri, at)).goal, "Nat");
  check("astral: its UTF-16 range", (await c6.plainTermGoal(uri, at)).range.start, at);
  check("astral: elsewhere it is null", await c6.plainTermGoal(uri, { line: 1, character: 4 }), null);
  c6.close();
}

// ## 11. Nothing escaped



await sleep(30);
check("no unhandled rejections", rejections.length, 0);
if (rejections.length) console.log(rejections.map((r) => String(r && r.stack ? r.stack : r)).join("\n"));
if (failed) {
  console.log(`selfhost lsp: ${failed} check(s) failed`);
  process.exit(1);
}
console.log("selfhost lsp: all checks passed");
