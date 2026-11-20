// The playground's language client and goals panel under Node: a mock WebSocket server
// (`web/mock_lsp_server.mjs`) stands in for `wiz lsp --ws`, so the test needs no Wiz
// build, no browser and no network.
//
//   usage: node web/playground_lsp_test.mjs
//
// Covers: endpoint parsing, the RFC 6455 frames, the handshake
// (initialize/initialized), didOpen with empty diagnostics, goals and term goals
// rendered as HTML (hypotheses, expected type, term tree, source spans), UTF-16
// positions, a diagnostics update after didChange, the plainGoal fallback, close and
// reconnect (documents re-opened), and the no-server path. No unhandled rejection is
// allowed anywhere: the page must keep working without a server.
"use strict";
import { startMockServer, FIXTURE_TEXT } from "./mock_lsp_server.mjs";
import { connectWebSocket } from "./ws_node_client.mjs";
import { LspClient, LspError, parseEndpoint, endpointFromSearch, withToken, withoutToken } from "./lsp-client.js";
import {
  renderPanel, renderGoalResult, renderTermResult, renderInfoItems, readGoalState, offsetAt, positionAt, rangeOffsets,
  parseSpan, spanText, taggedTreeHtml, escapeHtml, plainText,
} from "./goals.js";
import { encodeFrame, acceptKey, FrameReader, OPCODE } from "./ws_frames.mjs";
import { document as minidoc } from "./framework/minidom.mjs";
import { startInfoview } from "./playground-lsp.js";
import { rules } from "./framework/editor-model.mjs";
import { selfhostEndpoint, withPrelude } from "./selfhost-lsp-shim.js";

let failed = 0;
function check(name, got, want) {
  if (Object.is(got, want)) {
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

// An unhandled rejection anywhere is a failure: the page may not spam the console.
const rejections = [];
process.on("unhandledRejection", (reason) => rejections.push(reason));

// Wait for a client event, with a timeout.
function waitFor(client, type, predicate = () => true, ms = 3000) {
  return new Promise((resolve, reject) => {
    let off = null;
    const timer = setTimeout(() => {
      if (off) off();
      reject(new Error(`timed out waiting for ${type}`));
    }, ms);
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

// ## 1. Endpoints

check("endpoint: a ws URL", parseEndpoint("ws://127.0.0.1:8765").url, "ws://127.0.0.1:8765");
check("endpoint: a bare port", parseEndpoint("8765").url, "ws://127.0.0.1:8765");
check("endpoint: a host and port", parseEndpoint("localhost:9000").url, "ws://localhost:9000");
check("endpoint: off", parseEndpoint("off"), null);
check("endpoint: absent", parseEndpoint(null), null);
check("endpoint: from an empty query", endpointFromSearch(""), null);
check("endpoint: from ?lsp=", endpointFromSearch("?lsp=ws://example:1").url, "ws://example:1");
check("endpoint: ?lsp=off", endpointFromSearch("?lsp=off"), null);
// (#430) the server's token: from `?token=`, into the socket's URL, never into the label
check("token: a port and ?token=", endpointFromSearch("?lsp=8765&token=abc").url, "ws://127.0.0.1:8765/?token=abc");
check("token: the label leaves it out", endpointFromSearch("?lsp=8765&token=abc").label, "ws://127.0.0.1:8765/");
check("token: already in the ?lsp= URL", endpointFromSearch("?lsp=ws://h:1/?token=x&token=y").url, "ws://h:1/?token=x");
check("token: with a fallback endpoint", endpointFromSearch("?token=t", "lsp", "ws://127.0.0.1:9").url, "ws://127.0.0.1:9/?token=t");
check("token: ?lsp= wins over the fallback", endpointFromSearch("?lsp=off&token=t", "lsp", "ws://127.0.0.1:9"), null);
check("token: none, the URL unchanged", withToken("ws://h:1", ""), "ws://h:1");
check("token: escaped", withToken("ws://h:1/", "a b&c"), "ws://h:1/?token=a+b%26c");
check("token: withoutToken keeps the rest", withoutToken("ws://h:1/?a=1&token=t"), "ws://h:1/?a=1");

// ## 2. The RFC 6455 frames (the mock server and the test client share them)

check("handshake: the RFC example key", acceptKey("dGhlIHNhbXBsZSBub25jZQ=="), "s3pPLMBiTxaQ9kYGzzhZRbK+xOo=");
for (const size of [5, 200, 70000]) {
  const reader = new FrameReader();
  const frame = encodeFrame(OPCODE.text, Buffer.alloc(size, 0x61), { mask: true });
  const first = reader.push(frame.subarray(0, 3));
  const second = reader.push(frame.subarray(3));
  const frames = first.concat(second);
  check(`frame ${size} bytes: one message`, frames.length, 1);
  check(`frame ${size} bytes: payload`, frames.length ? frames[0].payload.length : -1, size);
}
{
  const reader = new FrameReader();
  const head = encodeFrame(OPCODE.text, Buffer.from("he"), { mask: true });
  head[0] &= 0x7f;                                   // FIN off: a fragment
  const tail = encodeFrame(OPCODE.continuation, Buffer.from("llo"), { mask: true });
  const frames = reader.push(head).concat(reader.push(tail));
  check("frame: fragments reassembled", frames.length === 1 ? frames[0].payload.toString() : "", "hello");
}

// ## 3. Geometry (UTF-16 code units, the negotiated encoding)

const line2 = FIXTURE_TEXT.split("\n").slice(0, 2).join("\n").length + 1;
check("offsetAt: line 2, character 8", offsetAt(FIXTURE_TEXT, { line: 2, character: 8 }), line2 + 8);
check("positionAt: the inverse", positionAt(FIXTURE_TEXT, line2 + 8).character, 8);
const emoji = "a😀b\nc";
check("UTF-16: an emoji is two code units", offsetAt(emoji, { line: 0, character: 3 }), 3);
check("UTF-16: the second line", offsetAt(emoji, { line: 1, character: 1 }), 6);
check("span: round trip", spanText(parseSpan("2:8-3:9")), "2:8-3:9");
check("span: offsets", rangeOffsets("abcdef\nghij", { start: { line: 1, character: 1 }, end: { line: 1, character: 3 } }).start, 8);

// ## 4. Handshake, didOpen and diagnostics

const mock = await startMockServer();
const uri = "file:///test.wiz";
const client = new LspClient({ url: mock.url, WebSocketImpl: connectWebSocket, requestTimeout: 3000 });
await client.connect();
check("handshake: open", client.state, "open");
check("handshake: serverInfo", client.serverInfo && client.serverInfo.name, "wiz-mock");
check("handshake: wiz infoview capability", client.infoview && client.infoview.version, 1);
check("handshake: initialize sent", mock.stats.initialize, 1);
await sleep(20);   // the server processes notifications on its own turn
check("handshake: initialized sent", mock.stats.initialized, 1);

const firstDiagnostics = waitFor(client, "diagnostics", (p) => p.uri === uri);
client.openDocument(uri, FIXTURE_TEXT);
const opened = await firstDiagnostics;
check("didOpen: sent once", mock.stats.didOpen, 1);
check("didOpen: empty diagnostics", opened.diagnostics.length, 0);

// ## 5. Goals, the panel and source spans

const goals = await client.interactiveGoals(uri, { line: 4, character: 8 });
check("interactiveGoals: one goal", goals.goals.length, 1);
check("interactiveGoals: hypotheses", goals.goals[0].hyps.map((h) => h.names.join(" ")).join(","), "n,b");
check("interactiveGoals: expected type", plainText(goals.goals[0].type), "Nat");
check("interactiveGoals: session", goals.session, 1);

const term = await client.interactiveTermGoal(uri, { line: 4, character: 8 });
check("interactiveTermGoal: expected type", plainText(term.goal.type), "Nat");

// `textDocument/completion`: the request the popup makes, and the list a server answers.
const completions = await client.completion(uri, { line: 1, character: 0 }, { triggerKind: 1 });
check("completion: the list", completions.items.length, 5);
check("completion: an item's label", completions.items[0].label, "Nat.add");
check("completion: the request's method and position",
  mock.stats.completionArgs.length === 1 && mock.stats.completionArgs[0].position.character === 0, true);
check("completion: the context's trigger", mock.stats.completionArgs[0].context.triggerKind, 1);
check("completion: the item with a textEdit", completions.items[4].textEdit.newText, "twice");

const panel = { innerHTML: "" };
const openView = {
  state: "open", endpoint: mock.url, serverInfo: client.serverInfo, infoview: client.infoview,
  diagnostics: [], goals, goalsKind: "interactive", term, termKind: "interactive", info: null,
};
renderPanel(panel, openView);
const html = panel.innerHTML;
checkThat("panel: a hypothesis name", html.includes('class="names"'));
checkThat("panel: the turnstile", html.includes("⊢ "));
checkThat("panel: a tagged constant", html.includes("tt k-const"));
checkThat("panel: the source span of a hypothesis", html.includes('data-span="2:8-2:9"'));
checkThat("panel: the goal's range on the goal", html.includes('data-span="1:28-4:9"'));
checkThat("panel: the term tree", html.includes('class="tree"'));
checkThat("panel: the tree's nodes", html.includes("Nat.add"));
checkThat("panel: no diagnostics yet", html.includes("no diagnostics"));

const drawn = taggedTreeHtml(goals.tree);
checkThat("tree: drawn", drawn.nodes > 2, `nodes = ${drawn.nodes}`);
check("tree: escaped", escapeHtml("<a&b>"), "&lt;a&amp;b&gt;");

// ## 6. A diagnostics update after didChange, and the panel's clickable range

const secondDiagnostics = waitFor(client, "diagnostics", (p) => p.uri === uri);
client.changeDocument(uri, "BAD import Prelude\n");
const changed = await secondDiagnostics;
check("didChange: sent once", mock.stats.didChange, 1);
check("didChange: one diagnostic", changed.diagnostics.length, 1);
check("didChange: the message", changed.diagnostics[0].message, "mock: unknown identifier");
const stateAfterChange = await readGoalState(client, uri, { line: 4, character: 8 });
check("readGoalState: interactive goals", stateAfterChange.goalsKind, "interactive");
check("readGoalState: the new session", stateAfterChange.session, 2);
renderPanel(panel, Object.assign({}, openView, {
  diagnostics: changed.diagnostics, goals: stateAfterChange.goals,
  goalsKind: stateAfterChange.goalsKind, term: stateAfterChange.term,
  termKind: stateAfterChange.termKind,
}));
const withDiagnostic = panel.innerHTML;
checkThat("panel: the diagnostic", withDiagnostic.includes("mock: unknown identifier"));
checkThat("panel: the diagnostic's span", withDiagnostic.includes('data-span="0:0-0:3"'));
checkThat("panel: the severity", withDiagnostic.includes("sev-error"));

// ## 6b. Diagnostics versions: an older publish does not replace a newer one
{
  const ordered = new LspClient({ url: "ws://127.0.0.1:1" });
  const orderedUri = "file:///ordered.wiz";
  let events = 0;
  ordered.on("diagnostics", () => { events++; });
  const publish = (version, message) => ordered.receive(JSON.stringify({
    jsonrpc: "2.0", method: "textDocument/publishDiagnostics",
    params: Object.assign({ uri: orderedUri, diagnostics: [{ message }] },
      version === undefined ? {} : { version }),
  }));
  publish(2, "v2");
  const stored = () => ordered.diagnostics.get(orderedUri);
  const messages = () => {
    const s = stored();
    return s && s.diagnostics ? s.diagnostics.map((d) => d.message) : null;
  };
  check("diagnostics: the version is stored", stored() && stored().version, 2);
  check("diagnostics: the diagnostics are stored beside it", messages() && messages().join(","), "v2");
  publish(1, "v1 (stale)");
  check("diagnostics: an older version is ignored", messages() && messages().join(","), "v2");
  check("diagnostics: a stale publish is not emitted", events, 1);
  publish(3, "v3");
  check("diagnostics: a newer version replaces it", messages() && messages().join(","), "v3");

  // A server that sends no version (the Lean server today) still gets last-arrival.
  const loose = new LspClient({ url: "ws://127.0.0.1:1" });
  const looseUri = "file:///loose.wiz";
  const unpublish = (message) => loose.receive(JSON.stringify({
    jsonrpc: "2.0", method: "textDocument/publishDiagnostics",
    params: { uri: looseUri, diagnostics: [{ message }] },
  }));
  unpublish("first");
  unpublish("second");
  const looseStored = loose.diagnostics.get(looseUri);
  check("diagnostics: unversioned publishes keep the last arrival",
    looseStored && looseStored.diagnostics ? looseStored.diagnostics.map((d) => d.message).join(",") : null, "second");
}

// ## 6c. Malformed results: "nothing at the cursor", not "no goals" or an empty goal

// A result that is not the protocol's shape is not the positive claim `goals: []` makes
// ("the proof is complete"). Only the required field being absent is malformed; `null`
// already means "nothing at the cursor".
{
  const nothing = (html) => typeof html === "string" && html.includes("nothing at the cursor");
  check("malformed: an interactive result without goals is nothing at the cursor",
    nothing(renderGoalResult({ range: { start: { line: 0, character: 0 } } }, "interactive")), true);
  check("malformed: it does not claim no goals",
    renderGoalResult({ range: {} }, "interactive").includes("no goals"), false);
  check("malformed: a non-array goals field", nothing(renderGoalResult({ goals: "n : Nat" }, "interactive")), true);
  check("malformed: a plain result without goals or rendered", nothing(renderGoalResult({ range: {} }, "plain")), true);
  check("malformed: a term result without a goal is nothing at the cursor",
    nothing(renderTermResult({ range: {} }, "interactive")), true);
  check("malformed: it does not draw an empty turnstile",
    renderTermResult({ range: {} }, "interactive").includes("⊢"), false);

  // The valid empty shapes still work.
  check("malformed: an empty goals array is no goals",
    renderGoalResult({ goals: [] }, "interactive").includes("no goals"), true);
  check("malformed: a plain rendered no-goals result",
    renderGoalResult({ rendered: "no goals" }, "plain").includes("no goals"), true);
  check("malformed: a plain term goal still renders",
    renderTermResult({ goal: "⊢ Nat", range: {} }, "plain").includes("⊢ Nat"), true);
}

// ## 7. The plainGoal fallback (a server with only the text methods)

const plainMock = await startMockServer({ mode: "plain" });
const plainClient = new LspClient({ url: plainMock.url, WebSocketImpl: connectWebSocket, requestTimeout: 3000 });
await plainClient.connect();
plainClient.openDocument(uri, FIXTURE_TEXT);
const plainState = await readGoalState(plainClient, uri, { line: 4, character: 8 });
check("fallback: plain goals", plainState.goalsKind, "plain");
check("fallback: plain term", plainState.termKind, "plain");
check("fallback: the goal text", plainState.goals.goals[0], "n : Nat\nb : Bool\n⊢ Nat");
renderPanel(panel, {
  state: "open", endpoint: plainMock.url, goals: plainState.goals, goalsKind: plainState.goalsKind,
  term: plainState.term, termKind: plainState.termKind, diagnostics: [], info: null,
});
const plainHtml = panel.innerHTML;
checkThat("fallback: rendered as text", plainHtml.includes("n : Nat"));
checkThat("fallback: no tagged spans", !plainHtml.includes("tt k-"));
checkThat("fallback: the plain term's span", plainHtml.includes('data-span="1:21-1:23"'));
plainClient.close();
await plainMock.close();

// ## 8. Close and reconnect

const didOpenBefore = mock.stats.didOpen;
const closed = waitFor(client, "close");
mock.dropClients();
const closeEvent = await closed;
checkThat("close: reported", typeof closeEvent.code === "number");
check("close: state", client.state, "closed");
let rejected = null;
try {
  await client.interactiveGoals(uri, { line: 4, character: 8 });
} catch (e) {
  rejected = e;
}
checkThat("close: a request rejects with LspError", rejected instanceof LspError, String(rejected));
check("close: the code", rejected && rejected.code, -32097);

const reopened = waitFor(client, "diagnostics", (p) => p.uri === uri);
await client.reconnect();
await reopened;
check("reconnect: open", client.state, "open");
check("reconnect: the document is opened again", mock.stats.didOpen, didOpenBefore + 1);
const afterReconnect = await readGoalState(client, uri, { line: 4, character: 8 });
check("reconnect: goals again", afterReconnect.goalsKind, "interactive");

// ## 9. No server: the page's fallback

const probe = await startMockServer();
const deadUrl = probe.url;
await probe.close();
const noServer = new LspClient({ url: deadUrl, WebSocketImpl: connectWebSocket, connectTimeout: 1500 });
let connectError = null;
try {
  await noServer.connect();
} catch (e) {
  connectError = e;
}
checkThat("no server: connect rejects", connectError instanceof Error, String(connectError));
check("no server: state", noServer.state, "failed");
const empty = await readGoalState(noServer, uri, { line: 0, character: 0 });
check("no server: readGoalState resolves", empty.goalsKind, null);
renderPanel(panel, { state: "no-server" });
const noServerHtml = panel.innerHTML;
checkThat("no server: the panel says so", noServerHtml.includes("no language server"));
checkThat("no server: it says how to start one", noServerHtml.includes("wiz lsp --ws"));
checkThat("no server: no goals are drawn", !noServerHtml.includes("class=\"goal\""));
noServer.close();

// ## 10. The page's wiring (a stub textarea and panel, no browser)

function fakeEditor(value) {
  return {
    value, selectionStart: 0, selectionEnd: 0, scrollTop: 0, clientHeight: 200,
    listeners: {},
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
// The DOM the overlays need: minidom's elements plus the bits the page provides
// (`web/hover.js` appends its card to the body, the completion overlay dispatches an
// `Event`, and the squiggle layer parses through `createRange`).
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

const wireMock = await startMockServer();
const editor = fakeEditor(FIXTURE_TEXT);
const wirePanel = fakePanel();
const pageDocument = fakeDocument();
const app = startInfoview({
  rules,
  editor, panel: wirePanel, config: { url: wireMock.url }, uri: "file:///wire.wiz",
  document: pageDocument,
});
checkThat("wiring: the pane says it is connecting", wirePanel.innerHTML.includes("connecting"));
checkThat("wiring: goals arrive", await waitUntil(() => wirePanel.innerHTML.includes('class="names"')));
checkThat("wiring: it opened the editor's text",
  wireMock.documents.get("file:///wire.wiz") !== undefined &&
  wireMock.documents.get("file:///wire.wiz").text === FIXTURE_TEXT);
checkThat("wiring: the connection status", wirePanel.innerHTML.includes("connected"));

// Cursor → LSP: moving the caret asks for the goals at the new position (after the
// debounce), and the caret's position is what the request carries.
const beforeMoves = wireMock.stats.goalPositions.length;
editor.selectionStart = line2 + 8;
editor.selectionEnd = line2 + 8;
for (const fn of editor.listeners.keyup || []) fn({ type: "keyup" });
checkThat("wiring: a caret move asks again",
  await waitUntil(() => wireMock.stats.goalPositions.length > beforeMoves &&
    wireMock.stats.goalPositions[wireMock.stats.goalPositions.length - 1].line === 2), JSON.stringify(wireMock.stats.goalPositions));
checkThat("wiring: the request carries the UTF-16 caret",
  wireMock.stats.goalPositions[wireMock.stats.goalPositions.length - 1].character === 8);

// Clicking a hypothesis (a `[data-span]` element) selects its source span.
const clickTarget = { dataset: { span: "2:8-2:9" }, parentElement: null, closest: () => null };
wirePanel.listeners.click[0]({ target: clickTarget, preventDefault() {} });
check("wiring: a click selects the span", editor.selectionStart, line2 + 8);
check("wiring: the selection ends there", editor.selectionEnd, line2 + 9);

// Hover at the caret (`textDocument/hover`) and F12 / Ctrl-click go to definition
// (`textDocument/definition`): the card is the page's, the answers are the mock's.
editor.selectionStart = editor.selectionEnd = 0;
const hovered = await app.hover().inquire();
check("wiring: textDocument/hover was asked", wireMock.stats.hover, 1);
checkThat("wiring: the hover card is up", hovered !== null && app.hover().isOpen());
checkThat("wiring: the hover card shows the signature",
  app.hover().content().includes("Nat.add : Nat → Nat → Nat"), app.hover().content());
checkThat("wiring: the hover card shows the doc comment",
  app.hover().content().includes("Adds two Nats."));

// A definition in this document moves the caret and selects the name. The mock answers
// in this file for a caret on the fixture's last line.
const fixtureLastLine = offsetAt(FIXTURE_TEXT, { line: 4, character: 2 });
editor.selectionStart = editor.selectionEnd = fixtureLastLine;
for (const fn of editor.listeners.click || []) fn({ ctrlKey: true, metaKey: false, preventDefault() {} });
checkThat("wiring: Ctrl-click asked for the definition",
  await waitUntil(() => wireMock.stats.definition === 1), `requests = ${wireMock.stats.definition}`);
checkThat("wiring: the definition moves the caret",
  await waitUntil(() => editor.selectionStart === offsetAt(FIXTURE_TEXT, { line: 1, character: 4 })),
  `caret = ${editor.selectionStart}`);
checkThat("wiring: the card closes after a jump", !app.hover().isOpen());

// A definition in a library has no page here: the card names the place instead.
app.hover().close();
editor.selectionStart = editor.selectionEnd = 0;
for (const fn of editor.listeners.keydown || []) fn({ key: "F12", preventDefault() {} });
checkThat("wiring: F12 asked for the definition",
  await waitUntil(() => wireMock.stats.definition === 2), `requests = ${wireMock.stats.definition}`);
checkThat("wiring: a library definition is named",
  await waitUntil(() => app.hover().content().includes("Prelude.wiz:7:1")), app.hover().content());

// `?hover=off` (or `hover: false`) mounts nothing.
const noHover = startInfoview({ editor: fakeEditor(""), panel: fakePanel(), config: null, hover: false });
check("wiring: hover: false turns it off", noHover.hover(), null);

// Diagnostics → squiggles: the overlay underlines the same range the panel lists.
// An edit sends didChange and the goals are asked again.
editor.value = "nope import Prelude\n";
editor.selectionStart = 0;
for (const fn of editor.listeners.input || []) fn();
checkThat("wiring: didChange after an edit",
  await waitUntil(() => wireMock.stats.didChange === 1 && wirePanel.innerHTML.includes("mock: unknown identifier")));
checkThat("wiring: a squiggle for the diagnostic", app.squiggles() && app.squiggles().segments().length === 1,
  JSON.stringify(app.squiggles() && app.squiggles().segments()));
check("wiring: the squiggle's range",
  app.squiggles().segments().map((s) => s.start + "-" + s.stop).join(","), "0-3");

// An edit reaches the server before the goal refresh. A keyup asks for goals 120 ms
// later, while didChange used to wait 250 ms, so the server was asked about a position
// in pre-typing text; `onEdit` now sends didChange at once and debounces only the refresh.
await sleep(50);   // let the refresh the previous diagnostics scheduled settle
const typedText = "import Prelude\ndef moved : Nat := 2\n";
editor.value = typedText;
editor.selectionStart = typedText.length;
editor.selectionEnd = typedText.length;
const beforeGoalTexts = wireMock.stats.goalTexts.length;
for (const fn of editor.listeners.input || []) fn({ type: "input" });
for (const fn of editor.listeners.keyup || []) fn({ type: "keyup" });
checkThat("wiring: a goal after an edit is asked about the text the server has",
  await waitUntil(() => wireMock.stats.goalTexts.length > beforeGoalTexts),
  JSON.stringify(wireMock.stats.goalTexts));
check("wiring: the goal's document is the edited text",
  wireMock.stats.goalTexts[wireMock.stats.goalTexts.length - 1], typedText);
checkThat("wiring: its version is the one didChange sent",
  wireMock.stats.goalVersions[wireMock.stats.goalVersions.length - 1] ===
    wireMock.documents.get("file:///wire.wiz").version);

// Completions: the popup asks the client at the caret and inserts the chosen item.
editor.value = "Nat.";
editor.selectionStart = 4;
editor.selectionEnd = 4;
const popup = app.completions();
checkThat("wiring: a completion popup", !!popup);
const shown = await popup.requestAtCaret();
check("wiring: the popup filtered the list", shown.map((i) => i.label).join(","), "Nat.sub,Nat.succ,Nat.add");
const lastCompletion = wireMock.stats.completionArgs[wireMock.stats.completionArgs.length - 1];
check("wiring: the completion request's line", lastCompletion.position.line, 0);
check("wiring: the completion request's character", lastCompletion.position.character, 4);
popup.handleKey({ key: "Enter", preventDefault() {}, stopPropagation() {} });
check("wiring: the accepted item replaced the prefix", editor.value, "Nat.sub");
check("wiring: the caret after accepting", editor.selectionStart, 7);
app.stop();
checkThat("wiring: stop closes the hover card", !app.hover().isOpen());
await wireMock.close();

// ## 10a. The same three flows against the in-page server (`?lsp=selfhost`)
//
// The page is given `selfhostEndpoint` instead of a WebSocket: every request goes through
// the same `startInfoview` code, so completion, hover and definition must answer in the
// shapes the mock does, from the check's declaration index.
const SELF_TEXT = "def twice (n : Nat) : Nat := n + n\ndef pred (n : Nat) : Nat := n\n#eval twice\n";
const SELF_P = withPrelude(SELF_TEXT).prefix.length;
const selfDecl = (name, detail, at, kind) => ({
  s: SELF_P + at, e: SELF_P + at + name.length, kind: "decl", name, detail, ckind: kind,
});
const SELF_INDEX = [
  selfDecl("twice", "(n : Nat) → Nat", SELF_TEXT.indexOf("twice"), 3),
  selfDecl("pred", "Nat → Nat", SELF_TEXT.indexOf("pred"), 3),
];
const selfCheck = () => JSON.stringify({ v: 1, lines: [], index: SELF_INDEX });
const selfEditor = fakeEditor(SELF_TEXT);
const selfPanel = fakePanel();
const selfDocument = fakeDocument();
const selfApp = startInfoview({
  rules,
  editor: selfEditor, panel: selfPanel, uri: "file:///in-page.wiz", document: selfDocument,
  config: selfhostEndpoint({ evaluate: () => "", check: selfCheck }),
});
checkThat("in-page: connected", await waitUntil(() => selfPanel.innerHTML.includes("connected")),
  selfPanel.innerHTML.slice(0, 300));

const useAt = SELF_TEXT.lastIndexOf("twice");
selfEditor.selectionStart = selfEditor.selectionEnd = useAt + 2;   // after `tw`
const selfShown = await selfApp.completions().requestAtCaret();
check("in-page completion: the prefix", selfShown.map((i) => i.label).join(","), "twice");
check("in-page completion: the textEdit", JSON.stringify(selfShown[0].textEdit),
  JSON.stringify({ range: { start: positionAt(SELF_TEXT, useAt), end: positionAt(SELF_TEXT, useAt + 2) }, newText: "twice" }));

selfEditor.selectionStart = selfEditor.selectionEnd = useAt + 2;
const selfHover = await selfApp.hover().inquire();
checkThat("in-page hover: the signature", selfHover !== null &&
  selfApp.hover().content().includes("twice : (n : Nat) → Nat"), selfApp.hover().content());

selfEditor.selectionStart = selfEditor.selectionEnd = useAt + 2;
const selfDefinition = await selfApp.hover().goToDefinition();
check("in-page definition: the declaration", JSON.stringify(selfDefinition && selfDefinition.range),
  JSON.stringify({ start: positionAt(SELF_TEXT, SELF_TEXT.indexOf("twice")), end: positionAt(SELF_TEXT, SELF_TEXT.indexOf("twice") + 5) }));
check("in-page definition: the caret moved", selfEditor.selectionStart, SELF_TEXT.indexOf("twice"));
check("in-page definition: nothing else in the document", selfDefinition && selfDefinition.uri, "file:///in-page.wiz");
selfApp.stop();

const idlePanel = fakePanel();
startInfoview({ editor: fakeEditor(""), panel: idlePanel, config: null });
checkThat("wiring: no endpoint → no server", idlePanel.innerHTML.includes("no language server"));

// A failed connection is the same state, with a reason and a reconnect button.
const deadPanel = fakePanel();
startInfoview({
  editor: fakeEditor(""), panel: deadPanel, uri: "file:///dead.wiz",
  config: { url: deadUrl, WebSocketImpl: connectWebSocket },
});
checkThat("wiring: a failed connection is no server",
  await waitUntil(() => deadPanel.innerHTML.includes("no language server")), deadPanel.innerHTML.slice(0, 300));
checkThat("wiring: the failure is explained", deadPanel.innerHTML.includes("cannot connect"));
checkThat("wiring: a reconnect button", deadPanel.innerHTML.includes('data-action="reconnect"'));

// ## 10b. Follow mode (`web/infoview.html?follow=1`): no document of its own
//
// The standalone infoview page shows another editor's document. The server owns it, so
// the pane must not open, change or close one; it moves with `wiz/infoview/cursor` and
// asks about that URI.

const followMock = await startMockServer();
const followPanel = fakePanel();
const followed = startInfoview({
  editor: fakeEditor(""), panel: followPanel, config: { url: followMock.url }, follow: true,
});
checkThat("follow: the pane connects", await waitUntil(() => followPanel.innerHTML.includes("connected")));
check("follow: no document of its own is opened", followMock.stats.didOpen, 0);
checkThat("follow: the client is there to subscribe", !!followed.client());
followed.client().on("wiz/infoview/cursor", (p) => followed.goTo(p.textDocument.uri, p.position));
followMock.notify("wiz/infoview/cursor", {
  textDocument: { uri: "file:///editor.wiz" },
  position: { line: 4, character: 8 },
  session: 1,
});
checkThat("follow: the state at the editor's cursor",
  await waitUntil(() => followPanel.innerHTML.includes('class="names"')), followPanel.innerHTML.slice(0, 300));
check("follow: still no document opened", followMock.stats.didOpen, 0);
check("follow: still no document changed", followMock.stats.didChange, 0);
check("follow: the followed position's line", followed.view.position && followed.view.position.line, 4);
check("follow: the followed position's character", followed.view.position && followed.view.position.character, 8);
check("follow: the target is the editor's document", followed.target(), "file:///editor.wiz");
followed.stop();
check("follow: it does not close the editor's document", followMock.stats.didClose, 0);
await followMock.close();

// ## 10c. The selected subterm in its own element (`#info` on the infoview page)
//
// With `info`, the panel leaves the selection out and the box renders it, so the
// standalone page keeps its separate `#info` (and its CSS).

const infoMock = await startMockServer();
const infoPanel = fakePanel();
const infoBox = { innerHTML: "" };
const infoApp = startInfoview({
  editor: fakeEditor(FIXTURE_TEXT), panel: infoPanel, info: infoBox,
  config: { url: infoMock.url }, uri: "file:///info.wiz",
});
checkThat("info: the goals arrive", await waitUntil(() => infoPanel.innerHTML.includes('class="names"')));
const infoTag = {
  dataset: { ref: "5", span: "2:8-2:9" }, parentElement: null,
  closest: () => infoTag,
};
infoPanel.listeners.click[0]({ target: infoTag, preventDefault() {} });
checkThat("info: the subterm is described", await waitUntil(() => infoBox.innerHTML.includes('class="kind"')),
  infoBox.innerHTML);
checkThat("info: its kind", infoBox.innerHTML.includes('class="kind">const</span>'), infoBox.innerHTML);
checkThat("info: its type", infoBox.innerHTML.includes("Type"), infoBox.innerHTML);
checkThat("info: the panel does not repeat it", !infoPanel.innerHTML.includes('class="selection"'));
infoApp.stop();
await infoMock.close();

// ## 10d. The page hook (`onRender`) sees every state

const renders = [];
const hookMock = await startMockServer();
const hooked = startInfoview({
  editor: fakeEditor(FIXTURE_TEXT), panel: fakePanel(), config: { url: hookMock.url },
  onRender: (view) => renders.push(view.state),
});
check("hook: the first render", renders[0], "connecting");
checkThat("hook: it reaches open", await waitUntil(() => renders.includes("open")));
hooked.stop();
await hookMock.close();
// A reconnect after a *failed first connect* must open the document: the page has to
// store the text before the handshake (a client whose first connect failed has an empty
// document map, and `connect()` only opens documents it already knows).
{
  const probePort = await startMockServer();
  const recoverPort = probePort.port;
  await probePort.close();
  const recoverEditor = fakeEditor("def recovered : Nat := 1\n");
  const recoverPanel = fakePanel();
  const recoverApp = startInfoview({
    editor: recoverEditor, panel: recoverPanel, uri: "file:///recovered.wiz",
    config: { url: `ws://127.0.0.1:${recoverPort}`, WebSocketImpl: connectWebSocket },
  });
  checkThat("reconnect: the first connection fails",
    await waitUntil(() => recoverPanel.innerHTML.includes('data-action="reconnect"')),
    recoverPanel.innerHTML.slice(0, 300));
  check("reconnect: the page already knows the document", recoverApp.client().docs.size, 1);
  const recoverMock = await startMockServer({ port: recoverPort });
  await recoverApp.reconnect();
  checkThat("reconnect: the document is opened after a failed first connect",
    await waitUntil(() => recoverMock.stats.didOpen === 1), `didOpen ${recoverMock.stats.didOpen}`);
  check("reconnect: the server has the editor's text",
    recoverMock.documents.get("file:///recovered.wiz") &&
      recoverMock.documents.get("file:///recovered.wiz").text, recoverEditor.value);
  recoverApp.stop();
  await recoverMock.close();
}

// ## 10e. The token (#430): the mock refuses like `wiz lsp --ws`; a client with the
// page's `?token=` gets in, one without it does not

const tokenMock = await startMockServer({ token: "s3cr3t" });
const bare = new LspClient({ url: tokenMock.url, WebSocketImpl: connectWebSocket, connectTimeout: 1500 });
let bareError = null;
try { await bare.connect(); } catch (e) { bareError = e; }
checkThat("token: no token, refused", bareError instanceof Error && tokenMock.stats.refused === 1, String(bareError));
bare.close();
const wrongEp = endpointFromSearch("?lsp=" + tokenMock.port + "&token=nope");
const wrong = new LspClient({ url: wrongEp.url, WebSocketImpl: connectWebSocket, connectTimeout: 1500 });
let wrongError = null;
try { await wrong.connect(); } catch (e) { wrongError = e; }
checkThat("token: a wrong token, refused", wrongError instanceof Error && tokenMock.stats.refused === 2, String(wrongError));
wrong.close();
const tokenPanel = fakePanel();
const tokenApp = startInfoview({
  editor: fakeEditor(FIXTURE_TEXT), panel: tokenPanel, uri: "file:///token.wiz",
  config: { ...endpointFromSearch("?lsp=" + tokenMock.port + "&token=s3cr3t"), WebSocketImpl: connectWebSocket },
});
checkThat("token: the page's ?token= gets in",
  await waitUntil(() => tokenPanel.innerHTML.includes('class="names"')), tokenPanel.innerHTML.slice(0, 300));
checkThat("token: the panel does not show it", !tokenPanel.innerHTML.includes("s3cr3t"));
tokenApp.stop();
await tokenMock.close();

// ## 10f. Widget items (`#plot`): the self-contained SVG is inserted, a script is not

const plotBundle = JSON.stringify({
  schema: "wiz.widget/1", kind: "plot", mimeType: "image/svg+xml",
  title: "Sales", summary: "plot: Sales (1 series, 320×240)",
  svg: '<svg xmlns="http://www.w3.org/2000/svg" width="10" height="10"><rect width="10" height="10"/></svg>',
  html: '<figure class="wiz-plot"><svg xmlns="http://www.w3.org/2000/svg" width="10" height="10"><rect width="10" height="10"/></svg><figcaption>Sales</figcaption></figure>',
});
const widgetItem = { kind: "widget", title: "plot", text: "WIZ_WIDGET:" + plotBundle };
checkThat("widget: the HTML (an inline SVG) is rendered",
  renderInfoItems([widgetItem]).includes('<figure class="wiz-plot">') &&
  renderInfoItems([widgetItem]).includes("<svg"));
checkThat("widget: the title is carried for the caption",
  renderInfoItems([widgetItem]).includes('data-widget-title="Sales"'));
checkThat("widget: an item of another kind is not drawn",
  renderInfoItems([{ kind: "message", title: "info", text: "hello" }]) === "");
checkThat("widget: a payload with a script is refused",
  !renderInfoItems([{ kind: "widget", title: "x",
    text: 'WIZ_WIDGET:{"html":"<figure><script>alert(1)</script></figure>"}' }]).includes("<script"));
checkThat("widget: a payload with an external reference is refused",
  !renderInfoItems([{ kind: "widget", title: "x",
    text: 'WIZ_WIDGET:{"html":"<figure><img src=\\"https://example.invalid/x.png\\"></figure>"}' }]).includes("example.invalid"));

// ## 11. Nothing escaped

client.close();
await mock.close();
await sleep(30);
check("no unhandled rejections", rejections.length, 0);
if (rejections.length) console.log(rejections.map((r) => String(r && r.stack ? r.stack : r)).join("\n"));

if (failed) {
  console.log(`playground lsp: ${failed} check(s) failed`);
  process.exit(1);
}
console.log("playground lsp: all checks passed");
