// The P0 wire and the adopt contract, without a browser.
//
// This is the contract test for `web/framework/wire.js` and `web/framework/adopt.js`:
// the envelope encode/decode, the caps, the monitor's call/reply transitions, the
// adopt-versus-replace decision on a `minidom` container, and the single validation
// table's wire rows. The model is `docs/notes/loom-wire-protocol.md`; this test reads
// that table and fails when the two copies drift.
//
//   node web/framework/wire_test.mjs
"use strict";
import { readFileSync } from "node:fs";
import {
  WIRE_VERSION, CAPS, VALIDATION, WIRE_VALIDATION_IDS, WireError,
  encode, decode, validateMessage, validatePayload, Monitor,
} from "./wire.js";
import { hashHtml, islandInfo, decideAdopt, writeError } from "./adopt.js";
import { mount } from "./mount.js";
import { parse, serialize, document as minidom } from "./minidom.mjs";

let failed = 0;
const ok = (cond, what, detail = "") => {
  if (cond) console.log("ok: " + what);
  else { failed++; console.log("FAIL: " + what + (detail ? "\n  " + detail : "")); }
};
const eq = (what, want, got) => ok(Object.is(got, want), what,
  `want ${JSON.stringify(want)}\n  got  ${JSON.stringify(got)}`);

function throws(what, fn, code) {
  let err = null;
  try { fn(); } catch (e) { err = e; }
  ok(err instanceof WireError && (code === undefined || err.code === code), what,
    err ? `code ${err.code}: ${err.message}` : "no error");
  return err;
}

// ## The envelope

const V = WIRE_VERSION;
const call = (seq, id, extra = {}) => ({
  v: V, ch: "editor.calls", op: "call", src: "host", seq, id,
  payload: { schema: "wiz.call/1", method: "run", args: {}, ...extra.payload },
  ...extra,
});
const request = (seq, id, kind = "run") => ({
  v: V, ch: "editor.replies", op: "request", src: "runtime", seq, id,
  payload: { schema: "wiz.effect/1", kind, payload: "" },
});
const result = (seq, id, okv = true) => ({
  v: V, ch: "editor.calls", op: "result", src: "host", seq, id,
  payload: okv ? { schema: "wiz.effect-result/1", ok: true, value: { text: "ok" } }
    : { schema: "wiz.effect-result/1", ok: false, error: "failed" },
});
const reply = (seq, id, okv = true) => ({
  v: V, ch: "editor.replies", op: "reply", src: "runtime", seq, id,
  payload: okv ? { schema: "wiz.call-reply/1", ok: true, value: null }
    : { schema: "wiz.call-reply/1", ok: false, error: "failed" },
});

const callText = encode(call(1, 7));
const decoded = decode(callText);
eq("a call encodes and decodes", 7, decoded.id);
eq("the version is exact", V, decoded.v);
eq("canonical keys are sorted", "ch,id,op,payload,seq,src,v",
  Object.keys(JSON.parse(callText)).join(","));

const trace = [call(1, 7), request(1, 7), result(2, 7), reply(2, 7)];
for (const m of trace) {
  const again = decode(encode(m));
  eq("round trip " + m.ch + "." + m.op, m.seq, again.seq);
}

// ## The transport refusals (row 4)

throws("a wrong version is refused, never downgraded", () =>
  decode(JSON.stringify({ ...call(1, 1), v: "wiz.loom.wire/2" })), "version");
throws("no version is a version error", () =>
  decode(JSON.stringify({ ...call(1, 1), v: undefined })), "version");
throws("an unknown channel is refused", () =>
  validateMessage({ ...call(1, 1), ch: "editor.events" }), "channel");
throws("an unknown op is refused", () =>
  validateMessage({ ...call(1, 1), op: "nope" }), "op");
throws("the wrong sender on a channel is refused", () =>
  validateMessage({ ...call(1, 1), src: "runtime" }), "channel");
throws("a reply cannot come from the host", () =>
  validateMessage({ ...reply(1, 7), src: "host" }), "channel");
throws("a payload schema must match the channel/op", () =>
  validateMessage({ ...call(1, 1), payload: { schema: "wiz.call-reply/1" } }), "payload");
throws("an unknown payload schema is a payload error", () =>
  validatePayload({ schema: "wiz.what/1" }), "payload");
throws("a duplicate reserved key is refused by the reviver", () =>
  decode('{"v":"' + V + '","__proto__":{"x":1}}'), "payload");
throws("a frame over 1 MiB is refused before parsing", () =>
  decode("x".repeat(CAPS.frame + 1)), "cap");
throws("a deeply nested payload is refused", () => {
  let value = 0;
  for (let i = 0; i < CAPS.jsonDepth + 2; i++) value = [value];
  validatePayload({ schema: "wiz.effect/1", kind: "run", payload: value });
}, "cap");
throws("an over-long array is refused", () =>
  validatePayload({ schema: "wiz.effect/1", kind: "run", payload: new Array(CAPS.jsonArray + 1).fill(0) }), "cap");
throws("a method outside the editor set is refused", () =>
  validatePayload({ schema: "wiz.call/1", method: "rm -rf", args: {} }), "payload");
ok((() => {
  try { validatePayload({ schema: "wiz.call/1", method: "wiz_loom_editor_foo", mode: "query", args: {} }); return true; }
  catch { return false; }
})(), "a query may name a read-only method");
throws("a failed result must name its error", () =>
  validatePayload({ schema: "wiz.effect-result/1", ok: false }), "payload");
throws("a negative ack rev is refused", () =>
  validatePayload({ schema: "wiz.ack/1", rev: -1 }), "payload");
throws("a wire error needs a known code", () =>
  validatePayload({ schema: "wiz.wire.error/1", code: "oops", message: "", fatal: true }), "payload");
throws("a wire error needs a fatal flag", () =>
  validatePayload({ schema: "wiz.wire.error/1", code: "channel", message: "x" }), "payload");
throws("a patch op must be known", () =>
  validatePayload({ schema: "wiz.patch/1", base: 0, rev: 1, ops: [{ op: "wat", path: "" }] }), "payload");
throws("a patch path must be in range", () =>
  validatePayload({ schema: "wiz.patch/1", base: 0, rev: 1, ops: [{ op: "text", path: new Array(70).fill("0").join("."), text: "" }] }), "cap");

// ## The monitor's transitions (rows 5 and 6)

{
  const m = new Monitor();
  eq("the monitor starts empty", 0, m.snapshot().open.length);
  ok(m.check(call(1, 7)).ok, "a call opens an id");
  ok(m.check(request(1, 7)).ok, "the runtime may request an effect for it");
  eq("the request is tracked", 1, m.snapshot().requests.length);
  ok(m.check(result(2, 7)).ok, "the host result retires the request");
  eq("the call is still open until the reply", 1, m.snapshot().open.length);
  ok(m.check(reply(2, 7)).ok, "the reply closes the call");
  eq("nothing is left open", 0, m.snapshot().open.length);
}

{
  const m = new Monitor();
  ok(m.check(call(1, 1)).ok, "call 1");
  ok(m.check(call(2, 2)).ok, "call 2 is pipelined before reply 1");
  ok(m.check(reply(1, 2)).ok, "replies may be out of order");
  ok(m.check(reply(2, 1)).ok, "and the older reply is still valid");
  eq("both ids retired", 0, m.snapshot().open.length);
}

{
  const m = new Monitor();
  const r = m.check(reply(1, 1));
  ok(!r.ok && r.error.code === "id", "a reply for an unopened id is refused");
  eq("a refused message changes no state", 0, m.snapshot().used.length);
}

{
  const m = new Monitor();
  ok(m.check(call(1, 1)).ok, "call before a result");
  const r = m.check(result(2, 1));
  ok(!r.ok && r.error.code === "id", "a result for an id the runtime did not request is refused");
  eq("the state is unchanged after the refused result", 1, m.snapshot().open.length);
}

{
  const m = new Monitor();
  ok(m.check(call(1, 1)).ok, "call for the seq test");
  const dup = m.check(call(1, 2));
  ok(!dup.ok && dup.error.code === "seq", "a duplicate seq is refused");
  const gap = m.check(call(3, 2));
  ok(!gap.ok && gap.error.code === "seq", "a gapped seq is refused");
  eq("the seq did not advance", 1, m.snapshot().seq["editor.calls"]);
  const reused = m.check(call(2, 1));
  ok(!reused.ok && reused.error.code === "id", "an id is not reused");
}

{
  const m = new Monitor();
  ok(m.check(call(1, 1)).ok, "call to cancel");
  ok(m.check(request(1, 1)).ok, "the runtime requested an effect before the cancel");
  ok(m.check({ v: V, ch: "editor.calls", op: "cancel", src: "host", seq: 2, id: 1,
    payload: { schema: "wiz.cancel/1" } }).ok, "cancel retires the id");
  ok(m.check(result(3, 1)).ok, "a late result after cancel is ignored, not fatal");
  eq("the late result consumes the retired id", 0, m.snapshot().cancelled.length);
}

{
  const m = new Monitor();
  ok(m.check(call(1, 1)).ok, "call to cancel before a reply");
  ok(m.check({ v: V, ch: "editor.calls", op: "cancel", src: "host", seq: 2, id: 1,
    payload: { schema: "wiz.cancel/1" } }).ok, "cancel retires the id");
  ok(m.check(reply(1, 1)).ok, "a late reply after cancel is ignored, not fatal");
  eq("the cancelled id is gone", 0, m.snapshot().cancelled.length);
}

{
  const m = new Monitor();
  ok(m.check({ v: V, ch: "editor.calls", op: "close", src: "host", seq: 1 }).ok,
    "a call channel can close");
  const after = m.check(call(2, 1));
  ok(!after.ok && after.error.code === "state", "a message after close is refused");
}

{
  const m = new Monitor();
  const r = m.check({ v: V, ch: "wire", op: "error", src: "runtime", seq: 1,
    payload: { schema: "wiz.wire.error/1", code: "channel", message: "closed", fatal: false } });
  ok(r.ok, "the diagnostic channel is accepted");
  eq("it opens no call", 0, m.snapshot().open.length);
}

{
  const m = new Monitor();
  const r = m.check({ ...call(1, 1), ch: "widgets.events", src: "host" });
  ok(!r.ok && r.error.code === "channel", "an unregistered capability is a channel error");
}

// ## The adopt contract (row 13)

function fakeEnv() {
  const dom = minidom();
  const doc = {
    body: { appendChild: () => {} },
    querySelector: () => null,
    defaultView: { Event: class FakeEvent { constructor(type) { this.type = type; } } },
    createElement: (tag) => dom.createElement(tag),
    createTextNode: dom.createTextNode,
    createRange: dom.createRange,
  };
  return { document: doc, navigator: {}, localStorage: { getItem: () => null, setItem: () => {} },
    history: { replaceState: () => {} }, URL: { createObjectURL: () => "", revokeObjectURL: () => {} },
    Blob: class {}, requestAnimationFrame: () => 0, cancelAnimationFrame: () => {},
    ResizeObserver: class { observe() {} disconnect() {} }, setTimeout: () => 0 };
}

function stubModule(html, { ssrHash } = {}) {
  const strings = new Map();
  const steps = [];
  let next = 1;
  const put = (s) => { const p = next++; strings.set(p, s); return p; };
  const module = {
    default: async (opts) => {
      module.options = opts;
      const wasm = {
        _wiz_loom_init: () => 7,
        _wiz_loom_html: () => put(html),
        _wiz_loom_step: (state, p) => { steps.push(strings.get(Number(p))); return Number(state) + 1; },
        stringToNewUTF8: put,
        UTF8ToString: (p) => strings.get(Number(p)) || "",
        _free: (p) => { strings.delete(Number(p)); },
      };
      if (ssrHash !== undefined) wasm._wiz_loom_ssr_hash = () => put(ssrHash);
      return wasm;
    },
    steps,
  };
  return module;
}

function islandRoot(attrs, html) {
  const root = minidom().createElement("div");
  for (const [k, v] of Object.entries(attrs)) root.setAttribute(k, v);
  const frag = parse(html);
  for (const c of [...frag.childNodes]) root.appendChild(c);
  return root;
}

const SSR = '<div class="app"><textarea id="ed">hello</textarea>' +
  '<details open=""><summary>s</summary>x</details>' +
  '<button data-wiz-on-click="0">go</button></div>';
const HASH = hashHtml(SSR);

eq("hashHtml is FNV-1a 32 over UTF-8", "811c9dc5", hashHtml(""));
eq("hashHtml vector 1", "c7574f58", hashHtml('<div class="x">a</div>'));
eq("hashHtml vector 2 (Unicode)", "04ec678c", hashHtml("héllo ☃ 𝄞"));

{
  const root = islandRoot({ "data-wiz-island": "loom/1", "data-wiz-ssr": HASH,
    "data-wiz-props": '{"n":1}' }, SSR);
  const first = root.childNodes[0];
  const field = first.childNodes[0];
  field.value = "typed";
  field.selectionStart = 2;
  field.selectionEnd = 2;
  const runtime = stubModule(SSR);
  const app = await mount(root, { module: runtime, env: fakeEnv(), parse });
  eq("an equal SSR hash adopts", "adopt", app.mode);
  ok(app.adopted, "the handle says adopted");
  ok(root.childNodes[0] === first, "adopt touches no node");
  eq("the textarea keeps its live value", "typed", field.value);
  eq("the textarea keeps its caret", 2, field.selectionStart);
  eq("details keeps its open state", "", first.childNodes[1].getAttribute("open"));
  eq("props reach the transport", 1, runtime.options.transport.props.n);
  eq("props are published", 1, globalThis.wizTransport.props.n);
  eq("the client hash is reported", HASH, app.ssrHash);
  first.childNodes[2].dispatchEvent({ type: "click" });
  eq("adopt still installs the delegated listeners", "click\n0\n", runtime.steps[0]);
}

{
  const root = islandRoot({ "data-wiz-island": "loom/1", "data-wiz-ssr": "deadbeef" }, SSR);
  const first = root.childNodes[0];
  const warnings = [];
  const app = await mount(root, { module: stubModule(SSR), env: fakeEnv(), parse,
    warn: (m) => warnings.push(m) });
  eq("an unequal SSR hash replaces", "replace", app.mode);
  ok(root.childNodes[0] !== first, "replace installs a fresh tree");
  eq("replace warns exactly once", 1, warnings.length);
  ok(/hash does not match/.test(warnings[0]), "the warning names the reason", warnings[0]);
}

{
  const root = islandRoot({ "data-wiz-island": "loom/1" }, SSR);
  const first = root.childNodes[0];
  const warnings = [];
  const app = await mount(root, { module: stubModule(SSR), env: fakeEnv(), parse,
    warn: (m) => warnings.push(m) });
  eq("a missing SSR hash replaces", "replace", app.mode);
  ok(root.childNodes[0] !== first, "the missing hash is a replace");
  eq("missing hash warns once", 1, warnings.length);
  eq("the reason is no-ssr-hash", "no-ssr-hash", app.decision.reason);
}

{
  // The runtime may export its own hash; it wins over hashing the HTML.
  const root = islandRoot({ "data-wiz-island": "loom/1", "data-wiz-ssr": "00000001" }, SSR);
  const first = root.childNodes[0];
  const app = await mount(root, { module: stubModule(SSR, { ssrHash: "00000001" }),
    env: fakeEnv(), parse });
  eq("wiz_loom_ssr_hash is used when exported", "adopt", app.mode);
  ok(root.childNodes[0] === first, "the exported hash adopts without hashing html");
}

{
  const root = islandRoot({ "data-wiz-island": "loom/1", "data-wiz-ssr": HASH }, SSR);
  const first = root.childNodes[0];
  let thrown = null;
  try {
    await mount(root, { module: async () => ({}), env: fakeEnv(), parse });
  } catch (e) { thrown = e; }
  ok(thrown && /does not export/.test(thrown.message), "an ABI failure still throws");
  ok(root.childNodes[0] === first, "the static DOM is left in place");
  const error = root.childNodes.find((n) => n.getAttribute && n.getAttribute("data-wiz-error") != null);
  ok(error && /does not export/.test(error.textContent), "a plain-text data-wiz-error is written",
    error && error.textContent);
}

{
  const root = islandRoot({ "data-wiz-island": "loom/1", "data-wiz-ssr": HASH,
    "data-wiz-props": "{not json" }, SSR);
  const warnings = [];
  const app = await mount(root, { module: stubModule(SSR), env: fakeEnv(), parse,
    warn: (m) => warnings.push(m) });
  eq("malformed props do not fail the mount", "adopt", app.mode);
  ok(warnings.some((m) => /data-wiz-props/.test(m)), "malformed props warn");
  eq("no props are published", null, globalThis.wizProps);
}

{
  const root = islandRoot({}, SSR);
  eq("a non-island container is not adopted", "no-island",
    decideAdopt({ root, html: SSR }).reason);
  const info = islandInfo(root);
  ok(!info.island, "islandInfo sees no island");
  writeError(root, null, "why");
  const error = root.childNodes.find((n) => n.getAttribute && n.getAttribute("data-wiz-error") != null);
  ok(error && error.textContent === "why", "writeError writes plain text");
}

// ## The single validation table

const doc = readFileSync(new URL("../../docs/notes/loom-wire-protocol.md", import.meta.url), "utf8");
const rows = new Map();
for (const line of doc.split("\n")) {
  const m = /^\|\s*(\d+)\s*\|\s*([^|]+?)\s*\|/.exec(line);
  if (m) rows.set(Number(m[1]), m[2].trim());
}
eq("the wire owns rows 3-7 and 10", "3,4,5,6,7,10", WIRE_VALIDATION_IDS.join(","));
for (const row of VALIDATION) {
  eq(`row ${row.id} names the same boundary in doc and code`, row.boundary, rows.get(row.id));
}
ok(/FNV-1a 32-bit/.test(doc), "the doc names the adopt hash");
ok(/data-wiz-island/.test(doc) && /data-wiz-ssr/.test(doc) && /data-wiz-props/.test(doc),
  "the doc names the island attributes");
ok(/no general hydration diff/i.test(doc), "the doc keeps general hydration out of scope");

console.log(failed === 0 ? "wire: all checks passed" : `wire: ${failed} failure(s)`);
process.exit(failed === 0 ? 0 : 1);
