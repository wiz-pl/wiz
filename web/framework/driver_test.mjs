// The Loom driver's ABI under Node (web/framework/driver.js): mount a stub module's SSR
// into minidom, dispatch DOM events, and check the event string each step receives —
// `event "\n" index "\n" payload`, with a form control's live value for input/change and
// the key for keydown/keyup. This is the contract `Loom.LiveApp` parses in Wiz
// (`web/playground_editor_gen.wiz` checks the Wiz side); a browser is not needed.
//
//   node web/framework/driver_test.mjs
"use strict";
import { start, payloadOf, utf8Length } from "./driver.js";
import { parse, serialize } from "./minidom.mjs";

let failed = 0;
const ok = (cond, what, detail = "") => {
  if (cond) console.log("ok: " + what);
  else { failed++; console.log("FAIL: " + what + (detail ? "\n  " + detail : "")); }
};
const eq = (what, want, got) => ok(Object.is(got, want), what,
  `want ${JSON.stringify(want)}\n  got  ${JSON.stringify(got)}`);

const SSR = '<div><textarea id="editor" data-wiz-on-input="0">x</textarea>' +
  '<button data-wiz-on-click="1" data-wiz-on-keydown="2">Run</button></div>';

// A stub module: the three exports driver.js calls, a pointer table for the strings, and
// a step that records what it was sent.
const steps = [];
function stubModule(html) {
  const strings = new Map();
  let next = 1;
  const put = (s) => { const p = next++; strings.set(p, s); return p; };
  return {
    _wiz_loom_init: () => 7,
    _wiz_loom_html: () => put(html),
    _wiz_loom_step: (state, p) => {
      steps.push({ state: Number(state), event: strings.get(Number(p)) });
      return Number(state) + 1;
    },
    stringToNewUTF8: (s) => put(s),
    UTF8ToString: (p) => strings.get(Number(p)) || "",
    _free: (p) => { strings.delete(Number(p)); },
    strings,
  };
}

const wasm = stubModule(SSR);
const root = parse("");
const seen = [];
const app = start(wasm, root, {
  parse,
  events: ["click", "input", "keydown"],
  onStep: (state, event, index, payload) => seen.push({ state, event, index, payload }),
});

// ## The mount
ok(serialize(root) === SSR, "the SSR is mounted", serialize(root));
ok(app.state() === 7, "the state starts at wiz_loom_init", String(app.state()));

// ## The payload rule
const target = (value, attrs = {}) => ({ value, getAttribute: (k) => attrs[k] ?? null });
ok(payloadOf("input", { target: target("a\nb") }) === "a\nb", "input: the live value (newlines kept)");
ok(payloadOf("change", { target: target("<x>") }) === "<x>", "change: the live value");
ok(payloadOf("input", { target: target(undefined, { value: "attr" }) }) === "attr",
  "input: the value attribute when there is no property");
ok(payloadOf("keydown", { key: "Enter" }) === "Enter", "keydown: the key");
ok(payloadOf("keydown", { key: "Enter", ctrlKey: true }) === "Enter\nc",
  "keydown: Ctrl is carried after the key");
ok(payloadOf("keydown", { key: "s", metaKey: true }) === "s\nm",
  "keydown: ⌘ is carried after the key");
ok(payloadOf("keydown", { key: "Enter", ctrlKey: true, shiftKey: true }) === "Enter\ncs",
  "keydown: every modifier, in a fixed order");
ok(payloadOf("keyup", { key: "⌘" }) === "⌘", "keyup: the key");
ok(payloadOf("keydown", { key: "Tab", target: { selectionStart: 1, selectionEnd: 3 } }) === "Tab\n\n@1@3",
  "keydown: a text field's selection follows the key");
ok(payloadOf("keydown", { key: "Enter", ctrlKey: true, target: { selectionStart: 2, selectionEnd: 2 } })
  === "Enter\nc\n@2@2", "keydown: modifiers and selection together");
ok(payloadOf("click", { target: target("x") }) === "", "click: no payload");

// ## The event strings (the DOM path too: the delegated listeners on `root`)
const textarea = root.childNodes[0].childNodes[0];
const button = root.childNodes[0].childNodes[1];
const fire = (node, e) => { node.dispatchEvent(e); };

textarea.value = "a\nb";
fire(textarea, { type: "input" });
fire(button, { type: "keydown", key: "Enter" });
fire(button, { type: "click" });

ok(steps.length === 3, "three events, three steps", String(steps.length));
ok(steps[0] && steps[0].event === "input\n0\na\nb", "input sends its value as the payload",
  JSON.stringify(steps[0] && steps[0].event));
ok(steps[1] && steps[1].event === "keydown\n2\nEnter", "keydown sends the key",
  JSON.stringify(steps[1] && steps[1].event));
ok(steps[2] && steps[2].event === "click\n1\n", "click sends an empty payload",
  JSON.stringify(steps[2] && steps[2].event));
ok(steps[0].state === 7 && steps[2].state === 9, "each step gets the previous state",
  JSON.stringify(steps.map((s) => s.state)));

// ## onStep sees the payload and the new state
ok(seen.length === 3 && seen[0].payload === "a\nb" && seen[0].event === "input" && seen[0].index === 0,
  "onStep reports event, index and payload", JSON.stringify(seen[0]));
ok(seen[2].state === 10, "onStep gets the state after the step", JSON.stringify(seen[2]));

// ## `Loom.onPrevent`: the runtime decides whether a marked handler consumes the key
const guardedSSR = '<div><textarea data-wiz-on-keydown="0" data-wiz-prevent-keydown="1"></textarea></div>';
const guarded = stubModule(guardedSSR);
const asks = [];
guarded._wiz_loom_consume = (_state, p) => {
  const ev = guarded.strings.get(Number(p)) || "";
  asks.push(ev);
  return /^keydown\n0\nEnter/.test(ev) ? 1 : 0;   // the runtime consumes Ctrl+Enter
};
const guardedRoot = parse("");
const mainPatch = globalThis.wizPatch;   // the main tree's applier (the guard test has its own)
start(guarded, guardedRoot, { parse, events: ["keydown"] });
globalThis.wizPatch = mainPatch;
const area = guardedRoot.childNodes[0].childNodes[0];
const key = (e) => { area.dispatchEvent(e); return !!e.defaultPrevented; };
ok(key({ type: "keydown", key: "a" }) === false,
  "an unconsumed key still types (the runtime did not prevent)");
ok(key({ type: "keydown", key: "Enter", ctrlKey: true }) === true,
  "a consumed key is prevented");
ok(asks.length === 2 && asks[0] === "keydown\n0\na\n\n@0@0" &&
   asks[1] === "keydown\n0\nEnter\nc\n@0@0",
  "the consume query gets the same event string the step did", JSON.stringify(asks));

// ## js_patch is wired to the patch applier
globalThis.wizPatch(JSON.stringify([{ op: "text", path: "0.0", text: "patched" }]));
ok(serialize(root).includes("patched"), "wizPatch applies a patch to the mounted tree", serialize(root));
eq("a non-island mount reports the replace mode", "replace", globalThis.wizLoomMode);

// ## resync is the JS-on reload: one full replace, never a partial adopt
const beforeResync = root.childNodes[0];
app.resync();
ok(root.childNodes[0] !== beforeResync, "resync replaces the container's tree");
ok(serialize(root) === SSR, "resync re-renders the current state's SSR", serialize(root));

// ## setState: a page that changed the state itself hands it back
app.setState(41);
// resync above replaced the tree, so take the button from the current root.
const current = root.childNodes[0].childNodes[1];
fire(current, { type: "click" });
ok(steps[steps.length - 1].state === 41, "the next event steps from the state the page set",
  JSON.stringify(steps[steps.length - 1]));

// ## The i32 word entry (`wiz-web/1`): the same event strings as Numbers
// A browser module exports `wiz_step(state, payload_ptr, payload_len) -> state` instead
// of the i64 `wiz_loom_step`; the driver must use it, pass unsigned words, and normalise
// the (sign-extended) i32 result. The i64 entry stays the fallback the rest of this file
// exercises.
ok(app.abi === "i64", "a module without wiz_step steps through the i64 entry", app.abi);

function wordModule(html) {
  const strings = new Map();
  const calls = [];
  let next = 1;
  const put = (s) => { const p = next++; strings.set(p, s); return p; };
  const module = {
    answer: undefined,          // the word `_wiz_step` returns (undefined: the state + 1)
    calls,
    htmlStates: [],             // the type of the state the i64 entries are given
    _wiz_loom_init: () => 7,
    _wiz_loom_html: (state) => { module.htmlStates.push(typeof state); return put(html); },
    _wiz_step: (state, p, len) => {
      calls.push({ state, p, len, event: strings.get(p) });
      return module.answer === undefined ? state + 1 : module.answer;
    },
    stringToNewUTF8: put,
    UTF8ToString: (p) => strings.get(p) || "",
    _free: (p) => { strings.delete(p); },
  };
  return module;
}

const wordWasm = wordModule(SSR);
const wordRoot = parse("");
const wordSeen = [];
const wordApp = start(wordWasm, wordRoot, {
  parse,
  events: ["input", "click"],
  onStep: (state) => wordSeen.push(state),
});
eq("the module's step entry is reported", "i32", wordApp.abi);
eq("the SSR is mounted through the word entry too", SSR, serialize(wordRoot));
eq("a word module's html call still gets a BigInt state", "bigint", wordWasm.htmlStates[0]);

const wordArea = wordRoot.childNodes[0].childNodes[0];
wordArea.value = "héllo";
fire(wordArea, { type: "input" });
const one = wordWasm.calls[0];
ok(one !== undefined, "the event reaches wiz_step", JSON.stringify(wordWasm.calls));
eq("the event string is the same one the i64 entry gets", "input\n0\nhéllo", one && one.event);
ok(one && typeof one.state === "number" && typeof one.p === "number" && typeof one.len === "number",
  "the state, the address and the length are Numbers (no BigInt on the step path)",
  JSON.stringify(one && { state: typeof one.state, p: typeof one.p, len: typeof one.len }));
eq("the length is the payload's UTF-8 byte count", 14, one && one.len);
eq("the state is the word the step returned", 8, wordApp.state());
eq("onStep sees the word state", 8, wordSeen[0]);

// A Wasm i32 result arrives in JavaScript sign-extended: the handle is unsigned, so the
// driver normalises it, and the next step passes the same word back.
wordWasm.answer = -1;                                   // 0xFFFFFFFF as Wasm returns it
fire(wordRoot.childNodes[0].childNodes[1], { type: "click" });
eq("an i32 result above 0x7FFFFFFF is normalised to an unsigned word", 4294967295, wordApp.state());
fire(wordRoot.childNodes[0].childNodes[1], { type: "click" });
eq("and the next step passes that word back", 4294967295, wordWasm.calls[2] && wordWasm.calls[2].state);

// The length rule itself.
eq("utf8Length: ASCII", 3, utf8Length("abc"));
eq("utf8Length: two bytes for U+00E9", 2, utf8Length("é"));
eq("utf8Length: four bytes above U+FFFF", 4, utf8Length("😀"));
eq("utf8Length: a lone surrogate is written as U+FFFD (three bytes)", 3, utf8Length("\ud800"));

console.log(failed === 0 ? "loom driver: all checks passed" : `loom driver: ${failed} failure(s)`);
process.exit(failed === 0 ? 0 : 1);
