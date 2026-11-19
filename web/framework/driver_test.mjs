// The Loom driver's ABI under Node (web/framework/driver.js): mount a stub module's SSR
// into minidom, dispatch DOM events, and check the event string each step receives —
// `event "\n" index "\n" payload`, with a form control's live value for input/change and
// the key for keydown/keyup. This is the contract `Loom.LiveApp` parses in Wiz
// (`web/playground_editor_gen.wiz` checks the Wiz side); a browser is not needed.
//
//   node web/framework/driver_test.mjs
"use strict";
import { start, payloadOf } from "./driver.js";
import { parse, serialize } from "./minidom.mjs";

let failed = 0;
const ok = (cond, what, detail = "") => {
  if (cond) console.log("ok: " + what);
  else { failed++; console.log("FAIL: " + what + (detail ? "\n  " + detail : "")); }
};

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
      return state + 1;
    },
    stringToNewUTF8: (s) => put(s),
    UTF8ToString: (p) => strings.get(Number(p)) || "",
    _free: (p) => { strings.delete(Number(p)); },
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
ok(payloadOf("keyup", { key: "⌘" }) === "⌘", "keyup: the key");
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

// ## js_patch is wired to the patch applier
globalThis.wizPatch(JSON.stringify([{ op: "text", path: "0.0", text: "patched" }]));
ok(serialize(root).includes("patched"), "wizPatch applies a patch to the mounted tree", serialize(root));

// ## setState: a page that changed the state itself hands it back
app.setState(41);
fire(button, { type: "click" });
ok(steps[steps.length - 1].state === 41, "the next event steps from the state the page set",
  JSON.stringify(steps[steps.length - 1]));

console.log(failed === 0 ? "loom driver: all checks passed" : `loom driver: ${failed} failure(s)`);
process.exit(failed === 0 ? 0 : 1);
