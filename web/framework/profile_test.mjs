// The profile seam (web/framework/profile.js): a Wasm instance and a `--target js` module
// namespace normalise to one interface, and `driver.start` drives both the same way. No
// Wasm build and no browser: two stubs, minidom, and the driver's real DOM path.
//
//   node web/framework/profile_test.mjs
"use strict";
import { profile, kindOf, hasABI, isWasm, isJs } from "./profile.js";
import { start } from "./driver.js";
import { parse, serialize } from "./minidom.mjs";

let failed = 0;
const ok = (cond, what, detail = "") => {
  if (cond) console.log("ok: " + what);
  else { failed++; console.log("FAIL: " + what + (detail ? "\n  " + detail : "")); }
};
const eq = (what, want, got) => ok(Object.is(got, want), what,
  `want ${JSON.stringify(want, (k, v) => typeof v === "bigint" ? String(v) + "n" : v)}\n` +
  `  got  ${JSON.stringify(got, (k, v) => typeof v === "bigint" ? String(v) + "n" : v)}`);

const SSR = '<div><button data-wiz-on-click="0" data-wiz-prevent-click="1">go</button>' +
  '<main>home</main></div>';

// ## A Wasm instance: `_` names, i64 state, UTF-8 in linear memory, retain/free
function wasmStub() {
  const strings = new Map();
  const log = { retained: 0, freed: 0, htmlStates: [], steps: [], consumed: [] };
  let next = 1;
  const put = (s) => { const p = next++; strings.set(p, s); return p; };
  return {
    log,
    _wiz_loom_init: () => 7n,
    _wiz_loom_html: (state) => { log.htmlStates.push(state); return put(SSR); },
    _wiz_loom_step: (state, p) => {
      log.steps.push(strings.get(Number(p)));
      return state + 1n;
    },
    _wiz_loom_consume: (_state, p) => { log.consumed.push(strings.get(Number(p))); return 1; },
    _wiz_retain: () => { log.retained++; },
    stringToNewUTF8: put,
    UTF8ToString: (p) => strings.get(Number(p)) || "",
    _free: (p) => { log.freed++; strings.delete(Number(p)); },
  };
}

// ## A `--target js` module namespace: bare names, a value state, JS strings, no memory
function jsStub() {
  const log = { steps: [], consumed: [] };
  return {
    log,
    wiz_loom_init: () => ({ route: "home" }),
    wiz_loom_html: () => SSR,
    wiz_loom_step: (state, ev) => { log.steps.push(ev); return { route: "home", after: ev }; },
    wiz_loom_consume: (_state, ev) => { log.consumed.push(ev); return 1n; },
    wizStringToJs: (v) => v,
  };
}

// ## Detection: the two kinds cannot be confused (the `_` prefix is the difference)
eq("a Wasm instance is the wasm kind", "wasm", kindOf(wasmStub()));
eq("a JS namespace is the js kind", "js", kindOf(jsStub()));
eq("neither is null", null, kindOf({}));
ok(isWasm(wasmStub()) && !isJs(wasmStub()), "isWasm/isJs are exclusive");
ok(isJs(jsStub()) && !isWasm(jsStub()), "and the other way");
ok(hasABI(wasmStub()) && hasABI(jsStub()), "both have the whole ABI");
ok(!hasABI({ wiz_loom_init: () => 0 }), "a partial ABI is refused");
ok(!hasABI(null), "nothing is not a runtime");

// ## The interface: the same members, whatever the kind
const wm = wasmStub();
const jm = jsStub();
const wp = profile(wm);
const jp = profile(jm);
eq("a profile is a profile", wp, profile(wp));
for (const name of ["present", "init", "html", "step", "requests", "consume", "ssrHash",
  "call", "ask", "stringOf"]) {
  ok(typeof wp[name] === "function" && typeof jp[name] === "function",
    "both profiles have " + name);
}

// ## Wasm: the ownership rule, unchanged (retain before a read, free the string)
eq("html returns the module's string", SSR, wp.html(7n));
eq("a read-only call takes one extra reference", 1, wm.log.retained);
eq("and frees the string it copied", 1, wm.log.freed);
eq("the state it read is the one it was given", 7n, wm.log.htmlStates[0]);
eq("init returns the module's state", 7n, wp.init());
eq("step marshals the event string", 8n, wp.step(7n, "click\n0\n"));
eq("the event string the runtime saw", "click\n0\n", wm.log.steps[0]);
eq("consume asks the runtime", true, wp.consume(7n, "click\n0\n"));

// ## JS: nothing to allocate, nothing to free, the state is the module's own value
const jsState = jm.wiz_loom_init();
eq("html is the module's string", SSR, jp.html(jsState));
const nextState = jp.step(jsState, "click\n0\n");
ok(typeof nextState === "object" && nextState !== jsState,
  "step returns the module's next state value");
eq("the event string the runtime saw", "click\n0\n", jm.log.steps[0]);
eq("consume is the module's Nat", true, jp.consume(jsState, "click\n0\n"));
eq("stringOf passes a JS string through", "x", jp.stringOf("x"));
const wizStringLike = { t: 0, f: [] };
eq("stringOf hands a non-string to the module's wizStringToJs", wizStringLike,
  jp.stringOf(wizStringLike));

// ## A runtime with no optional exports: the absence rules are the driver's old ones
const minimal = {
  _wiz_loom_init: () => 1n,
  _wiz_loom_html: () => 0,
  _wiz_loom_step: (s) => s,
  UTF8ToString: () => "",
  _free: () => {},
  stringToNewUTF8: () => 0,
};
const mp = profile(minimal);
eq("requests is empty when the runtime has none", "", mp.requests(1n));
eq("ssrHash is null when the runtime has none", null, mp.ssrHash(1n));
eq("consume keeps the old rule when the runtime has none", true, mp.consume(1n, "click\n0\n"));
eq("present says what is there", false, mp.present("wiz_loom_requests"));

// ## The driver does not branch on the kind: same DOM, same event strings, same answer
function drive(module) {
  const root = parse("");
  const steps = [];
  const app = start(module, root, {
    parse,
    events: ["click"],
    onStep: (state, event, index, payload) => steps.push({ state, event, index, payload }),
  });
  const button = root.childNodes[0].childNodes[0];
  const event = { type: "click" };
  button.dispatchEvent(event);
  return { root, steps, app, html: serialize(root), prevented: event.defaultPrevented === true };
}
const wasmRun = drive(wasmStub());
const jsRun = drive(jsStub());
eq("both mount the same SSR", wasmRun.html, jsRun.html);
eq("both report the event and the handler index", "click/0",
  `${wasmRun.steps[0].event}/${wasmRun.steps[0].index}`);
eq("and the js run agrees", "click/0", `${jsRun.steps[0].event}/${jsRun.steps[0].index}`);
eq("both prevent the default the runtime consumed", true, wasmRun.prevented && jsRun.prevented);
eq("the wasm state is an i64", 8n, wasmRun.app.state());
ok(typeof jsRun.app.state() === "object", "the js state is the runtime's value");
eq("the driver reports the kind it normalised", "wasm", wasmRun.app.profile.kind);
eq("and the js one", "js", jsRun.app.profile.kind);

// ## A module that is not a runtime
let threw = null;
try { profile({ wiz_loom_init: () => 0 }); } catch (e) { threw = e; }
ok(threw instanceof TypeError && /wiz_loom_init/.test(threw.message),
  "a module without the whole ABI is a TypeError", threw && threw.message);

console.log(failed === 0 ? "profile: all checks passed" : `profile: ${failed} failure(s)`);
process.exit(failed === 0 ? 0 : 1);
