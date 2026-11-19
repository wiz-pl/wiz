// The mount contract under Node (web/framework/mount.js): the module exports one
// function, it finds or creates the element, instantiates the runtime, mounts its SSR,
// turns DOM events into steps, marshals the page's `call`s, and installs the host
// capabilities a Wiz runtime cannot reach itself (clipboard, download, storage, URL,
// animation frames, resize). A browser is not needed: the DOM is minidom and the browser
// globals are a fake env.
//
//   node web/framework/mount_test.mjs
"use strict";
import * as contract from "./mount.js";
import { mount } from "./mount.js";
import { parse, serialize, document as minidom } from "./minidom.mjs";

let failed = 0;
const ok = (cond, what, detail = "") => {
  if (cond) console.log("ok: " + what);
  else { failed++; console.log("FAIL: " + what + (detail ? "\n  " + detail : "")); }
};
const eq = (what, want, got) => ok(Object.is(got, want), what,
  `want ${JSON.stringify(want)}\n  got  ${JSON.stringify(got)}`);

// ## One export: the page has nothing else to call
eq("mount is the module's only export", "mount", Object.keys(contract).sort().join(","));
eq("and it is a function", "function", typeof contract.mount);

// ## A fake browser env (the host's capabilities, recorded)
function fakeEnv() {
  const dom = minidom();
  const created = [];
  const anchors = [];
  const frames = [];
  const blobs = [];
  const storage = new Map();
  const urlCalls = [];
  const observers = [];
  const doc = {
    body: { appendChild: (el) => { created.push(el); return el; } },
    querySelector: () => null,
    createElement: (tag) => {
      const el = dom.createElement(tag);
      el.style = {};
      el.select = () => { el.selected = true; };
      el.remove = () => { el.removed = true; };
      el.click = () => { anchors.push(el); };
      return el;
    },
    createTextNode: dom.createTextNode,
    createRange: dom.createRange,
    execCommand: () => true,
  };
  return {
    document: doc,
    navigator: { clipboard: { writeText: async (t) => { doc.clipboard = t; } } },
    localStorage: {
      getItem: (k) => (storage.has(k) ? storage.get(k) : null),
      setItem: (k, v) => { storage.set(k, String(v)); },
    },
    history: { replaceState: (_s, _t, href) => { urlCalls.push(href); } },
    URL: {
      createObjectURL: (b) => { blobs.push(b); return "blob:" + blobs.length; },
      revokeObjectURL: () => {},
    },
    Blob: class { constructor(parts, opts) { this.parts = parts; this.type = opts && opts.type; } },
    requestAnimationFrame: (fn) => { frames.push(fn); return frames.length; },
    cancelAnimationFrame: () => {},
    ResizeObserver: class { constructor(fn) { this.fn = fn; observers.push(this); } observe(el) { this.el = el; } disconnect() { this.gone = true; } },
    setTimeout: (fn) => { fn(); return 0; },
    created, anchors, frames, blobs, storage, urlCalls, observers, doc,
  };
}

// A stub runtime: the three ABI exports a mount needs, plus the page's `show`.
function stubModule(html) {
  const strings = new Map();
  const steps = [];
  const shown = [];
  let next = 1;
  const put = (s) => { const p = next++; strings.set(p, s); return p; };
  const module = {
    default: async (opts) => {
      module.options = opts;
      return {
        _wiz_loom_init: () => 7,
        _wiz_loom_html: () => put(html),
        _wiz_loom_step: (state, p) => { steps.push({ state: Number(state), event: strings.get(Number(p)) }); return Number(state) + 1; },
        _wiz_loom_show: (state, p) => { shown.push(strings.get(Number(p))); return Number(state) + 1; },
        stringToNewUTF8: put,
        UTF8ToString: (p) => strings.get(Number(p)) || "",
        _free: (p) => { strings.delete(Number(p)); },
      };
    },
    steps, shown,
  };
  return module;
}

const SSR = '<div><button data-wiz-on-click="0">go</button></div>';
const env = fakeEnv();
const runtime = stubModule(SSR);
const transport = { engine: { evaluate: () => "" } };
const app = await mount("#root", { module: runtime, transport, env, parse });

// ## The element: found, or created from a selector
ok(env.created.length === 1 && env.created[0].getAttribute("id") === "root",
  "a missing #id element is created and mounted", JSON.stringify(env.created.map((e) => e.getAttribute("id"))));
const root = env.created[0];
eq("the SSR is mounted inside the created element", '<div id="root">' + SSR + "</div>", serialize(root));
eq("the state starts at wiz_loom_init", 7, app.state());
eq("the transport reaches the module factory", transport, runtime.options.transport);
eq("and is published for the runtime", transport, globalThis.wizTransport);

// ## Events: the delegated listener steps the runtime
root.childNodes[0].childNodes[0].dispatchEvent({ type: "click" });
eq("the event is the driver's string", "click\n0\n", runtime.steps[0] && runtime.steps[0].event);
eq("the state moves", 8, app.state());

// ## The page's entry points: `call` owns the strings and keeps the returned state
app.call("wiz_loom_show", "ok\n3 : Nat");
eq("a string argument arrives", "ok\n3 : Nat", runtime.shown[0]);
eq("the state is the call's return", 9, app.state());
let threw = false;
try { app.call("wiz_loom_missing"); } catch (e) { threw = /no wiz_loom_missing/.test(e.message); }
ok(threw, "an unknown entry point is an error, not a silent no-op");

// ## The host capabilities (the only browser reach a runtime gets)
const host = globalThis.wizHost;
eq("the host is published", host, app.host);
eq("clipboard", true, await host.clipboard("copied"));
eq("clipboard reached navigator", "copied", env.doc.clipboard);
host.storage.set("wiz-playground-draft-v1", "{}");
eq("storage.set", "{}", env.storage.get("wiz-playground-draft-v1"));
eq("storage.get", "{}", host.storage.get("wiz-playground-draft-v1"));
eq("storage.get on a missing key", null, host.storage.get("absent"));
eq("url", true, host.url("./?code=x"));
eq("url reached history", "./?code=x", env.urlCalls[0]);
eq("download", true, host.download("playground.wiz", "code"));
ok(env.anchors.length === 1 && env.anchors[0].download === "playground.wiz",
  "download clicks a named link", JSON.stringify(env.anchors.map((a) => a.download)));
eq("download carries the text", "code", env.blobs[0] && env.blobs[0].parts[0]);

let ticked = 0;
const cancel = host.tick(() => { ticked++; });
env.frames[0]();
eq("tick runs on an animation frame", 1, ticked);
cancel();
let resized = 0;
host.onResize(() => { resized++; });
env.observers[0].fn();
eq("onResize observes the mount point", 1, resized);
ok(env.observers[0].el === root, "onResize observes the mount point itself");

// ## A module that is not a runtime is refused before the page is touched
let rejected = null;
try { await mount("#root", { module: async () => ({}) , env, parse }); }
catch (e) { rejected = e; }
ok(rejected instanceof TypeError && /does not export/.test(rejected.message),
  "a module without the Loom ABI is refused", rejected && rejected.message);

// ## The element may be an element (the browser's document.body, a test's root)
const direct = parse("");
const app2 = await mount(direct, { module: stubModule(SSR), env, parse });
eq("an element target is used as it is", SSR, serialize(direct));
eq("and its own state starts fresh", 7, app2.state());

// ## Effect requests: the runtime's `wiz_loom_requests` JSON reaches `onRequest` in
// order, and an acknowledged request is not reported again.
function requestModule(html) {
  const strings = new Map();
  let next = 1;
  const put = (s) => { const p = next++; strings.set(p, s); return p; };
  const module = {
    default: async () => ({
      _wiz_loom_init: () => 1,
      _wiz_loom_html: () => put(html),
      _wiz_loom_step: (s) => s,
      _wiz_loom_requests: () => put(JSON.stringify(module.pending)),
      _wiz_loom_effect: (_s, kp, ap) => {
        // The page acknowledges `effect("ack", <request kind>)`: the first string is
        // "ack", the second is the request kind.
        if (strings.get(Number(kp)) !== "ack") return 1;
        const kind = strings.get(Number(ap));
        module.pending = module.pending.filter((r) => r.kind !== kind);
        return 1;
      },
      stringToNewUTF8: put,
      UTF8ToString: (p) => strings.get(Number(p)) || "",
      _free: (p) => { strings.delete(Number(p)); },
    }),
    pending: [],
  };
  return module;
}
const req = requestModule(SSR);
const requested = [];
let reqApp = null;
const reqRoot = parse("");
reqApp = await mount(reqRoot, {
  module: req, env: fakeEnv(), parse,
  onRequest: (kind, payload) => {
    requested.push(kind + ":" + payload);
    reqApp.call("wiz_loom_effect", "ack", kind, "");   // the page acks what it serviced
  },
});
ok(requested.length === 0, "no request is reported until there is one");
req.pending = [{ kind: "run", payload: "" }, { kind: "sync", payload: "{}" }];
reqRoot.childNodes[0].childNodes[0].dispatchEvent({ type: "click" });
eq("a step reports both requests, in order", "run:|sync:{}", requested.join("|"));
eq("the acknowledged requests are gone", 0, JSON.parse(reqApp.requests() || "[]").length);

console.log(failed === 0 ? "mount: all checks passed" : `mount: ${failed} failure(s)`);
process.exit(failed === 0 ? 0 : 1);
