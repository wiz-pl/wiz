/* Mount the Loom ABI demo (`examples/js-loom/boot.wiz`, built with `--target js`) the way
 * a page does — `web/framework/mount.js`, which goes through `driver.js` and `profile.js` —
 * with the fake DOM behind the module's `extern "js.wiz.dom.…"` calls and `minidom.mjs`
 * as the rendered page. A browser is not needed, and no Wasm is involved: the runtime is
 * an ES module namespace.
 *
 *   wiz build examples/js-loom/boot.wiz --target js -o /tmp/boot.mjs
 *   node examples/js-loom/mount_test.mjs /tmp/boot.mjs
 *
 * What it proves: `wiz_loom_init` gives the state, `wiz_loom_html` the first paint,
 * `wiz_loom_step` an event (whose patch list lands in the tree through `wizPatch`),
 * `wiz_loom_requests`/`wiz_loom_effect` the effect round trip, `wiz_loom_consume` the
 * default-action answer, and `wiz_loom_probe` a Wiz closure registered on a real
 * listener. Exit code 0 means every assertion passed.
 */

import { pathToFileURL } from "node:url";
import { resolve } from "node:path";
import { install as installFake } from "./fake-dom.mjs";
import { mount } from "../../web/framework/mount.js";
import { parse, serialize, document as minidomDocument } from "../../web/framework/minidom.mjs";

const file = process.argv[2];
if (!file) {
  console.error("usage: node examples/js-loom/mount_test.mjs BUILT.mjs");
  process.exit(2);
}

let failed = 0;
const ok = (cond, what, detail = "") => {
  if (cond) console.log("ok: " + what);
  else { failed++; console.log("FAIL: " + what + (detail ? "\n  " + detail : "")); }
};
const eq = (what, want, got) => ok(Object.is(got, want), what,
  `want ${JSON.stringify(want)}\n  got  ${JSON.stringify(got)}`);

// The module's DOM: the fake DOM, which also installs `globalThis.document` so
// `js.document.createElement` resolves. The *page* is minidom (`env` + `parse`).
const dom = installFake();
const root = parse("");
const steps = [];
const requests = [];

const app = await mount(root, {
  module: () => import(pathToFileURL(resolve(file)).href),
  env: { document: minidomDocument() },
  parse,
  events: ["click", "keydown"],
  onStep: (state, event, index, payload) => steps.push({ event, index, payload }),
  onRequest: (kind, payload) => requests.push({ kind, payload }),
});

const SSR = '<div id="app"><nav><a href="#/" data-wiz-on-click="0">Home</a> ' +
  '<a href="#/about" data-wiz-on-click="1" data-wiz-prevent-click="1">About</a></nav>' +
  '<main data-view="home" data-effects="0">Home</main></div>';

// ## The seam: a JS module namespace is a runtime
eq("profile.js recognises the module as the js kind", "js", app.profile.kind);
ok(app.profile.module && typeof app.profile.module.wiz_loom_step === "function",
  "the profile keeps the module it normalised");
ok(typeof app.state() === "object" && app.state() !== null,
  "the state is a Wiz value (a JavaScript object), not a pointer");
eq("wiz_loom_html is the first paint", SSR, app.html());
eq("mount rendered it into the page", SSR, serialize(root));
eq("a non-island mount reports the replace mode", "replace", globalThis.wizLoomMode);

// ## wiz_loom_step: a click routes, and the patch list lands in the tree
const walk = (n, f) => {
  if (f(n)) return n;
  for (const c of (n.childNodes || [])) {
    const found = walk(c, f);
    if (found) return found;
  }
  return null;
};
const aboutLink = walk(root, (n) => n.getAttribute && n.getAttribute("data-wiz-on-click") === "1");
ok(aboutLink !== null, "the About link is in the mounted tree");
const mainEl = walk(root, (n) => String(n.tagName || "").toLowerCase() === "main");
ok(mainEl !== null && mainEl.textContent === "Home", "the initial view is Home");

const event = { type: "click" };
aboutLink.dispatchEvent(event);
eq("the step saw the handler index", 1, steps[0] && steps[0].index);
eq("the step's event is a click", "click", steps[0] && steps[0].event);
eq("the patch list set the new title", "About", mainEl.textContent);
eq("the patch list set data-view", "about", mainEl.getAttribute("data-view"));
eq("a marked click consumed its default", true, event.defaultPrevented === true);

// ## wiz_loom_requests + wiz_loom_effect: the effect round trip
eq("the step asked the host for the URL change", "#/about", requests[0] && requests[0].payload);
eq("the request is a url effect", "url", requests[0] && requests[0].kind);
ok((app.requests() || "").includes("#/about"), "the request stays pending until acknowledged",
  app.requests());
app.call("wiz_loom_effect", "url", "ack", "");
eq("the effect cleared the request", "[]", app.requests());
eq("the effect is counted in the tree", "1", mainEl.getAttribute("data-effects"));
eq("no second request was raised", 1, requests.length);

// ## wiz_loom_probe: a Wiz closure on a listener, through the fake DOM
await app.module.wiz_loom_probe();
const box = dom.root.children[0];
const button = box && box.children[0];
ok(box && box.attrs.get("id") === "probe", "the probe built its box in the host's root");
eq("the probe set the box's text", "ready", box && box.text);
ok(button && button.listeners.length === 1 && button.listeners[0].event === "click",
  "the probe registered one click listener");
app.module.wizApply(button.listeners[0].fn, [button, 0]);
eq("the Wiz closure ran on the click", "clicked", box.text);
eq("and set its attribute", "1", box.attrs.get("data-clicked"));

if (failed === 0) {
  console.log("PASS loom mount: init, html, step, effect and a listener, through mount()");
} else {
  console.log(`FAIL loom mount: ${failed} assertion(s) failed`);
  process.exitCode = 1;
}
