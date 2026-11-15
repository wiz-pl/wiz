// Test the widget half under Node, with no browser: render each widget kind, apply
// `Widget.handle`'s patches to the SSR HTML with web/framework/runtime.js and
// web/framework/minidom.mjs, and drive the front end's event extraction.
//
//   node web/widget/test.mjs FIXTURE.json
//
// The fixture is web/widget/gen.wiz's stdout. The patcher and DOM test double are the
// same ones web/framework/test.mjs uses; the widget front end imports runtime.js too.
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";

import { parse, serialize, DocumentFragment, Element } from "../framework/minidom.mjs";
import { applyPatches, mount } from "../framework/runtime.js";
import { WidgetView, MIME, TARGET } from "../../tools/jupyter/static/widget.js";
import { renderElement, commById } from "../../tools/jupyter/static/loader.js";

const fixture = JSON.parse(readFileSync(process.argv[2], "utf8"));
let checks = 0;
function ok(name, fn) {
  fn();
  checks += 1;
  console.log("ok: " + name);
}

function applied(html, patches) {
  const root = new DocumentFragment();
  mount(root, html, parse);
  applyPatches(root, patches, parse);
  return serialize(root);
}

// -- each kind renders the VDOM the front end expects -------------------------

for (const [key, id, kind, event] of [
  ["sliderHtml", "gain", "slider", "input"],
  ["buttonHtml", "play", "button", "click"],
  ["textHtml", "name", "text", "input"],
  ["plotHtml", "trace", "plot", "click"],
]) {
  ok(`a ${kind} is one fragment with its id, kind and event`, () => {
    const html = fixture[key];
    assert.equal(serialize(parse(html)), html, "the restricted parser round-trips");
    assert.match(html, new RegExp(`class="wiz-widget wiz-${kind}"`));
    assert.match(html, new RegExp(`data-wiz-widget="${id}"`));
    assert.match(html, new RegExp(`data-wiz-widget-kind="${kind}"`));
    assert.match(html, new RegExp(`data-wiz-widget-event="${event}"`));
    assert.match(html, /data-wiz-widget-root=""/);
  });
}

ok("the slider has a range input and the output text a patch can address", () => {
  assert.match(fixture.sliderHtml, /<input type="range" min="0" max="1" step="0.05" value="0.50"/);
  assert.match(fixture.sliderHtml, /<output class="wiz-widget-value">0.50<\/output>/);
});

ok("the plot carries opaque data, escaped in the attribute", () => {
  assert.match(fixture.plotHtml, /data-wiz-widget-data="\{&quot;points&quot;:\[1,2,3\]\}"/);
  assert.match(fixture.plotHtml, /<div class="wiz-plot-canvas"><\/div>/);
});

// -- the display bundle -------------------------------------------------------

ok("the display is prefixed, parses as JSON, and carries the SSR html", () => {
  assert.ok(fixture.display.startsWith("WIZ_WIDGET:"));
  const bundle = JSON.parse(fixture.display.slice("WIZ_WIDGET:".length));
  assert.equal(bundle.schema, "wiz.widget/1");
  assert.equal(bundle.html, fixture.allHtml);
  assert.equal(bundle.count, 4);
  assert.deepEqual(bundle.widgets.map((w) => w.id), fixture.keys);
  assert.deepEqual(bundle.widgets.map((w) => w.kind), ["slider", "button", "text", "plot"]);
  for (const w of bundle.widgets) assert.equal(w.callback, "onEvent");
});

ok("display is deterministic (the Wiz renderer is pure)", () => {
  assert.equal(fixture.deterministic, true);
});

// -- patches ------------------------------------------------------------------

ok("a slider event patches the wrapper, the input attribute and the output text", () => {
  const ops = fixture.patches.map((p) => p.op);
  assert.deepEqual(ops, ["setAttr", "setAttr", "text"]);
  assert.equal(applied(fixture.oldHtml, fixture.patches), fixture.newHtml);
  assert.match(fixture.newHtml, /<output class="wiz-widget-value">0.75<\/output>/);
});

ok("a keyed rotation is moves, and applies to exactly the rotated SSR", () => {
  assert.deepEqual(fixture.rotatePatches.map((p) => p.op), ["move", "move", "move"]);
  assert.equal(applied(fixture.rotateOld, fixture.rotatePatches), fixture.rotateNew);
});

ok("a removal is one remove, and applies to exactly the shortened SSR", () => {
  assert.deepEqual(fixture.editPatches.map((p) => p.op), ["remove"]);
  assert.equal(applied(fixture.editOld, fixture.editPatches), fixture.editNew);
});

// -- the front end: mount, apply, extract an event ----------------------------

ok("WidgetView mounts a bundle, applies an update and reports the event", () => {
  const root = new DocumentFragment();
  const sent = [];
  const view = new WidgetView(root, { parse, send: (data) => sent.push(data) });
  const bundle = JSON.parse(fixture.display.slice("WIZ_WIDGET:".length));
  view.render(bundle);
  assert.equal(serialize(root), fixture.allHtml);

  view.apply({ html: fixture.newHtml, patches: fixture.patches });
  assert.equal(serialize(root), fixture.newHtml);

  // The slider's input is the live control; a browser gives it a `value` property.
  const fragment = root.childNodes[0];
  const slider = fragment.childNodes[0];
  const input = slider.childNodes[0];
  input.value = "0.75";
  assert.equal(view.handleEvent({ type: "input", target: input }), true);
  assert.deepEqual(sent[0], { method: "event", widget_id: "gain", event: "input", value: "0.75" });
});

ok("WidgetView reads a text input's value and a button's data value", () => {
  const root = new DocumentFragment();
  const sent = [];
  const view = new WidgetView(root, { parse, send: (data) => sent.push(data) });
  view.render(JSON.parse(fixture.display.slice("WIZ_WIDGET:".length)));
  const fragment = root.childNodes[0];
  const text = fragment.childNodes[2];
  const textInput = text.childNodes[0];
  textInput.value = "grace";
  view.handleEvent({ type: "input", target: textInput });
  const button = fragment.childNodes[1];
  view.handleEvent({ type: "click", target: button });
  assert.deepEqual(sent[0], { method: "event", widget_id: "name", event: "input", value: "grace" });
  assert.deepEqual(sent[1], { method: "event", widget_id: "play", event: "click", value: "play" });
});

ok("WidgetView ignores a click outside any widget", () => {
  const root = new DocumentFragment();
  const sent = [];
  const view = new WidgetView(root, { parse, send: (data) => sent.push(data) });
  view.render(JSON.parse(fixture.display.slice("WIZ_WIDGET:".length)));
  assert.equal(view.handleEvent({ type: "click", target: root }), false);
  assert.equal(sent.length, 0);
});

ok("a comm binding sends events and applies the kernel's update", () => {
  const root = new DocumentFragment();
  let onMsg = null;
  const sent = [];
  const comm = { send: (data) => sent.push(data), on_msg: (fn) => { onMsg = fn; } };
  const view = new WidgetView(root, { parse }).bindComm(comm);
  view.render(JSON.parse(fixture.display.slice("WIZ_WIDGET:".length)));
  const fragment = root.childNodes[0];
  const input = fragment.childNodes[0].childNodes[0];
  input.value = "0.75";
  view.handleEvent({ type: "input", target: input });
  assert.deepEqual(sent[0], { method: "event", widget_id: "gain", event: "input", value: "0.75" });
  onMsg({ content: { data: {
    method: "update",
    bundle: { html: fixture.newHtml, patches: fixture.patches },
  } } });
  assert.equal(serialize(root), fixture.newHtml);
});

ok("the MIME type and comm target are the documented strings", () => {
  assert.equal(MIME, "application/vnd.wiz.widget+json");
  assert.equal(TARGET, "wiz.widgets");
});

// -- the loader: adopt SSR, bind a comm, look one up --------------------------

ok("renderElement adopts an already-rendered fragment without re-mounting", () => {
  const bundle = JSON.parse(fixture.display.slice("WIZ_WIDGET:".length));
  const element = new Element("div");
  for (const child of parse(bundle.html).childNodes) element.appendChild(child);
  const sent = [];
  const comm = { send: (data) => sent.push(data), on_msg: () => {} };
  const view = renderElement(element, bundle, { parse, comm });
  assert.equal(serialize(element.childNodes[0]), bundle.html);
  assert.equal(element.getAttribute("data-wiz-widget-ready"), "1");
  const input = element.childNodes[0].childNodes[0].childNodes[0];
  input.value = "0.75";
  assert.equal(view.handleEvent({ type: "input", target: input }), true);
  assert.equal(sent[0].widget_id, "gain");
});

ok("renderElement mounts into an empty element (the mime-renderer path)", () => {
  const bundle = JSON.parse(fixture.display.slice("WIZ_WIDGET:".length));
  const element = new Element("div");
  const view = renderElement(element, bundle, { parse });
  assert.equal(serialize(element.childNodes[0]), bundle.html);
  assert.ok(view instanceof WidgetView);
  assert.equal(view.handleEvent({ type: "click", target: element }), false);
});

ok("commById reads a Map or an object from a classic Notebook manager", () => {
  const comm = { send() {}, on_msg() {} };
  assert.equal(commById({ comms: new Map([["a", comm]]) }, "a"), comm);
  assert.equal(commById({ comms: { a: comm } }, "a"), comm);
  assert.equal(commById({ comms: {} }, "a"), null);
  assert.equal(commById(null, "a"), null);
});

console.log(`\nwiz widgets: all ${checks} checks passed`);
