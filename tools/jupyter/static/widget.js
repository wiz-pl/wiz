// The browser front end for a Wiz notebook widget.
//
// A widget is a comm (Jupyter's `comm_open` / `comm_msg` / `comm_close`) whose state is
// a React-style VNode tree from `lib/Web/React.wiz`.  The kernel sends the server-side
// rendered HTML in `comm_open` and a patch list (the output of `React.patchesJson`) for
// every update; this module mounts it with the same patch applier and event delegation
// the framework's own pages use (`web/framework/runtime.js`), and sends DOM events back
// over the comm.
//
// It is an ES module, like `web/framework/runtime.js` and `web/tagged.js`: no bundler
// and no framework.  `tools/jupyter/static/widget_test.mjs` is the headless-browser
// test; it drives this file with a fake comm (`fake_comm.mjs`), so neither Python nor a
// Jupyter kernel is needed.
"use strict";

import { applyPatches, delegate, mount } from "../../../web/framework/runtime.js";

// The events a widget view may handle.  `web/framework/driver.js` passes a subset; a
// widget uses the same defaults as `runtime.delegate`.
export const EVENT_TYPES = ["click", "input", "change", "submit", "keydown", "keyup"];

// Events whose DOM target carries a value the Wiz side usually needs (a slider, a text
// field, a select).  `React.App.event` only receives `(event, index)`, so the value is
// forwarded in the comm payload; a kernel that understands it can return a patch for
// it (see `fake_comm.mjs`).
const VALUED_EVENTS = new Set(["input", "change"]);

// Mount `root` (an element or a DocumentFragment) as the view of `comm`.  `comm` is a
// Jupyter Comm-like object: `on_msg(fn)` and `send(data)`.  `parse(html)` is the
// framework's HTML parser; the default is `runtime.js`'s `document` one, and the Node
// test passes `minidom.parse`.
//
// Returns `{ apply, onMsg }`: `apply` applies a patch list, `onMsg` is the comm handler
// (exposed for a client that already owns the comm subscription).
export function mountWidget(root, comm, { parse, events = EVENT_TYPES } = {}) {
  const apply = (patch) => applyPatches(root, parsePatch(patch), parse);
  const onMsg = (msg) => {
    const type = msg && msg.header && msg.header.msg_type;
    const content = (msg && msg.content) || {};
    const data = content.data || {};
    if (type === "comm_open") {
      if (typeof data.html === "string") mount(root, data.html, parse);
      if (data.patches) apply(data.patches);
    } else if (type === "comm_msg") {
      if (data.method === "update" || data.method === "patch") {
        apply(data.patch !== undefined ? data.patch : data.patches);
      } else if (data.method === "render" && typeof data.html === "string") {
        mount(root, data.html, parse);
      }
    }
  };
  comm.on_msg(onMsg);
  delegate(root, (event, index, domEvent) => {
    const payload = { event, index };
    if (VALUED_EVENTS.has(event)) {
      const value = eventValue(domEvent);
      if (value !== undefined) payload.value = value;
    }
    comm.send(payload);
    return true; // a handled event does not also submit a form or follow a link
  }, events);
  return { apply, onMsg };
}

// The value a form control reports for an event.  `undefined` when the target is not a
// control (a button click), so the payload stays exactly `{event, index}` there.
function eventValue(e) {
  const target = e && e.target;
  if (!target || target.value === undefined || target.value === null) return undefined;
  return String(target.value);
}

// `React.patchesJson` is a JSON string; a client may already have parsed it.
function parsePatch(patch) {
  if (typeof patch === "string") return JSON.parse(patch);
  return patch || [];
}
