// The browser half of lib/Web/Widget.wiz: render the widget fragment a notebook cell
// displays, apply the kernel's VDOM patches, and forward widget events as comm
// messages.
//
// The renderer is **not** a second implementation. It imports the patch applier and
// mount from web/framework/runtime.js — the same file lib/Web/React.wiz's patches are
// written for — and the Node test drives it with web/framework/minidom.mjs. The only
// widget-specific code is event extraction (walk to `data-wiz-widget`, read the input
// or the `data-wiz-widget-value`) and the comm binding.
//
// The Wiz→JS encoding is the one React already emits: one `div.wiz-widgets` fragment
// whose HTML is `React.toHtml (Widget.vnodes ws)`, and patches addressed by
// child-index paths ("" is the fragment, "0" its first child). Widget roots carry
// `data-wiz-widget`, `data-wiz-widget-kind`, `data-wiz-widget-event` and
// `data-wiz-widget-value`; the control is a child with `data-wiz-widget-input`. That is
// documentation, not a protocol: nothing outside React's output is parsed here.
"use strict";

import { applyPatches, mount } from "../../../web/framework/runtime.js";

/** The notebook MIME type of a widget display. */
export const MIME = "application/vnd.wiz.widget+json";
/** The comm target the kernel opens widget fragments on. */
export const TARGET = "wiz.widgets";
/** The bundle schema `Widget.bundle` writes. */
export const SCHEMA = "wiz.widget/1";
/** The prefix `Widget.display` puts in front of the JSON. */
export const PREFIX = "WIZ_WIDGET:";

/** A display string (`WIZ_WIDGET:{...}`), the JSON text, or an already-parsed bundle. */
export function parseBundle(value) {
  if (value && typeof value === "object") return value;
  if (typeof value !== "string") throw new TypeError("not a widget bundle");
  const text = value.startsWith(PREFIX) ? value.slice(PREFIX.length) : value;
  return JSON.parse(text);
}

function defaultParse(html) {
  return document.createRange().createContextualFragment(html);
}

function parentOf(node) {
  return node ? node.parentNode : null;
}

/** The innermost element at or above `node` (up to `root`) with `data-wiz-widget`. */
export function widgetTarget(node, root) {
  let t = node;
  while (t && t !== root) {
    if (t.getAttribute && t.getAttribute("data-wiz-widget") != null) return t;
    t = parentOf(t);
  }
  return null;
}

/** The value an event carries: an input's live `value`/`checked`, else the widget's
 *  `data-wiz-widget-value` (a button's value). */
export function eventValue(target, event) {
  const node = event && event.target;
  // A browser's `tagName` is upper case, the Node test double's is the source case.
  if (node && String(node.tagName || "").toUpperCase() === "INPUT") {
    const type = (node.getAttribute("type") || "").toLowerCase();
    if (type === "checkbox") return node.checked ? "true" : "false";
    if (typeof node.value === "string") return node.value;
  }
  const value = target.getAttribute("data-wiz-widget-value");
  return value == null ? "" : value;
}

/**
 * One displayed widget fragment.
 *
 * `root` is the element the fragment lives in (a `div.wiz-widget-fragment` from the
 * kernel's `text/html`, or any empty container). `render` mounts the bundle's HTML;
 * `adopt` takes an already-server-rendered fragment (the progressive-enhancement path);
 * `apply` replays a patch list; `handleEvent` turns a DOM event into the comm payload.
 */
export class WidgetView {
  constructor(root, { parse, send, onError, events } = {}) {
    if (!root) throw new TypeError("WidgetView needs a root element");
    this.root = root;
    this.parse = parse || defaultParse;
    this.send = send || (() => {});
    this.onError = onError || ((message) => console.error("wiz widget:", message));
    this.events = events || ["click", "input", "change"];
    this.comm = null;
    this.bundle = null;
    this._listening = false;
  }

  /** Mount `bundle` (a display string or object), replacing the root's children. */
  render(bundle) {
    this.bundle = parseBundle(bundle);
    mount(this.root, this.bundle.html || "", this.parse);
    this._listen();
    return this;
  }

  /** Take an already-rendered fragment: keep the DOM, remember the bundle. */
  adopt(bundle) {
    this.bundle = parseBundle(bundle);
    if (!this.root.firstChild) return this.render(this.bundle);
    this._listen();
    return this;
  }

  /** Listen on the container once; an event bubbles from the control to its widget. */
  _listen() {
    if (this._listening || typeof this.root.addEventListener !== "function") return;
    this._listening = true;
    for (const type of this.events) {
      this.root.addEventListener(type, (event) => {
        if (!this.handleEvent(event)) return;
        if ((type === "click" || type === "submit") && event.preventDefault) {
          event.preventDefault();
        }
      }, false);
    }
  }

  /** Apply an update: `data.patches` (preferred) or a full `bundle` with `html`. */
  apply(data) {
    const bundle = data.bundle || data;
    const patches = data.patches || bundle.patches || [];
    if (patches.length === 0) {
      if (bundle.html != null && bundle.html !== (this.bundle && this.bundle.html)) {
        return this.render(bundle);
      }
      this.bundle = parseBundle(bundle);
      return this;
    }
    applyPatches(this.root, patches, this.parse);
    this.bundle = parseBundle(bundle);
    return this;
  }

  /** Handle an iopub `comm_msg` content object
   *  (`{method: "update", bundle, patches}`). */
  update(data) {
    if (!data) return this;
    if (data.method === "error") {
      this.onError(data.error || data.message || "widget update failed");
      return this;
    }
    if (data.method === "update") return this.apply(data);
    if (data.method === "close") return this;
    return this.apply(data);
  }

  /** Extract the widget event from a DOM event, send it, and say whether it was one. */
  handleEvent(event) {
    const target = widgetTarget(event.target, this.root);
    if (!target) return false;
    const widgetId = target.getAttribute("data-wiz-widget");
    const declared = target.getAttribute("data-wiz-widget-event") || event.type;
    // A slider declares `input` but a browser may also fire `change`; both mean the
    // same value. A click on a slider's label is not its event and is ignored.
    const accepts = declared === event.type ||
      (declared === "input" && event.type === "change") ||
      (declared === "change" && event.type === "input");
    if (!accepts) return false;
    this.send({
      method: "event",
      widget_id: widgetId,
      event: declared,
      value: eventValue(target, event),
    });
    return true;
  }

  /** Bind a Jupyter comm: events go out, `comm_msg` updates come in. */
  bindComm(comm) {
    this.comm = comm;
    this.send = (data) => comm.send(data);
    comm.on_msg((message) => {
      const content = (message && message.content) || {};
      this.update(content.data || {});
    });
    return this;
  }
}

/** A view for `root` (a convenience for the loader and for tests). */
export function attach(root, options) {
  return new WidgetView(root, options);
}
