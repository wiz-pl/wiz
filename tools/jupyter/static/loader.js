// The small loader for the Wiz widget MIME type.
//
// The kernel renders every widget display twice, on purpose:
//
//   * `text/html` — the React SSR fragment wrapped in
//     `<div class="wiz-widget-fragment" data-wiz-widget-comm="ID">…</div>`. It is
//     readable with JavaScript off and is what this loader adopts (no re-render flash).
//   * `application/vnd.wiz.widget+json` — the same fragment plus the descriptors and
//     the comm id, for a mime-renderer extension.
//
// `install()` binds the two: it registers the `wiz.widgets` comm target (the kernel
// opens one per display), then scans rendered output for `[data-wiz-widget-comm]` and
// attaches a `WidgetView` — patches from the comm apply to the adopted DOM, and DOM
// events go back as `{method: "event", widget_id, event, value}`.
//
// Classic Notebook / nbclassic: load this module from custom.js and call `install()`.
// JupyterLab: a notebook extension must register a renderer for
// `application/vnd.wiz.widget+json` that calls `renderElement(el, bundle)`; this file
// does not ship the extension, so JupyterLab shows the SSR HTML without events.
"use strict";

import { WidgetView, MIME, TARGET } from "./widget.js";

function managerOf(Jupyter) {
  return (Jupyter && Jupyter.notebook && Jupyter.notebook.kernel &&
    Jupyter.notebook.kernel.comm_manager) || null;
}

/** The comm with id `commId` from a classic Notebook comm manager (Map or object). */
export function commById(manager, commId) {
  if (!manager || !manager.comms || !commId) return null;
  if (typeof manager.comms.get === "function") return manager.comms.get(commId) || null;
  return manager.comms[commId] || null;
}

/** Mount a bundle into `element` and bind it to `comm` when one is given. */
export function renderElement(element, bundle, { parse, comm, onError } = {}) {
  const view = new WidgetView(element, { parse, onError });
  if (element.firstChild) view.adopt(bundle);
  else view.render(bundle);
  if (comm) view.bindComm(comm);
  element.__wizWidgetView = view;
  element.setAttribute("data-wiz-widget-ready", "1");
  return view;
}

/**
 * Adopt every rendered widget fragment under `root`.
 *
 * A fragment with no comm (a notebook opened without running it) keeps its static
 * HTML and drops events: `onError` is not called, `send` is a no-op. That is the
 * honest degradation, not a silent failure.
 */
export function renderAll(root, { Jupyter, parse, onError } = {}) {
  const manager = managerOf(Jupyter);
  const nodes = root.querySelectorAll
    ? root.querySelectorAll("[data-wiz-widget-comm]")
    : [];
  const views = [];
  for (const element of nodes) {
    if (element.getAttribute("data-wiz-widget-ready") != null) continue;
    const commId = element.getAttribute("data-wiz-widget-comm");
    const comm = commById(manager, commId);
    const bundle = (comm && comm.__wizBundle) || { html: element.innerHTML };
    views.push(renderElement(element, bundle, { parse, comm, onError }));
  }
  return views;
}

/** Render one `application/vnd.wiz.widget+json` value into an empty element. */
export function renderMime(element, bundle, { Jupyter, parse, onError } = {}) {
  const manager = managerOf(Jupyter);
  const comm = commById(manager, bundle && bundle.comm_id);
  return renderElement(element, bundle, { parse, comm, onError });
}

/**
 * Install the classic-Notebook wiring. Returns `{scan, renderAll}` or null when there
 * is no classic Notebook kernel to talk to.
 *
 * The kernel's `comm_open` arrives before `execute_result`, so the target callback may
 * run before the output element exists; `scan` on `output_appended` and after a
 * kernel message finds it.
 */
export function install({ Jupyter, document, parse, onError } = {}) {
  const manager = managerOf(Jupyter);
  if (!manager) return null;
  const doc = document || globalThis.document;
  const scan = () => renderAll(doc, { Jupyter, parse, onError });
  if (manager.register_target) {
    manager.register_target(TARGET, (comm, message) => {
      const content = (message && message.content) || {};
      comm.__wizBundle = content.data || {};
      scan();
    });
  }
  const events = Jupyter.notebook.events;
  if (events && events.on) {
    events.on("kernel_connected.Kernel", scan);
    events.on("notebook_loaded.Notebook", scan);
    events.on("output_appended.OutputArea", scan);
  }
  scan();
  return { scan, renderAll: () => scan() };
}

export { WidgetView, MIME, TARGET };
