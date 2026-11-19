// (playground, ?ui=react) The right-hand pane rendered by the repo's Loom
// framework (`lib/Web/Loom.wiz`, through web/ui-framework.wiz) instead of by
// `document.createElement` in web/playground.js.
//
// It is behind the `?ui=react` flag and additive: with no flag, `playground.js`'s
// existing DOM path renders exactly what it did before. Under the flag the page loads a
// second, small Wasm module (`wiz-playground-ui.mjs`, built by
// web/build-playground.sh from web/playground-ui.wiz) exporting
//
//     wiz_ui_html  : Model → String
//     wiz_ui_patch : Old → New → String
//
// and web/framework/driver.js's `startModel` mounts the HTML and applies the patches.
// The model is JSON built here, so any text the page has (output lines, the goals
// panel's HTML) can flow into the tree without the framework's static-message
// limitation. If the module is missing or has no exports, `startPageUi` returns null and
// the page keeps its DOM path (that is also what the Node tests do: no Wasm, no browser).
//
// Still imperative (documented in docs/playground-lsp.md, "?ui=react"): the textarea,
// the squiggle overlay and the completion popup, the header's status, the Run button and
// the footer's engine line.
"use strict";
import { startModel } from "./framework/driver.js";

// The Wasm exports the UI module must have.
export const UI_EXPORTS = { html: "_wiz_ui_html", patch: "_wiz_ui_patch" };

// Whether a loaded module can render the page's UI.
export function reactUiAvailable(wasm) {
  return !!wasm && typeof wasm[UI_EXPORTS.html] === "function";
}

// `startPageUi({wasm, root, model, document, parse})` → the driver's api, or null.
//
// `model` is `{count, lines, goals}` (see `emptyModel`); it is serialised as it is. The
// defaults for `document`/`parse` are the page's; the tests pass minidom's.
export function startPageUi({ wasm, root, model, document: doc, parse } = {}) {
  if (!root || !reactUiAvailable(wasm)) return null;
  const initial = JSON.stringify(normalizeModel(model || emptyModel()));
  return startModel(wasm, root, {
    model: initial,
    document: doc,
    parse,
    htmlExport: UI_EXPORTS.html,
    patchExport: UI_EXPORTS.patch,
  });
}

// The model the pane starts with: nothing has run, the goals pane has not rendered.
export function emptyModel() {
  return { count: "", lines: [], goals: "" };
}

// A model with every field present and the right shape: a page event supplies a partial
// model and the rest is kept (or defaulted). `lines` is copied so a caller's array cannot
// change under the renderer.
export function normalizeModel(model) {
  const m = model && typeof model === "object" ? model : {};
  const lines = Array.isArray(m.lines) ? m.lines : [];
  return {
    count: m.count === undefined || m.count === null ? "" : String(m.count),
    lines: lines
      .filter((l) => l && typeof l.text === "string")
      .map((l) => ({
        kind: l.kind === undefined || l.kind === null ? "" : String(l.kind),
        text: String(l.text),
      })),
    goals: m.goals === undefined || m.goals === null ? "" : String(m.goals),
  };
}

// The page's model plus a change, as one object. The page keeps the merged model, so a
// goals update and an output update never overwrite each other.
export function mergeModel(model, patch) {
  return normalizeModel(Object.assign({}, normalizeModel(model), patch || {}));
}

// A small handle the page holds: `update({lines})` merges and renders, `set(model)`
// replaces. `model()` returns a copy (the driver owns the string).
export function createPageUi({ wasm, root, model, document: doc, parse } = {}) {
  let current = normalizeModel(model || emptyModel());
  const driver = startPageUi({ wasm, root, model: current, document: doc, parse });
  if (!driver) return null;
  return {
    model: () => normalizeModel(current),
    html: () => driver.html(),
    renders: () => driver.renders(),
    update(patch) {
      current = mergeModel(current, patch);
      driver.render(JSON.stringify(current));
      return current;
    },
    set(next) {
      current = normalizeModel(next);
      driver.render(JSON.stringify(current));
      return current;
    },
  };
}
