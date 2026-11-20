// Squiggles under the playground's editor: diagnostics drawn on the offending source,
// not only listed in the goals pane.
//
// **Dependency decision: none.** The editor stays a plain `<textarea>`. A contenteditable
// editor (CodeMirror, Monaco, …) would bring a build step, a licence and a third-party
// dependency into a page that today is four ES modules and a Wasm binary, so instead the
// textarea gets a **mirror**: an absolutely positioned `div` behind it with the same font,
// padding and wrapping, containing the editor's text with a `<span class="squiggle">`
// around every diagnostic range. The textarea's own background is transparent, so the
// underline shows through; the mirror never takes a pointer event, so typing, selection
// and scrolling are the textarea's.
//
// The mirror is the fragile part of any plain-textarea decoration: it only lines up if
// its font metrics and wrap points are the textarea's. Layout is therefore copied from
// `getComputedStyle(editor)` on every layout, `white-space: pre-wrap` and
// `overflow-wrap: break-word` are set on both sides (web/overlays.css), and a trailing
// blank line is appended so a text ending in `\n` has the height the textarea shows. If
// the two ever drift, only the underline's position is wrong: the textarea can still be
// typed in and read, which a contenteditable rewrite could not promise. `?squiggles=off`
// turns the layer off, and the goals pane's diagnostics stay clickable either way.
//
// **The editor is never wrapped.** A wrapper would move the textarea one level deeper in
// the tree, and a patch applier that addresses nodes by child index — `web/framework/
// runtime.js`, which the Loom page (`?ui=loom`) uses — would then resolve the editor's
// path to the wrapper and quietly set the textarea's *default* value instead of its live
// one. The layer is appended to the editor's existing parent instead, after every node
// that parent renders; the editor's own index never changes, and a later insert at the
// end of the parent goes before this layer (see web/loom_overlay_test.mjs). The parent is
// made a containing block so the layer can sit over the textarea's box.
//
// `web/framework/editor-model.mjs` (the test oracle) used to compute the ranges; this
// file only turns them into DOM. The ranges are now `lib/Web/EditorModel.wiz`'s and
// arrive through `options.segments(text, diagnostics)`; this widget paints them.
"use strict";

// The class suffix for a severity (the runtime sends `severityName` too; this is the
// paint fallback).
const SEVERITY_NAME = { 1: "error", 2: "warning", 3: "info", 4: "hint" };

// The properties that change where a character sits. Copied from the textarea's computed
// style; web/playground.css has the same declarations so a page without
// `getComputedStyle` (the Node tests) still lays out sanely.
const TEXT_STYLE = [
  "font-family", "font-size", "font-weight", "font-style", "font-variant",
  "letter-spacing", "word-spacing", "line-height", "text-transform", "text-indent",
  "tab-size", "white-space", "word-break", "overflow-wrap",
  "padding-top", "padding-right", "padding-bottom", "padding-left",
  "border-top-width", "border-right-width", "border-bottom-width", "border-left-width",
  "box-sizing",
];

function setStyle(element, property, value) {
  if (element && element.style && value !== undefined && value !== null && value !== "") {
    element.style.setProperty ? element.style.setProperty(property, value)
      : (element.style[property] = value);
  }
}

function attr(element, name, value) {
  if (value === null || value === undefined) element.removeAttribute(name);
  else element.setAttribute(name, String(value));
}

// The editor's existing parent, made a containing block. Returns it, or the page's body
// when the editor is detached (the Node tests mount an editor with no parent).
function layerHost(editor, doc) {
  const parent = editor.parentNode;
  if (parent && typeof parent.appendChild === "function") {
    let position = null;
    try {
      position = typeof getComputedStyle === "function" ? getComputedStyle(parent).position : null;
    } catch (_) { /* no layout: the inline style below is the fallback */ }
    if (!position || position === "static") setStyle(parent, "position", "relative");
    return parent;
  }
  return doc && doc.body && typeof doc.body.appendChild === "function" ? doc.body : null;
}

// The styling the mirror needs: the textarea's own where the browser can tell us.
function copyTextStyle(editor, text) {
  let style = null;
  try {
    style = typeof getComputedStyle === "function" ? getComputedStyle(editor) : null;
  } catch (_) { /* no layout: the CSS file's declarations apply */ }
  if (!style) return null;
  for (const property of TEXT_STYLE) {
    const value = style.getPropertyValue ? style.getPropertyValue(property) : style[property];
    setStyle(text, property, value);
  }
  // The textarea's box is the mirror's box: no extra border of its own, and the padding
  // is carried by the text so it scrolls with it (as the textarea's content does).
  setStyle(text, "border", "0");
  setStyle(text, "box-sizing", "border-box");
  return style;
}

// The layer's box is the textarea's *client* box: no border of its own, and a visible
// scrollbar's room is left out so the text wraps where the textarea wraps it. The layer is
// absolutely positioned in the editor's parent (which `layerHost` made relative), so the
// textarea's offset within that parent is the layer's position; without layout (a Node
// test) the layer falls back to the parent's whole box.
function layoutLayer(editor, layer, style) {
  const size = (n) => typeof n === "number" && isFinite(n) && n >= 0;
  if (!size(editor.offsetWidth) || !size(editor.offsetHeight)) {
    setStyle(layer, "left", "0");
    setStyle(layer, "top", "0");
    setStyle(layer, "width", "100%");
    setStyle(layer, "height", "100%");
    return;
  }
  const border = (parseFloat(style && style.borderLeftWidth) || 0) +
    (parseFloat(style && style.borderRightWidth) || 0);
  const width = size(editor.clientWidth) ? editor.clientWidth : editor.offsetWidth - border;
  const height = size(editor.clientHeight) ? editor.clientHeight : editor.offsetHeight;
  setStyle(layer, "left", (size(editor.offsetLeft) ? editor.offsetLeft : 0) + "px");
  setStyle(layer, "top", (size(editor.offsetTop) ? editor.offsetTop : 0) + "px");
  setStyle(layer, "width", Math.max(0, width) + "px");
  setStyle(layer, "height", Math.max(0, height) + "px");
}

// `mountSquiggles(editor, options)` → `{update(diagnostics), refresh(), segments(), destroy()}`.
// `options.segments(text, diagnostics)` is the runtime's rule (a list of `{start, stop,
// severity, severityName?, message}`); `options.document` defaults to the editor's own
// document (tests pass a double).
export function mountSquiggles(editor, options = {}) {
  const doc = options.document || editor.ownerDocument || (typeof document !== "undefined" ? document : null);
  const segmentsOf = options.segments;
  if (!editor || !doc || typeof doc.createElement !== "function" || typeof segmentsOf !== "function") return null;
  const host = layerHost(editor, doc);
  if (!host) return null;
  const layer = doc.createElement("div");
  attr(layer, "class", "squiggle-layer");
  attr(layer, "data-squiggle-layer", "1");
  attr(layer, "aria-hidden", "true");
  const text = doc.createElement("div");
  attr(text, "class", "squiggle-text");
  layer.appendChild(text);
  // Last child, after everything the parent renders: the editor stays where it was and no
  // existing sibling changes index (the Loom page's patch paths).
  host.appendChild(layer);
  let spans = [];
  let diagnostics = [];

  const initialStyle = copyTextStyle(editor, text);
  layoutLayer(editor, layer, initialStyle);

  function render() {
    // The mirror is rebuilt rather than patched: a diagnostic changes the tree's shape,
    // and the editor's value is the source of truth anyway. This is a text update per
    // keystroke on a document of a few hundred lines, which is cheap.
    while (text.childNodes && text.childNodes.length) text.removeChild(text.childNodes[0]);
    const value = typeof editor.value === "string" ? editor.value : "";
    let at = 0;
    for (const span of spans) {
      const start = Math.max(at, Math.min(value.length, span.start));
      const end = Math.max(start, Math.min(value.length, span.stop));
      if (start > at) text.appendChild(doc.createTextNode(value.slice(at, start)));
      if (end > start) {
        const mark = doc.createElement("span");
        attr(mark, "class", "squiggle sev-" + (span.severityName || SEVERITY_NAME[span.severity] || "info"));
        if (span.message) attr(mark, "title", span.message);
        mark.appendChild(doc.createTextNode(value.slice(start, end)));
        text.appendChild(mark);
      }
      at = end;
    }
    if (at < value.length) text.appendChild(doc.createTextNode(value.slice(at)));
    // A textarea shows one line box after a trailing newline; the mirror needs one too.
    text.appendChild(doc.createTextNode("\n "));
    attr(layer, "hidden", spans.length ? null : "");
    attr(host, "data-squiggles", spans.length);
  }

  function syncScroll() {
    const x = typeof editor.scrollLeft === "number" ? editor.scrollLeft : 0;
    const y = typeof editor.scrollTop === "number" ? editor.scrollTop : 0;
    setStyle(text, "transform", "translate(" + (-x) + "px, " + (-y) + "px)");
  }

  function refresh() {
    const style = copyTextStyle(editor, text);
    layoutLayer(editor, layer, style);
    render();
    syncScroll();
  }

  function update(next) {
    diagnostics = Array.isArray(next) ? next : [];
    spans = segmentsOf(typeof editor.value === "string" ? editor.value : "", diagnostics) || [];
    refresh();
    return spans;
  }

  // Typing changes the text under stale offsets: re-ask the runtime for the same
  // diagnostics against the new value (the merge/clip rules are the runtime's).
  function onInput() {
    spans = segmentsOf(typeof editor.value === "string" ? editor.value : "", diagnostics) || [];
    render();
    syncScroll();
  }
  const onScroll = () => syncScroll();
  const onResize = () => refresh();
  if (typeof editor.addEventListener === "function") {
    editor.addEventListener("input", onInput);
    editor.addEventListener("scroll", onScroll);
  }
  if (typeof addEventListener === "function") addEventListener("resize", onResize);
  let observer = null;
  if (typeof ResizeObserver === "function") {
    observer = new ResizeObserver(onResize);
    try { observer.observe(editor); } catch (_) { /* a detached editor */ }
  }

  render();
  syncScroll();

  return {
    update,
    refresh,
    segments: () => spans.map((s) => Object.assign({}, s)),
    layout() {
      const style = copyTextStyle(editor, text);
      layoutLayer(editor, layer, style);
      render();
      syncScroll();
    },
    destroy() {
      if (typeof editor.removeEventListener === "function") {
        editor.removeEventListener("input", onInput);
        editor.removeEventListener("scroll", onScroll);
      }
      if (typeof removeEventListener === "function") removeEventListener("resize", onResize);
      if (observer) { try { observer.disconnect(); } catch (_) { /* gone */ } }
      if (layer.parentNode) layer.parentNode.removeChild(layer);
      attr(host, "data-squiggles", null);
    },
  };
}

// The page's flag: `?squiggles=off` (also 0/none/false/no) turns the layer off; anything
// else, including no parameter, leaves it on.
export function wantsSquiggles(search) {
  try {
    const value = new URLSearchParams(search || "").get("squiggles");
    if (value === null) return true;
    return !/^\s*(off|none|no|0|false)\s*$/i.test(value);
  } catch (_) {
    return true;
  }
}
