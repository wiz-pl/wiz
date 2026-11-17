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
// `overflow-wrap: break-word` are set on both sides (web/playground.css), and a trailing
// blank line is appended so a text ending in `\n` has the height the textarea shows. If
// the two ever drift, only the underline's position is wrong: the textarea can still be
// typed in and read, which a contenteditable rewrite could not promise. `?squiggles=off`
// turns the layer off, and the goals pane's diagnostics stay clickable either way.
//
// `web/editor-model.js` computes the ranges (the pure half, tested in Node); this file
// only turns them into DOM.
"use strict";
import { squiggleSegments, SEVERITY_NAME } from "./editor-model.js";

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

// Put `editor` inside a positioned wrapper (or reuse one), so the mirror can sit exactly
// over it. Returns the wrapper.
function ensureWrapper(editor, doc) {
  const parent = editor.parentNode;
  if (parent && parent.getAttribute && parent.getAttribute("data-editor-wrap") === "1") return parent;
  const wrapper = doc.createElement("div");
  attr(wrapper, "class", "editor-wrap");
  attr(wrapper, "data-editor-wrap", "1");
  if (parent) parent.insertBefore(wrapper, editor);
  wrapper.appendChild(editor);
  return wrapper;
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

// The mirror's available width is the textarea's *client* width: a visible scrollbar takes
// room from the text, so the layer's right edge is inset by it (and wraps land where the
// textarea wraps them). An overlay scrollbar reports 0 and changes nothing.
function layoutLayer(editor, layer, style) {
  if (!style || typeof editor.offsetWidth !== "number") { setStyle(layer, "right", "0"); return; }
  const border = (parseFloat(style.borderLeftWidth) || 0) + (parseFloat(style.borderRightWidth) || 0);
  const scrollbar = (editor.offsetWidth || 0) - (editor.clientWidth || 0) - border;
  setStyle(layer, "right", (scrollbar > 0 ? scrollbar : 0) + "px");
}

// `mountSquiggles(editor, options)` → `{update(diagnostics), refresh(), segments(), destroy()}`.
// `options.document` defaults to the editor's own document (tests pass a double).
export function mountSquiggles(editor, options = {}) {
  const doc = options.document || editor.ownerDocument || (typeof document !== "undefined" ? document : null);
  if (!editor || !doc || typeof doc.createElement !== "function") return null;
  const wrapper = ensureWrapper(editor, doc);
  const layer = doc.createElement("div");
  attr(layer, "class", "squiggle-layer");
  attr(layer, "aria-hidden", "true");
  const text = doc.createElement("div");
  attr(text, "class", "squiggle-text");
  layer.appendChild(text);
  wrapper.appendChild(layer);
  let spans = [];

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
      const end = Math.max(start, Math.min(value.length, span.end));
      if (start > at) text.appendChild(doc.createTextNode(value.slice(at, start)));
      if (end > start) {
        const mark = doc.createElement("span");
        attr(mark, "class", "squiggle sev-" + (SEVERITY_NAME[span.severity] || "info"));
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
    attr(wrapper, "data-squiggles", spans.length);
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

  function update(diagnostics) {
    spans = squiggleSegments(typeof editor.value === "string" ? editor.value : "", diagnostics || []);
    render();
    syncScroll();
    return spans;
  }

  const onInput = () => { render(); syncScroll(); };
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
