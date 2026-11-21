// The completion popup: `textDocument/completion` on Ctrl-Space or while typing an
// identifier, a keyboard-navigable list under the caret, and the insert an accepted item
// makes. No dependency: a `div` with `role="listbox"` fixed over the page, positioned from
// the textarea's font metrics (the editor is monospace, so a character column is
// `character * charWidth`).
//
// The decisions — which items match, the keyboard's index arithmetic, what an accepted
// item replaces — are `lib/Web/EditorModel.wiz`'s pure functions, reached through
// `options.rules` (the runtime's `wiz_loom_editor_*` queries). This file is the DOM and
// the timers:
//
//   * **Triggers.** Ctrl/⌘-Space asks unconditionally; typing an identifier character
//     asks after `debounce` ms (120 by default), outside a line comment. A non-identifier
//     key closes the list.
//   * **Keys.** Up/Down/PageUp/PageDown move (wrapping), Enter/Tab accept, Escape closes.
//     While the list is open those keys belong to it, so the editor does not also insert
//     a newline or a tab.
//   * **Insertion.** The accepted item's `textEdit` if the server sent one, else its
//     `insertText`/`label` over the identifier prefix; the page sees a normal `input`
//     event, so the document is re-sent to the server by the existing `didChange` path.
//   * **Closing.** Escape, a blur, a non-identifier key, an empty result, or a server
//     error. Nothing here throws at the page: a server without completion is silent.
"use strict";
import { caretOffset } from "./framework/editor-text.js";

const PAGE = 10;

function attr(element, name, value) {
  if (!element) return;
  if (value === null || value === undefined) element.removeAttribute(name);
  else element.setAttribute(name, String(value));
}

function setStyle(element, property, value) {
  if (element && element.style && value !== undefined && value !== null) element.style[property] = value;
}

// The caret as `{line, character}` from the runtime's position rule.
function caretPosition(rules, editor) {
  const value = typeof editor.value === "string" ? editor.value : "";
  return rules.position(value, caretOffset(editor));
}

// `mountCompletions({editor, rules, onRequest, document?, debounce?, autoTrigger?})`.
// `rules` is the runtime's pure editor model (`items`, `popup`, `move`, `accept`,
// `trigger`, `position`); `onRequest(position)` returns a `textDocument/completion`
// result (a promise) or null.
export function mountCompletions(options = {}) {
  const editor = options.editor;
  const rules = options.rules;
  const onRequest = options.onRequest;
  const doc = options.document || (editor && editor.ownerDocument) ||
    (typeof document !== "undefined" ? document : null);
  if (!editor || !doc || typeof doc.createElement !== "function" ||
      typeof onRequest !== "function" || !rules) return null;
  const debounce = options.debounce === undefined ? 120 : options.debounce;
  const autoTrigger = options.autoTrigger !== false;

  const list = doc.createElement("div");
  attr(list, "class", "completions");
  attr(list, "role", "listbox");
  attr(list, "aria-label", "completions");
  attr(list, "hidden", "");
  const where = doc.body || (doc.documentElement ? doc.documentElement : null);
  if (where && typeof where.appendChild === "function") where.appendChild(list);

  let open = false;
  let items = [];               // the server's items, unfiltered
  let filtered = [];            // what the popup draws
  let index = -1;
  let prefix = { start: 0, word: "" };
  let seq = 0;                  // a request generation: a stale answer is dropped
  let timer = null;
  let destroyed = false;
  let suppressInput = false;    // the input event our own insertion dispatches

  const value = () => (typeof editor.value === "string" ? editor.value : "");

  function metrics() {
    // The editor is monospace (web/playground.css), so one measured glyph is the column
    // width. Without layout (a Node test, a hidden pane) the defaults keep the popup on
    // the page rather than at NaN.
    const out = { lineHeight: 21, charWidth: 8, paddingLeft: 0, paddingTop: 0 };
    let style = null;
    try {
      style = typeof getComputedStyle === "function" ? getComputedStyle(editor) : null;
    } catch (_) { /* no layout */ }
    if (style) {
      const lineHeight = parseFloat(style.lineHeight);
      if (isFinite(lineHeight) && lineHeight > 0) out.lineHeight = lineHeight;
      const paddingLeft = parseFloat(style.paddingLeft);
      if (isFinite(paddingLeft)) out.paddingLeft = paddingLeft;
      const paddingTop = parseFloat(style.paddingTop);
      if (isFinite(paddingTop)) out.paddingTop = paddingTop;
      out.charWidth = measureCharWidth(doc, style) || out.charWidth;
    }
    return out;
  }

  function place() {
    const position = caretPosition(rules, editor);
    const m = metrics();
    const rect = typeof editor.getBoundingClientRect === "function"
      ? editor.getBoundingClientRect() : { left: 0, top: 0 };
    const scrollLeft = typeof editor.scrollLeft === "number" ? editor.scrollLeft : 0;
    const scrollTop = typeof editor.scrollTop === "number" ? editor.scrollTop : 0;
    let left = (rect.left || 0) + m.paddingLeft + position.character * m.charWidth - scrollLeft;
    let top = (rect.top || 0) + m.paddingTop + (position.line + 1) * m.lineHeight - scrollTop;
    const width = typeof list.offsetWidth === "number" && list.offsetWidth > 0 ? list.offsetWidth : 240;
    const height = (typeof list.offsetHeight === "number" && list.offsetHeight > 0 ? list.offsetHeight : 0) ||
      Math.min(filtered.length, 8) * m.lineHeight + 4;
    const viewWidth = typeof innerWidth === "number" ? innerWidth : 1024;
    const viewHeight = typeof innerHeight === "number" ? innerHeight : 768;
    if (left + width > viewWidth - 4) left = Math.max(4, viewWidth - width - 4);
    if (top + height > viewHeight - 4) {
      top = (rect.top || 0) + m.paddingTop + position.line * m.lineHeight - scrollTop - height;
      if (top < 4) top = 4;
    }
    setStyle(list, "left", Math.max(0, left) + "px");
    setStyle(list, "top", Math.max(0, top) + "px");
  }

  function render() {
    while (list.childNodes && list.childNodes.length) list.removeChild(list.childNodes[0]);
    filtered.forEach((item, i) => {
      const row = doc.createElement("div");
      attr(row, "class", "completion" + (i === index ? " sel" : ""));
      attr(row, "role", "option");
      attr(row, "data-index", i);
      attr(row, "aria-selected", i === index ? "true" : "false");
      const title = rules.itemTitle(item);
      if (title) attr(row, "title", title);
      // Two spans: the label and the detail, styled apart (and never as markup).
      const label = doc.createElement("span");
      attr(label, "class", "completion-label");
      label.appendChild(doc.createTextNode(String(item.label || "")));
      row.appendChild(label);
      if (item.detail !== undefined && item.detail !== null && String(item.detail) !== "") {
        const detail = doc.createElement("span");
        attr(detail, "class", "completion-detail");
        detail.appendChild(doc.createTextNode(String(item.detail)));
        row.appendChild(detail);
      }
      list.appendChild(row);
    });
    attr(list, "hidden", open && filtered.length ? null : "");
    attr(list, "data-count", filtered.length);
    const selected = list.childNodes[index];
    if (selected && typeof selected.scrollIntoView === "function") {
      try { selected.scrollIntoView({ block: "nearest" }); } catch (_) { /* no layout */ }
    }
  }

  function close() {
    open = false;
    index = -1;
    filtered = [];
    seq++;                        // any answer still in flight is now stale
    if (timer) { clearTimeout(timer); timer = null; }
    render();
  }

  function show(result) {
    items = rules.items(result) || [];
    if (!items.length) { close(); return []; }
    const state = rules.popup(value(), caretOffset(editor), items, 0);
    filtered = state.items.slice();
    prefix = { start: state.prefixStart, word: state.prefixWord };
    if (!filtered.length) { close(); return []; }
    open = true;
    index = state.index < 0 ? 0 : state.index;
    render();
    place();
    return filtered.slice();
  }

  // Ask the server at `position` (the caret by default). Re-entrant: the newest request
  // wins, and an answer that arrives after a newer one is dropped.
  async function request(position) {
    if (destroyed) return [];
    const at = position || caretPosition(rules, editor);
    const mine = ++seq;
    let result;
    try {
      result = await onRequest(at);
    } catch (_) {
      if (mine === seq) close();
      return [];
    }
    if (mine !== seq || destroyed) return [];
    return show(result);
  }

  function requestAtCaret() { return request(caretPosition(rules, editor)); }

  function accept() {
    if (!open || index < 0 || !filtered[index]) return false;
    const item = filtered[index];
    const before = value();
    const accepted = rules.accept(item, before, caretOffset(editor));
    close();
    if (accepted.text !== before) {
      editor.value = accepted.text;
      try { editor.setSelectionRange(accepted.caret, accepted.caret); } catch (_) {
        editor.selectionStart = accepted.caret;
        editor.selectionEnd = accepted.caret;
      }
      // The page's own `input` listeners (didChange, the squiggle refresh) see a normal
      // edit, so completion needs no second synchronisation path.
      const EventImpl = (doc.defaultView && doc.defaultView.Event) ||
        (typeof Event === "function" ? Event : null);
      if (EventImpl && typeof editor.dispatchEvent === "function") {
        suppressInput = true;
        try { editor.dispatchEvent(new EventImpl("input", { bubbles: true })); } catch (_) {
          suppressInput = false;
        }
      }
    } else {
      try { editor.setSelectionRange(accepted.caret, accepted.caret); } catch (_) { /* not a field */ }
    }
    return true;
  }

  function move(delta) {
    if (!open || !filtered.length) return;
    index = rules.move(index, delta, filtered.length);
    if (index < 0) index = 0;
    render();
  }

  // Whether an event is Ctrl/⌘-Space (the editor's "ask now"): the runtime's rule.
  function isAskKey(event) {
    if (!event) return false;
    return rules.askKey(event.key, event.code, !!event.ctrlKey, !!event.metaKey);
  }

  // The editor's keydown handler. Returns true when the event belonged to the popup (and
  // was prevented); the tests call it directly.
  function handleKey(event) {
    if (!event) return false;
    if (isAskKey(event)) {
      if (typeof event.preventDefault === "function") event.preventDefault();
      requestAtCaret();
      return true;
    }
    if (!open) return false;
    switch (event.key) {
      case "ArrowDown": move(1); break;
      case "ArrowUp": move(-1); break;
      case "PageDown": move(PAGE); break;
      case "PageUp": move(-PAGE); break;
      case "Enter":
      case "Tab":
        if (accept()) {
          if (typeof event.preventDefault === "function") event.preventDefault();
          if (typeof event.stopPropagation === "function") event.stopPropagation();
          return true;
        }
        return false;
      case "Escape":
        close();
        if (typeof event.preventDefault === "function") event.preventDefault();
        return true;
      default:
        return false;
    }
    if (typeof event.preventDefault === "function") event.preventDefault();
    return true;
  }

  // The editor's input handler: re-filter at once (the popup follows the typing), then
  // ask the server once the typing settles.
  function onInput() {
    if (suppressInput) { suppressInput = false; return; }
    if (!autoTrigger) { if (open) close(); return; }
    const text = value();
    const at = caretOffset(editor);
    const typed = text.slice(Math.max(0, at - 1), at);
    if (!rules.trigger(text, at, typed)) { close(); return; }
    if (open && items.length) {
      const state = rules.popup(text, at, items, index);
      filtered = state.items.slice();
      prefix = { start: state.prefixStart, word: state.prefixWord };
      index = filtered.length ? state.index : -1;
      if (index < 0) index = filtered.length ? 0 : -1;
      if (!filtered.length) { close(); return; }
      render();
      place();
    }
    if (timer) clearTimeout(timer);
    timer = setTimeout(() => { timer = null; requestAtCaret(); }, debounce);
  }

  function onBlur() { if (open) close(); }
  function onKeyDown(event) { handleKey(event); }

  if (typeof editor.addEventListener === "function") {
    editor.addEventListener("keydown", onKeyDown);
    editor.addEventListener("input", onInput);
    editor.addEventListener("blur", onBlur);
  }

  return {
    request,
    requestAtCaret,
    close,
    accept,
    handleKey,
    isOpen: () => open,
    items: () => filtered.slice(),
    selectedIndex: () => index,
    prefix: () => ({ start: prefix.start, word: prefix.word }),
    element: () => list,
    setItems(result) { return show(result); },
    destroy() {
      destroyed = true;
      if (timer) clearTimeout(timer);
      if (typeof editor.removeEventListener === "function") {
        editor.removeEventListener("keydown", onKeyDown);
        editor.removeEventListener("input", onInput);
        editor.removeEventListener("blur", onBlur);
      }
      if (list.parentNode) list.parentNode.removeChild(list);
    },
  };
}

// The width of one character in the editor's font, measured with a hidden span; null
// when there is no layout to measure.
function measureCharWidth(doc, style) {
  if (!doc || typeof doc.createElement !== "function" || !doc.body) return null;
  const probe = doc.createElement("span");
  attr(probe, "class", "completion-probe");
  attr(probe, "aria-hidden", "true");
  probe.appendChild(doc.createTextNode("0000000000"));
  setStyle(probe, "position", "absolute");
  setStyle(probe, "visibility", "hidden");
  if (style && style.font) setStyle(probe, "font", style.font);
  try {
    doc.body.appendChild(probe);
    const width = probe.getBoundingClientRect ? probe.getBoundingClientRect().width : 0;
    return width > 0 ? width / 10 : null;
  } catch (_) {
    return null;
  } finally {
    if (probe.parentNode) probe.parentNode.removeChild(probe);
  }
}

// The page's flag: `?completions=off` (also 0/none/false/no) turns the popup off;
// anything else, including no parameter, leaves it on.
export function wantsCompletions(search) {
  try {
    const value = new URLSearchParams(search || "").get("completions");
    if (value === null) return true;
    return !/^\s*(off|none|no|0|false)\s*$/i.test(value);
  } catch (_) {
    return true;
  }
}
