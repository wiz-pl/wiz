// Hover at the caret and go-to-definition: the page's half.
//
// The card's contents and markup are `lib/Web/Hover.wiz`'s, and so are the two rules this
// file used to carry: the caret's LSP position (`Web.EditorModel.position`, injected as
// `options.position`) and a `textDocument/definition` answer's target, range and label
// (`Web.Hover.targetJson`, injected as `options.target`). This module keeps what needs a
// browser or a timer: when to ask (`schedule`), the request generation, the editor's
// caret and the card's position. `show(raw, label)` is the page's way into the runtime:
// `raw` is a `textDocument/hover` result as JSON (empty to close), `label` names a
// definition the page cannot open. Nothing here builds DOM or interprets Markdown.
"use strict";

// `?hover=off` (also `0`, `none`, `false`) turns the feature off. On by default.
export function wantsHover(search) {
  try {
    const value = new URLSearchParams(search || "").get("hover");
    return value === null || !/^\s*(off|none|no|0|false)\s*$/i.test(value);
  } catch (_) {
    return true;
  }
}

const NAVIGATION = new Set(["ArrowUp", "ArrowDown", "ArrowLeft", "ArrowRight",
  "Home", "End", "PageUp", "PageDown"]);

// `mountHover({editor, position, target, onHover, onDefinition, onJump, document, delay,
// show})`: the timing and the keyboard; `position(text, offset)` is the runtime's caret
// rule, `target(result)` its definition rule, and `show(raw, label)` hands an answer to
// the runtime card. Without a position rule there is nothing to ask about; a definition
// also needs the target rule, so `onDefinition` without it mounts no widget.
export function mountHover(options = {}) {
  const editor = options.editor;
  const onHover = options.onHover;
  const onDefinition = options.onDefinition;
  const onJump = options.onJump;
  const positionRule = options.position;
  const targetRule = options.target;
  const show = typeof options.show === "function" ? options.show : () => {};
  const doc = options.document || (editor && editor.ownerDocument) ||
    (typeof document !== "undefined" ? document : null);
  if (!editor || !doc || typeof doc.createElement !== "function") return null;
  if (typeof positionRule !== "function") return null;
  if (typeof onHover !== "function" && typeof onDefinition !== "function") return null;
  if (typeof onDefinition === "function" && typeof targetRule !== "function") return null;
  const delay = typeof options.delay === "number" && options.delay >= 0 ? options.delay : 350;

  let timer = null;
  let seq = 0;
  let shownAt = -1;

  const value = () => (typeof editor.value === "string" ? editor.value : "");
  const caret = () => {
    const at = typeof editor.selectionStart === "number" ? editor.selectionStart : 0;
    return Math.max(0, Math.min(value().length, Math.trunc(at)));
  };
  const position = () => positionRule(value(), caret());

  function cancel() {
    if (timer !== null) {
      clearTimeout(timer);
      timer = null;
    }
  }

  const card = () => (doc.getElementById ? doc.getElementById("wiz-hover") : null);

  // Hide the card and drop an answer still in flight.
  function close() {
    cancel();
    seq++;
    show("", "");
    shownAt = -1;
  }

  // Put the card just under the caret. The editor is monospace, so a line's height and
  // the textarea's padding are enough; the browser's layout is still the only authority.
  function place() {
    const el = card();
    if (!el || !el.style || typeof el.style !== "object") return;
    let lineHeight = 21;
    let paddingLeft = 0;
    let paddingTop = 0;
    try {
      const style = typeof getComputedStyle === "function" ? getComputedStyle(editor) : null;
      if (style) {
        const height = parseFloat(style.lineHeight);
        if (isFinite(height) && height > 0) lineHeight = height;
        const left = parseFloat(style.paddingLeft);
        if (isFinite(left)) paddingLeft = left;
        const top = parseFloat(style.paddingTop);
        if (isFinite(top)) paddingTop = top;
      }
    } catch (_) { /* no layout: the defaults */ }
    const rect = typeof editor.getBoundingClientRect === "function"
      ? editor.getBoundingClientRect() : { left: 0, top: 0 };
    const scrollTop = typeof editor.scrollTop === "number" ? editor.scrollTop : 0;
    const at = position();
    let left = (rect.left || 0) + paddingLeft + 8;
    let top = (rect.top || 0) + paddingTop + (at.line + 1) * lineHeight - scrollTop;
    const width = el.offsetWidth > 0 ? el.offsetWidth : 320;
    const height = el.offsetHeight > 0 ? el.offsetHeight : 60;
    const viewWidth = typeof innerWidth === "number" ? innerWidth : 1024;
    const viewHeight = typeof innerHeight === "number" ? innerHeight : 768;
    if (left + width > viewWidth - 8) left = Math.max(8, viewWidth - width - 8);
    if (top + height > viewHeight - 8) {
      top = (rect.top || 0) + paddingTop + at.line * lineHeight - scrollTop - height;
      if (top < 8) top = 8;
    }
    el.style.position = "fixed";
    el.style.left = Math.round(left) + "px";
    el.style.top = Math.round(top) + "px";
    el.style.zIndex = "40";
  }

  // Ask for the hover at the caret now. Returns the server's answer (or null).
  async function inquire() {
    cancel();
    if (typeof onHover !== "function") return null;
    const at = caret();
    const mine = ++seq;
    let result = null;
    try {
      result = await onHover(position());
    } catch (_) {
      result = null;             // MethodNotFound, not connected, a timeout: silence
    }
    if (mine !== seq || caret() !== at) return null;
    show(result && typeof result === "object" ? JSON.stringify(result) : "", "");
    place();
    shownAt = at;
    return result;
  }

  function schedule() {
    cancel();
    timer = setTimeout(() => { timer = null; inquire(); }, delay);
  }

  // F12 / Ctrl-⌘-click: where is the identifier at the caret declared? The answer's
  // target, range and label are the runtime's (`targetRule`).
  async function goToDefinition() {
    if (typeof onDefinition !== "function" || typeof targetRule !== "function") return null;
    cancel();
    const mine = ++seq;
    let result = null;
    try {
      result = await onDefinition(position());
    } catch (_) {
      result = null;
    }
    if (mine !== seq) return null;
    const target = targetRule(result);
    if (!target || typeof target.uri !== "string" || !target.range) return null;
    const jump = { uri: target.uri, range: target.range };
    let jumped = false;
    if (typeof onJump === "function") {
      try { jumped = onJump(jump) === true; } catch (_) { jumped = false; }
    }
    if (jumped) {
      close();
      return jump;
    }
    show("", target.label || "");
    place();
    return jump;
  }

  function onKeydown(event) {
    if (!event) return;
    if (event.key === "Escape") {
      close();
      if (typeof event.preventDefault === "function") event.preventDefault();
      return;
    }
    if (event.key === "F12") {
      if (typeof event.preventDefault === "function") event.preventDefault();
      goToDefinition();
      return;
    }
    if (NAVIGATION.has(event.key)) close();   // the card describes the old caret
  }

  function onKeyup(event) {
    if (event && NAVIGATION.has(event.key)) schedule();
  }

  function onClick(event) {
    if (event && (event.ctrlKey === true || event.metaKey === true)) {
      if (typeof event.preventDefault === "function") event.preventDefault();
      goToDefinition();
      return;
    }
    schedule();               // the browser has moved the caret by the click
  }

  if (typeof editor.addEventListener === "function") {
    editor.addEventListener("keydown", onKeydown);
    editor.addEventListener("keyup", onKeyup);
    editor.addEventListener("click", onClick);
    editor.addEventListener("select", schedule);
    editor.addEventListener("input", close);
    editor.addEventListener("scroll", close);
    editor.addEventListener("blur", close);
  }

  return {
    inquire, schedule, close, goToDefinition, place,
    isOpen: () => { const el = card(); return !!el && el.getAttribute("hidden") === null; },
    content: () => { const el = card(); return el ? el.textContent || "" : ""; },
    describedAt: () => shownAt,
    destroy() { close(); },
  };
}
