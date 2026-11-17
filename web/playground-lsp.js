// The playground's goals pane: the bridge between the page's textarea and the language
// client (`web/lsp-client.js`), with the rendering in `web/goals.js`.
//
// What it does, in the order the page needs it:
//
//   * `?lsp=` (or a config object) names the server; with none, or when the connection
//     fails, the pane says so and the playground stays exactly a local Wasm checker.
//   * After the handshake it opens the editor's text as one document (a fresh
//     `file:///playground-….wiz` URI, so pages do not overwrite each other), sends
//     `didChange` on edits, and asks for goals at the caret.
//   * The panel renders the goals, the expected type and the term tree; clicking a
//     hypothesis or a subterm selects its source span in the textarea, and a `wiz/subtermInfo`
//     answer (when the server has one) describes it. Hover and arrow keys reuse
//     `web/tagged.js`'s `delegate`, the infoview's own highlighting code.
//
// Positions are UTF-16 code units, as `lsp-client.js` negotiates; `positionAt` is the
// only conversion the page needs.
"use strict";
import { LspClient, endpointFromSearch } from "./lsp-client.js";
import { readGoalState, renderPanel, positionAt, parseSpan, rangeOffsets } from "./goals.js";
import { delegate } from "./tagged.js";

// A document URI of our own: the server shares documents between every page, so two
// playground tabs must not edit the same file.
function scratchUri() {
  const random = Math.random().toString(36).slice(2, 10);
  return `file:///playground-${random}.wiz`;
}

// `config` is `{url}` (a `ws://` URL, or `null` for no server) or the whole endpoint
// from `parseEndpoint`; `search` defaults to the page's query string.
export function startInfoview({ editor, panel, config, search, uri } = {}) {
  if (!editor || !panel) return null;
  const endpoint = config === undefined
    ? endpointFromSearch(search === undefined ? (typeof location !== "undefined" ? location.search : "") : search)
    : (typeof config === "string" ? { url: config } : config);
  const documentUri = uri || scratchUri();
  let client = null;
  let generation = 0;
  let refreshTimer = null;
  let changeTimer = null;
  let settleTimer = null;
  let suppressCursor = false;
  let selected = -1;

  const view = {
    state: endpoint ? "connecting" : "no-server",
    endpoint: endpoint ? endpoint.url : null,
    serverInfo: null,
    infoview: null,
    message: null,
    diagnostics: [],
    goals: null,
    goalsKind: null,
    term: null,
    termKind: null,
    info: null,
    position: null,
    completions: null,
    canReconnect: false,
  };

  // Keep the panel's scroll position across re-renders (a click re-renders the panel).
  function render() {
    const top = panel.scrollTop || 0;
    renderPanel(panel, view);
    panel.scrollTop = top;
  }

  // ## Source highlighting (a textarea's native selection: UTF-16 offsets)

  function highlight(span) {
    const { start, end } = rangeOffsets(editor.value, span);
    suppressCursor = true;
    try { editor.focus({ preventScroll: true }); } catch (_) { try { editor.focus(); } catch (_) { /* no focus */ } }
    try { editor.setSelectionRange(start, end); } catch (_) { /* not a text field */ }
    try {
      const line = span && span.start ? span.start.line : 0;
      const style = typeof getComputedStyle === "function" ? getComputedStyle(editor) : null;
      const lineHeight = (style && parseFloat(style.lineHeight)) || 21;
      const top = line * lineHeight;
      if (top < editor.scrollTop || top + lineHeight > editor.scrollTop + editor.clientHeight) {
        editor.scrollTop = Math.max(0, top - lineHeight * 2);
      }
    } catch (_) { /* a stub editor in a test */ }
    setTimeout(() => { suppressCursor = false; }, 0);
  }

  function spanOf(element) {
    for (let el = element; el && el !== panel; el = el.parentElement) {
      if (el.dataset && el.dataset.span) return parseSpan(el.dataset.span);
    }
    return null;
  }

  // ## Asking the server

  async function refresh() {
    if (!client || client.state !== "open") return;
    const mine = ++generation;
    const position = positionAt(editor.value, editor.selectionStart || 0);
    view.position = position;
    const state = await readGoalState(client, documentUri, position);
    if (mine !== generation) return;   // a newer cursor/edit won
    view.goals = state.goals;
    view.goalsKind = state.goalsKind;
    view.term = state.term;
    view.termKind = state.termKind;
    if (state.session !== null) view.session = state.session;
    view.info = null;
    view.message = state.goalsKind === null && state.termKind === null && state.errors.length
      ? state.errors[0] : null;
    render();
  }

  function scheduleRefresh(delay = 120) {
    clearTimeout(refreshTimer);
    refreshTimer = setTimeout(refresh, delay);
  }

  function onEdit() {
    closeCompletions();
    clearTimeout(changeTimer);
    changeTimer = setTimeout(() => {
      if (!client || client.state !== "open") return;
      client.changeDocument(documentUri, editor.value);
      // Diagnostics or `wiz/elaborated` normally arrive first; this is the fallback.
      clearTimeout(settleTimer);
      settleTimer = setTimeout(refresh, 400);
    }, 250);
  }

  function onCursor() {
    if (suppressCursor) return;
    scheduleRefresh();
  }

  // ## Clicking and the keyboard

  async function describeSubterm(tag) {
    const ref = tag && tag.dataset ? tag.dataset.ref : undefined;
    if (ref === undefined || view.session === null || view.session === undefined) return;
    if (!client || client.state !== "open") return;
    const mine = generation;
    try {
      const info = await client.subtermInfo(documentUri, view.session, Number(ref));
      if (mine !== generation) return;
      view.info = info;
      render();
    } catch (_) {
      // A stale session (ContentModified) or a server without subtermInfo: keep the
      // goal view and say nothing.
    }
  }

  function selectTag(index) {
    const tags = Array.from(panel.querySelectorAll(".tt"));
    if (tags.length === 0) return;
    selected = Math.max(0, Math.min(tags.length - 1, index));
    for (let i = 0; i < tags.length; i++) tags[i].classList.toggle("sel", i === selected);
    const tag = tags[selected];
    const span = spanOf(tag);
    if (span) highlight(span);
    // Keep the keys on the panel: `highlight` focused the editor to show the selection,
    // and a second arrow must walk the tags again rather than the caret.
    try { panel.focus({ preventScroll: true }); } catch (_) { /* a stub panel in a test */ }
    try { tag.scrollIntoView({ block: "nearest" }); } catch (_) { /* a stub panel in a test */ }
  }

  function clearSelection() {
    selected = -1;
    for (const tag of panel.querySelectorAll(".tt.sel")) tag.classList.remove("sel");
  }

  panel.addEventListener("click", (event) => {
    const choice = event.target.closest ? event.target.closest("[data-completion]") : null;
    if (choice && choice.dataset && choice.dataset.completion !== undefined) {
      event.preventDefault();
      acceptCompletion(Number(choice.dataset.completion));
      return;
    }
    const action = event.target.closest ? event.target.closest("[data-action]") : null;
    if (action && action.dataset.action === "reconnect") {
      event.preventDefault();
      reconnect();
      return;
    }
    const span = spanOf(event.target);
    if (span) {
      event.preventDefault();
      highlight(span);
    }
    const tag = event.target.closest ? event.target.closest(".tt") : null;
    if (tag) {
      selected = Array.from(panel.querySelectorAll(".tt")).indexOf(tag);
      describeSubterm(tag);
    }
  });

  // Hovering a subterm is the infoview's `.hover`; the arrows walk the tags in order and
  // Escape clears the selection. `delegate` adds the classes and prevents the default.
  delegate(panel, {
    key: (name) => {
      if (name === "Escape") { clearSelection(); return; }
      const step = name === "ArrowDown" || name === "ArrowRight" ? 1 : -1;
      selectTag(selected < 0 ? 0 : selected + step);
    },
  });

  // ## Completions
  //
  // A textarea has no popup, so `Ctrl-Space` asks the server for the names that start with
  // the identifier before the caret and the panel shows them as a list (above Goals):
  // ArrowUp/ArrowDown choose, Tab or Enter inserts the chosen label over the prefix,
  // Escape closes, and typing closes it too (the list would be stale). The server does the
  // prefix filtering, so a page whose module has no `wiz_playground_names` shows an empty
  // list rather than failing.
  let completing = { open: false, items: [], index: 0, prefix: "", start: 0 };
  let completionGeneration = 0;

  function closeCompletions() {
    completionGeneration++;
    if (!completing.open) return;
    completing = { open: false, items: [], index: 0, prefix: "", start: 0 };
    view.completions = null;
    render();
  }

  async function requestCompletions() {
    if (!client || client.state !== "open") return null;
    const text = editor.value;
    const caret = editor.selectionStart || 0;
    let start = caret;
    while (start > 0 && /[A-Za-z0-9_'.]/.test(text[start - 1])) start--;
    const prefix = text.slice(start, caret);
    const mine = ++completionGeneration;
    let result = null;
    try {
      result = await client.completion(documentUri, positionAt(text, caret));
    } catch (_) {
      result = null;
    }
    if (mine !== completionGeneration) return null;
    const items = result && Array.isArray(result.items) ? result.items.slice(0, 200) : [];
    completing = { open: true, items, index: 0, prefix, start };
    view.completions = completing;
    render();
    return completing;
  }

  // Insert the chosen item's label over the identifier before the caret; returns whether
  // something was inserted.
  function acceptCompletion(which) {
    if (!completing.open) return false;
    const item = completing.items[typeof which === "number" ? which : completing.index];
    if (!item || typeof item.label !== "string") { closeCompletions(); return false; }
    const text = editor.value;
    const caret = editor.selectionStart || 0;
    let start = caret;
    while (start > 0 && /[A-Za-z0-9_'.]/.test(text[start - 1])) start--;
    const value = text.slice(0, start) + item.label + text.slice(caret);
    const at = start + item.label.length;
    editor.value = value;
    try { editor.setSelectionRange(at, at); } catch (_) { /* not a text field */ }
    try { editor.focus({ preventScroll: true }); } catch (_) { try { editor.focus(); } catch (_) { /* no focus */ } }
    closeCompletions();
    onEdit();
    scheduleRefresh(0);
    return true;
  }

  editor.addEventListener("keydown", (event) => {
    const key = event.key;
    const space = key === " " || key === "Spacebar" || event.code === "Space";
    if (space && (event.ctrlKey || event.metaKey)) {
      event.preventDefault();
      requestCompletions();
      return;
    }
    if (!completing.open) return;
    if (key === "ArrowDown" || key === "ArrowUp") {
      event.preventDefault();
      const n = completing.items.length;
      if (n === 0) return;
      completing.index = (completing.index + (key === "ArrowDown" ? 1 : n - 1)) % n;
      view.completions = completing;
      render();
      return;
    }
    if (key === "Tab" || key === "Enter") {
      event.preventDefault();
      acceptCompletion();
      return;
    }
    if (key === "Escape") {
      event.preventDefault();
      closeCompletions();
    }
  });

  // ## The connection

  async function start() {
    if (!endpoint) { view.state = "no-server"; render(); return null; }
    view.state = "connecting";
    view.message = null;
    view.canReconnect = true;
    render();
    client = new LspClient({
      url: endpoint.url,
      WebSocketImpl: endpoint.WebSocketImpl,
      requestTimeout: endpoint.requestTimeout,
      languageId: endpoint.languageId,
    });
    client.on("close", (info) => {
      if (info && info.intentional) return;
      view.state = "closed";
      view.info = null;
      render();
    });
    client.on("diagnostics", (params) => {
      if (!params || params.uri !== documentUri) return;
      view.diagnostics = params.diagnostics || [];
      render();
      clearTimeout(settleTimer);
      scheduleRefresh(0);
    });
    client.on("wiz/elaborated", (params) => {
      if (!params || params.uri !== documentUri) return;
      clearTimeout(settleTimer);
      scheduleRefresh(0);
    });
    try {
      await client.connect();
    } catch (e) {
      view.state = "failed";
      view.message = e && e.message ? e.message : String(e);
      view.serverInfo = null;
      view.infoview = null;
      render();
      return null;
    }
    if (client.state !== "open") return null;
    view.state = "open";
    view.serverInfo = client.serverInfo;
    view.infoview = client.infoview;
    client.openDocument(documentUri, editor.value);
    render();
    refresh();
    return api;
  }

  async function reconnect() {
    if (!client) return start();
    view.state = "connecting";
    view.message = null;
    view.goals = null;
    view.goalsKind = null;
    view.term = null;
    view.termKind = null;
    render();
    try {
      await client.reconnect();
    } catch (e) {
      view.state = "failed";
      view.message = e && e.message ? e.message : String(e);
      render();
      return null;
    }
    view.state = "open";
    view.serverInfo = client.serverInfo;
    view.infoview = client.infoview;
    render();
    refresh();
    return api;
  }

  const api = {
    uri: documentUri,
    view,
    client: () => client,
    refresh,
    reconnect,
    complete: requestCompletions,
    acceptCompletion,
    closeCompletions,
    completions: () => completing,
    stop() {
      if (!client) return;
      client.closeDocument(documentUri);
      client.close();
    },
  };

  editor.addEventListener("input", onEdit);
  editor.addEventListener("keyup", onCursor);
  editor.addEventListener("click", onCursor);
  editor.addEventListener("select", onCursor);
  if (typeof addEventListener === "function") addEventListener("pagehide", () => api.stop());

  start();
  return api;
}
