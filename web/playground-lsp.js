// The goals pane: the bridge between a page's editor and a language client
// (`web/lsp-client.js`), with the rendering in `web/goals.js`. It is the one
// implementation of the browser infoview, shared by the playground
// (`web/playground.html`, `web/playground.js`) and the standalone infoview page
// (`web/infoview.html`, `web/infoview.js`, served by `wiz lsp --ws`). The file keeps
// the name it grew up with: `web/build-playground.sh` lists the playground's scripts by
// name, and it is not this change's to touch (`agent/engine-trampoline` owns it);
// renaming it is a one-line follow-up once that branch lands.
//
// What it does, in the order a page needs it:
//
//   * `?lsp=` (or a config object) names the server; with none, or when the connection
//     fails, the pane says so and the playground stays exactly a local Wasm checker.
//     The transport is the config's: a WebSocket URL (`ws://`, the standalone page and
//     `?lsp=ws://…`), or a `WebSocketImpl` that is not a socket at all (the playground's
//     in-page server, `web/selfhost-lsp-shim.js`, `?lsp=selfhost`).
//   * After the handshake it opens the editor's text as one document (a fresh
//     `file:///playground-….wiz` URI, so pages do not overwrite each other), sends
//     `didChange` on edits, and asks for goals at the caret.
//   * `follow: true` is the standalone page's `?follow=1`: no document of its own and no
//     editor events. The page calls `goTo(uri, position)` on the server's
//     `wiz/infoview/cursor` notification, and the pane shows the state there — the
//     editor's document, not a copy (the server shares documents between connections).
//   * The panel renders the goals, the expected type and the term tree; clicking a
//     hypothesis or a subterm selects its source span in the textarea, and a
//     `wiz/subtermInfo` answer (when the server has one) describes it. Hover and arrow
//     keys reuse `web/tagged.js`'s `delegate`, the infoview's own highlighting code.
//   * `info` (an element) puts the selected subterm in its own box (the standalone
//     page's `#info`) instead of at the end of the panel; `onRender(view)` is called
//     after every render, so the page can mirror the state into its own status line.
//
// Positions are UTF-16 code units, as `lsp-client.js` negotiates; `positionAt` is the
// only conversion the page needs.
"use strict";
import { LspClient, endpointFromSearch } from "./lsp-client.js";
import { readGoalState, renderPanel, renderSelection, positionAt, parseSpan, rangeOffsets } from "./goals.js";
import { delegate } from "./tagged.js";
import { mountSquiggles, wantsSquiggles } from "./squiggles.js";
import { mountCompletions, wantsCompletions } from "./completions.js";
import { mountHover, wantsHover } from "./hover.js";
import { caretOffset } from "./editor-model.js";

// A document URI of our own: the server shares documents between every page, so two
// playground tabs must not edit the same file.
function scratchUri() {
  const random = Math.random().toString(36).slice(2, 10);
  return `file:///playground-${random}.wiz`;
}

// `config` is `{url}` (a `ws://` URL, or `null` for no server) or the whole endpoint
// from `parseEndpoint`; `search` defaults to the page's query string. `follow` makes the
// pane a viewer of another editor's document (`api.goTo`); `info` is an optional element
// for the selected subterm; `onRender` sees the view after every render.
//
// Options: `squiggles`/`completions` (false disables the overlay; they are on by
// default), `hover: false` (or `?hover=off`) turns the hover card and go-to-definition
// off, `onRender(view)` (called after every panel render: the Loom page uses it to
// mirror the panel HTML into its model), `eventsFrom` (the element the panel's clicks and
// keys arrive on; `panel` itself by default, and the live Loom container when the panel
// is rendered into a model), `document` (the page's document; the Node tests pass a
// double), and `positionDebounce` (ms, 120 by default).
export function startInfoview({
  editor, panel, config, search, uri, follow = false, info, onRender, eventsFrom,
  document: pageDocument, squiggles: wantSquigglesLayer, completions: wantCompletionsPopup,
  hover: wantHover, positionDebounce = 120,
} = {}) {
  if (!editor || !panel) return null;
  // The panel's markup may be produced here and rendered elsewhere (the `?ui=loom`
  // model): clicks and arrow keys then arrive on the live container, not on `panel`.
  const eventRoot = eventsFrom || panel;
  const query = search === undefined ? (typeof location !== "undefined" ? location.search : "") : search;
  const endpoint = config === undefined
    ? endpointFromSearch(query)
    : (typeof config === "string" ? { url: config } : config);
  let documentUri = uri || (follow ? null : scratchUri());
  let followPosition = null;
  let client = null;
  let generation = 0;
  let refreshTimer = null;
  let settleTimer = null;
  let suppressCursor = false;
  let selected = -1;
  let lastCursor = null;          // the position the goals were last asked about

  const view = {
    state: endpoint ? "connecting" : "no-server",
    // (#430: the label leaves the token out)
    endpoint: endpoint ? (endpoint.label || endpoint.url) : null,
    serverInfo: null,
    infoview: null,
    message: null,
    diagnostics: [],
    goals: null,
    goalsKind: null,
    term: null,
    termKind: null,
    info: null,
    items: [],
    position: null,
    canReconnect: false,
    follow,
  };

  // ## Hover and go-to-definition

  // The card shows the server's `textDocument/hover` at the caret and jumps to a
  // definition (`textDocument/definition`). A definition in the editor's own document
  // moves the caret and selects the name; one in a library has no page here, so the card
  // says `Prelude.wiz:7:1` and the editor stays where it was.
  const hover = wantHover === false || !wantsHover(query) ? null : mountHover({
    editor,
    document: pageDocument,
    onHover: (position) => (client && client.state === "open" ? client.hover(documentUri, position) : null),
    onDefinition: (position) => (client && client.state === "open" ? client.definition(documentUri, position) : null),
    onJump: (target) => {
      if (!target || target.uri !== documentUri) return false;
      highlight(target.range);
      return true;
    },
  });

  // Keep the panel's scroll position across re-renders (a click re-renders the panel).
  function render() {
    const top = panel.scrollTop || 0;
    // With `info`, the panel leaves the selection out and the box has it alone.
    renderPanel(panel, info ? Object.assign({}, view, { info: null }) : view);
    panel.scrollTop = top;
    if (info) info.innerHTML = view.info ? renderSelection(view.info) : "";
    if (typeof onRender === "function") {
      try { onRender(view); } catch (_) { /* the page's mirror must not break the pane */ }
    }
  }

  // The editor's features: squiggles under the diagnostics, and the completion popup at
  // the caret. Both are plain overlay DIVs (no dependency, no editor rewrite) and both
  // are absent without a DOM (the Node tests pass a stub textarea).
  const squiggles = wantSquigglesLayer === false || !wantsSquiggles(query)
    ? null : mountSquiggles(editor, { document: pageDocument });
  const completions = wantCompletionsPopup === false || !wantsCompletions(query)
    ? null : mountCompletions({
      editor,
      document: pageDocument,
      onRequest: (position) => {
        if (!client || client.state !== "open") return null;
        return client.completion(documentUri, position);
      },
    });

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
    for (let el = element; el && el !== eventRoot; el = el.parentElement) {
      if (el.dataset && el.dataset.span) return parseSpan(el.dataset.span);
    }
    return null;
  }

  // ## Asking the server

  // The position the pane asks about: the caret in its own editor, or the position the
  // followed editor announced (`?follow=1`).
  function currentPosition() {
    if (follow) return followPosition;
    return positionAt(editor.value, editor.selectionStart || 0);
  }

  async function refresh() {
    if (!client || client.state !== "open") return;
    if (!documentUri) return;   // following: nothing announced yet
    const position = currentPosition();
    if (!position) return;
    const mine = ++generation;
    const doc = client.docs.get(documentUri);
    const version = doc ? doc.version : null;
    view.position = position;
    // What else is at the cursor (`wiz/interactiveInfo`): a `#plot` message is a widget
    // item. A server without the request (or a stale session) simply shows none.
    const infoP = client.interactiveInfo(documentUri, position).then(
      (answer) => (answer && Array.isArray(answer.items) ? answer.items : []),
      () => []);
    const state = await readGoalState(client, documentUri, position);
    const items = await infoP;
    if (mine !== generation) return;   // a newer cursor/edit won
    // The text moved while the answer was in flight: the server answered about a
    // version the page no longer has, so its goals and ranges point at other text.
    const current = client.docs.get(documentUri);
    if (version !== null && (!current || current.version !== version)) return;
    lastCursor = position.line + ":" + position.character;
    view.goals = state.goals;
    view.goalsKind = state.goalsKind;
    view.term = state.term;
    view.termKind = state.termKind;
    if (state.session !== null) view.session = state.session;
    view.items = items;
    view.info = null;
    view.message = state.goalsKind === null && state.termKind === null && state.errors.length
      ? state.errors[0] : null;
    render();
  }

  function scheduleRefresh(delay = positionDebounce) {
    clearTimeout(refreshTimer);
    refreshTimer = setTimeout(refresh, delay);
  }

  function onEdit() {
    // An edit invalidates a queued and an in-flight refresh, and the server gets the
    // new text at once: a goal asked 120 ms after a keyup must not be about text the
    // server has not received (didChange used to wait 250 ms, and continuous typing
    // reset that timer, so no didChange was sent at all until the user paused).
    clearTimeout(refreshTimer);
    generation++;
    if (!client || client.state !== "open") return;
    client.changeDocument(documentUri, editor.value);
    // Diagnostics or `wiz/elaborated` normally arrive first; this is the fallback for a
    // server that sends neither.
    clearTimeout(settleTimer);
    settleTimer = setTimeout(refresh, 400);
  }

  // The caret moved: ask for the goals there after a short pause. `closePopup` is set by
  // a mouse selection (the user is going somewhere else); a keyup is how typing settles,
  // and must not close the completion list the typing just opened.
  function onCursor(closePopup = false) {
    if (suppressCursor) return;
    if (closePopup && completions) completions.close();
    const position = positionAt(editor.value, caretOffset(editor));
    const where = position.line + ":" + position.character;
    // The same caret: the server already answered (diagnostics still force a re-ask).
    if (where === lastCursor && view.goalsKind !== null) return;
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
    const tags = Array.from(eventRoot.querySelectorAll(".tt"));
    if (tags.length === 0) return;
    selected = Math.max(0, Math.min(tags.length - 1, index));
    for (let i = 0; i < tags.length; i++) tags[i].classList.toggle("sel", i === selected);
    const tag = tags[selected];
    // Following another editor: there is no local source to select a span in.
    const span = follow ? null : spanOf(tag);
    if (span) highlight(span);
    // Keep the keys on the panel: `highlight` focused the editor to show the selection,
    // and a second arrow must walk the tags again rather than the caret. In the Loom
    // page the panel is a detached model, and the focusable element is `#goals` inside
    // the live container.
    const focusTarget = panel === eventRoot ? panel
      : (eventRoot.querySelector ? (eventRoot.querySelector("#goals") || eventRoot) : eventRoot);
    try { focusTarget.focus({ preventScroll: true }); } catch (_) { /* a stub panel in a test */ }
    try { tag.scrollIntoView({ block: "nearest" }); } catch (_) { /* a stub panel in a test */ }
  }

  function clearSelection() {
    selected = -1;
    for (const tag of eventRoot.querySelectorAll(".tt.sel")) tag.classList.remove("sel");
  }

  eventRoot.addEventListener("click", (event) => {
    const action = event.target.closest ? event.target.closest("[data-action]") : null;
    if (action && action.dataset.action === "reconnect") {
      event.preventDefault();
      reconnect();
      return;
    }
    const span = follow ? null : spanOf(event.target);
    if (span) {
      event.preventDefault();
      highlight(span);
    }
    const tag = event.target.closest ? event.target.closest(".tt") : null;
    if (tag) {
      // Select it the way the arrows do (the infoview's `.sel`), then describe it.
      selectTag(Array.from(eventRoot.querySelectorAll(".tt")).indexOf(tag));
      describeSubterm(tag);
    }
  });

  // Hovering a subterm is the infoview's `.hover`; the arrows walk the tags in order and
  // Escape clears the selection. `delegate` adds the classes and prevents the default.
  delegate(eventRoot, {
    key: (name) => {
      if (name === "Escape") { clearSelection(); return; }
      const step = name === "ArrowDown" || name === "ArrowRight" ? 1 : -1;
      selectTag(selected < 0 ? 0 : selected + step);
    },
  });

  // ## Following another editor's cursor (`?follow=1`)

  function goTo(nextUri, position) {
    if (!follow || !nextUri || !position) return;
    documentUri = nextUri;
    followPosition = { line: position.line || 0, character: position.character || 0 };
    refresh();
  }

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
    // Store the text before the handshake: `openDocument` sends nothing while the
    // client is not open, and `connect()` opens every stored document. A first connect
    // that fails therefore leaves the document in the map, and a later reconnect opens
    // it instead of leaving the pane "connected" with a server that has no document.
    if (!follow && documentUri) client.openDocument(documentUri, editor.value);
    client.on("close", (info) => {
      if (info && info.intentional) return;
      if (hover) hover.close();
      view.state = "closed";
      view.info = null;
      view.diagnostics = [];
      if (squiggles) squiggles.update([]);
      render();
    });
    client.on("diagnostics", (params) => {
      if (!params || params.uri !== documentUri) return;
      view.diagnostics = params.diagnostics || [];
      if (squiggles) squiggles.update(view.diagnostics);
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
    // Following: the document belongs to the editor that opened it; do not touch it.
    if (!follow) client.openDocument(documentUri, editor.value);
    render();
    refresh();
    return api;
  }

  async function reconnect() {
    if (!client) return start();
    // The editor's text may have changed while the connection was down. Store it (this
    // sends nothing unless the client is open) and let `connect()` open it after the
    // handshake; `connect()` only re-opens documents already in its map.
    if (client.state !== "open" && !follow && documentUri) client.openDocument(documentUri, editor.value);
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
    // `uri` is the document opened at start; `target` is the one being shown (they differ
    // only in follow mode, where the server's notification moves it).
    uri: documentUri,
    target: () => documentUri,
    view,
    client: () => client,
    hover: () => hover,
    refresh,
    reconnect,
    // The caret as the page and the tests see it (UTF-16, line 0-based).
    position: () => positionAt(editor.value, caretOffset(editor)),
    squiggles: () => squiggles,
    completions: () => completions,
    goTo,
    stop() {
      if (hover) hover.close();
      if (completions) completions.destroy();
      if (squiggles) squiggles.destroy();
      if (!client) return;
      if (!follow && documentUri) client.closeDocument(documentUri);
      client.close();
    },
  };

  if (!follow) {
    editor.addEventListener("input", onEdit);
    // Caret → LSP: a keyup is typing settling, a click/mouseup/select is the user moving
    // the caret (and closes a popup they are leaving).
    editor.addEventListener("keyup", () => onCursor(false));
    editor.addEventListener("click", () => onCursor(true));
    editor.addEventListener("mouseup", () => onCursor(true));
    editor.addEventListener("select", () => onCursor(true));
    editor.addEventListener("focus", () => onCursor(false));
  }
  if (typeof addEventListener === "function") addEventListener("pagehide", () => api.stop());

  start();
  return api;
}
