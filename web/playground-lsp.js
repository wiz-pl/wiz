// The goals pane's transport: the language client (`web/lsp-client.js`) and the editor's
// carets, with the rendering in `lib/Web/Goals.wiz` and the card in `lib/Web/Hover.wiz`.
// The pane itself is a runtime; this file sends it the server's answers (`update`) and
// does what it asks for (`request`: reveal a source span, describe a subterm, reconnect).
//
// What stays here is host work: the URL's endpoint rule, the WebSocket, document sync,
// the debounce, the underlines (`web/squiggles.js`) and the completion popup
// (`web/completions.js`). The page's `update(kind, a, b)` is its runtime effect.
"use strict";
import { LspClient, endpointFromSearch } from "./lsp-client.js";
import { mountWidgets } from "./widgets.js";
import { mountSquiggles, wantsSquiggles } from "./squiggles.js";
import { mountCompletions, wantsCompletions } from "./completions.js";
import { mountHover, wantsHover } from "./hover.js";
import { caretOffset } from "./framework/editor-text.js";

// A document URI of our own: the server shares documents between every page, so two
// playground tabs must not edit the same file.
function scratchUri() {
  const random = Math.random().toString(36).slice(2, 10);
  return `file:///playground-${random}.wiz`;
}

// The runtime's position index (`lib/Web/EditorModel.wiz`), read through `mount.ask`.
// `ask(name, ...strings) -> string` invokes a `wiz_loom_*` export; `versionOf()` (when
// given) is the document version the cache is keyed by. The line table is built once per
// (version, text) and reused by every query: the previous keyup path rebuilt the whole
// UTF-16 expansion on each call, and the selfhost index repeated it per caret.
export function createIndexer(ask, versionOf = null) {
  let cache = { text: null, version: undefined, index: "" };
  const indexOf = (text) => {
    const version = versionOf ? versionOf() : undefined;
    if (cache.text === text && cache.version === version) return cache.index;
    const index = ask("wiz_loom_editor_index", "0", text);
    cache = { text, version, index };
    return index;
  };
  return {
    index: indexOf,
    position: (text, offset) =>
      JSON.parse(ask("wiz_loom_editor_position_index", indexOf(text), String(offset | 0))),
    offset: (text, position) => {
      const line = position && Number.isFinite(position.line) ? Math.trunc(position.line) : 0;
      const character = position && Number.isFinite(position.character) ? Math.trunc(position.character) : 0;
      return Number(ask("wiz_loom_editor_offset_index", indexOf(text),
        String(line), String(character)));
    },
    lineEnd: (text, offset) =>
      Number(ask("wiz_loom_editor_line_end_index", indexOf(text), String(offset | 0))),
    range: (text, from, to) => ({
      start: JSON.parse(ask("wiz_loom_editor_position_index", indexOf(text), String(from | 0))),
      end: JSON.parse(ask("wiz_loom_editor_position_index", indexOf(text), String(to | 0))),
    }),
    utf16: (text, codePoints) => Number(ask("wiz_loom_editor_utf16", text, String(codePoints | 0))),
    editorOffset: (text, prefix, codePoints) =>
      Number(ask("wiz_loom_editor_editor_offset", text, prefix, String(codePoints | 0))),
    segments: (text, diagnostics) =>
      JSON.parse(ask("wiz_loom_editor_segments_index", indexOf(text), text,
        JSON.stringify(diagnostics || []), "0")),
    build: (text, entries, prefix) =>
      ask("wiz_loom_index_build", text, prefix || "", JSON.stringify(entries || [])),
    size: (index) => Number(ask("wiz_loom_index_size", index)),
    term: (text, index, offset) =>
      JSON.parse(ask("wiz_loom_index_term", text, index, String(offset | 0))),
    goal: (text, index, offset) =>
      JSON.parse(ask("wiz_loom_index_goal", text, index, String(offset | 0))),
    declarations: (text, index) => JSON.parse(ask("wiz_loom_index_declarations", text, index)),
    declarationNamed: (text, index, name) =>
      JSON.parse(ask("wiz_loom_index_declaration", text, index, name)),
    // The in-page server's pure rules (`Web.Selfhost.wiz`): the initialize capabilities,
    // the engine's lines as diagnostics, the command splitter, the Prelude rule and the
    // completion/hover/definition answers. The shim is the server around them.
    initializeCapabilities: () => JSON.parse(ask("wiz_loom_lsp_capabilities")),
    withPrelude: (text) => JSON.parse(ask("wiz_loom_lsp_prelude", text)),
    splitCommands: (text) => JSON.parse(ask("wiz_loom_lsp_commands", text)),
    outputLines: (output) => JSON.parse(ask("wiz_loom_lsp_output_lines", output)),
    parseErrorOffset: (line) => {
      const n = Number(ask("wiz_loom_lsp_parse_error", line));
      return n < 0 ? null : n;
    },
    diagnosticsFromOutput: (text, output) =>
      JSON.parse(ask("wiz_loom_lsp_diagnostics_output", text, output)),
    parseCheck(json) {
      const text = json === null || json === undefined ? ""
        : (typeof json === "string" ? json : JSON.stringify(json));
      return JSON.parse(ask("wiz_loom_lsp_parse_check", text));
    },
    diagnosticsFromCheck: (text, answer) =>
      JSON.parse(ask("wiz_loom_lsp_diagnostics_check", text,
        JSON.stringify(answer === null || answer === undefined ? {} : answer))),
    completionPrefix: (text, offset) =>
      JSON.parse(ask("wiz_loom_lsp_completion_prefix", text, String(offset | 0))),
    wordAt: (text, offset) =>
      JSON.parse(ask("wiz_loom_lsp_word_at", text, String(offset | 0))),
    filterCompletions: (names, prefix, limit = 200) =>
      JSON.parse(ask("wiz_loom_lsp_filter_completions", JSON.stringify(names || []),
        String(prefix || ""), String(limit))),
    completion: (text, index, position) =>
      JSON.parse(ask("wiz_loom_lsp_completion", text, index || "",
        JSON.stringify(position || {}))),
    hover: (text, index, position) =>
      JSON.parse(ask("wiz_loom_lsp_hover", text, index || "",
        JSON.stringify(position || {}))),
    definition: (text, index, position, uri) =>
      JSON.parse(ask("wiz_loom_lsp_definition", text, index || "",
        JSON.stringify(position || {}), uri || "")),
    // The completion popup's paint facts (`web/completions.js`) and the goals pane's
    // source spans (`highlight`), so neither decides a rule.
    itemTitle: (item) => ask("wiz_loom_editor_item_title", JSON.stringify(item || {})),
    askKey: (key, code, ctrl, meta) =>
      ask("wiz_loom_editor_ask_key", String(key || ""), String(code || ""),
        ctrl ? "1" : "0", meta ? "1" : "0") === "1",
    span: (text, span) => JSON.parse(ask("wiz_loom_editor_span", text, span)),
    rangeText: (range) => ask("wiz_loom_editor_range_text", JSON.stringify(range || {})),
    // A `textDocument/definition` answer's target, range and label (`Web.Hover`); the
    // page only decides whether it can open the target's document.
    target: (result) => JSON.parse(ask("wiz_loom_hover_target",
      result === null || result === undefined ? "null" : JSON.stringify(result))),
  };
}

// `config` is `{url}` (a `ws://` URL, or `null` for no server), an endpoint from
// `endpointFromSearch`, or the page's in-page endpoint (`?lsp=selfhost`). `update(kind,
// a, b)` is the runtime's effect (`view`, `info`, `hover`); a page that still passes a
// `render` callback (the Node tests) gets the same events there. `widgetPane` is an
// element for the widget host: the cards are mounted there by `mountWidgets`, never
// rendered into the goals panel.
export function startInfoview({
  editor, update, render, config, search, uri, follow = false,
  document: pageDocument, squiggles: wantSquigglesLayer, completions: wantCompletionsPopup,
  hover: wantHover, positionDebounce = 120, onRender, rules, widgetPane,
} = {}) {
  if (!editor && !follow) return null;
  const send = typeof update === "function" ? update
    : (kind, a, b) => { if (typeof render === "function") render(kind, a, b); };
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
  let lastCursor = null;

  const view = {
    state: endpoint ? "connecting" : "no-server",
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

  // The widget pane is rebuilt only when the payload changed: `mountWidgets` clears the
  // container and sanitises every card, and `publish` runs on every answer, diagnostics
  // notification and cursor move (a plot's SVG is up to 2 MB). The key is the serialized
  // payload, so identical items keep the mounted DOM (and its `<details open>`, scroll
  // and focus) across publishes.
  let lastWidgets = null;
  const widgetKey = (items) => {
    try { return JSON.stringify(items || []); } catch { return ""; }
  };
  const publish = () => {
    send("view", JSON.stringify(view), "");
    if (widgetPane) {
      const key = widgetKey(view.items);
      if (key !== lastWidgets) {
        mountWidgets(widgetPane, view.items, pageDocument || globalThis.document);
        lastWidgets = key;
      }
    }
    if (typeof onRender === "function") {
      try { onRender(view); } catch (_) { /* the page's mirror must not break the pane */ }
    }
  };
  const publishInfo = (info) => send("info", JSON.stringify(info), "");

  // ## Hover

  const hover = wantHover === false || !wantsHover(query) || !rules ||
    typeof rules.position !== "function" ? null : mountHover({
    editor,
    document: pageDocument,
    // The caret and the definition answer are the runtime's rules (`Web.EditorModel`,
    // `Web.Hover`); this module supplies the browser's caret and the socket's answer.
    position: (text, offset) => rules.position(text, offset),
    target: typeof rules.target === "function" ? (result) => rules.target(result) : undefined,
    onHover: (position) => (client && client.state === "open" ? client.hover(documentUri, position) : null),
    onDefinition: (position) => (client && client.state === "open" ? client.definition(documentUri, position) : null),
    onJump: (target) => {
      if (!target || target.uri !== documentUri) return false;
      highlight(target.range);
      return true;
    },
    show: (raw, label) => {
      send("hover", JSON.stringify({ raw, label }), "");
      if (hover) hover.place();
    },
  });

  // The editor's features: squiggles under the diagnostics, and the completion popup at
  // the caret. Both are plain overlay DIVs (no dependency, no editor rewrite) and both
  // are absent without a DOM or without the runtime's rules (the standalone infoview
  // passes `squiggles: false`/`completions: false`).
  const squiggles = wantSquigglesLayer === false || !wantsSquiggles(query) || !rules
    ? null : mountSquiggles(editor, {
      document: pageDocument,
      segments: (text, diagnostics) => rules.segments(text, diagnostics),
    });
  const completions = wantCompletionsPopup === false || !wantsCompletions(query) || !rules
    ? null : mountCompletions({
      editor,
      document: pageDocument,
      rules,
      onRequest: (position) => {
        if (!client || client.state !== "open") return null;
        return client.completion(documentUri, position);
      },
    });

  // ## Source highlighting (the textarea's native selection)

  function highlight(range) {
    if (!editor || !rules) return;
    const span = rules.span(editor.value,
      typeof range === "string" ? range : rules.rangeText(range || {}));
    if (!span) return;
    const start = span[0];
    const end = Math.max(start, span[1]);
    suppressCursor = true;
    try { editor.focus({ preventScroll: true }); } catch (_) { try { editor.focus(); } catch (_) { /* no focus */ } }
    try { editor.setSelectionRange(start, end); } catch (_) { /* not a text field */ }
    try {
      const lineHeight = 21;
      const top = rules.position(editor.value, start).line * lineHeight;
      if (top < editor.scrollTop || top + lineHeight > editor.scrollTop + editor.clientHeight) {
        editor.scrollTop = Math.max(0, top - lineHeight * 2);
      }
    } catch (_) { /* a stub editor in a test */ }
    setTimeout(() => { suppressCursor = false; }, 0);
  }

  function currentPosition() {
    if (follow) return followPosition;
    return rules ? rules.position(editor.value, caretOffset(editor)) : null;
  }

  // ## Asking the server

  async function refresh() {
    if (!client || client.state !== "open") return;
    if (!documentUri) return;
    const position = currentPosition();
    if (!position) return;
    const mine = ++generation;
    const doc = client.docs.get(documentUri);
    const version = doc ? doc.version : null;
    view.position = position;
    const infoP = client.interactiveInfo(documentUri, position).then(
      (answer) => (answer && Array.isArray(answer.items) ? answer.items : []),
      () => []);
    const goals = await client.interactiveGoals(documentUri, position).then(
      (answer) => ({ value: answer, kind: "interactive" }),
      async () => {
        try { return { value: await client.plainGoal(documentUri, position), kind: "plain" }; } catch (_) { return null; }
      });
    const term = await client.interactiveTermGoal(documentUri, position).then(
      (answer) => ({ value: answer, kind: "interactive" }),
      async () => {
        try { return { value: await client.plainTermGoal(documentUri, position), kind: "plain" }; } catch (_) { return null; }
      });
    const items = await infoP;
    if (mine !== generation) return;
    const current = client.docs.get(documentUri);
    if (version !== null && (!current || current.version !== version)) return;
    lastCursor = position.line + ":" + position.character;
    view.goals = goals ? goals.value : null;
    view.goalsKind = goals ? goals.kind : null;
    view.term = term ? term.value : null;
    view.termKind = term ? term.kind : null;
    if (goals && goals.value && typeof goals.value.session === "number") view.session = goals.value.session;
    else if (term && term.value && term.value.goal && typeof term.value.goal.session === "number") view.session = term.value.goal.session;
    view.items = items;
    view.info = null;
    view.message = !view.goalsKind && !view.termKind ? "nothing at the cursor" : null;
    publish();
  }

  function scheduleRefresh(delay = positionDebounce) {
    clearTimeout(refreshTimer);
    refreshTimer = setTimeout(refresh, delay);
  }

  function onEdit() {
    clearTimeout(refreshTimer);
    generation++;
    if (!client || client.state !== "open") return;
    client.changeDocument(documentUri, editor.value);
    clearTimeout(settleTimer);
    settleTimer = setTimeout(refresh, 400);
  }

  function onCursor(closePopup = false) {
    if (suppressCursor) return;
    if (closePopup && completions) completions.close();
    if (!rules) return;
    const position = rules.position(editor.value, caretOffset(editor));
    const where = position.line + ":" + position.character;
    if (where === lastCursor && view.goalsKind !== null) return;
    scheduleRefresh();
  }

  async function describeSubterm(ref) {
    if (view.session === null || view.session === undefined) return;
    if (!client || client.state !== "open") return;
    const mine = generation;
    try {
      const info = await client.subtermInfo(documentUri, view.session, Number(ref));
      if (mine !== generation) return;
      view.info = info;
      publishInfo(info);
    } catch (_) { /* a stale session or a server without subtermInfo: say nothing */ }
  }

  // ## Following another editor's cursor (`?follow=1`)

  function goTo(nextUri, position) {
    if (!follow || !nextUri || !position) return;
    documentUri = nextUri;
    followPosition = { line: position.line || 0, character: position.character || 0 };
    refresh();
  }

  // ## The connection

  async function start() {
    if (!endpoint) { view.state = "no-server"; publish(); return null; }
    view.state = "connecting";
    view.message = null;
    view.canReconnect = true;
    publish();
    client = new LspClient({
      url: endpoint.url,
      WebSocketImpl: endpoint.WebSocketImpl,
      requestTimeout: endpoint.requestTimeout,
      languageId: endpoint.languageId,
    });
    if (!follow && documentUri) client.openDocument(documentUri, editor.value);
    client.on("close", (info) => {
      if (info && info.intentional) return;
      if (hover) hover.close();
      view.state = "closed";
      view.info = null;
      view.items = [];
      view.diagnostics = [];
      if (squiggles) squiggles.update([]);
      publish();
    });
    client.on("diagnostics", (params) => {
      if (!params || params.uri !== documentUri) return;
      view.diagnostics = params.diagnostics || [];
      if (squiggles) squiggles.update(view.diagnostics);
      publish();
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
      publish();
      return null;
    }
    if (client.state !== "open") return null;
    view.state = "open";
    view.serverInfo = client.serverInfo;
    view.infoview = client.infoview;
    if (!follow) client.openDocument(documentUri, editor.value);
    publish();
    refresh();
    return api;
  }

  async function reconnect() {
    if (!client) return start();
    if (client.state !== "open" && !follow && documentUri) client.openDocument(documentUri, editor.value);
    view.state = "connecting";
    view.message = null;
    view.goals = null;
    view.goalsKind = null;
    view.term = null;
    view.termKind = null;
    view.items = [];
    publish();
    try {
      await client.reconnect();
    } catch (e) {
      view.state = "failed";
      view.message = e && e.message ? e.message : String(e);
      publish();
      return null;
    }
    view.state = "open";
    view.serverInfo = client.serverInfo;
    view.infoview = client.infoview;
    publish();
    refresh();
    return api;
  }

  // ## The runtime's requests

  function request(kind, payload) {
    if (kind === "reveal") highlight(payload);
    else if (kind === "subterm") describeSubterm(payload);
    else if (kind === "reconnect") reconnect();
  }

  const api = {
    uri: documentUri,
    target: () => documentUri,
    view,
    client: () => client,
    hover: () => hover,
    refresh,
    reconnect,
    // The caret as the page and the tests see it (UTF-16, line 0-based).
    position: () => editor && rules
      ? rules.position(editor.value, caretOffset(editor))
      : { line: 0, character: 0 },
    squiggles: () => squiggles,
    completions: () => completions,
    goTo,
    request,
    stop() {
      if (hover) hover.close();
      if (completions) completions.destroy();
      if (squiggles) squiggles.destroy();
      if (!client) return;
      if (!follow && documentUri) client.closeDocument(documentUri);
      client.close();
    },
  };

  if (!follow && editor) {
    editor.addEventListener("input", onEdit);
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
