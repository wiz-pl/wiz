// The playground's language client: JSON-RPC 2.0 over a WebSocket, with no
// `Content-Length` framing (`wiz lsp --ws PORT` sends one JSON message per text frame,
// infoview protocol §8.2). The transport is injected, so the same client drives a
// browser WebSocket, a Node WebSocket used by the tests, or a self-hosted server that
// speaks the same protocol.
//
// The client is transport-agnostic in two senses:
//
//   * `WebSocketImpl` defaults to `globalThis.WebSocket`, so a page needs no
//     dependency; tests pass a minimal RFC 6455 client (`web/ws_node_client.mjs`).
//   * `parseEndpoint` accepts the `?lsp=` value (a `ws://` URL, or a bare port for
//     `ws://127.0.0.1:PORT`), and `LspClient` takes `{url, ...}`; nothing else in the
//     page knows the difference between a Wiz server and a future self-hosted one.
//   * (#430) `wiz lsp --ws` refuses a connection without its token: the page's
//     `?token=` (or a `token=` already in the `?lsp=` URL) goes into the socket's URL
//     (`withToken`); `label` is the URL without it, for the panel to show.
//
// Positions are UCS-2/UTF-16 code units, which is what LSP's default
// `positionEncoding` says and what a JavaScript string index counts. The `initialize`
// request therefore sends `general.positionEncodings: ["utf-16"]`; the contract is
// `docs/playground-lsp.md`.
"use strict";

// The JSON-RPC and Wiz protocol error codes the panel reacts to.
export const LSP_ERROR = {
  methodNotFound: -32601,
  invalidParams: -32602,
  contentModified: -32801,
  // (ours) the socket is not there, or the request timed out
  notConnected: -32098,
  closed: -32097,
};

export class LspError extends Error {
  constructor(code, message, data) {
    super(message || "LSP error " + code);
    this.name = "LspError";
    this.code = code;
    if (data !== undefined) this.data = data;
  }
  get isMethodNotFound() { return this.code === LSP_ERROR.methodNotFound; }
  get isStale() { return this.code === LSP_ERROR.contentModified; }
}

// `?lsp=` → `{url}` or null ("no server"). Nothing, "", "off", "none", "0" and "false"
// mean no server; a bare number is a local port; a value without a scheme gets `ws://`.
export function parseEndpoint(value) {
  if (value === null || value === undefined) return null;
  const raw = String(value).trim();
  if (raw === "" || /^(off|none|no|0|false)$/i.test(raw)) return null;
  if (/^\d+$/.test(raw)) return { url: "ws://127.0.0.1:" + raw };
  if (/^wss?:\/\//i.test(raw)) return { url: raw };
  return { url: "ws://" + raw };
}

// (#430) `url` with `?token=` (or `&token=`) added, unless it has one already.
export function withToken(url, token) {
  if (!token) return url;
  let u;
  try { u = new URL(url); } catch (_) { return url; }
  if (!u.searchParams.has("token")) u.searchParams.set("token", token);
  return u.toString();
}

// (#430) A URL without its token, to show (the token is a secret).
export function withoutToken(url) {
  let u;
  try { u = new URL(url); } catch (_) { return url; }
  if (!u.searchParams.has("token")) return url;
  u.searchParams.delete("token");
  return u.toString();
}

// ## Text edits (`WorkspaceEdit`), in UTF-16 offsets

// The UTF-16 offset of an LSP position in `text`. LSP's default position encoding is
// UTF-16 code units, which is what a JavaScript string index counts; a character past
// the line's end clamps to the line end (a client convention, as `ofPos` in the server).
export function textOffset(text, position) {
  const value = typeof text === "string" ? text : "";
  const line = Math.max(0, Math.trunc((position && position.line) || 0));
  const character = Math.max(0, Math.trunc((position && position.character) || 0));
  let offset = 0;
  for (let l = 0; l < line; l++) {
    const newline = value.indexOf("\n", offset);
    if (newline < 0) return value.length;
    offset = newline + 1;
  }
  const newline = value.indexOf("\n", offset);
  return Math.min(newline < 0 ? value.length : newline, offset + character);
}

// The LSP position of a UTF-16 offset (the inverse of `textOffset`).
export function textPosition(text, offset) {
  const value = typeof text === "string" ? text : "";
  const at = Math.max(0, Math.min(value.length, Math.trunc(offset || 0)));
  const before = value.slice(0, at);
  const line = (before.match(/\n/g) || []).length;
  return { line, character: at - (before.lastIndexOf("\n") + 1) };
}

// The text `edits` make of `text`. Each edit's range is converted with `offsetOf`
// (UTF-16 by default), and the edits are applied from the end so earlier ranges stay
// valid. Overlapping edits are refused (LSP forbids them) instead of corrupting text.
export function applyTextEdits(text, edits, offsetOf = textOffset) {
  const value = typeof text === "string" ? text : "";
  const spans = (Array.isArray(edits) ? edits : []).map((edit) => {
    const range = (edit && edit.range) || {};
    const start = offsetOf(value, range.start || {});
    const end = offsetOf(value, range.end || {});
    return {
      start: Math.min(start, end),
      end: Math.max(start, end),
      text: edit && typeof edit.newText === "string" ? edit.newText : "",
    };
  }).sort((a, b) => b.start - a.start);
  let out = value;
  let limit = value.length;
  for (const span of spans) {
    if (span.end > limit) {
      throw new LspError(LSP_ERROR.invalidParams, "overlapping text edits");
    }
    out = out.slice(0, span.start) + span.text + out.slice(span.end);
    limit = span.start;
  }
  return out;
}

// Where `offset` (a UTF-16 index in the text *before* the edits) is after `edits`: an
// offset outside every edited span shifts by that span's length change; one inside keeps
// its distance from the span's start, clamped to the replacement text. Formatting uses
// this to keep the caret in the same place in the text it was in.
export function mapOffset(edits, offset, text, offsetOf = textOffset) {
  const value = typeof text === "string" ? text : "";
  let out = Math.max(0, Math.trunc(offset || 0));
  const spans = (Array.isArray(edits) ? edits : []).map((edit) => {
    const range = (edit && edit.range) || {};
    const start = offsetOf(value, range.start || {});
    const end = offsetOf(value, range.end || {});
    return {
      start: Math.min(start, end),
      end: Math.max(start, end),
      length: edit && typeof edit.newText === "string" ? edit.newText.length : 0,
    };
  }).sort((a, b) => a.start - b.start);
  for (const span of spans) {
    if (out <= span.start) break;
    if (out >= span.end) {
      out += span.length - (span.end - span.start);
      continue;
    }
    out = span.start + Math.min(out - span.start, span.length);
    break;
  }
  return Math.max(0, out);
}

// A `FormattingOptions` object with the playground's defaults.
export function formattingOptions(options) {
  return Object.assign({ tabSize: 2, insertSpaces: true }, options || {});
}

// The endpoint from a location's query string (`location.search`, or any `?…` text);
// its `token` parameter is the server's token. `fallback` is the endpoint when `name`
// is absent (a page's own `--lsp`); `?token=` applies to it too.
export function endpointFromSearch(search, name = "lsp", fallback = null) {
  try {
    const params = new URLSearchParams(search || "");
    const endpoint = params.has(name) ? parseEndpoint(params.get(name)) : parseEndpoint(fallback);
    if (!endpoint) return null;
    const url = withToken(endpoint.url, params.get("token"));
    return { url, label: withoutToken(url) };
  } catch (_) {
    return null;
  }
}

// The tag of a language server that advertised the Wiz infoview methods, if any.
export function infoviewTag(capabilities) {
  const wiz = capabilities && capabilities.experimental && capabilities.experimental.wizInfoview;
  if (!wiz) return null;
  return { version: wiz.version || 0, methods: Array.isArray(wiz.methods) ? wiz.methods.slice() : [] };
}

const OPEN = 1;

export class LspClient {
  // options: {url, WebSocketImpl?, requestTimeout?, connectTimeout?, clientInfo?,
  //           rootUri?, languageId?, log?}
  constructor(options = {}) {
    this.url = options.url;
    this.WebSocketImpl = options.WebSocketImpl || globalThis.WebSocket;
    this.requestTimeout = options.requestTimeout === undefined ? 10000 : options.requestTimeout;
    this.connectTimeout = options.connectTimeout === undefined ? 5000 : options.connectTimeout;
    this.clientInfo = options.clientInfo || { name: "wiz-playground" };
    this.rootUri = options.rootUri === undefined ? null : options.rootUri;
    this.languageId = options.languageId || "wiz";
    this.log = typeof options.log === "function" ? options.log : null;
    this.state = "idle";          // idle | connecting | open | closed | failed
    this.capabilities = null;
    this.capabilitiesRaw = null;
    this.serverInfo = null;
    this.diagnostics = new Map(); // uri → {version, diagnostics} (the last publish)
    this.handlers = Object.create(null);
    this.pending = new Map();     // id → {resolve, reject, timer, method}
    this.docs = new Map();        // uri → {uri, text, version, languageId}
    this.nextId = 1;
    this.socket = null;
    this.connecting = null;
    this.intentionalClose = false;
  }

  // on("state"|"ready"|"close"|"diagnostics"|"notification"|<method>, fn) → unsubscribe
  on(type, fn) {
    (this.handlers[type] || (this.handlers[type] = [])).push(fn);
    return () => this.off(type, fn);
  }

  off(type, fn) {
    const list = this.handlers[type];
    if (!list) return;
    const i = list.indexOf(fn);
    if (i >= 0) list.splice(i, 1);
  }

  emit(type, payload) {
    const list = this.handlers[type];
    if (!list) return;
    for (const fn of list.slice()) {
      // A listener must not break the client (or the page's event loop).
      try { fn(payload); } catch (e) { this.lastHandlerError = e; }
    }
  }

  setState(state, detail) {
    this.state = state;
    this.emit("state", { state, detail });
  }

  get isOpen() { return this.state === "open"; }

  // Connect and complete the LSP handshake. On a reconnect the documents the client
  // already knows are opened again, so the server and the page agree on the text.
  connect() {
    if (this.state === "open") return Promise.resolve(this.capabilitiesRaw);
    if (this.connecting) return this.connecting;
    if (typeof this.WebSocketImpl !== "function") {
      return Promise.reject(new LspError(LSP_ERROR.notConnected, "this environment has no WebSocket"));
    }
    this.intentionalClose = false;
    this.setState("connecting");
    let socket;
    try {
      socket = new this.WebSocketImpl(this.url);
    } catch (e) {
      const err = new LspError(LSP_ERROR.notConnected, "cannot connect to " + this.url + ": " + (e.message || e));
      this.setState("failed", { message: err.message });
      return Promise.reject(err);
    }
    this.socket = socket;
    const opened = new Promise((resolve, reject) => {
      let settled = false;
      const finish = (err) => {
        if (settled) return;
        settled = true;
        clearTimeout(timer);
        if (err) reject(err); else resolve();
      };
      const timer = setTimeout(() => {
        finish(new LspError(LSP_ERROR.notConnected, "timed out connecting to " + this.url));
      }, this.connectTimeout);
      socket.onopen = () => finish();
      socket.onerror = () => finish(new LspError(LSP_ERROR.notConnected, "cannot connect to " + this.url));
      socket.onclose = (ev) => finish(new LspError(LSP_ERROR.notConnected,
        "the server closed the connection before the handshake" + (ev && ev.reason ? ": " + ev.reason : "")));
    });
    this.connecting = opened.then(async () => {
      socket.onmessage = (ev) => this.receive(ev.data);
      socket.onclose = (ev) => this.onClose(socket, ev);
      socket.onerror = () => {};
      const init = await this.sendRequest("initialize", this.initializeParams());
      this.capabilitiesRaw = init || {};
      this.capabilities = this.capabilitiesRaw.capabilities || {};
      this.serverInfo = this.capabilitiesRaw.serverInfo || null;
      this.notify("initialized", {});
      this.setState("open");
      for (const doc of this.docs.values()) this.sendDidOpen(doc);
      this.emit("ready", { capabilities: this.capabilities, serverInfo: this.serverInfo });
      return this.capabilitiesRaw;
    }).catch((err) => {
      this.setState(this.intentionalClose ? "closed" : "failed", { message: err && err.message });
      if (this.socket === socket) this.socket = null;
      try { socket.close(); } catch (_) { /* already gone */ }
      throw err;
    }).finally(() => { this.connecting = null; });
    return this.connecting;
  }

  // Close the socket. Pending requests are rejected (with a `closed` LspError); a client
  // that is already closed stays closed.
  close() {
    this.intentionalClose = true;
    const socket = this.socket;
    this.socket = null;
    if (socket) { try { socket.close(); } catch (_) { /* already gone */ } }
    this.rejectPending(new LspError(LSP_ERROR.closed, "connection closed"));
    if (this.state !== "closed") this.setState("closed", { intentional: true });
    this.emit("close", { code: 1000, reason: "client closed", intentional: true });
  }

  // Close and connect again; the open documents are sent again after the handshake.
  async reconnect() {
    this.close();
    this.intentionalClose = false;
    return this.connect();
  }

  initializeParams() {
    return {
      processId: null,
      clientInfo: this.clientInfo,
      rootUri: this.rootUri,
      workspaceFolders: null,
      capabilities: {
        general: { positionEncodings: ["utf-16"] },
        workspace: { workspaceFolders: false, configuration: false },
        window: { workDoneProgress: false },
        textDocument: {
          synchronization: { dynamicRegistration: false, willSave: false, didSave: false },
          publishDiagnostics: { relatedInformation: false, versionSupport: true },
          hover: { contentFormat: ["markdown", "plaintext"] },
          formatting: { dynamicRegistration: false },
          rangeFormatting: { dynamicRegistration: false },
          // Snippets are not expanded by the playground's popup, so say so; a server may
          // still send them and acceptCompletion strips the placeholders.
          completion: {
            dynamicRegistration: false,
            contextSupport: true,
            completionItem: {
              snippetSupport: false,
              documentationFormat: ["plaintext", "markdown"],
              insertReplaceSupport: false,
            },
          },
        },
        // Ask for `wiz/elaborated` (the server only sends it to clients that do).
        experimental: { wizElaborated: true, wizInfoview: true },
      },
    };
  }

  // A request once the handshake is done. Rejects (never throws) when the client is not
  // connected; callers can always `.catch` or `Promise.allSettled`.
  request(method, params, options = {}) {
    if (this.state !== "open") {
      const code = this.state === "closed" ? LSP_ERROR.closed : LSP_ERROR.notConnected;
      return Promise.reject(new LspError(code, `not connected (${this.state})`));
    }
    return this.sendRequest(method, params, options.timeout);
  }

  sendRequest(method, params, timeout = this.requestTimeout) {
    return new Promise((resolve, reject) => {
      const socket = this.socket;
      if (!socket || (typeof socket.readyState === "number" && socket.readyState !== OPEN)) {
        reject(new LspError(LSP_ERROR.notConnected, "the WebSocket is not open"));
        return;
      }
      const id = this.nextId++;
      const timer = timeout > 0 ? setTimeout(() => {
        if (!this.pending.delete(id)) return;
        reject(new LspError(LSP_ERROR.notConnected, `request ${method} timed out`));
      }, timeout) : null;
      this.pending.set(id, { resolve, reject, timer, method });
      try {
        socket.send(JSON.stringify({ jsonrpc: "2.0", id, method, params }));
      } catch (e) {
        this.pending.delete(id);
        if (timer) clearTimeout(timer);
        reject(new LspError(LSP_ERROR.notConnected, `sending ${method} failed: ${e.message || e}`));
      }
    });
  }

  notify(method, params) {
    const socket = this.socket;
    if (!socket || (typeof socket.readyState === "number" && socket.readyState !== OPEN)) return false;
    try {
      socket.send(JSON.stringify({ jsonrpc: "2.0", method, params }));
      return true;
    } catch (e) {
      if (this.log) this.log("notify " + method + " failed: " + (e.message || e));
      return false;
    }
  }

  receive(data) {
    if (typeof data !== "string") return;   // the protocol uses text frames only
    let message;
    try {
      message = JSON.parse(data);
    } catch (e) {
      this.emit("protocolError", { message: "not JSON: " + (e.message || e), data });
      return;
    }
    if (Array.isArray(message)) { for (const m of message) this.dispatch(m); return; }
    this.dispatch(message);
  }

  dispatch(message) {
    if (!message || typeof message !== "object") return;
    const isResponse = message.id !== undefined && message.id !== null &&
      message.method === undefined && ("result" in message || "error" in message);
    if (isResponse) {
      const pending = this.pending.get(message.id);
      if (!pending) return;   // a reply to a request the page already forgot
      this.pending.delete(message.id);
      if (pending.timer) clearTimeout(pending.timer);
      if (message.error) {
        pending.reject(new LspError(message.error.code, message.error.message, message.error.data));
      } else {
        pending.resolve(message.result);
      }
      return;
    }
    if (typeof message.method !== "string") return;
    if (message.id !== undefined && message.id !== null) {
      // A server → client request. The playground serves none: say so instead of hanging.
      this.reply(message.id, null, {
        code: LSP_ERROR.methodNotFound,
        message: "the playground client has no handler for " + message.method,
      });
      return;
    }
    this.dispatchNotification(message.method, message.params);
  }

  reply(id, result, error) {
    const socket = this.socket;
    if (!socket || (typeof socket.readyState === "number" && socket.readyState !== OPEN)) return;
    const out = error ? { jsonrpc: "2.0", id, error } : { jsonrpc: "2.0", id, result };
    try { socket.send(JSON.stringify(out)); } catch (_) { /* the close handler reports it */ }
  }

  dispatchNotification(method, params) {
    if (method === "textDocument/publishDiagnostics" && params && params.uri) {
      const diagnostics = Array.isArray(params.diagnostics) ? params.diagnostics : [];
      // The client advertises `versionSupport`: a publish for an older document version
      // than the one already stored is dropped (a second connection, or a server that
      // fans work out, can deliver them out of order). A server that sends no version
      // keeps last-arrival, and the last version seen is remembered across such
      // publishes so a later numbered one is still ordered.
      const version = typeof params.version === "number" && isFinite(params.version)
        ? params.version : null;
      const previous = this.diagnostics.get(params.uri);
      if (version !== null && previous && typeof previous.version === "number" && version < previous.version) {
        return;
      }
      const kept = version !== null ? version : (previous ? previous.version : null);
      this.diagnostics.set(params.uri, { version: kept, diagnostics });
      this.emit("diagnostics", { uri: params.uri, diagnostics, version: params.version });
    }
    this.emit("notification", { method, params });
    this.emit(method, params);
  }

  onClose(socket, ev) {
    if (socket !== this.socket) return;   // a close from a socket the client already replaced
    this.socket = null;
    this.rejectPending(new LspError(LSP_ERROR.closed, "the server closed the connection"));
    this.setState("closed", { code: ev && ev.code, reason: (ev && ev.reason) || "" });
    this.emit("close", {
      code: ev && typeof ev.code === "number" ? ev.code : 1006,
      reason: (ev && ev.reason) || "",
      intentional: this.intentionalClose,
    });
  }

  rejectPending(error) {
    for (const [id, pending] of this.pending) {
      if (pending.timer) clearTimeout(pending.timer);
      pending.reject(error);
      this.pending.delete(id);
    }
  }

  // ## Documents (full-text sync: textDocumentSync = 1)

  sendDidOpen(doc) {
    this.notify("textDocument/didOpen", {
      textDocument: { uri: doc.uri, languageId: doc.languageId, version: doc.version, text: doc.text },
    });
  }

  openDocument(uri, text, options = {}) {
    const doc = {
      uri,
      text,
      version: options.version === undefined ? 1 : options.version,
      languageId: options.languageId || this.languageId,
    };
    this.docs.set(uri, doc);
    // `didOpen` starts a new document lifecycle: a publish from the previous one must
    // not make the new lifecycle's (lower) versions look stale.
    this.diagnostics.delete(uri);
    if (this.state === "open") this.sendDidOpen(doc);
    return doc;
  }

  changeDocument(uri, text) {
    const doc = this.docs.get(uri);
    if (!doc) return this.openDocument(uri, text);
    doc.text = text;
    doc.version += 1;
    if (this.state === "open") {
      this.notify("textDocument/didChange", {
        textDocument: { uri, version: doc.version },
        contentChanges: [{ text }],
      });
    }
    return doc;
  }

  closeDocument(uri) {
    if (!this.docs.delete(uri)) return;
    this.diagnostics.delete(uri);
    if (this.state === "open") this.notify("textDocument/didClose", { textDocument: { uri } });
  }

  documentText(uri) {
    const doc = this.docs.get(uri);
    return doc ? doc.text : null;
  }

  // ## Workspace edits

  // Apply a `WorkspaceEdit` to the open documents: `changes` (per URI) and
  // `documentChanges` (text edits with an optional version). The one applier serves
  // formatting now and code actions/rename later. It returns per-document
  // `{uri, text, previousText, version}` and sends no `didChange`: the caller writes the
  // text (the page's textarea) and its normal input path sends it, so there is one
  // synchronisation path. A stale edit is refused with `ContentModified`; file
  // operations (create/rename/delete) are refused, since this client edits open
  // documents only.
  applyWorkspaceEdit(edit, options = {}) {
    const offsetOf = typeof options.offsetOf === "function" ? options.offsetOf : textOffset;
    const expected = options.expectedVersion;
    const groups = [];
    if (edit && edit.changes && typeof edit.changes === "object") {
      for (const uri of Object.keys(edit.changes)) {
        groups.push({ uri, edits: Array.isArray(edit.changes[uri]) ? edit.changes[uri] : [], version: expected });
      }
    }
    if (edit && Array.isArray(edit.documentChanges)) {
      for (const change of edit.documentChanges) {
        if (!change || typeof change !== "object") continue;
        if (change.textDocument && Array.isArray(change.edits)) {
          groups.push({
            uri: change.textDocument.uri,
            edits: change.edits,
            version: typeof change.textDocument.version === "number"
              ? change.textDocument.version : expected,
          });
        } else if (change.kind) {
          throw new LspError(LSP_ERROR.invalidParams,
            "the playground client edits open documents, not files (" + change.kind + ")");
        }
      }
    }
    if (!groups.length) {
      throw new LspError(LSP_ERROR.invalidParams, "the edit changes no document");
    }
    return groups.map((group) => {
      const doc = this.docs.get(group.uri);
      if (!doc) throw new LspError(LSP_ERROR.invalidParams, "no open document " + group.uri);
      if (typeof group.version === "number" && doc.version !== group.version) {
        throw new LspError(LSP_ERROR.contentModified,
          "the document changed before the edit was applied");
      }
      return {
        uri: group.uri,
        text: applyTextEdits(doc.text, group.edits, offsetOf),
        previousText: doc.text,
        version: doc.version,
      };
    });
  }

  // ## The Wiz infoview requests (docs/playground-lsp.md)

  positionParams(uri, position) {
    return { textDocument: { uri }, position: { line: position.line, character: position.character } };
  }

  // The editor's requests: the type at the caret and where the identifier is declared
  // (both already advertised in `initializeParams`'s capabilities). A server without
  // them answers `MethodNotFound`; `web/hover.js` treats that as "nothing to show".
  hover(uri, position) { return this.request("textDocument/hover", this.positionParams(uri, position)); }
  definition(uri, position) { return this.request("textDocument/definition", this.positionParams(uri, position)); }

  // `wiz fmt` through the server: a `TextEdit[]` (or null for "no change"), applied by
  // `applyWorkspaceEdit`. The server advertises `documentFormattingProvider` and
  // `documentRangeFormattingProvider`; a server that does not answers `MethodNotFound`.
  formatting(uri, options) {
    return this.request("textDocument/formatting", {
      textDocument: { uri }, options: formattingOptions(options),
    });
  }
  rangeFormatting(uri, range, options) {
    return this.request("textDocument/rangeFormatting", {
      textDocument: { uri }, range, options: formattingOptions(options),
    });
  }

  plainGoal(uri, position) { return this.request("wiz/plainGoal", this.positionParams(uri, position)); }
  plainTermGoal(uri, position) { return this.request("wiz/plainTermGoal", this.positionParams(uri, position)); }
  interactiveGoals(uri, position) { return this.request("wiz/interactiveGoals", this.positionParams(uri, position)); }
  interactiveTermGoal(uri, position) { return this.request("wiz/interactiveTermGoal", this.positionParams(uri, position)); }
  subtermInfo(uri, session, ref) {
    return this.request("wiz/subtermInfo", { textDocument: { uri }, session, ref });
  }
  interactiveInfo(uri, position) { return this.request("wiz/interactiveInfo", this.positionParams(uri, position)); }

  // `textDocument/completion` at the caret. `context` is LSP's
  // `{triggerKind, triggerCharacter}`: 1 = invoked (Ctrl-Space), 2 = a character typed.
  // The result is an array or a `CompletionList`; the popup accepts either (and a
  // `MethodNotFound` simply closes it).
  completion(uri, position, context) {
    const params = {
      textDocument: { uri },
      position: { line: position.line, character: position.character },
    };
    if (context) params.context = context;
    return this.request("textDocument/completion", params);
  }

  // The server's advertised infoview tag, if it has one.
  get infoview() { return infoviewTag(this.capabilities); }
}
