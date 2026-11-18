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
    this.diagnostics = new Map(); // uri → the last published array
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
      this.diagnostics.set(params.uri, diagnostics);
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
    if (this.state === "open") this.notify("textDocument/didClose", { textDocument: { uri } });
  }

  documentText(uri) {
    const doc = this.docs.get(uri);
    return doc ? doc.text : null;
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

  plainGoal(uri, position) { return this.request("wiz/plainGoal", this.positionParams(uri, position)); }
  plainTermGoal(uri, position) { return this.request("wiz/plainTermGoal", this.positionParams(uri, position)); }
  interactiveGoals(uri, position) { return this.request("wiz/interactiveGoals", this.positionParams(uri, position)); }
  interactiveTermGoal(uri, position) { return this.request("wiz/interactiveTermGoal", this.positionParams(uri, position)); }
  subtermInfo(uri, session, ref) {
    return this.request("wiz/subtermInfo", { textDocument: { uri }, session, ref });
  }
  interactiveInfo(uri, position) { return this.request("wiz/interactiveInfo", this.positionParams(uri, position)); }

  // The server's advertised infoview tag, if it has one.
  get infoview() { return infoviewTag(this.capabilities); }
}
