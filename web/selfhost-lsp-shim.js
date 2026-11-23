// An in-page language server for the playground (`?lsp=selfhost`): a WebSocket stand-in
// that answers the JSON-RPC of `docs/playground-lsp.md` by calling the self-hosted
// frontend the page already loaded (`wiz_playground_eval`, web/playground-exports.wiz).
// There is no socket, no thread and no Lean server: `LspClient` is given
// `WebSocketImpl: SelfhostSocket` and cannot tell the difference.
//
// This is stage 0 of wiz-notes' playground-selfhost-lsp plan. It implements:
//
//   * the handshake (`initialize`/`initialized`, `shutdown`/`exit`);
//   * full-text `didOpen`/`didChange`/`didClose`, each answered with
//     `textDocument/publishDiagnostics` (and `wiz/elaborated` when the client asked);
//   * `wiz/plainGoal`/`wiz/plainTermGoal` answered from the check's position index (the
//     expected type and, before a tactic step, the goal state at the caret), and the
//     interactive methods with `MethodNotFound`, so the panel takes its plain path;
//   * `textDocument/completion`, `textDocument/hover` and `textDocument/definition`
//     answered from the check's declaration index (below).
//
// The diagnostics come from `wiz_playground_eval`'s text: one line per command (an
// `import` or a grammar command prints none), errors start with `error:` or
// `parse error N:`. Only a parse error names an offset (N, a code-point offset into the
// checked text); every other line is placed on its command by counting commands in the
// source (`splitCommands`). When the count does not match, the line is reported at the
// top of the document and says so. The next stage replaces this guesswork with an export
// that keeps the frontend's `@OFFSET` tags (`runCommands` without `stripAts`).
//
// Stage 1: when the module has `wiz_playground_check` (the same check as JSON, each line
// with its command's code-point offset), `check` is used and the counting is not needed;
// a module without it falls back to the text above. The answer may also carry an
// `index` (positions → expected types and goal states); `Web.EditorModel`'s index
// answers `wiz/plainTermGoal`/`wiz/plainGoal` from it with no further engine call.
//
// Completions, hover and definition: the check's `index` carries one `decl` entry per
// declaration the module added (`{"s","e","name","detail","ckind"}`: the source name, its
// printed type, and an LSP CompletionItemKind). `initialize` advertises the three
// providers; `textDocument/completion` filters the declarations by the identifier before
// the caret and gives each item a `textEdit` over that prefix; `textDocument/hover`
// answers Markdown with the declaration's signature; `textDocument/definition` answers a
// `Location` in this document. A caret on a name without a declaration (a Prelude global,
// a local binder) is `null`, never an error, since the index covers this module only.
//
// `SelfhostServer.handle(text) → [message]` has the shape of the planned wasm export
// `wiz_lsp_handle : String → String` (one JSON-RPC message in, a JSON array out), so a
// later stage swaps its body for that call and keeps the socket.
"use strict";

export const SELFHOST_URL = "selfhost://playground";
export const SELFHOST_LABEL = "the in-page self-hosted checker";
export const SERVER_INFO = { name: "wiz-selfhost", version: "prototype" };
// The methods this server answers (the panel labels the server with the version).
export const SELFHOST_METHODS = ["wiz/plainGoal", "wiz/plainTermGoal"];

const ERR = { methodNotFound: -32601, invalidParams: -32602, internal: -32603 };

// `?lsp=selfhost` (any case) selects this server.
export function isSelfhostSearch(search) {
  try {
    const value = new URLSearchParams(search || "").get("lsp");
    return value !== null && /^\s*selfhost\s*$/i.test(value);
  } catch (_) {
    return false;
  }
}

// The page's default: the in-page server when the URL names no endpoint at all (so the
// published page has a Goals pane with nothing to start); `?lsp=selfhost` names it
// explicitly. `?lsp=off`/`none`/`0`/`false` disables the pane, and a `ws://` URL or a
// port keeps the external-server client.
export function wantsSelfhost(search) {
  try {
    const value = new URLSearchParams(search || "").get("lsp");
    if (value === null) return true;
    return /^\s*selfhost\s*$/i.test(value);
  } catch (_) {
    return true;
  }
}

// ## The runtime's pure rules

// `Web.Selfhost.wiz` owns the engine's lines as diagnostics, the command splitter and
// the completion/hover/definition answers; `lib/Web/EditorModel.wiz` owns positions and
// the check's position/declaration index. The shim receives both as `index`, the same
// adapter the page's overlays use (`createIndexer` in web/playground-lsp.js):
//
//   position/offset/lineEnd/range/utf16/editorOffset   -- Web.EditorModel's positions
//   build/size/term/goal/declarations/declarationNamed -- the check's index
//   withPrelude/splitCommands/outputLines/parseErrorOffset
//   diagnosticsFromOutput/parseCheck/diagnosticsFromCheck
//   completionPrefix/wordAt/filterCompletions/completion/hover/definition
//
// `web/framework/index-oracle.mjs` is the Node test oracle for them (test-only); the
// page passes an adapter backed by `mount.ask`.

function requireIndex(index) {
  const methods = [
    "position", "range", "offset", "utf16", "editorOffset", "lineEnd",
    "build", "size", "term", "goal", "declarations", "declarationNamed",
    "initializeCapabilities", "withPrelude", "splitCommands", "outputLines", "parseErrorOffset",
    "diagnosticsFromOutput", "parseCheck", "diagnosticsFromCheck",
    "completionPrefix", "wordAt", "filterCompletions", "completion", "hover", "definition",
  ];
  if (!index || methods.some((name) => typeof index[name] !== "function")) {
    throw new TypeError("selfhost-lsp-shim: pass { index } (Web.Selfhost's rules and Web.EditorModel's position index)");
  }
  return index;
}

// ## The server (one per connection; documents are per connection)

// `evaluate(source) → string | Promise<string>` is `wiz_playground_eval` (the page waits
// for its engine inside it); `check(source) → string | null | Promise<…>` is
// `wiz_playground_check`, or null when the module has none (then `evaluate` is used).
export class SelfhostServer {
  constructor({ evaluate, check = null, index = null, serverInfo = SERVER_INFO } = {}) {
    this.evaluate = evaluate;
    this.check = check;
    this.index = requireIndex(index);
    this.serverInfo = serverInfo;
    this.docs = new Map();     // uri → {text, version, index?}
    this.session = 0;
    this.wantsElaborated = false;
    this.shutdown = false;
  }

  // One JSON-RPC message (text) in, the messages to send back out (objects), in order.
  // The shape of the planned `wiz_lsp_handle : String → String`.
  async handle(text) {
    let message;
    try {
      message = JSON.parse(text);
    } catch (e) {
      return [{ jsonrpc: "2.0", id: null, error: { code: -32700, message: "parse error: " + (e.message || e) } }];
    }
    if (Array.isArray(message)) {
      const out = [];
      for (const m of message) out.push(...await this.dispatch(m));
      return out;
    }
    return this.dispatch(message);
  }

  async dispatch(message) {
    if (!message || typeof message.method !== "string") return [];   // a response: none are expected
    const isRequest = message.id !== undefined && message.id !== null;
    const params = message.params || {};
    try {
      const out = isRequest
        ? await this.request(message.id, message.method, params)
        : await this.notification(message.method, params);
      return out;
    } catch (e) {
      return isRequest
        ? [{ jsonrpc: "2.0", id: message.id, error: { code: ERR.internal, message: String(e && e.message ? e.message : e) } }]
        : [];
    }
  }

  async request(id, method, params) {
    const ok = (result) => [{ jsonrpc: "2.0", id, result }];
    const fail = (code, message) => [{ jsonrpc: "2.0", id, error: { code, message } }];
    switch (method) {
      case "initialize": {
        const caps = params.capabilities || {};
        this.wantsElaborated = !!(caps.experimental && caps.experimental.wizElaborated);
        return ok({ capabilities: this.index.initializeCapabilities(), serverInfo: this.serverInfo });
      }
      case "shutdown":
        this.shutdown = true;
        return ok(null);
      case "wiz/plainGoal":
      case "wiz/plainTermGoal": {
        const uri = params.textDocument && params.textDocument.uri;
        const doc = this.docs.get(uri);
        if (!doc) return fail(ERR.invalidParams, "the document is not open: " + uri);
        // Answered from the last check's index; without one (stage 0, or a module whose
        // check has no index yet) there is nothing at the cursor.
        if (!doc.index || !this.index || !this.index.size(doc.index) || !params.position) return ok(null);
        const offset = this.index.offset(doc.text, params.position);
        return ok(method === "wiz/plainGoal"
          ? this.index.goal(doc.text, doc.index, offset)
          : this.index.term(doc.text, doc.index, offset));
      }
      case "textDocument/completion": {
        const uri = params.textDocument && params.textDocument.uri;
        const doc = this.docs.get(uri);
        if (!doc) return fail(ERR.invalidParams, "the document is not open: " + uri);
        if (!params.position) return ok({ isIncomplete: false, items: [] });
        if (!doc.index || !this.index) return ok({ isIncomplete: false, items: [] });
        return ok(this.index.completion(doc.text, doc.index, params.position));
      }
      case "textDocument/hover": {
        const uri = params.textDocument && params.textDocument.uri;
        const doc = this.docs.get(uri);
        if (!doc) return fail(ERR.invalidParams, "the document is not open: " + uri);
        if (!doc.index || !this.index || !this.index.size(doc.index) || !params.position) return ok(null);
        return ok(this.index.hover(doc.text, doc.index, params.position));
      }
      case "textDocument/definition": {
        const uri = params.textDocument && params.textDocument.uri;
        const doc = this.docs.get(uri);
        if (!doc) return fail(ERR.invalidParams, "the document is not open: " + uri);
        if (!doc.index || !this.index || !this.index.size(doc.index) || !params.position) return ok(null);
        return ok(this.index.definition(doc.text, doc.index, params.position, uri));
      }
      default:
        return fail(ERR.methodNotFound, "the self-hosted playground server has no " + method);
    }
  }

  async notification(method, params) {
    switch (method) {
      case "textDocument/didOpen": {
        const doc = params.textDocument || {};
        if (!doc.uri) return [];
        this.docs.set(doc.uri, { text: String(doc.text || ""), version: doc.version || 1 });
        return this.publish(doc.uri);
      }
      case "textDocument/didChange": {
        const id = params.textDocument || {};
        const changes = params.contentChanges || [];
        if (!id.uri || !changes.length) return [];
        // Full sync: the last change is the whole text.
        this.docs.set(id.uri, { text: String(changes[changes.length - 1].text || ""), version: id.version || 0 });
        return this.publish(id.uri);
      }
      case "textDocument/didClose": {
        const id = params.textDocument || {};
        this.docs.delete(id.uri);
        return [];
      }
      default:
        return [];   // initialized, exit, $/… : nothing to say
    }
  }

  async publish(uri) {
    const doc = this.docs.get(uri);
    if (!doc) return [];
    const session = ++this.session;
    const version = doc.version;
    let diagnostics;
    let index = null;
    try {
      const { source, prefix } = this.index.withPrelude(doc.text);
      const answer = this.check ? this.index.parseCheck(await this.check(source)) : null;
      if (answer) {
        diagnostics = this.index.diagnosticsFromCheck(doc.text, answer);
        index = answer.index && Array.isArray(answer.index)
          ? this.index.build(doc.text, answer.index, prefix) : null;
      } else {
        diagnostics = this.index.diagnosticsFromOutput(doc.text, await this.evaluate(source));
      }
    } catch (e) {
      diagnostics = [{
        severity: 1, source: "wiz-selfhost", range: this.index.range(doc.text, 0, 0),
        message: "the self-hosted engine failed: " + (e && e.message ? e.message : String(e)),
      }];
    }
    // A newer text arrived while this one was checked: its own publish follows.
    const now = this.docs.get(uri);
    if (!now || now.version !== version || session !== this.session) return [];
    now.index = index;
    const out = [{ jsonrpc: "2.0", method: "textDocument/publishDiagnostics", params: { uri, version, diagnostics } }];
    if (this.wantsElaborated) out.push({ jsonrpc: "2.0", method: "wiz/elaborated", params: { uri, version, session } });
    return out;
  }
}

// ## The WebSocket stand-in

// A class with the WebSocket surface `LspClient` uses (`readyState`, `send`, `close`,
// `onopen`/`onmessage`/`onclose`/`onerror`), backed by a `SelfhostServer`. Messages are
// handled in order, one at a time; every callback runs on a later turn, as a socket's do.
export function selfhostSocketClass(options = {}) {
  return class SelfhostSocket {
    constructor(url) {
      this.url = url;
      this.readyState = 0;
      this.onopen = null;
      this.onmessage = null;
      this.onclose = null;
      this.onerror = null;
      this.server = new SelfhostServer(options);
      this.queue = Promise.resolve();
      setTimeout(() => {
        if (this.readyState !== 0) return;
        this.readyState = 1;
        if (this.onopen) this.onopen({ type: "open" });
      }, 0);
    }

    send(data) {
      if (this.readyState !== 1) throw new Error("the self-hosted server is not open");
      const text = String(data);
      this.queue = this.queue.then(() => this.server.handle(text)).then((out) => {
        for (const message of out) {
          if (this.readyState !== 1) return;
          if (this.onmessage) this.onmessage({ data: JSON.stringify(message) });
        }
      }).catch(() => { /* handle() answers its own errors; nothing reaches the page */ });
    }

    close(code = 1000, reason = "") {
      if (this.readyState >= 2) return;
      this.readyState = 3;
      setTimeout(() => { if (this.onclose) this.onclose({ code, reason, wasClean: true }); }, 0);
    }
  };
}

// The endpoint `startInfoview({config})` takes for `?lsp=selfhost`.
export function selfhostEndpoint(options = {}) {
  return { url: SELFHOST_URL, label: SELFHOST_LABEL, WebSocketImpl: selfhostSocketClass(options) };
}
