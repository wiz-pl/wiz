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
//   * `wiz/plainGoal`/`wiz/plainTermGoal` answered `null` ("nothing at the cursor"), and
//     the interactive methods with `MethodNotFound`, so the panel takes its plain path.
//
// The diagnostics come from `wiz_playground_eval`'s text: one line per command (an
// `import` or a grammar command prints none), errors start with `error:` or
// `parse error N:`. Only a parse error names an offset (N, a code-point offset into the
// checked text); every other line is placed on its command by counting commands in the
// source (`splitCommands`). When the count does not match, the line is reported at the
// top of the document and says so. The next stage replaces this guesswork with an export
// that keeps the frontend's `@OFFSET` tags (`runCommands` without `stripAts`).
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

// The page's rule (web/playground.js): a source without an `import` gets the embedded
// Prelude. `prefix` is what was added, so offsets can be moved back into the editor.
export function withPrelude(text) {
  if (/^\s*import\b/m.test(text)) return { source: text, prefix: "" };
  const prefix = "import Prelude\n\n";
  return { source: prefix + text, prefix };
}

// ## Positions (LSP: 0-based lines, UTF-16 code units)

export function positionOf(text, offset) {
  const end = Math.max(0, Math.min(offset, text.length));
  let line = 0;
  let lineStart = 0;
  for (let i = 0; i < end; i++) {
    if (text.charCodeAt(i) === 10) { line++; lineStart = i + 1; }
  }
  return { line, character: end - lineStart };
}

// A code-point offset (what the self-hosted frontend counts: `String.codes`) as a UTF-16
// offset into the same text.
export function utf16OfCodePoints(text, codePoints) {
  let i = 0;
  for (let n = 0; n < codePoints && i < text.length; n++) {
    const c = text.charCodeAt(i);
    i += c >= 0xd800 && c <= 0xdbff && i + 1 < text.length ? 2 : 1;
  }
  return i;
}

function lineEnd(text, offset) {
  const nl = text.indexOf("\n", offset);
  return nl < 0 ? text.length : nl;
}

// ## Commands

// Commands that print no line (stepCommand in selfhost/Frontend.wiz: imports, the
// grammar-changing commands, and `deriving instance` when it succeeds).
const SILENT = /^(import|syntax|notation|infixl|infixr|infix|prefix|postfix|macro_rules|macro|declare_syntax_cat|deriving\s+instance)\b/;
// Lines at column 0 that continue a command instead of starting one.
const CONTINUES = /^(\||where\b|deriving\b|with\b|\)|\]|\}|,|:=)/;
// What the frontend prints for these is a result worth showing as information.
const RESULT = /^#(check|eval|reduce|print)\b/;

// The top-level commands of `text`: a command starts at column 0 (after any doc comment
// or attribute lines, which belong to it), and runs to the next one. Comments, blank
// lines and the body of a `mutual … end` block do not start a command. Each command is
// `{start, head, end, keyword, silent, result}` in UTF-16 offsets: `start` is the doc
// comment's or attribute's start, `head` the keyword line's.
export function splitCommands(text) {
  const commands = [];
  const lines = text.split("\n");
  let offset = 0;
  let inBlock = 0;          // nesting depth of `/- … -/`
  let inMutual = false;
  let pending = null;       // a doc comment or attribute waiting for its command
  for (const line of lines) {
    const here = offset;
    offset += line.length + 1;
    if (inBlock > 0) {
      inBlock = blockDepth(line, inBlock);
      continue;
    }
    if (line.trim() === "" || /^\s*--/.test(line)) continue;
    if (/^\s/.test(line)) continue;              // indented: part of the previous command
    if (line.startsWith("/-")) {
      const depth = blockDepth(line, 0);
      if (line.startsWith("/--") && pending === null) pending = here;
      inBlock = depth;
      continue;
    }
    if (inMutual) {
      if (/^end\b/.test(line)) inMutual = false;
      continue;
    }
    if (CONTINUES.test(line)) continue;
    if (line.startsWith("@[") && !/\]\s*\S/.test(line)) {
      if (pending === null) pending = here;      // an attribute on a line of its own
      continue;
    }
    const keyword = line.replace(/^@\[[^\]]*\]\s*/, "")
      .replace(/^((private|protected|noncomputable|partial|unsafe)\s+)*/, "");
    const command = {
      start: pending === null ? here : pending,
      head: here,
      end: text.length,
      keyword: (keyword.match(/^\S+/) || [""])[0],
      silent: SILENT.test(keyword),
      result: RESULT.test(keyword),
    };
    pending = null;
    if (commands.length) commands[commands.length - 1].end = command.start;
    commands.push(command);
    if (/^mutual\b/.test(keyword)) inMutual = true;
  }
  return commands;
}

function blockDepth(line, depth) {
  for (let i = 0; i + 1 < line.length; i++) {
    if (line[i] === "/" && line[i + 1] === "-") { depth++; i++; }
    else if (line[i] === "-" && line[i + 1] === "/") { depth = Math.max(0, depth - 1); i++; }
  }
  return depth;
}

// ## The frontend's lines as diagnostics

// `wiz_playground_eval`'s output: pgJoin ends every line with "\n", and a command may
// print an empty line, so only the final empty piece is dropped.
export function outputLines(output) {
  const lines = String(output || "").split("\n");
  if (lines.length && lines[lines.length - 1] === "") lines.pop();
  return lines;
}

// `parse error 57: …` → 57 (a code-point offset), as selfhost/Cli.wiz's `parseOff`.
export function parseErrorOffset(line) {
  const m = /^parse error (\d+):/.exec(line);
  return m ? Number(m[1]) : null;
}

function severityOf(line) {
  if (line.startsWith("error:") || line.startsWith("parse error")) return 1;
  if (line.startsWith("warning:")) return 2;
  return 3;
}

function messageOf(line) {
  if (line.startsWith("error: ")) return line.slice(7);
  if (line.startsWith("warning: ")) return line.slice(9);
  const m = /^parse error (\d+): ?(.*)$/.exec(line);
  if (m) return "parse error: " + m[2];
  return line;
}

function range(text, from, to) {
  return { start: positionOf(text, from), end: positionOf(text, to) };
}

// The diagnostics for `text` (the editor's) given `output`, the engine's answer for
// `withPrelude(text).source`. Errors and warnings always; the result of a `#check`/
// `#eval`/`#reduce`/`#print` as information when its command is known.
export function diagnosticsFromOutput(text, output) {
  const { prefix } = withPrelude(text);
  const lines = outputLines(output);
  const commands = splitCommands(text).filter((c) => !c.silent);
  const last = lines.length ? lines[lines.length - 1] : null;
  const parseAt = last === null ? null : parseErrorOffset(last);
  // Lines before a parse error belong to the commands before it, one each.
  const placed = parseAt === null ? lines.length : lines.length - 1;
  const aligned = parseAt === null ? placed === commands.length : placed <= commands.length;
  const diagnostics = [];
  for (let i = 0; i < placed; i++) {
    const line = lines[i];
    const severity = severityOf(line);
    const command = aligned ? commands[i] : null;
    if (severity === 3 && !(command && command.result)) continue;
    if (severity === 3 && line === "") continue;
    const diagnostic = { severity, source: "wiz-selfhost", message: messageOf(line) };
    if (command) {
      diagnostic.range = range(text, command.head, lineEnd(text, command.head));
    } else {
      diagnostic.range = range(text, 0, 0);
      diagnostic.message += " (position unknown: the output did not line up with the commands)";
    }
    diagnostics.push(diagnostic);
  }
  if (parseAt !== null) {
    const source = prefix + text;
    const at = Math.max(0, utf16OfCodePoints(source, parseAt) - prefix.length);
    let to = at;
    while (to < text.length && !/\s/.test(text[to])) to++;
    diagnostics.push({
      severity: 1, source: "wiz-selfhost", code: "parse-error",
      message: messageOf(last), range: range(text, at, Math.max(to, Math.min(at + 1, text.length))),
    });
  }
  return diagnostics;
}

// ## The server (one per connection; documents are per connection)

// `evaluate(source) → string | Promise<string>` is `wiz_playground_eval` (the page waits
// for its engine inside it).
export class SelfhostServer {
  constructor({ evaluate, serverInfo = SERVER_INFO } = {}) {
    this.evaluate = evaluate;
    this.serverInfo = serverInfo;
    this.docs = new Map();     // uri → {text, version}
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
        return ok({
          capabilities: {
            positionEncoding: "utf-16",
            textDocumentSync: 1,
            hoverProvider: false,
            experimental: { wizInfoview: { version: 1, methods: SELFHOST_METHODS.slice() } },
          },
          serverInfo: this.serverInfo,
        });
      }
      case "shutdown":
        this.shutdown = true;
        return ok(null);
      case "wiz/plainGoal":
      case "wiz/plainTermGoal": {
        const uri = params.textDocument && params.textDocument.uri;
        if (!this.docs.has(uri)) return fail(ERR.invalidParams, "the document is not open: " + uri);
        // Stage 0 has no positions inside a command: nothing at the cursor.
        return ok(null);
      }
      case "textDocument/hover":
        return ok(null);
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
    try {
      const output = await this.evaluate(withPrelude(doc.text).source);
      diagnostics = diagnosticsFromOutput(doc.text, output);
    } catch (e) {
      diagnostics = [{
        severity: 1, source: "wiz-selfhost", range: range(doc.text, 0, 0),
        message: "the self-hosted engine failed: " + (e && e.message ? e.message : String(e)),
      }];
    }
    // A newer text arrived while this one was checked: its own publish follows.
    const now = this.docs.get(uri);
    if (!now || now.version !== version || session !== this.session) return [];
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
