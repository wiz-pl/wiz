// LSP conformance corpus: drive a real Wiz language server over stdio and compare its
// answers with `Tests/data/lsp-conformance/*.json`.
//
//   usage: node web/lsp_conformance_test.mjs [--only NAME[,NAME...]] [--server host|selfhost]
//                                            [--list] [--verbose]
//
// Servers (one process per case per server, so no state leaks between cases):
//   host     `$WIZ_HOST_BIN lsp`           (the Lean-hosted server, `Wiz/LSP.lean`)
//   selfhost `$WIZ_SELFHOST_COMPILER lsp`  (the self-hosted server, `selfhost/Cli.wiz`)
// A server whose variable is unset is SKIPPED with a printed reason, never passed
// silently; a run with no server available at all exits 3. `cwd` is the repository root,
// so both servers find `lib/Prelude.wiz`.
//
// Session: `initialize` (advertising `general.positionEncodings: ["utf-16"]`, with the
// repository's `lib/` as the workspace folder so the self-hosted server can resolve
// `import Prelude`), `initialized`, `didOpen`, wait for that document's
// `publishDiagnostics` (60 s on the first case, 30 s after), the case's requests (30 s
// each), `shutdown`, any `afterShutdown` requests, `exit`, then exit code 0 within 5 s.
//
// Framing: the reader keeps a byte `Buffer`, parses the `Content-Length` (UTF-8 bytes)
// up to `\r\n\r\n` and decodes exactly that many bytes; writes count
// `Buffer.byteLength`. Notifications are queued by method, responses matched by id.
//
// A case file (see the corpus note `wiz-notes/lsp-conformance-corpus-2026-11-23.md`):
//
//   { "name": "goal-inner-by", "servers": ["host", "selfhost"],
//     "uri": "file:///conf/goal-inner-by.wiz", "text": "import Prelude\n…",
//     "requests": [ { "method": "wiz/plainGoal",
//                     "params": { "position": { "line": 2, "character": 9 } } } ],
//     "expected": [ { "match": "exact", "path": "result.goals", "value": ["⊢ Nat → Nat"] } ],
//     "knownGap": [ { "server": "selfhost", "reason": "outermost by (task 4)", "issue": "task 4" } ] }
//
// * `expected[i]` belongs to `requests[i]`; `afterShutdown[i]` expectations follow the
//   request ones. `textDocument: {uri}` is filled into each request's params.
// * `path` resolves against the whole response message (`result.goals`, `error.code`,
//   `result.items.0`); `.N` indexes an array. `match: "error"` defaults to `error.code`.
// * `match` modes: `exact` (deep equality), `subset` (objects: every expected key;
//   arrays: every expected element is present), `absent` (missing or null),
//   `error` (the error code equals the value), `applyEquals` (apply the returned
//   `TextEdit[]` to `text` and compare the result with the value).
// * `diagnostics` (optional, top level): the same match objects, resolved against the
//   `params` of the `didOpen`'s `publishDiagnostics`.
// * `knownGap`: for that server a failing case is XFAIL; a passing one is XPASS, which
//   fails the run so the stale gap gets removed.
//
// Normalisation before comparing: the case's uri is replaced with `$URI`, and arrays
// named `items`, `diagnostics`, `references` and `symbols` are sorted (their order is
// not part of the protocol).
//
// The meta-test (`meta advertised==answered`) runs on each selected server: every
// `*Provider` key in the `initialize` result and every
// `capabilities.experimental.wizInfoview.methods` entry must be answered without an
// error, and every probe of the unadvertised list must be answered with `-32601`.
// `positionEncoding`, when present, must be `"utf-16"`. The host's `wiz/frobnicate`
// is a known gap (H1: an unknown request gets `result: null`, not `-32601`).
//
// Cost: light against already-built binaries. The host elaborates Prelude per case;
// split with `--only` if one run is too long.
import { spawn } from "node:child_process";
import { readFileSync, readdirSync } from "node:fs";
import { dirname, join, resolve } from "node:path";
import { fileURLToPath } from "node:url";

const ROOT = resolve(dirname(fileURLToPath(import.meta.url)), "..");
const CASES_DIR = join(ROOT, "Tests/data/lsp-conformance");
const LIB_URI = "file://" + join(ROOT, "lib");

// --- servers ------------------------------------------------------------------------

const SERVERS = {
  host: { env: "WIZ_HOST_BIN", args: ["lsp"] },
  selfhost: { env: "WIZ_SELFHOST_COMPILER", args: ["lsp"] },
};

// --- JSON helpers -------------------------------------------------------------------

function deepEqual(a, b) {
  return stable(a) === stable(b);
}

function stable(value) {
  if (value === null || typeof value !== "object") return JSON.stringify(value);
  if (Array.isArray(value)) return "[" + value.map(stable).join(",") + "]";
  const keys = Object.keys(value).sort();
  return "{" + keys.map((k) => JSON.stringify(k) + ":" + stable(value[k])).join(",") + "}";
}

/** Replace the case's uri with `$URI` and sort the arrays whose order is not protocol. */
function normalize(value, key, uri, sortables) {
  if (typeof value === "string") return uri ? value.split(uri).join("$URI") : value;
  if (value === null || typeof value !== "object") return value;
  if (Array.isArray(value)) {
    const out = value.map((v) => normalize(v, key, uri, sortables));
    for (const s of sortables) if (key === s) out.sort((a, b) => (stable(a) < stable(b) ? -1 : stable(a) > stable(b) ? 1 : 0));
    return out;
  }
  const out = {};
  for (const k of Object.keys(value)) out[k] = normalize(value[k], k, uri, sortables);
  return out;
}

/** The value at a dotted path; `.N` indexes an array. `undefined` when missing. */
function atPath(value, path) {
  if (!path) return value;
  let cur = value;
  for (const part of path.split(".")) {
    if (cur === null || typeof cur !== "object") return undefined;
    cur = Array.isArray(cur) ? cur[Number(part)] : cur[part];
  }
  return cur;
}

/** `subset`: objects match key by key; arrays need every expected element somewhere. */
function subsetMatch(exp, act) {
  if (exp === null || typeof exp !== "object") return deepEqual(exp, act);
  if (Array.isArray(exp)) {
    return Array.isArray(act) && exp.every((e) => act.some((a) => subsetMatch(e, a)));
  }
  if (act === null || typeof act !== "object" || Array.isArray(act)) return false;
  return Object.entries(exp).every(([k, v]) => subsetMatch(v, act[k]));
}

const show = (v) => (v === undefined ? "<missing>" : JSON.stringify(v));

// --- positions and text edits -------------------------------------------------------

/** The UTF-16 offset of an LSP position (0-based line and UTF-16 character). */
function offsetOf(text, line, character) {
  let off = 0;
  for (let l = 0; l < line; l++) {
    const nl = text.indexOf("\n", off);
    if (nl < 0) return text.length;
    off = nl + 1;
  }
  const end = text.indexOf("\n", off);
  const lineEnd = end < 0 ? text.length : end;
  // walk UTF-16 code units, never past the line
  let units = 0;
  let i = off;
  while (i < lineEnd && units < character) {
    const c = text.charCodeAt(i);
    const width = c >= 0xd800 && c <= 0xdbff ? 2 : 1;
    i += width;
    units += width;
  }
  return units < character ? lineEnd : i;
}

/** Apply `TextEdit[]` to `text` (against the original text, as LSP specifies). */
function applyEdits(text, edits) {
  const spans = edits.map((e) => ({
    start: offsetOf(text, e.range.start.line, e.range.start.character),
    end: offsetOf(text, e.range.end.line, e.range.end.character),
    newText: e.newText,
  }));
  spans.sort((a, b) => b.start - a.start);
  let out = text;
  for (const s of spans) out = out.slice(0, s.start) + s.newText + out.slice(s.end);
  return out;
}

// --- the server process -------------------------------------------------------------

class Conn {
  constructor(name, bin, uri) {
    this.name = name;
    this.uri = uri;
    this.buf = Buffer.alloc(0);
    this.nextId = 1;
    this.pending = new Map(); // id -> { resolve, reject, timer }
    this.notes = new Map(); // method -> [{ params }]
    this.waiters = []; // { method, uri, resolve, timer }
    this.stderr = "";
    this.code = null;
    this.child = spawn(bin, SERVERS[name].args, { cwd: ROOT, stdio: ["pipe", "pipe", "pipe"] });
    this.child.stdout.on("data", (b) => this.feed(b));
    this.child.stderr.on("data", (b) => {
      this.stderr += b.toString("utf8");
      if (this.stderr.length > 20000) this.stderr = this.stderr.slice(-20000);
    });
    this.exited = new Promise((res) => {
      this.child.on("exit", (code, signal) => {
        this.code = code;
        this.signal = signal;
        for (const [, p] of this.pending) {
          clearTimeout(p.timer);
          p.reject(new Error(`server exited (${code ?? signal}) before the response`));
        }
        this.pending.clear();
        for (const w of this.waiters) {
          clearTimeout(w.timer);
          w.reject(new Error(`server exited (${code ?? signal}) before ${w.method}`));
        }
        this.waiters = [];
        res();
      });
    });
    this.child.on("error", (e) => {
      this.stderr += String(e);
    });
    // a write to a server that has already died is an EPIPE, not a crash of the driver
    this.child.stdin.on("error", () => {});
  }

  feed(chunk) {
    this.buf = Buffer.concat([this.buf, chunk]);
    for (;;) {
      const head = this.buf.indexOf("\r\n\r\n");
      if (head < 0) return;
      const header = this.buf.subarray(0, head).toString("ascii");
      const m = /^Content-Length:\s*(\d+)\s*$/im.exec(header);
      if (!m) throw new Error(`${this.name}: a message without Content-Length: ${JSON.stringify(header)}`);
      const len = Number(m[1]);
      if (this.buf.length < head + 4 + len) return;
      const body = this.buf.subarray(head + 4, head + 4 + len).toString("utf8");
      this.buf = this.buf.subarray(head + 4 + len);
      let msg;
      try {
        msg = JSON.parse(body);
      } catch (e) {
        throw new Error(`${this.name}: a body that is not JSON (${e.message}): ${body.slice(0, 200)}`);
      }
      this.dispatch(msg);
    }
  }

  dispatch(msg) {
    if (msg.id !== undefined && msg.id !== null && (msg.result !== undefined || msg.error !== undefined)) {
      const p = this.pending.get(msg.id);
      if (!p) return;
      this.pending.delete(msg.id);
      clearTimeout(p.timer);
      p.resolve(msg);
      return;
    }
    if (typeof msg.method === "string") {
      const uri = msg.params && msg.params.uri;
      const i = this.waiters.findIndex((w) => w.method === msg.method && (!w.uri || w.uri === uri));
      if (i >= 0) {
        const w = this.waiters.splice(i, 1)[0];
        clearTimeout(w.timer);
        w.resolve(msg);
        return;
      }
      if (!this.notes.has(msg.method)) this.notes.set(msg.method, []);
      this.notes.get(msg.method).push(msg.params);
    }
  }

  send(msg) {
    const body = Buffer.from(JSON.stringify(msg), "utf8");
    this.child.stdin.write(Buffer.concat([Buffer.from(`Content-Length: ${body.length}\r\n\r\n`, "ascii"), body]));
  }

  notify(method, params) {
    this.send({ jsonrpc: "2.0", method, params });
  }

  request(method, params, timeoutMs) {
    const id = this.nextId++;
    return new Promise((resolvePromise, reject) => {
      const timer = setTimeout(() => {
        this.pending.delete(id);
        reject(new Error(`${method}: no response within ${timeoutMs / 1000} s`));
      }, timeoutMs);
      this.pending.set(id, { resolve: resolvePromise, reject, timer });
      this.send({ jsonrpc: "2.0", id, method, params });
    });
  }

  waitNotification(method, uri, timeoutMs) {
    const queued = this.notes.get(method);
    if (queued && queued.length) {
      const params = queued.shift();
      return Promise.resolve({ jsonrpc: "2.0", method, params });
    }
    return new Promise((resolvePromise, reject) => {
      const timer = setTimeout(() => {
        this.waiters = this.waiters.filter((w) => w.timer !== timer);
        reject(new Error(`no ${method}${uri ? " for " + uri : ""} within ${timeoutMs / 1000} s`));
      }, timeoutMs);
      this.waiters.push({ method, uri, resolve: resolvePromise, reject, timer });
    });
  }

  async stop(timeoutMs = 5000) {
    try {
      this.child.stdin.end();
    } catch {}
    const timer = setTimeout(() => {
      this.child.kill("SIGKILL");
    }, timeoutMs);
    await this.exited;
    clearTimeout(timer);
    return this.code;
  }
}

// --- one case on one server ---------------------------------------------------------

const pos = (line, character) => ({ position: { line, character } });
const range = (a, b) => ({ range: { start: { line: a[0], character: a[1] }, end: { line: b[0], character: b[1] } } });
const SORTABLES = ["items", "diagnostics", "references", "symbols"];

function judge(exp, actual, text, uri) {
  const sortables = SORTABLES;
  const normActual = normalize(actual, null, uri, sortables);
  const normValue = normalize(exp.value, null, uri, sortables);
  const mode = exp.match || "exact";
  if (mode === "error") {
    const code = exp.path ? atPath(normActual, exp.path) : atPath(normActual, "error.code");
    if (deepEqual(code, normValue)) return null;
    return `expected the error code ${show(normValue)}, got ${show(code)}${atPath(normActual, "result") !== undefined ? " (with a result)" : ""}`;
  }
  if (mode === "absent") {
    const got = atPath(normActual, exp.path);
    return got === undefined || got === null ? null : `expected ${exp.path} to be absent, got ${show(got)}`;
  }
  if (mode === "applyEquals") {
    const edits = atPath(normActual, exp.path);
    if (!Array.isArray(edits)) return `expected a TextEdit[] at ${exp.path}, got ${show(edits)}`;
    const got = applyEdits(text, edits);
    if (got === exp.value) return null;
    return `applied ${exp.path} gives ${JSON.stringify(got)}, expected ${JSON.stringify(exp.value)}`;
  }
  const got = atPath(normActual, exp.path);
  const ok = mode === "subset" ? subsetMatch(normValue, got) : deepEqual(normValue, got);
  if (ok) return null;
  return `${mode} at ${exp.path}: expected ${show(normValue)}, got ${show(got)}`;
}

async function runCase(c, server, timeoutMs) {
  const bin = process.env[SERVERS[server].env];
  const conn = new Conn(server, bin, c.uri);
  const problems = [];
  try {
    const init = await conn.request(
      "initialize",
      {
        processId: process.pid,
        rootUri: LIB_URI,
        workspaceFolders: [{ uri: LIB_URI, name: "lib" }],
        capabilities: {
          general: { positionEncodings: ["utf-16"] },
          textDocument: { hover: { contentFormat: ["markdown"] }, publishDiagnostics: { relatedInformation: true } },
          experimental: { wizElaborated: false },
        },
      },
      timeoutMs,
    );
    if (init.error) problems.push(`initialize: ${show(init.error)}`);
    conn.notify("initialized", {});
    conn.notify("textDocument/didOpen", {
      textDocument: { uri: c.uri, languageId: "wiz", version: 1, text: c.text },
    });
    // the didOpen's diagnostics: every case waits, so a server that never publishes is
    // a failure, not a silent pass
    const diag = await conn.waitNotification("textDocument/publishDiagnostics", c.uri, timeoutMs);
    for (const exp of c.diagnostics || []) {
      const problem = judge(exp, diag.params, c.text, c.uri);
      if (problem) problems.push(`diagnostics ${problem}`);
    }
    if (!c.diagnostics && diag.params && Array.isArray(diag.params.diagnostics) && diag.params.diagnostics.length) {
      problems.push(`unexpected diagnostics (add a "diagnostics" expectation): ${show(normalize(diag.params.diagnostics, null, c.uri, SORTABLES))}`);
    }
    // (`diagnostics` absent means the document must be clean: a case whose text does not
    // mean what it looks like publishes something and is caught here)
    const responses = [];
    for (const req of c.requests || []) {
      const params = { ...(req.params || {}), textDocument: { uri: c.uri } };
      responses.push({ label: req.method, msg: await conn.request(req.method, params, timeoutMs) });
    }
    const shutdown = await conn.request("shutdown", null, timeoutMs);
    if (shutdown.error) problems.push(`shutdown: ${show(shutdown.error)}`);
    for (const req of c.afterShutdown || []) {
      const params = { ...(req.params || {}), textDocument: { uri: c.uri } };
      responses.push({ label: `${req.method} (after shutdown)`, msg: await conn.request(req.method, params, timeoutMs) });
    }
    conn.notify("exit", null);
    const expected = [...(c.expected || [])];
    if (expected.length !== responses.length) {
      problems.push(`${responses.length} responses but ${expected.length} expectations`);
    }
    for (let i = 0; i < Math.min(expected.length, responses.length); i++) {
      const problem = judge(expected[i], responses[i].msg, c.text, c.uri);
      if (problem) problems.push(`${responses[i].label} #${i}: ${problem}`);
    }
    const code = await conn.stop();
    if (code !== 0) problems.push(`exit code ${code} (expected 0)${conn.stderr.trim() ? ": " + conn.stderr.trim().slice(-1500) : ""}`);
  } catch (e) {
    problems.push(e.message);
    if (conn.stderr.trim()) problems.push(`stderr: ${conn.stderr.trim().slice(-1500)}`);
    conn.child.kill("SIGKILL");
    await conn.exited;
  }
  return problems;
}

// --- the meta-test: advertised == answered ------------------------------------------

const META_DOC = "import Prelude\ndef two : Nat := 1\ndef three : Nat := tw\n";
const META_URI = "file:///conf/meta.wiz";

// A minimal valid request per advertised (or probed) method.
const META_PROBES = {
  hoverProvider: ["textDocument/hover", pos(1, 4)],
  definitionProvider: ["textDocument/definition", pos(1, 4)],
  declarationProvider: ["textDocument/declaration", pos(1, 4)],
  documentHighlightProvider: ["textDocument/documentHighlight", pos(1, 4)],
  referencesProvider: ["textDocument/references", { ...pos(1, 4), context: { includeDeclaration: true } }],
  renameProvider: ["textDocument/rename", { ...pos(1, 4), newName: "other" }],
  completionProvider: ["textDocument/completion", pos(2, 22)],
  signatureHelpProvider: ["textDocument/signatureHelp", pos(1, 13)],
  inlayHintProvider: ["textDocument/inlayHint", range([0, 0], [2, 0])],
  semanticTokensProvider: ["textDocument/semanticTokens/full", {}],
  documentSymbolProvider: ["textDocument/documentSymbol", {}],
  workspaceSymbolProvider: ["workspace/symbol", { query: "two" }],
  foldingRangeProvider: ["textDocument/foldingRange", {}],
  documentFormattingProvider: ["textDocument/formatting", { options: { tabSize: 2, insertSpaces: true } }],
  documentRangeFormattingProvider: [
    "textDocument/rangeFormatting",
    { ...range([0, 0], [3, 0]), options: { tabSize: 2, insertSpaces: true } },
  ],
  codeActionProvider: ["textDocument/codeAction", { ...range([1, 0], [1, 7]), context: { diagnostics: [] } }],
};

// The host's providers that the self-hosted server does not have (plus one that no
// server has): unadvertised on a server, each must answer -32601.
const META_UNADVERTISED = [
  "textDocument/declaration",
  "textDocument/references",
  "textDocument/rename",
  "textDocument/formatting",
  "textDocument/rangeFormatting",
  "textDocument/documentSymbol",
  "textDocument/foldingRange",
  "textDocument/signatureHelp",
  "textDocument/inlayHint",
  "textDocument/codeAction",
  "textDocument/semanticTokens/full",
  "workspace/symbol",
  "wiz/frobnicate",
];

const META_METHOD_PARAMS = new Map(
  Object.values(META_PROBES)
    .map(([method, params]) => [method, params])
    .concat([["wiz/frobnicate", {}]]),
);

const META_KNOWN_GAP = [{ server: "host", probe: "wiz/frobnicate", reason: "an unknown request gets result: null, not -32601 (H1)", issue: "H1" }];

async function runMeta(server, timeoutMs) {
  const bin = process.env[SERVERS[server].env];
  const conn = new Conn(server, bin, META_URI);
  const problems = [];
  try {
    const init = await conn.request(
      "initialize",
      {
        processId: process.pid,
        rootUri: LIB_URI,
        workspaceFolders: [{ uri: LIB_URI, name: "lib" }],
        capabilities: { general: { positionEncodings: ["utf-16"] } },
      },
      timeoutMs,
    );
    if (init.error) throw new Error(`initialize: ${show(init.error)}`);
    const caps = (init.result && init.result.capabilities) || {};
    conn.notify("initialized", {});
    conn.notify("textDocument/didOpen", {
      textDocument: { uri: META_URI, languageId: "wiz", version: 1, text: META_DOC },
    });
    await conn.waitNotification("textDocument/publishDiagnostics", META_URI, timeoutMs);

    if (caps.positionEncoding !== undefined && caps.positionEncoding !== "utf-16") {
      problems.push(`positionEncoding is ${show(caps.positionEncoding)}, not "utf-16"`);
    }

    // every advertised provider: an answer, not -32601
    const isOn = (key) => caps[key] !== undefined && caps[key] !== false;
    const providers = Object.keys(caps).filter((k) => k.endsWith("Provider"));
    for (const key of providers) {
      if (!isOn(key)) continue;
      const probe = META_PROBES[key];
      if (!probe) {
        problems.push(`advertised ${key} has no probe (add one to META_PROBES)`);
        continue;
      }
      const [method, params] = probe;
      const r = await conn.request(method, { ...params, textDocument: { uri: META_URI } }, timeoutMs);
      if (r.error) problems.push(`advertised ${key} -> ${method} answers ${show(r.error)}`);
    }
    const infoview = caps.experimental && caps.experimental.wizInfoview;
    for (const method of (infoview && infoview.methods) || []) {
      const params = META_METHOD_PARAMS.get(method) || pos(2, 4);
      const r = await conn.request(method, { ...params, textDocument: { uri: META_URI } }, timeoutMs);
      // an infoview method that needs a session/ref from a previous answer may reject
      // malformed params with -32602; what it may not do is say it does not exist
      if (r.error && r.error.code === -32601) problems.push(`advertised wizInfoview method ${method} answers -32601`);
      else if (r.error && !["wiz/subtermInfo", "wiz/interactiveInfo"].includes(method)) {
        problems.push(`advertised wizInfoview method ${method} answers ${show(r.error)}`);
      }
    }

    // every unadvertised probe: -32601
    const advertised = new Set();
    for (const [key, [method]] of Object.entries(META_PROBES)) if (isOn(key)) advertised.add(method);
    for (const method of (infoview && infoview.methods) || []) advertised.add(method);
    const gaps = [];
    const stale = [];
    for (const method of META_UNADVERTISED) {
      if (advertised.has(method)) continue;
      const r = await conn.request(method, { ...(META_METHOD_PARAMS.get(method) || {}), textDocument: { uri: META_URI } }, timeoutMs);
      const code = r.error && r.error.code;
      const gap = META_KNOWN_GAP.find((g) => g.server === server && g.probe === method);
      if (code === -32601) {
        // the gap is closed: the entry must go
        if (gap) stale.push(gap);
        continue;
      }
      if (gap) {
        gaps.push(gap);
        continue;
      }
      problems.push(`unadvertised ${method} answers ${r.error ? `error ${code}` : `result ${show(r.result)}`}, not -32601`);
    }

    const shutdown = await conn.request("shutdown", null, timeoutMs);
    if (shutdown.error) problems.push(`shutdown: ${show(shutdown.error)}`);
    conn.notify("exit", null);
    const exitCode = await conn.stop();
    if (exitCode !== 0) problems.push(`exit code ${exitCode} (expected 0)`);
    return { problems, gaps, stale };
  } catch (e) {
    problems.push(e.message);
    if (conn.stderr.trim()) problems.push(`stderr: ${conn.stderr.trim().slice(-1500)}`);
    conn.child.kill("SIGKILL");
    await conn.exited;
    return { problems, gaps: [], stale: [] };
  }
}

// --- the run ------------------------------------------------------------------------

function parseArgs(argv) {
  const opts = { only: null, server: null, list: false, verbose: false };
  for (let i = 0; i < argv.length; i++) {
    const a = argv[i];
    if (a === "--only") opts.only = (argv[++i] || "").split(",").filter(Boolean);
    else if (a.startsWith("--only=")) opts.only = a.slice(7).split(",").filter(Boolean);
    else if (a === "--server") opts.server = argv[++i];
    else if (a.startsWith("--server=")) opts.server = a.slice(9);
    else if (a === "--list") opts.list = true;
    else if (a === "--verbose" || a === "-v") opts.verbose = true;
    else if (a === "--help" || a === "-h") {
      console.log(readFileSync(fileURLToPath(import.meta.url), "utf8").split("\n").slice(0, 12).join("\n"));
      process.exit(0);
    } else {
      console.error(`lsp-conformance: unknown argument ${a}`);
      process.exit(2);
    }
  }
  if (opts.server && !SERVERS[opts.server]) {
    console.error(`lsp-conformance: --server is host or selfhost, not ${opts.server}`);
    process.exit(2);
  }
  return opts;
}

function loadCases() {
  const files = readdirSync(CASES_DIR)
    .filter((f) => f.endsWith(".json"))
    .sort();
  const cases = files.map((f) => {
    const c = JSON.parse(readFileSync(join(CASES_DIR, f), "utf8"));
    if (!c.name) c.name = f.replace(/\.json$/, "");
    if (c.name + ".json" !== f) console.warn(`lsp-conformance: ${f} names itself ${JSON.stringify(c.name)}`);
    return c;
  });
  const names = new Set();
  for (const c of cases) {
    if (names.has(c.name)) {
      console.error(`lsp-conformance: two cases named ${c.name}`);
      process.exit(2);
    }
    names.add(c.name);
  }
  return cases;
}

async function main() {
  const opts = parseArgs(process.argv.slice(2));
  const cases = loadCases();
  const selected = cases.filter((c) => !opts.only || opts.only.includes(c.name));
  const wantMeta = !opts.only || opts.only.includes("meta") || opts.only.includes("meta advertised==answered");
  if (opts.only) {
    const known = new Set(cases.map((c) => c.name).concat(["meta", "meta advertised==answered"]));
    const unknown = opts.only.filter((n) => !known.has(n));
    if (unknown.length) {
      console.error(`lsp-conformance: no case named ${unknown.join(", ")} (--list shows them)`);
      process.exit(2);
    }
  }
  if (opts.list) {
    for (const c of selected) console.log(`${c.name}\t[${(c.servers || ["host", "selfhost"]).join(",")}]`);
    if (wantMeta) console.log("meta advertised==answered");
    return;
  }
  const servers = (opts.server ? [opts.server] : ["host", "selfhost"]).filter((s) => {
    if (process.env[SERVERS[s].env]) return true;
    console.log(`skip ${s}: ${SERVERS[s].env} is unset (no binary to drive)`);
    return false;
  });
  if (!servers.length) {
    // a run with no server available is a skip, not a pass
    console.log("lsp-conformance: no server to drive (set WIZ_HOST_BIN and/or WIZ_SELFHOST_COMPILER)");
    process.exit(3);
  }
  if (opts.list) {
    for (const c of selected) console.log(`${c.name}\t[${(c.servers || ["host", "selfhost"]).join(",")}]`);
    if (wantMeta) console.log("meta advertised==answered");
    return;
  }
  const counts = { pass: 0, xfail: 0, xpass: 0, fail: 0, skip: 0 };
  const failures = [];
  // the first case on a server pays its start-up (the host loads Prelude, the self-hosted
  // server its toolchain): 60 s for that one, 30 s after
  const firstCase = new Set(servers);
  const timeoutFor = (server) => {
    const t = firstCase.has(server) ? 60000 : 30000;
    firstCase.delete(server);
    return t;
  };
  for (const c of selected) {
    for (const server of servers) {
      if (!(c.servers || ["host", "selfhost"]).includes(server)) {
        counts.skip++;
        console.log(`skip ${server} ${c.name}: not for this server`);
        continue;
      }
      const gap = (c.knownGap || []).find((g) => g.server === server);
      const problems = await runCase(c, server, timeoutFor(server));
      if (problems.length) {
        if (gap) {
          counts.xfail++;
          console.log(`XFAIL ${server} ${c.name}: ${gap.reason || gap.issue || "known gap"}`);
          if (opts.verbose) for (const p of problems) console.log(`  ${p}`);
        } else {
          counts.fail++;
          failures.push(`${server} ${c.name}`);
          console.log(`FAIL ${server} ${c.name}`);
          for (const p of problems) console.log(`  ${p}`);
        }
      } else if (gap) {
        counts.xpass++;
        failures.push(`${server} ${c.name} (XPASS)`);
        console.log(`XPASS ${server} ${c.name}: it passes now; remove the knownGap entry (${gap.reason || gap.issue})`);
      } else {
        counts.pass++;
        console.log(`ok ${server} ${c.name}`);
      }
      if (opts.verbose) console.log(`  (${problems.length} problem(s))`);
    }
  }
  if (wantMeta) {
    for (const server of servers) {
      const { problems, gaps, stale } = await runMeta(server, timeoutFor(server));
      if (problems.length) {
        counts.fail++;
        failures.push(`${server} meta advertised==answered`);
        console.log(`FAIL ${server} meta advertised==answered`);
        for (const p of problems) console.log(`  ${p}`);
      } else if (stale.length) {
        counts.xpass++;
        failures.push(`${server} meta advertised==answered (XPASS)`);
        console.log(
          `XPASS ${server} meta advertised==answered: ${stale.map((g) => g.probe).join(", ")} answers -32601 now; remove the known-gap entr${stale.length > 1 ? "ies" : "y"}`,
        );
      } else if (gaps.length) {
        counts.xfail++;
        console.log(`XFAIL ${server} meta advertised==answered: ${gaps.map((g) => `${g.probe} (${g.reason})`).join("; ")}`);
      } else {
        counts.pass++;
        console.log(`ok ${server} meta advertised==answered`);
      }
    }
  }
  console.log(
    `lsp-conformance: ${counts.pass} pass, ${counts.xfail} xfail, ${counts.xpass} xpass, ${counts.fail} fail, ${counts.skip} skip`,
  );
  if (failures.length) {
    console.log(`lsp-conformance: failed: ${failures.join("; ")}`);
    process.exit(1);
  }
}

main().catch((e) => {
  console.error(`lsp-conformance: ${e && e.stack ? e.stack : e}`);
  process.exit(2);
});
