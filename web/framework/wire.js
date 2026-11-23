// The P0 Loom wire: the envelope, the payload schemas, the two call/reply channels and
// the monitor that decides whether a message may reach the semantic handler.
//
// The model is canonical in `docs/notes/loom-wire-protocol.md`: the host / Loom runtime /
// SSR shell / designer-builder split, the data paths, the one validation table, and the
// adopt contract. This file implements the wire rows of that table (3–7 and 10) and the
// envelope. It does not restate the ownership model; a second prose description is a
// bug. `web/framework/wire_test.mjs` pins the table and the transitions.
//
// P0 is deliberately one interaction: `editor.calls` (host -> runtime) and
// `editor.replies` (runtime -> host), plus the diagnostic `wire` channel. Events,
// patches, widgets and the LSP bridge are P1/P2 and their channels are not registered,
// so a message that names them is `Wire.Error.channel` (an unregistered capability).
//
// A message is one JSON object:
//
//   {"v":"wiz.loom.wire/1","ch":"editor.calls","op":"call","src":"host","seq":1,
//    "id":7,"payload":{"schema":"wiz.call/1","method":"run","args":{}}}
//
// `seq` is per `(ch, src)` and starts at 1; `id` correlates a call with its reply, its
// effect request and its result; `v` is exact (a mismatch is refused, never
// downgraded). `encode` validates before serialising; `decode` validates the frame,
// the JSON, the envelope and the payload; `Monitor.check` additionally checks the
// per-connection state and never partially applies a message.
"use strict";

export const WIRE_VERSION = "wiz.loom.wire/1";
export const WIRE_PROTOCOL = "wiz.loom.protocol/1";

// The caps are data so the adapter, the monitor and the tests use the same numbers
// (§4.3 of the note). A violation is `Wire.Error.cap`, never a truncation.
export const CAPS = Object.freeze({
  frame: 1048576,        // one JSON frame
  envelope: 65536,       // the envelope without its payload
  payload: 262144,       // one generic payload
  text: 1048576,         // an editor document (P1's delta's `len`)
  patchHtml: 262144,     // one inserted/replaced subtree
  patchOps: 4096,        // one patch batch
  patchDepth: 64,        // a patch path's segments
  path: 256,             // a patch path's characters
  widget: 2000000,       // the existing sanitiser cap
  spans: 10000,
  spansBytes: 262144,
  jsonDepth: 32,
  jsonArray: 4096,
  jsonKeys: 1024,
  jsonKey: 256,
  inFlight: 64,
  outbox: 256,
  outboxBytes: 1048576,
  approx: 64,
});

export const ERROR_CODES = Object.freeze({
  VERSION: "version",
  HASH: "hash",
  CHANNEL: "channel",
  OP: "op",
  SEQ: "seq",
  ID: "id",
  PAYLOAD: "payload",
  CAP: "cap",
  STATE: "state",
  BACKPRESSURE: "backpressure",
  TIMEOUT: "timeout",
  CANCELLED: "cancelled",
  INTERNAL: "internal",
});

// The only methods P0's editor capability accepts. `resync` is a typed call from the
// start, so a patch gap has a recovery path before P1's patch stream. `mode:"query"` is
// the asynchronous form of the read-only `ask` fast path; it is still a call.
export const METHODS = Object.freeze(new Set([
  "run", "save", "share", "sync", "edit", "load", "panel", "ack", "resync",
]));

// The P0 channels. `from` is the only legal sender; `ops` maps an op to its outer
// payload schema (`null` for `close`, which carries no payload). Adding a channel here is
// registering a capability; a runtime built without it closes the channel.
export const CHANNELS = Object.freeze({
  "editor.calls": Object.freeze({
    from: Object.freeze(["host"]),
    ops: Object.freeze({
      call: "wiz.call/1",
      result: "wiz.effect-result/1",
      cancel: "wiz.cancel/1",
      ack: "wiz.ack/1",
      close: null,
    }),
  }),
  "editor.replies": Object.freeze({
    from: Object.freeze(["runtime"]),
    ops: Object.freeze({
      reply: "wiz.call-reply/1",
      request: "wiz.effect/1",
      fail: "wiz.failure/1",
      close: null,
    }),
  }),
  wire: Object.freeze({
    from: Object.freeze(["runtime"]),
    ops: Object.freeze({ error: "wiz.wire.error/1" }),
  }),
});

// The patch ops the host pre-validator/applier knows (row 10; the applier is
// `web/framework/runtime.js`, and P0 does not move the patch stream onto the wire).
export const PATCH_OPS = Object.freeze(new Set([
  "replace", "text", "setAttr", "removeAttr", "insert", "remove", "move",
]));

const REQUIRED_ID = Object.freeze({
  "editor.calls": Object.freeze(new Set(["call", "result", "cancel"])),
  "editor.replies": Object.freeze(new Set(["reply", "request", "fail"])),
  wire: Object.freeze(new Set()),
});

const RESERVED_KEYS = new Set(["__proto__", "constructor", "prototype"]);

export class WireError extends Error {
  constructor(code, message, detail = null) {
    super(message);
    this.name = "WireError";
    this.code = code;
    this.detail = detail;
    this.fatal = code === ERROR_CODES.VERSION || code === ERROR_CODES.HASH;
  }
}

function fail(code, message, detail = null) {
  throw new WireError(code, message, detail);
}

const isObject = (v) => v !== null && typeof v === "object" && !Array.isArray(v);
const isInt = (v) => Number.isInteger(v) && v >= 0;
const isUint32 = (v) => isInt(v) && v <= 0xffffffff;
const isString = (v, max = Infinity) => typeof v === "string" && v.length <= max;

// The UTF-8 length, and a check for a lone surrogate (invalid UTF-8 on the wire).
export function utf8Length(s) {
  let n = 0;
  const text = String(s);
  for (let i = 0; i < text.length; i++) {
    const c = text.charCodeAt(i);
    if (c >= 0xd800 && c <= 0xdbff) {
      const d = i + 1 < text.length ? text.charCodeAt(i + 1) : 0;
      if (d < 0xdc00 || d > 0xdfff) fail(ERROR_CODES.PAYLOAD, "a lone high surrogate is not UTF-8");
      n += 4;
      i++;
    } else if (c >= 0xdc00 && c <= 0xdfff) {
      fail(ERROR_CODES.PAYLOAD, "a lone low surrogate is not UTF-8");
    } else if (c < 0x80) n += 1;
    else if (c < 0x800) n += 2;
    else n += 3;
  }
  return n;
}

function validateJson(value, depth = 0, path = "payload") {
  if (depth > CAPS.jsonDepth) fail(ERROR_CODES.CAP, path + " is deeper than " + CAPS.jsonDepth);
  if (value === null || typeof value === "boolean" || typeof value === "string") return;
  if (typeof value === "number") {
    if (!Number.isFinite(value)) fail(ERROR_CODES.PAYLOAD, path + " is not a finite number");
    return;
  }
  if (Array.isArray(value)) {
    if (value.length > CAPS.jsonArray) fail(ERROR_CODES.CAP, path + " has more than " + CAPS.jsonArray + " items");
    for (let i = 0; i < value.length; i++) validateJson(value[i], depth + 1, path + "[" + i + "]");
    return;
  }
  if (isObject(value)) {
    const keys = Object.keys(value);
    if (keys.length > CAPS.jsonKeys) fail(ERROR_CODES.CAP, path + " has more than " + CAPS.jsonKeys + " keys");
    for (const key of keys) {
      if (RESERVED_KEYS.has(key)) fail(ERROR_CODES.PAYLOAD, path + " has a reserved key " + key);
      if (key.length > CAPS.jsonKey) fail(ERROR_CODES.CAP, path + " has a key longer than " + CAPS.jsonKey);
      validateJson(value[key], depth + 1, path + "." + key);
    }
    return;
  }
  fail(ERROR_CODES.PAYLOAD, path + " is not JSON");
}

function need(cond, code, message) {
  if (!cond) fail(code, message);
}

function validateValueOrString(v, max, what) {
  if (v === undefined || v === null) return;
  if (typeof v === "string") {
    need(v.length <= max, ERROR_CODES.CAP, what + " is longer than " + max);
    return;
  }
  validateJson(v, 0, what);
}

// The payload decoder (the generated decoders' P0 hand-written counterpart). An unknown
// outer schema is a payload error; unknown fields are ignored, as the note says.
export function validatePayload(payload) {
  need(isObject(payload), ERROR_CODES.PAYLOAD, "the payload is not an object");
  need(isString(payload.schema, 128) && payload.schema.length > 0, ERROR_CODES.PAYLOAD,
    "the payload has no schema");
  validateJson(payload, 0, "payload");
  switch (payload.schema) {
    case "wiz.call/1": {
      need(isString(payload.method, 128) && payload.method.length > 0, ERROR_CODES.PAYLOAD,
        "wiz.call/1 has no method");
      const query = payload.mode === "query";
      need(query || METHODS.has(payload.method), ERROR_CODES.PAYLOAD,
        "unknown editor method " + payload.method);
      if (query) need(isString(payload.method, 128) && payload.method.length > 0,
        ERROR_CODES.PAYLOAD, "a query has no method");
      validateValueOrString(payload.args, CAPS.payload, "wiz.call/1.args");
      break;
    }
    case "wiz.call-reply/1":
    case "wiz.effect-result/1": {
      need(typeof payload.ok === "boolean", ERROR_CODES.PAYLOAD,
        payload.schema + " has no ok");
      if (payload.ok) validateValueOrString(payload.value, CAPS.payload, payload.schema + ".value");
      else need(isString(payload.error, 1024) && payload.error.length > 0, ERROR_CODES.PAYLOAD,
        payload.schema + " failed without an error");
      break;
    }
    case "wiz.effect/1": {
      need(isString(payload.kind, 64) && payload.kind.length > 0, ERROR_CODES.PAYLOAD,
        "wiz.effect/1 has no kind");
      validateValueOrString(payload.payload, CAPS.payload, "wiz.effect/1.payload");
      break;
    }
    case "wiz.ack/1":
      need(isInt(payload.rev), ERROR_CODES.PAYLOAD, "wiz.ack/1 has no rev");
      break;
    case "wiz.cancel/1":
      break;
    case "wiz.failure/1":
      need(isString(payload.code, 64) && payload.code.length > 0, ERROR_CODES.PAYLOAD,
        "wiz.failure/1 has no code");
      need(isString(payload.message, 1024), ERROR_CODES.PAYLOAD,
        "wiz.failure/1 has no message");
      if (payload.detail !== undefined) validateJson(payload.detail, 0, "wiz.failure/1.detail");
      break;
    case "wiz.wire.error/1":
      need(isString(payload.code, 64) && Object.values(ERROR_CODES).includes(payload.code),
        ERROR_CODES.PAYLOAD, "wiz.wire.error/1 has an unknown code");
      need(isString(payload.message, 1024), ERROR_CODES.PAYLOAD,
        "wiz.wire.error/1 has no message");
      need(typeof payload.fatal === "boolean", ERROR_CODES.PAYLOAD,
        "wiz.wire.error/1 has no fatal flag");
      if (payload.detail !== undefined) validateJson(payload.detail, 0, "wiz.wire.error/1.detail");
      break;
    case "wiz.patch/1": {
      // The host pre-validates the patch batch (row 10) before any mutation; P0 keeps
      // js_patch as the DOM transport, but the schema is here so a P1 message is not a
      // second shape.
      need(isInt(payload.base), ERROR_CODES.PAYLOAD, "wiz.patch/1 has no base");
      need(isInt(payload.rev), ERROR_CODES.PAYLOAD, "wiz.patch/1 has no rev");
      need(Array.isArray(payload.ops) && payload.ops.length <= CAPS.patchOps, ERROR_CODES.CAP,
        "wiz.patch/1 has more than " + CAPS.patchOps + " ops");
      for (const op of payload.ops) {
        need(isObject(op) && PATCH_OPS.has(op.op), ERROR_CODES.PAYLOAD, "unknown patch op");
        need(isString(op.path, CAPS.path), ERROR_CODES.CAP, "a patch path is too long");
        const parts = op.path === "" ? [] : String(op.path).split(".");
        need(parts.length <= CAPS.patchDepth, ERROR_CODES.CAP, "a patch path is too deep");
        if (op.html !== undefined) need(isString(op.html, CAPS.patchHtml), ERROR_CODES.CAP,
          "a patch html is too large");
        if (op.text !== undefined) need(isString(op.text, CAPS.patchHtml), ERROR_CODES.CAP,
          "a patch text is too large");
      }
      break;
    }
    default:
      fail(ERROR_CODES.PAYLOAD, "unknown payload schema " + payload.schema);
  }
  return payload;
}

// The envelope validator (rows 4–6). It never looks at the channel state; `Monitor` adds
// the per-connection transitions.
export function validateMessage(msg) {
  need(isObject(msg), ERROR_CODES.PAYLOAD, "a wire message is not an object");
  need(msg.v === WIRE_VERSION, ERROR_CODES.VERSION,
    "expected " + WIRE_VERSION + ", got " + String(msg.v));
  need(isString(msg.ch, 128) && Object.prototype.hasOwnProperty.call(CHANNELS, msg.ch),
    ERROR_CODES.CHANNEL, "unknown channel " + String(msg.ch));
  const channel = CHANNELS[msg.ch];
  need(isString(msg.op, 64) && Object.prototype.hasOwnProperty.call(channel.ops, msg.op),
    ERROR_CODES.OP, "unknown op " + String(msg.op) + " on " + msg.ch);
  need(isString(msg.src, 32) && channel.from.includes(msg.src), ERROR_CODES.CHANNEL,
    "a " + msg.src + " message is not allowed on " + msg.ch);
  need(isInt(msg.seq) && msg.seq >= 1, ERROR_CODES.SEQ, "seq must be a positive integer");
  if (msg.id !== undefined) need(isUint32(msg.id), ERROR_CODES.ID, "id must be a uint32");
  if (REQUIRED_ID[msg.ch].has(msg.op)) need(msg.id !== undefined, ERROR_CODES.ID,
    msg.op + " has no id");
  if (msg.base !== undefined) need(isInt(msg.base), ERROR_CODES.PAYLOAD, "base must be a Nat");
  if (msg.rev !== undefined) need(isInt(msg.rev), ERROR_CODES.PAYLOAD, "rev must be a Nat");
  if (msg.ack !== undefined) need(isInt(msg.ack), ERROR_CODES.PAYLOAD, "ack must be a Nat");
  if (msg.op === "close") {
    need(msg.payload === undefined || msg.payload === null, ERROR_CODES.PAYLOAD,
      "close carries no payload");
  } else {
    need(isObject(msg.payload), ERROR_CODES.PAYLOAD, "a message needs a payload object");
    need(msg.payload.schema === channel.ops[msg.op], ERROR_CODES.PAYLOAD,
      msg.ch + "." + msg.op + " expects " + channel.ops[msg.op] + ", got " + String(msg.payload.schema));
    validatePayload(msg.payload);
  }
  // The envelope without the payload is small; the payload has its own cap.
  const { payload: _payload, ...envelope } = msg;
  need(utf8Length(JSON.stringify(envelope)) <= CAPS.envelope, ERROR_CODES.CAP,
    "the envelope is larger than " + CAPS.envelope);
  return msg;
}

// Canonical JSON: object keys sorted, no undefined fields. Two encoders that build the
// same message produce the same bytes, regardless of field order.
function canonical(value) {
  if (Array.isArray(value)) return value.map(canonical);
  if (isObject(value)) {
    const out = {};
    for (const key of Object.keys(value).sort()) {
      if (value[key] !== undefined) out[key] = canonical(value[key]);
    }
    return out;
  }
  return value;
}

// The generated adapter's P0 counterpart: validate before send (row 3), then the
// canonical JSON frame. A violation throws `WireError`; nothing is sent.
export function encode(msg) {
  const valid = validateMessage(msg);
  const text = JSON.stringify(canonical(valid));
  need(utf8Length(text) <= CAPS.frame, ERROR_CODES.CAP,
    "the frame is larger than " + CAPS.frame);
  return text;
}

// The transport's decode (row 4): frame size, UTF-8, a rejecting reviver, depth/array
// caps, the exact version and the payload schema. A failure throws `WireError`.
export function decode(text) {
  need(typeof text === "string", ERROR_CODES.PAYLOAD, "a frame is not a string");
  need(utf8Length(text) <= CAPS.frame, ERROR_CODES.CAP,
    "the frame is larger than " + CAPS.frame);
  let msg;
  try {
    msg = JSON.parse(text, (key, value) => {
      if (RESERVED_KEYS.has(key)) fail(ERROR_CODES.PAYLOAD, "a frame contains a reserved key " + key);
      return value;
    });
  } catch (e) {
    if (e instanceof WireError) throw e;
    fail(ERROR_CODES.PAYLOAD, "the frame is not JSON: " + (e && e.message ? e.message : e));
  }
  validateJson(msg, 0, "frame");
  return validateMessage(msg);
}

const STATE_ERROR = (message, detail) => new WireError(ERROR_CODES.STATE, message, detail);

// The runtime-side monitor. It is total: `check` either advances the state or returns
// `{ok:false, error}`; it never partially applies a message, so a rejected message
// cannot change app state or produce a patch (row 5). It checks the channel, the per
// `(ch, src)` sequence, the open-id table and the request/reply correlation.
export class Monitor {
  constructor({ role = "runtime" } = {}) {
    this.role = role;
    this.seq = new Map();
    this.open = new Map();       // call id -> { method }
    this.requests = new Map();   // call id -> { kind }
    this.cancelled = new Set();  // ids retired by a cancel (a late reply is ignored once)
    this.used = new Set();       // every call id ever opened (ids are not reused)
    this.closed = new Set();
  }

  check(message) {
    let msg;
    try {
      msg = validateMessage(message);
    } catch (e) {
      return { ok: false, error: e instanceof WireError ? e : new WireError(ERROR_CODES.INTERNAL, String(e)) };
    }
    if (this.closed.has(msg.ch)) {
      return { ok: false, error: STATE_ERROR("the channel " + msg.ch + " is closed") };
    }
    const expected = (this.seq.get(msg.ch) || 0) + 1;
    if (msg.seq !== expected) {
      return { ok: false, error: new WireError(ERROR_CODES.SEQ,
        "expected seq " + expected + " on " + msg.ch + ", got " + msg.seq) };
    }

    // Work on copies; commit only after every check passes.
    const open = new Map(this.open);
    const requests = new Map(this.requests);
    const cancelled = new Set(this.cancelled);
    const used = new Set(this.used);
    const closed = new Set(this.closed);

    const idOf = () => msg.id;
    const requireOpen = () => {
      if (!open.has(idOf())) throw new WireError(ERROR_CODES.ID, "no open call " + idOf());
    };
    try {
      if (msg.ch === "wire") {
        if (msg.payload.fatal) { /* the diagnostic is still accepted; the caller decides */ }
      } else if (msg.ch === "editor.calls") {
        switch (msg.op) {
          case "call": {
            if (used.has(idOf())) throw new WireError(ERROR_CODES.ID, "id " + idOf() + " was already used");
            if (open.size >= CAPS.inFlight) throw new WireError(ERROR_CODES.CAP,
              "more than " + CAPS.inFlight + " calls in flight");
            open.set(idOf(), { method: msg.payload.method });
            used.add(idOf());
            break;
          }
          case "result": {
            if (cancelled.has(idOf())) { cancelled.delete(idOf()); break; }   // the race is legitimate
            if (!requests.has(idOf())) throw new WireError(ERROR_CODES.ID,
              "result for an id the runtime did not request: " + idOf());
            requests.delete(idOf());
            break;
          }
          case "cancel": {
            if (!open.has(idOf()) && !requests.has(idOf())) throw new WireError(ERROR_CODES.ID,
              "cancel for an id that is not open: " + idOf());
            open.delete(idOf());
            requests.delete(idOf());
            cancelled.add(idOf());
            break;
          }
          case "ack":
            break;
          case "close":
            break;
          default:
            throw new WireError(ERROR_CODES.OP, "unknown editor.calls op " + msg.op);
        }
      } else if (msg.ch === "editor.replies") {
        switch (msg.op) {
          case "reply": {
            if (cancelled.has(idOf())) cancelled.delete(idOf());       // legitimate race
            else { requireOpen(); open.delete(idOf()); }
            break;
          }
          case "request": {
            requireOpen();
            if (requests.has(idOf())) throw new WireError(ERROR_CODES.ID,
              "a second request for id " + idOf());
            requests.set(idOf(), { kind: msg.payload.kind });
            break;
          }
          case "fail": {
            if (cancelled.has(idOf())) cancelled.delete(idOf());
            else { requireOpen(); open.delete(idOf()); }
            break;
          }
          case "close":
            break;
          default:
            throw new WireError(ERROR_CODES.OP, "unknown editor.replies op " + msg.op);
        }
      }
      if (msg.op === "close") closed.add(msg.ch);
    } catch (e) {
      return { ok: false, error: e instanceof WireError ? e : new WireError(ERROR_CODES.INTERNAL, String(e)) };
    }

    this.seq.set(msg.ch, msg.seq);
    this.open = open;
    this.requests = requests;
    this.cancelled = cancelled;
    this.used = used;
    this.closed = closed;
    return { ok: true, msg };
  }

  snapshot() {
    return {
      role: this.role,
      seq: Object.fromEntries(this.seq),
      open: Array.from(this.open, ([id, v]) => [id, v.method]),
      requests: Array.from(this.requests, ([id, v]) => [id, v.kind]),
      cancelled: Array.from(this.cancelled),
      used: Array.from(this.used),
      closed: Array.from(this.closed),
    };
  }
}

// The wire's six validation points, rows 3–7 and 10 of the single table in the canonical
// note. `wire_test.mjs` reads the doc's table and checks that these rows agree; a change
// to one without the other fails.
export const VALIDATION = Object.freeze([
  Object.freeze({
    id: 3, boundary: "generated adapter (host)", impl: "web/framework/wire.js#encode",
    validates: "method/channel/op legal, payload fields/caps, fresh id",
    doesNotValidate: "markup, class tokens",
    failure: "throws before send",
  }),
  Object.freeze({
    id: 4, boundary: "transport (host)", impl: "web/framework/wire.js#decode",
    validates: "frame size, UTF-8, JSON.parse reviver, depth/array caps, exact v",
    doesNotValidate: "business fields",
    failure: "connection refused/closed",
  }),
  Object.freeze({
    id: 5, boundary: "envelope monitor (runtime)", impl: "web/framework/wire.js#Monitor",
    validates: "ch/op/src/seq/id/base/rev, transition legality, caps, open ids",
    doesNotValidate: "HTML, URLs, class tokens",
    failure: "channel closed, no state, no patch",
  }),
  Object.freeze({
    id: 6, boundary: "payload decoder (runtime)", impl: "web/framework/wire.js#validatePayload",
    validates: "field type/length/range, schema known; unknown fields ignored",
    doesNotValidate: "what the text means",
    failure: "Wire.Error.payload, no state",
  }),
  Object.freeze({
    id: 7, boundary: "semantic layer (runtime)", impl: "lib/Web/Playground.wiz (Page.step/Page.effect)",
    validates: "handler index/event, draft/format, result shape",
    doesNotValidate: "DOM",
    failure: "no state change",
  }),
  Object.freeze({
    id: 10, boundary: "patch pre-validator/applier (host)", impl: "web/framework/runtime.js#applyPatches",
    validates: "every path resolves, op known, index/depth in range",
    doesNotValidate: "class semantics",
    failure: "discard batch + one resync",
  }),
]);

export const WIRE_VALIDATION_IDS = Object.freeze(VALIDATION.map((r) => r.id));
