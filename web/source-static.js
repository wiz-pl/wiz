// The source reader's static transport: the bundle loader, the one-time payload the
// Wiz runtime decodes, the `scry.source.answer/1` producer, the hash router and the
// mount wiring.
//
// The model is canonical in `/workspace/wiz-notes/scry-web-design.md` §2/§4 (a copy of
// the decisions is in the module comments of `lib/Web/Source/Model.wiz`). This file is
// the host half: it does the fetch, the file assembly and the answer lookup; it does not
// render, and it does not reimplement the reader's view or its line arithmetic (every
// span in the bundle is already UTF-16 and every display string is precomputed).
//
// It has no browser-only import at the top, so the Node acceptance test can import it
// directly; `mountSource` loads `./framework/mount.js` lazily.
//
//   import { loadBundle, bundlePayload, answer, route, mountSource } from "./source-static.js";
"use strict";

const SCHEMA_ANSWER = "scry.source.answer/1";
const SCHEMA_BUNDLE_UI = "scry.source.bundle-ui/1";

// ## Reading a bundle

export async function getJson(url, fetchImpl) {
  const fetch = fetchImpl || globalThis.fetch;
  if (typeof fetch !== "function") throw new Error("no fetch for " + url);
  const r = await fetch(url);
  if (!r || !r.ok) throw new Error("GET " + url + ": " + (r ? r.status : "no response"));
  return r.json();
}

// `base` is a data directory URL ("data/" in the browser, a file path in a Node host).
export async function loadBundle(base, fetchImpl) {
  const join = (p) => String(base).replace(/\/?$/, "/") + p;
  const manifest = await getJson(join("manifest.json"), fetchImpl);
  const filesJson = await getJson(join("files.json"), fetchImpl);
  const findingsJson = await getJson(join("findings.json"), fetchImpl);
  const perFile = {};
  for (const f of filesJson.files || []) {
    perFile[f.id] = await getJson(join("f/" + f.id + ".json"), fetchImpl);
  }
  return assemble(manifest, filesJson, findingsJson, perFile);
}

// The in-memory bundle the rest of this module (and the Node test) uses.
export function assemble(manifest, filesJson, findingsJson, perFile) {
  return {
    manifest,
    files: (filesJson && filesJson.files) || [],
    findings: (findingsJson && findingsJson.findings) || [],
    perFile: perFile || {},
  };
}

// The payload the runtime decodes through `wiz_loom_effect "bundle"` (one object, not
// one effect per file). It is `scry.source.bundle-ui/1`.
export function bundlePayload(bundle) {
  const files = [];
  const facts = [];
  for (const meta of bundle.files) {
    const f = bundle.perFile[meta.id];
    if (!f) continue;
    files.push({
      id: f.id, path: f.path, language: f.language,
      text: f.source, lines: f.lines,
    });
    for (const r of f.facts || []) facts.push(r);
  }
  return JSON.stringify({
    schema: SCHEMA_BUNDLE_UI,
    mode: (bundle.manifest && bundle.manifest.mode) || "static",
    tool: (bundle.manifest && bundle.manifest.tool) || "scry",
    files,
    findings: bundle.findings,
    facts,
  });
}

// ## Answers

function col(row, key) {
  for (const p of (row && row.columns) || []) {
    if (Array.isArray(p) && p[0] === key) return p[1];
  }
  return "";
}

function findFinding(bundle, id) {
  for (const f of bundle.findings) if (f.id === id) return f;
  return null;
}

function fileOf(bundle, fileId) {
  const meta = bundle.files.find((f) => f.id === fileId);
  return { meta: meta || null, data: bundle.perFile[fileId] || null };
}

// `FILEID@START-STOP` (the runtime's request payload) or `{fileId, start, stop}`.
export function parsePayload(payload) {
  if (payload && typeof payload === "object") {
    return { fileId: payload.fileId, start: payload.start, stop: payload.stop };
  }
  const at = String(payload == null ? "" : payload).lastIndexOf("@");
  if (at < 0) return null;
  const fileId = String(payload).slice(0, at);
  const range = String(payload).slice(at + 1).split("-");
  if (range.length < 2) return null;
  const start = Number(range[0]);
  const stop = Number(range[1]);
  if (!Number.isFinite(start) || !Number.isFinite(stop)) return null;
  return { fileId, start, stop };
}

function factsAt(bundle, fileId, offset) {
  const data = fileOf(bundle, fileId).data;
  const facts = (data && data.facts) || [];
  return facts.filter((r) => r.fileId === fileId &&
    r.span && r.span.start <= offset && offset < r.span.stop);
}

function findingsAt(bundle, fileId, offset) {
  return bundle.findings.filter((f) => f.fileId === fileId &&
    f.span && f.span.start <= offset && offset < f.span.stop);
}

function noneAnswer(request, fileId, spanText) {
  return JSON.stringify({
    schema: SCHEMA_ANSWER, request, status: "none", fileId: fileId || "",
    span: null, spanText: spanText || "", title: "no answer", rule: "", severity: "",
    findingId: "", lines: [], rows: [], findings: [],
  });
}

function hoverAnswer(bundle, fileId, rows) {
  const sink = rows.find((r) => r.kind === "sink") || rows[0];
  if (!sink) return noneAnswer("hover", fileId, "");
  const findingId = col(sink, "finding");
  const finding = findFinding(bundle, findingId);
  const rule = (finding && finding.rule) || col(sink, "rule");
  const severity = (finding && finding.severity) || col(sink, "severity");
  const message = (finding && finding.message) || col(sink, "message");
  const checked = finding ? !!finding.checked : false;
  const data = fileOf(bundle, fileId).data;
  const text = data && data.source ? data.source.slice(sink.span.start, sink.span.stop) : "";
  const lines = [
    { text: rule, code: false, rule: false, ellipsis: false },
    { text: "severity: " + severity + " · " + (checked
      ? "rule derivation checked against this EDB" : "no certificate (unchecked)"),
      code: false, rule: false, ellipsis: false },
    { text: message, code: false, rule: false, ellipsis: false },
    { text, code: true, rule: false, ellipsis: false },
  ];
  return JSON.stringify({
    schema: SCHEMA_ANSWER, request: "hover", status: "ok", fileId,
    span: sink.span, spanText: sink.spanText || "",
    title: rule + " (" + severity + ")", rule, severity, findingId,
    lines, rows: [], findings: [],
  });
}

function infoAnswer(bundle, fileId, rows, offset) {
  const fs = findingsAt(bundle, fileId, offset);
  const span = rows.length ? rows[0].span : { start: offset, stop: offset + 1 };
  const spanText = rows.length ? (rows[0].spanText || "") : "";
  return JSON.stringify({
    schema: SCHEMA_ANSWER, request: "info", status: "ok", fileId,
    span, spanText, title: "Info at " + spanText, rule: "", severity: "",
    findingId: "", lines: [], rows, findings: fs,
  });
}

// The one answer producer. `kind` is "hover" or "info"; `payload` is the runtime's
// `FILEID@START-STOP`. A host that cannot answer returns the "none" answer (the reader
// says "no answer", never an error banner).
export function answer(bundle, kind, payload) {
  const at = parsePayload(payload);
  if (!at) return noneAnswer(kind, "", "");
  const rows = factsAt(bundle, at.fileId, at.start);
  if (kind === "info") return infoAnswer(bundle, at.fileId, rows, at.start);
  return hoverAnswer(bundle, at.fileId, rows);
}

// ## Routing

// `#/f/<findingId>`, `#/src/<fileId>@L:C[-L:C]`, `#/file/<fileId>`. A fragment is never
// sent to a server; anything else is `{kind: "none"}` and the runtime lands on the list
// with a note.
export function route(hash) {
  const body = String(hash == null ? "" : hash).replace(/^#/, "");
  if (body.startsWith("/f/")) return { kind: "finding", findingId: body.slice(3) };
  if (body.startsWith("/file/")) return { kind: "file", fileId: body.slice(6) };
  if (body.startsWith("/src/")) {
    const rest = body.slice(5);
    const at = rest.lastIndexOf("@");
    if (at < 0) return { kind: "file", fileId: rest };
    return { kind: "source", fileId: rest.slice(0, at), fragment: rest.slice(at + 1) };
  }
  return { kind: "none" };
}

// ## The page's mount

// Mount the runtime on `el`, feed it the bundle, answer its requests and forward
// `hashchange` to it. `module` is the loader/factory mount accepts; `env` is the host
// object mount uses (defaults to `globalThis`).
export async function mountSource(el, { module, bundle, env = globalThis } = {}) {
  const { mount } = await import("./framework/mount.js");
  let handle = null;
  const onRequest = (kind, payload) => {
    if (handle && (kind === "hover" || kind === "info")) {
      handle.call("wiz_loom_effect", "answer", kind, answer(bundle, kind, payload));
    }
  };
  handle = await mount(el, {
    module, env, transport: { bundle: true }, onRequest,
  });
  handle.call("wiz_loom_effect", "bundle", bundlePayload(bundle), "");
  const nav = () => {
    const hash = (env.location && env.location.hash) || "";
    if (handle) handle.call("wiz_loom_effect", "route", hash, "");
  };
  if (env.addEventListener) env.addEventListener("hashchange", nav);
  nav();
  return handle;
}
