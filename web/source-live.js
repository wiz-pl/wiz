// The source reader's live transport: the same bundle, the same Loom runtime, and a
// `wiz lsp --ws` connection for the Wiz files the bundle carries. Two transports, one
// seam: this module produces `scry.source.answer/1` for a hover or a definition, exactly
// as `source-static.js` produces it from the precomputed facts, so the runtime and the
// view cannot tell which one answered.
//
// The page is `index.html` with `?lsp=PORT` (or `?lsp=ws://HOST:PORT`, and `?token=` for
// a `--token-file` server). `?lspRoot=` is the directory the bundle's paths are relative
// to; without it a path is used as given (an absolute path is always used as given), so
// `wiz lsp` can find the file and its `import`s. The root is a page parameter, not a
// manifest field: a bundle must not publish the machine it was built on.
//
// What the reader asks, and what this does:
//
//   * `hover` on a Wiz file  → `textDocument/hover`, sent raw to the runtime, whose
//     `Web.Source.Model.lspHover` stores it and whose view draws it with `Web.Hover.card`
//     (the playground's Markdown card: fences, rules, escaping).
//   * `definition` (a click on a source line) → `textDocument/definition`, parsed by
//     `Web.Hover.targetJson` (the editor's rule) into `{uri, range, label}`. The host maps
//     the URI back to a bundle file and converts the range through the runtime's
//     `wiz_loom_editor_offset` (`Web.EditorModel`, the one line table), so a target
//     inside the bundle is opened and outlined and one outside it is still named.
//   * `hover`/`info` on anything else, or with no server, → the bundle's static answer.
//
// Positions go the other way through `wiz_loom_editor_position`. No line arithmetic,
// Markdown or LSP-shape reading happens here; those are `Web.EditorModel`, `Web.Hover`
// and `wiz lsp`'s.
//
// A failed connection is one note in the footer and `data-lsp="failed"`: the static
// reader and its SSR are unchanged, and every later request takes the static path.
"use strict";

import { answer, mountSource, noneAnswer, parsePayload } from "./source-static.js";
import { LspClient, parseEndpoint, withToken, withoutToken } from "./lsp-client.js";

const SCHEMA_ANSWER = "scry.source.answer/1";

const errText = (e) => (e && e.message ? e.message : String(e));

// The absolute path a bundle file's `path` names, when the page named a root.
function absolutePath(root, path) {
  const p = String(path || "");
  if (/^[a-z][a-z0-9+.-]*:/i.test(p)) return p;      // already a URI
  if (p.startsWith("/")) return p;
  const base = String(root || "").replace(/\/+$/, "");
  return base ? base + "/" + p : p;
}

// A `file://` URI with each path segment encoded. `encodeURIComponent` per segment
// leaves `/` as the separator and escapes spaces, `#` and `?` (which would otherwise be
// read as a fragment or query by the server).
export function fileUri(root, path) {
  const abs = absolutePath(root, path);
  if (/^[a-z][a-z0-9+.-]*:/i.test(abs)) return abs;
  return "file://" + abs.split("/").map(encodeURIComponent).join("/");
}

// The bundle file a definition/location URI names, by whole-URI or decoded-path equality
// (the server builds its own `file://` spelling). `null` when the target is not in the
// bundle.
export function fileOfUri(bundle, root, uri) {
  const want = decodeURI(String(uri || ""));
  for (const f of bundle.files) {
    const have = fileUri(root, f.path);
    if (have === uri || decodeURI(have) === want) return f;
  }
  return null;
}

// ## The mount

export async function mountLive(el, { module, bundle, endpoint, token, root, env = globalThis } = {}) {
  const parsed = parseEndpoint(endpoint);
  if (!parsed) {
    // `?lsp=off` and friends: the static page, with no client and no extra imports.
    return mountSource(el, { module, bundle, env });
  }
  const url = withToken(parsed.url, token);
  const label = withoutToken(url);
  const files = new Map(bundle.files.map((f) => [f.id, f]));
  const wiz = bundle.files.filter((f) => f.language === "wiz");
  // The mode is the page's provenance, not the export's: the same bundle bytes are
  // mounted here, so only the copied in-memory manifest says live.
  const liveBundle = {
    ...bundle,
    manifest: { ...(bundle.manifest || {}), mode: "live" },
  };
  const client = new LspClient({
    url,
    rootUri: root ? fileUri("", root) : null,
    clientInfo: { name: "scry-source" },
    languageId: "wiz",
    requestTimeout: 30000,
  });

  let handle = null;
  let connected = false;
  let seq = 0;                 // the latest request; a stale LSP answer is dropped
  let hoverTimer = null;
  let lastHover = "";

  const setState = (state) => {
    try { el.setAttribute("data-lsp", state); } catch (_) { /* no attribute support */ }
  };
  const note = (text) => {
    if (handle) handle.call("wiz_loom_effect", "note", text, "");
  };
  const staticAnswer = (kind, payload) => {
    if (handle) handle.call("wiz_loom_effect", "answer", kind, answer(bundle, kind, payload));
  };
  const noAnswer = (request, fileId) => {
    if (handle) handle.call("wiz_loom_effect", "answer", request, noneAnswer(request, fileId || "", ""));
  };
  const positionOf = (text, offset) => {
    try {
      return JSON.parse(handle.ask("wiz_loom_editor_position", text, String(offset)));
    } catch (_) {
      return null;
    }
  };
  const offsetOf = (text, line, character) => {
    try {
      return Number(handle.ask("wiz_loom_editor_offset", text, String(line), String(character)));
    } catch (_) {
      return NaN;
    }
  };

  // The definition answer: one row per target (the model focuses the first located one).
  const definitionAnswer = (payload, target) => {
    if (!target) {
      noAnswer("definition", (parsePayload(payload) || {}).fileId);
      return;
    }
    const tmeta = fileOfUri(bundle, root, target.uri);
    let fileId = "";
    let span = { start: 0, stop: 0 };
    if (tmeta) {
      const start = offsetOf(tmeta.text, target.range.start.line, target.range.start.character);
      const stop = offsetOf(tmeta.text, target.range.end.line, target.range.end.character);
      if (Number.isFinite(start) && Number.isFinite(stop)) {
        fileId = tmeta.id;
        const lo = Math.min(start, stop);
        const hi = Math.max(start, stop);
        // A caret/zero-width location still gets one unit, so the outline is visible.
        span = { start: lo, stop: hi > lo ? hi : Math.min(tmeta.text.length, lo + 1) };
      }
    }
    const row = {
      kind: "definition", node: "", fileId, span,
      columns: [["target", target.label], ["uri", target.uri]],
    };
    handle.call("wiz_loom_effect", "answer", "definition", JSON.stringify({
      schema: SCHEMA_ANSWER, request: "definition", status: "ok",
      fileId, span: fileId ? span : null, spanText: target.label, title: "Definition",
      rule: "", severity: "", findingId: "", lines: [], rows: [row], findings: [],
    }));
  };

  const visible = (payload) => {
    const at = parsePayload(payload);
    if (!at) return null;
    const meta = files.get(at.fileId);
    if (!meta || meta.language !== "wiz") return null;
    return { at, meta };
  };

  const liveHover = async (payload) => {
    const v = visible(payload);
    const mine = ++seq;
    if (!v || !connected) {
      staticAnswer("hover", payload);
      return;
    }
    const pos = positionOf(v.meta.text, v.at.start);
    if (!pos) {
      staticAnswer("hover", payload);
      return;
    }
    try {
      const result = await client.hover(fileUri(root, v.meta.path), pos);
      if (mine !== seq) return;              // a newer hover/definition superseded this
      handle.call("wiz_loom_effect", "hover-lsp", payload,
        JSON.stringify(result === undefined ? null : result));
    } catch (e) {
      if (mine !== seq) return;
      note("live: hover failed (" + errText(e) + ")");
      noAnswer("hover", v.at.fileId);
    }
  };

  const liveDefinition = async (payload) => {
    const v = visible(payload);
    const mine = ++seq;
    if (!v || !connected) {
      noAnswer("definition", v ? v.at.fileId : (parsePayload(payload) || {}).fileId);
      return;
    }
    const pos = positionOf(v.meta.text, v.at.start);
    if (!pos) {
      noAnswer("definition", v.at.fileId);
      return;
    }
    try {
      const result = await client.definition(fileUri(root, v.meta.path), pos);
      // `Web.Hover`'s rule, through the runtime: the first usable location, its label
      // and range. A server may answer `null` (nothing there): "no answer", not an error.
      let target = null;
      try {
        target = JSON.parse(handle.ask("wiz_loom_hover_target",
          JSON.stringify(result === undefined ? null : result)));
      } catch (_) {
        target = null;
      }
      if (mine !== seq) return;
      definitionAnswer(payload, target);
    } catch (e) {
      if (mine !== seq) return;
      note("live: definition failed (" + errText(e) + ")");
      noAnswer("definition", v.at.fileId);
    }
  };

  const onRequest = (kind, payload) => {
    if (kind === "hover") { liveHover(payload); return; }
    if (kind === "definition") { liveDefinition(payload); return; }
    // The bundle's facts answer the info view (and anything else).
    staticAnswer(kind, payload);
  };

  handle = await mountSource(el, { module, bundle: liveBundle, env, onRequest });

  // ## Pointer → offset (the host's half: caret hit-testing needs the browser)

  // The character the pointer is over, as a UTF-16 offset in the line's file. `null`
  // when the pointer is not inside the line's code (the line number, a gap, a mark).
  const pointerOffset = (event) => {
    const target = event.target;
    if (!target || typeof target.closest !== "function") return null;
    if (target.closest(".src-mark")) return null;          // the mark's own Loom handler
    const line = target.closest(".src-line");
    if (!line) return null;
    const pane = line.closest("section.source-pane");
    const fileId = pane && pane.getAttribute("data-file");
    const meta = fileId ? files.get(fileId) : null;
    if (!meta || meta.language !== "wiz") return null;
    const code = line.querySelector("code.line");
    const startAttr = line.getAttribute("data-start");
    if (!code || startAttr === null) return null;
    const start = Number(startAttr);
    if (!Number.isFinite(start)) return null;
    const doc = env.document;
    if (!doc) return null;
    let range = null;
    if (typeof doc.caretRangeFromPoint === "function") {
      range = doc.caretRangeFromPoint(event.clientX, event.clientY);
    } else if (typeof doc.caretPositionFromPoint === "function") {
      const p = doc.caretPositionFromPoint(event.clientX, event.clientY);
      if (p) {
        range = doc.createRange();
        range.setStart(p.offsetNode, p.offset);
      }
    }
    if (!range || !range.startContainer || !code.contains(range.startContainer)) return null;
    const before = doc.createRange();
    before.selectNodeContents(code);
    before.setEnd(range.startContainer, range.startOffset);
    return { fileId, offset: start + before.toString().length };
  };

  if (el && typeof el.addEventListener === "function") {
    el.addEventListener("mouseover", (event) => {
      const at = pointerOffset(event);
      if (!at) { lastHover = ""; return; }
      const key = at.fileId + ":" + at.offset;
      if (key === lastHover) return;       // the same identifier: one request
      lastHover = key;
      if (hoverTimer !== null) clearTimeout(hoverTimer);
      hoverTimer = setTimeout(() => {
        hoverTimer = null;
        handle.call("wiz_loom_effect", "hover-at", at.fileId, String(at.offset));
      }, 160);
    }, true);
    el.addEventListener("click", (event) => {
      const at = pointerOffset(event);
      if (!at) return;
      lastHover = "";
      if (hoverTimer !== null) { clearTimeout(hoverTimer); hoverTimer = null; }
      handle.call("wiz_loom_effect", "definition-at", at.fileId, String(at.offset));
    }, true);
  }

  // ## The connection

  setState("connecting");
  // Open the Wiz documents before connecting: the client sends `didOpen` for each on
  // `initialized`, so the server's copy is the bundle's text, not a disk read.
  for (const f of wiz) client.openDocument(fileUri(root, f.path), f.text, { languageId: "wiz" });
  note("live: connecting to " + label + "…");
  try {
    await client.connect();
    connected = true;
    setState("open");
    note("live: " + wiz.length + " Wiz file(s) from " + label +
      " · hover for types, click for a definition");
  } catch (e) {
    connected = false;
    setState("failed");
    note("live: off (" + errText(e) + ") — the static reader is unchanged");
  }
  return handle;
}
