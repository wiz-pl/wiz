// The real-server half of the live reader's proof, without a browser: start
// `wiz lsp --ws`, open the bundle's Wiz file with the bundle's text, and ask the exact
// two questions the page asks (`textDocument/hover`, `textDocument/definition`) at the
// exact token the browser smoke uses (`Source.Span.contains` in
// `lib/Web/Source/Facts.wiz`). Facts.wiz and its target Span.wiz are small: the Wasm
// reader's JSON parser overflows its stack on a single string of about 50 KB, so the
// demo bundle does not carry a large source (EditorModel.wiz is 52 KB). The server's
// term-info elaboration dominates the first answer (51 s in the probe; the definition
// 60 ms after).
//
// The page's position rules are `Web.EditorModel`'s through `wiz_loom_editor_position`;
// this test has no runtime, so the few lines of line/character arithmetic below are the
// test's own and are checked by their obviousness (a UTF-16 offset in a string), not
// shared with the product.
//
//   node web/source_live_test.mjs BUNDLE WIZ_BIN [ROOT]
//
// `ROOT` is the directory the bundle's relative paths live under (default: cwd).
"use strict";
import { readFileSync } from "node:fs";
import { join, resolve } from "node:path";
import { LspClient } from "./lsp-client.js";
import { NodeWebSocket } from "./ws_node_client.mjs";
import { fileUri } from "./source-live.js";
import { startWizLsp } from "./source_lsp.mjs";

const [bundleArg, wizBin, rootArg] = process.argv.slice(2);
if (!bundleArg || !wizBin) {
  console.error("usage: node web/source_live_test.mjs BUNDLE WIZ_BIN [ROOT]");
  process.exit(2);
}
const bundle = resolve(bundleArg);
const root = resolve(rootArg || process.cwd());

let failed = 0;
const ok = (cond, what, detail = "") => {
  if (cond) console.log("ok: " + what);
  else { failed++; console.log("FAIL: " + what + (detail ? "\n  " + detail : "")); }
};
const readJson = (p) => JSON.parse(readFileSync(p, "utf-8"));

const files = readJson(join(bundle, "data", "files.json")).files || [];
const bySuffix = (suffix) =>
  files.find((f) => String(f.path).replace(/\\/g, "/").endsWith(suffix));
const source = bySuffix("Web/Source/Facts.wiz");
const target = bySuffix("Web/Source/Span.wiz");
if (!source || !target) {
  console.error("source live: the bundle has no Web/Source/Facts.wiz + Web/Source/Span.wiz (--source them)");
  process.exit(2);
}
const sourceData = readJson(join(bundle, "data", "f", source.id + ".json"));
const targetData = readJson(join(bundle, "data", "f", target.id + ".json"));
const text = sourceData.source;

// The bundle's own paths, as the checkout sees them (the same rule `source-live.js` is
// given by `?lspRoot=`).
const uriOf = (meta) => fileUri(root, meta.path);

// A UTF-16 offset as an LSP position (0-based line, UTF-16 character). Test-local.
function positionOf(text, offset) {
  const before = text.slice(0, offset);
  const line = (before.match(/\n/g) || []).length;
  const lineStart = before.lastIndexOf("\n") + 1;
  return { line, character: offset - lineStart };
}

const needle = "contains r.span offset";
const marker = "Source.Span.contains r.span offset";
const markerAt = text.indexOf(marker);
const useAt = markerAt + marker.indexOf(needle);
ok(markerAt >= 0, "the bundle's Facts.wiz has the `Source.Span.contains` use", String(markerAt));

const defLine = targetData.source.split("\n")
  .findIndex((line) => line.includes("def Source.Span.contains"));
ok(defLine >= 0, "the bundle's Span.wiz has `def Source.Span.contains`", String(defLine));

let srv = null;
let client = null;
try {
  srv = await startWizLsp(wizBin, root);
  client = new LspClient({
    url: srv.url,
    WebSocketImpl: NodeWebSocket,
    rootUri: fileUri("", root),
    clientInfo: { name: "scry-source-live-test" },
    languageId: "wiz",
    requestTimeout: 180000,
  });
  // Only the hovered file is opened: the page opens documents lazily too, and the
  // server's term-info elaboration is the expensive part. The definition target's text
  // is in the bundle, not in a document.
  client.openDocument(uriOf(source), sourceData.source, { languageId: "wiz" });
  await client.connect();
  ok(client.isOpen, "the real wiz lsp accepts the connection");
  // H2: the host advertises LSP's default encoding explicitly, so a client never has to
  // guess it from the text. Before H2 (`agent/lsp-host-h1-h3`) the capability was absent
  // and the server counted code points, whatever the client asked for.
  ok(client.capabilities && client.capabilities.positionEncoding === "utf-16",
    "the host advertises positionEncoding utf-16",
    JSON.stringify(client.capabilities || null).slice(0, 200));

  const pos = positionOf(text, useAt);
  const hover = await client.hover(uriOf(source), pos);
  const hoverText = hover ? JSON.stringify(hover) : "null";
  ok(hover && /contains/.test(hoverText), "the real server answers a hover on `contains`",
    hoverText.slice(0, 300));
  ok(hover && /contents/.test(hoverText), "the hover is the LSP contents shape",
    hoverText.slice(0, 120));

  const definition = await client.definition(uriOf(source), pos);
  const loc = Array.isArray(definition) ? definition[0] : definition;
  ok(!!loc, "the real server answers a definition on `contains`",
    JSON.stringify(definition).slice(0, 300));
  const targetUri = loc && (loc.uri || loc.targetUri);
  const range = loc && (loc.range || loc.targetSelectionRange || loc.targetRange);
  ok(!!targetUri && String(targetUri).endsWith("Web/Source/Span.wiz"),
    "the definition names Span.wiz", String(targetUri));
  ok(!!range && range.start && range.start.line === defLine,
    "the definition range is `def Source.Span.contains`'s line",
    range ? JSON.stringify(range) : "no range");

  // ## UTF-16 columns
  //
  // The use line carries a non-BMP character in an inline comment, so its UTF-16 column
  // is one more than its code-point column for everything after it. `positionOf` above
  // is a UTF-16 offset by construction (a JS string index); the last unit of `contains`
  // is the boundary that tells the two counts apart: a server that decoded the column as
  // code points would land one character to the right, past the name. The host side of
  // that is `Wiz/LSP.lean`'s `ofPos` (H2/H3); this is the request the page makes.
  const lastAt = useAt + "contains".length - 1;
  const lastLineStart = text.lastIndexOf("\n", lastAt - 1) + 1;
  const codePointColumn = [...text.slice(lastLineStart, lastAt)].length;
  const lastPos = positionOf(text, lastAt);
  ok(lastPos.character === codePointColumn + 1,
    "the use line is a real UTF-16 case (one astral character before the token)",
    JSON.stringify({ character: lastPos.character, codePointColumn }));
  const hoverLast = await client.hover(uriOf(source), lastPos);
  ok(hoverLast && /contains/.test(JSON.stringify(hoverLast)),
    "hover at the last UTF-16 unit of `contains` (after an astral character)",
    JSON.stringify(hoverLast === undefined ? null : hoverLast).slice(0, 300));
  const defLast = await client.definition(uriOf(source), lastPos);
  const locLast = Array.isArray(defLast) ? defLast[0] : defLast;
  const uriLast = locLast && (locLast.uri || locLast.targetUri);
  ok(!!locLast && String(uriLast).endsWith("Web/Source/Span.wiz"),
    "definition at the last UTF-16 unit of `contains` names Span.wiz",
    JSON.stringify(defLast === undefined ? null : defLast).slice(0, 300));

  // The same question at a position with no identifier (an empty line) is answered
  // `null`, not an error: the reader's "no answer" path.
  const blankLine = text.split("\n").findIndex((line) => line.trim() === "");
  ok(blankLine >= 0, "the bundle's Facts.wiz has an empty line", String(blankLine));
  const blank = await client.hover(uriOf(source), { line: Math.max(0, blankLine), character: 0 });
  ok(blank === null || blank === undefined,
    "a hover with nothing under it is null", JSON.stringify(blank));
} finally {
  if (client) client.close();
  if (srv) await srv.close();
}

console.log(failed === 0
  ? "source live (real wiz lsp): all checks passed"
  : `source live (real wiz lsp): ${failed} failure(s)`);
process.exit(failed === 0 ? 0 : 1);
