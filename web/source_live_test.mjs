// The real-server half of the live reader's proof, without a browser: start
// `wiz lsp --ws`, open the bundle's Wiz files with the bundle's text, and ask the exact
// two questions the page asks (`textDocument/hover`, `textDocument/definition`) at the
// exact token the browser smoke uses (`Source.Span.show` in `lib/Web/Source/Model.wiz`).
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
const model = bySuffix("Web/Source/Model.wiz");
const span = bySuffix("Web/Source/Span.wiz");
if (!model || !span) {
  console.error("source live: the bundle has no Web/Source/{Model,Span}.wiz (--source them)");
  process.exit(2);
}
const modelData = readJson(join(bundle, "data", "f", model.id + ".json"));
const spanData = readJson(join(bundle, "data", "f", span.id + ".json"));
const text = modelData.source;

// The bundle's own paths, as the checkout sees them (the same rule `source-live.js` is
// given by `?lspRoot=`).
const uriOf = (meta) => fileUri(root, meta.path);

// A UTF-16 offset as an LSP position (0-based line, UTF-16 character). Test-local.
function positionOf(source, offset) {
  const before = source.slice(0, offset);
  const line = (before.match(/\n/g) || []).length;
  const lineStart = before.lastIndexOf("\n") + 1;
  return { line, character: offset - lineStart };
}

const needle = "show i span";
const marker = "Source.Span.show i span";
const markerAt = text.indexOf(marker);
const useAt = markerAt + marker.indexOf(needle);
ok(markerAt >= 0, "the bundle's Model.wiz has the `Source.Span.show` use", String(markerAt));

const defLine = spanData.source.split("\n")
  .findIndex((line) => line.includes("def Source.Span.show"));
ok(defLine >= 0, "the bundle's Span.wiz has `def Source.Span.show`", String(defLine));

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
    requestTimeout: 30000,
  });
  for (const meta of [model, span]) {
    const data = meta === model ? modelData : spanData;
    client.openDocument(uriOf(meta), data.source, { languageId: "wiz" });
  }
  await client.connect();
  ok(client.isOpen, "the real wiz lsp accepts the connection");

  const pos = positionOf(text, useAt);
  const hover = await client.hover(uriOf(model), pos);
  const hoverText = hover ? JSON.stringify(hover) : "null";
  ok(hover && /show/.test(hoverText), "the real server answers a hover on `show`",
    hoverText.slice(0, 300));
  ok(hover && /contents/.test(hoverText), "the hover is the LSP contents shape",
    hoverText.slice(0, 120));

  const definition = await client.definition(uriOf(model), pos);
  const target = Array.isArray(definition) ? definition[0] : definition;
  ok(!!target, "the real server answers a definition on `show`",
    JSON.stringify(definition).slice(0, 300));
  const targetUri = target && (target.uri || target.targetUri);
  const range = target && (target.range || target.targetSelectionRange || target.targetRange);
  ok(!!targetUri && String(targetUri).endsWith("Web/Source/Span.wiz"),
    "the definition names Span.wiz", String(targetUri));
  ok(!!range && range.start && range.start.line === defLine,
    "the definition range is `def Source.Span.show`'s line",
    range ? JSON.stringify(range) : "no range");

  // The same question at a position with no identifier (an empty line) is answered
  // `null`, not an error: the reader's "no answer" path.
  const blankLine = text.split("\n").findIndex((line) => line.trim() === "");
  ok(blankLine >= 0, "the bundle's Model.wiz has an empty line", String(blankLine));
  const blank = await client.hover(uriOf(model), { line: Math.max(0, blankLine), character: 0 });
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
