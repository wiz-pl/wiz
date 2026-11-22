// Acceptance test for a static source-reader bundle (P0 of
// wiz-notes/scry-web-design.md):
//
//   scry web scry/tests/fixtures/report --out /tmp/b
//   node web/source_static_test.mjs /tmp/b
//
// It checks the bundle's data (the three public fixtures, semantic ids, UTF-16 spans),
// the one answer schema (`scry.source.answer/1`: hover at taint.c's sink returns its
// rule and span; the info view has one fact row and one finding), the hash route
// (`#/f/<id>` selects the finding), and the Loom half: every scripted interaction's
// patch list is applied to the previous state's SSR with `web/framework/runtime.js` and
// must reproduce the next state's SSR exactly, as `web/playground_loom_test.mjs` does
// for the playground.
//
// No Wasm and no browser: the SSR, the diff and the patch applier are the contract. The
// same `web/source-static.js` answer producer is used by the browser host.
//
//   node web/source_static_test.mjs BUNDLE_DIR
"use strict";
import { readFileSync } from "node:fs";
import { join } from "node:path";
import { applyPatches } from "./framework/runtime.js";
import { parse, serialize } from "./framework/minidom.mjs";
import { assemble, answer, route, bundlePayload, parsePayload } from "./source-static.js";

const dir = process.argv[2];
if (!dir) {
  console.error("usage: node web/source_static_test.mjs BUNDLE_DIR");
  process.exit(2);
}
const readJson = (p) => JSON.parse(readFileSync(p, "utf-8"));
const data = join(dir, "data");

let failed = 0;
const ok = (cond, what, detail = "") => {
  if (cond) console.log("ok: " + what);
  else { failed++; console.log("FAIL: " + what + (detail ? "\n  " + detail : "")); }
};

const manifest = readJson(join(data, "manifest.json"));
const filesJson = readJson(join(data, "files.json"));
const findingsJson = readJson(join(data, "findings.json"));
const ui = readJson(join(dir, "ui-trace.json"));
const perFile = {};
for (const f of filesJson.files) perFile[f.id] = readJson(join(data, "f", f.id + ".json"));
const bundle = assemble(manifest, filesJson, findingsJson, perFile);

const run = (oldHtml, patchesJson) => {
  const root = parse(oldHtml);
  applyPatches(root, JSON.parse(patchesJson), parse);
  return serialize(root);
};

// ## 1. The bundle's data

ok(manifest.schema === "scry.web.bundle/1", "the manifest names the bundle schema");
ok(manifest.mode === "static", "the manifest says this is a static export");
ok(manifest.counts && manifest.counts.files === 3, "the manifest counts three files",
  JSON.stringify(manifest.counts));
ok(manifest.hash && manifest.hash.hash === "fnv1a64" &&
  /not a signature/.test(manifest.hash.note || ""),
  "the manifest says FNV is a content identifier, not a signature");

const paths = filesJson.files.map((f) => f.path.replace(/\\/g, "/"));
ok(paths.length === 3 && paths.some((p) => p.endsWith("safe.c")) &&
  paths.some((p) => p.endsWith("taint.c")) && paths.some((p) => p.endsWith("xss.c")),
  "the three public fixtures are in the file table", JSON.stringify(paths));

for (const f of filesJson.files) {
  const d = perFile[f.id];
  ok(!!d && d.schema === "scry.source.file/1" && typeof d.source === "string" &&
    d.source.length > 0, "file " + f.id + " has its source");
  ok(!!f.contentHash && /^[0-9a-f]{16}$/.test(f.contentHash),
    "file " + f.id + " pins a content hash");
}

const findings = findingsJson.findings || [];
ok(findings.length === manifest.counts.findings, "the finding index matches the count",
  findings.length + " vs " + manifest.counts.findings);
ok(findings.every((f) => /^f_[0-9a-f]{16}$/.test(f.id)),
  "every finding has a semantic id", findings.map((f) => f.id).join(" "));
const ids = findings.map((f) => f.id);
ok(new Set(ids).size === ids.length, "the semantic ids are unique");
ok(ids.join(",") === [...ids].sort().join(","), "findings are ordered by semantic id");

const byPath = (suffix) => findings.filter((f) => f.path.replace(/\\/g, "/").endsWith(suffix));
ok(byPath("safe.c").length === 0, "safe.c has no finding");
ok(byPath("taint.c").length === 1, "taint.c has one finding");
ok(byPath("xss.c").length === 1, "xss.c has one finding");

const taint = byPath("taint.c")[0];
ok(!!taint && taint.rule === "command-injection",
  "taint.c's finding is command-injection", taint && taint.rule);
ok(!!taint && taint.span && taint.span.stop > taint.span.start,
  "the finding has a non-empty UTF-16 span", taint && JSON.stringify(taint.span));
ok(!!taint && /^[0-9]+:[0-9]+-[0-9]+:[0-9]+$/.test(taint.spanText || ""),
  "the span also carries its display text", taint && taint.spanText);
ok(!!taint && typeof taint.checked === "boolean",
  "the finding carries its derivation status", String(taint && taint.checked));
ok(!!taint && "claimId" in taint && taint.claimId === "",
  "claimId is present and empty (certificates are P1)");

// Every finding is in its file's JSON and is listed in the SSR by semantic id.
for (const f of findings) {
  const d = perFile[f.fileId];
  ok(!!d && (d.findings || []).some((x) => x.id === f.id),
    "finding " + f.id + " is in its file's JSON");
  ok(ui.initial.includes('data-finding="' + f.id + '"'),
    "the first paint lists " + f.id);
}

// ## 2. The answer schema (hover, from precomputed facts)

ok(taint && taint.fileId, "the finding names its file id");
const payload = taint ? taint.fileId + "@" + taint.span.start + "-" + taint.span.stop : "";
const at = parsePayload(payload);
ok(!!at && at.fileId === taint.fileId && at.start === taint.span.start,
  "the request payload is FILEID@START-STOP", payload);

const hover = JSON.parse(answer(bundle, "hover", payload));
ok(hover.schema === "scry.source.answer/1", "the hover answer names the schema");
ok(hover.request === "hover" && hover.status === "ok", "the hover answer is an ok hover");
ok(hover.rule === "command-injection", "hovering taint.c's sink returns its rule",
  hover.rule);
ok(!!hover.span && hover.span.start === taint.span.start &&
  hover.span.stop === taint.span.stop, "hovering the sink returns its span",
  JSON.stringify(hover.span));
ok(hover.spanText === taint.spanText, "the hover carries the span's display text",
  hover.spanText);
ok(hover.findingId === taint.id, "the hover names the finding");
ok(Array.isArray(hover.lines) && hover.lines.length >= 3 &&
  hover.lines.some((l) => l.code === true),
  "the hover card has text lines and the sink's code");
ok(!JSON.stringify(hover).includes("/workspace"),
  "the answer holds no checkout path");

// ## 3. The info view (one fact row, one finding at the sink)

const info = JSON.parse(answer(bundle, "info", payload));
ok(info.schema === "scry.source.answer/1" && info.request === "info" &&
  info.status === "ok", "the info answer names the schema and is ok");
ok(info.rows.length === 1, "the info view has one fact row at the sink",
  JSON.stringify(info.rows.map((r) => r.kind)));
ok(info.rows[0] && info.rows[0].kind === "sink", "the fact row is the sink fact");
ok(info.findings.length === 1 && info.findings[0].id === taint.id,
  "the info view has one finding at the sink");

// A node with no fact is an empty, honest answer, not an error.
const empty = JSON.parse(answer(bundle, "info", taint.fileId + "@0-1"));
ok(empty.status === "ok" && empty.rows.length === 0 && empty.findings.length === 0,
  "a node with no fact answers ok with no rows");

// ## 4. The hash route

const target = route("#/f/" + taint.id);
ok(target.kind === "finding" && target.findingId === taint.id,
  "#/f/<id> routes to the finding", JSON.stringify(target));
ok(route("#/src/" + taint.fileId + "@" + taint.spanText).kind === "source",
  "#/src/<file>@L:C-L:C routes to a source span");
ok(route("#/f/nope").findingId === "nope", "a missing id still routes (the UI notes it)");

// The trace's route step must actually select the finding in the rendered page.
const routeStep = (ui.steps || []).find((s) => s.name === "route:#/f/" + taint.id);
ok(!!routeStep, "the trace has the #/f/<id> route step");
if (routeStep) {
  const html = run(ui.initial, routeStep.patches);
  ok(html === routeStep.html, "the route patches reproduce the route's SSR");
  ok(html.includes('data-finding="' + taint.id + '"') &&
    html.includes('aria-selected="true"'),
    "#/f/<id> selects the finding in the DOM");
}

// ## 5. The Loom trace: every patch list reproduces the next SSR

ok(ui.schema === "scry.source.ui/1", "the trace names its schema");
// The `route:` steps are entry points from the initial page (a shared link), not part
// of the chained interaction sequence; each is applied to `ui.initial` below.
const chained = (ui.steps || []).filter((s) => !s.name.startsWith("route:"));
let current = ui.initial;
let replayed = 0;
for (const step of chained) {
  const next = run(current, step.patches);
  if (next !== step.html) {
    failed++;
    console.log("FAIL: trace step " + step.name + " reproduces its SSR");
    console.log("  got  " + next.slice(0, 400));
    console.log("  want " + step.html.slice(0, 400));
  }
  current = step.html;
  replayed++;
}
ok(replayed >= 3, "the trace replays the scripted interactions", String(replayed));
ok((ui.steps || []).some((s) => s.name.startsWith("route:")) &&
  (ui.steps || []).filter((s) => s.name.startsWith("route:")).every((s) =>
    run(ui.initial, s.patches) === s.html),
  "every route step is an entry point from the initial page");
ok((ui.steps || []).some((s) => s.name === "select:" + taint.id),
  "the trace selects the taint finding");

// The hover step's DOM: the card shows the rule and the span.
const hoverStep = (ui.steps || []).find((s) => s.name === "hover:" + taint.id);
ok(!!hoverStep, "the trace has the hover step");
if (hoverStep) {
  ok(hoverStep.html.includes('class="wiz-hover"'), "the hover step renders a card");
  ok(hoverStep.html.includes("command-injection"),
    "the hover card shows the rule");
  ok(hoverStep.html.includes(taint.spanText),
    "the hover card shows the span", taint.spanText);
  ok(hoverStep.html.includes('data-rule="command-injection"'),
    "the card's host carries the rule for a test");
}

// The info step's DOM: one fact row and one finding.
const infoStep = (ui.steps || []).find((s) => s.name === "info:" + taint.id);
ok(!!infoStep, "the trace has the info step");
if (infoStep) {
  const rows = (infoStep.html.match(/class="fact-row"/g) || []).length;
  const fs = (infoStep.html.match(/class="fact-finding"/g) || []).length;
  ok(rows === 1, "the info view shows one fact row", String(rows));
  ok(fs === 1, "the info view shows one finding", String(fs));
  ok(infoStep.html.includes("Info"), "the info view names itself");
}

// ## 6. Escaping: the source is untrusted text

const xss = byPath("xss.c")[0];
if (xss) {
  const step = (ui.steps || []).find((s) => s.name === "select:" + xss.id);
  ok(!!step, "the trace has the xss.c select step");
  if (step) {
    ok(!step.html.includes("<script>alert("), "the source's <script> is escaped");
    ok(step.html.includes("&lt;script&gt;"), "the escaped form is on the page");
  }
}

// ## 7. The host payload

const restored = JSON.parse(bundlePayload(bundle));
ok(restored.schema === "scry.source.bundle-ui/1" &&
  restored.files.length === 3 && restored.findings.length === findings.length &&
  restored.facts.length > 0,
  "the host payload carries the three tables",
  restored.files.length + "/" + restored.findings.length + "/" + restored.facts.length);

// ## Done

console.log(failed === 0 ? "source static: all checks passed"
  : `source static: ${failed} failure(s)`);
process.exit(failed === 0 ? 0 : 1);
