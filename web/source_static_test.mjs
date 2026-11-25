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
// **Which bundle.** `scry web` writes it from a `*.c` tree; `scry cs --bundle` writes the
// same format from a `*.cs` tree (a C# bundle has no `ui-trace.json`, since the analysis
// command does not link the reader's runtime). The C-specific section below is skipped,
// with a note, when the bundle has no `taint.c` finding — a C# bundle is not a failure
// here — and a bundle of *neither* shape fails, because a bundle with no known fixture is
// not something this test can vouch for.
//
//   node web/source_static_test.mjs BUNDLE_DIR
"use strict";
import { existsSync, readFileSync } from "node:fs";

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
const perFile = {};
// A file the manifest lists but `data/f/` does not have is a red here, not a crash: the
// reader cannot mount it, so the bundle is incomplete however well its index reads.
for (const f of filesJson.files) {
  const p = join(data, "f", f.id + ".json");
  if (existsSync(p)) perFile[f.id] = readJson(p);
}
const bundle = assemble(manifest, filesJson, findingsJson, perFile);
// `ui-trace.json` is the C export's scripted patch trace; the C# analysis command does
// not link the reader's Loom runtime, so a C# bundle has a plain page instead and the
// trace checks below are skipped.
const hasTrace = existsSync(join(dir, "ui-trace.json"));
const ui = hasTrace ? readJson(join(dir, "ui-trace.json")) : null;
const isCSharp = manifest.language === "csharp" || (filesJson.files || []).some(
  (f) => f.language === "csharp");
const isC = (filesJson.files || []).some((f) => /safe\.c$/.test(f.path)) ||
  (findingsJson.findings || []).some((f) => /taint\.c$/.test(f.path));
if (!isC && !isCSharp) {
  console.log("FAIL: the bundle is neither the C fixtures' nor a C# export " +
    "(no safe.c, no csharp file): this test cannot vouch for it");
  process.exit(1);
}

const run = (oldHtml, patchesJson) => {
  const root = parse(oldHtml);
  applyPatches(root, JSON.parse(patchesJson), parse);
  return serialize(root);
};

// ## 1. The bundle's data

ok(manifest.schema === "scry.web.bundle/1", "the manifest names the bundle schema");
ok(manifest.mode === "static", "the manifest says this is a static export");
// The C fixtures are three files; a C# bundle counts whatever tree it exported.
ok(manifest.counts && manifest.counts.files === filesJson.files.length,
  "the manifest counts the file table", JSON.stringify(manifest.counts));
ok(manifest.hash && manifest.hash.hash === "fnv1a64" &&
  /not a signature/.test(manifest.hash.note || ""),
  "the manifest says FNV is a content identifier, not a signature");

const paths = filesJson.files.map((f) => f.path.replace(/\\/g, "/"));
ok(paths.length === (manifest.counts && manifest.counts.files),
  "every counted file is in the table", JSON.stringify(paths));
ok(paths.every((p) => !p.startsWith("/") && !p.includes("..")),
  "no path escapes the bundle", JSON.stringify(paths));
if (isC) {
  ok(paths.some((p) => p.endsWith("safe.c")) &&
    paths.some((p) => p.endsWith("taint.c")) && paths.some((p) => p.endsWith("xss.c")),
    "the three public fixtures are in the file table", JSON.stringify(paths));
}

for (const f of filesJson.files) {
  const d = perFile[f.id];
  ok(!!d && d.schema === "scry.source.file/1" && typeof d.source === "string" &&
    d.source.length > 0, "file " + f.id + " has its source in data/f/");
  ok(!!f.contentHash && /^[0-9a-f]{16}$/.test(f.contentHash),
    "file " + f.id + " pins a content hash");
}

const findings = findingsJson.findings || [];
ok(findings.length === manifest.counts.findings, "the finding index matches the count",
  findings.length + " vs " + manifest.counts.findings);

// Every finding's span is inside its own file. The reader slices the source by these
// offsets (`Web.Source.Span` is UTF-16, so the bound is the string's own length), and a
// span past the end renders an empty or wrong selection instead of failing loudly: the
// export gate's first mutation is exactly that, so the bound is checked here, not assumed.
for (const f of findings) {
  const d = perFile[f.fileId];
  const len = d && typeof d.source === "string" ? d.source.length : -1;
  ok(!!f.span && f.span.start >= 0 && f.span.stop > f.span.start && f.span.stop <= len,
    "finding " + f.id + " has its span inside its file",
    JSON.stringify(f.span) + " of " + len + " UTF-16 units");
}

ok(findings.every((f) => /^f_[0-9a-f]{16}$/.test(f.id)),
  "every finding has a semantic id", findings.map((f) => f.id).join(" "));
const ids = findings.map((f) => f.id);
ok(new Set(ids).size === ids.length, "the semantic ids are unique");
ok(ids.join(",") === [...ids].sort().join(","), "findings are ordered by semantic id");

// The scripted trace's steps, or none when the bundle has no trace (a C# export).
const traceSteps = () => (ui && ui.steps) || [];

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
//
// The C fixture's finding drives this section; a C# bundle has no `taint.c`, and its
// hover/info answers are `web/source_cs_gate.sh`'s and the C# golden's contract.

if (!taint) {
  console.log("note: no taint.c finding, so the C-specific answer/trace sections are skipped");
  ok(isCSharp, "a bundle without the C fixture's finding is a C# bundle");
}
if (taint) {

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
ok(route("#/def/" + taint.fileId + "@" + taint.spanText).kind === "definition",
  "#/def/<file>@L:C-L:C routes to a definition range");
ok(route("#/f/nope").findingId === "nope", "a missing id still routes (the UI notes it)");

// The trace's route step must actually select the finding in the rendered page.
const routeStep = traceSteps().find((s) => s.name === "route:#/f/" + taint.id);
ok(!!routeStep, "the trace has the #/f/<id> route step");
if (routeStep) {
  const html = run(ui.initial, routeStep.patches);
  ok(html === routeStep.html, "the route patches reproduce the route's SSR");
  ok(html.includes('data-finding="' + taint.id + '"') &&
    html.includes('aria-selected="true"'),
    "#/f/<id> selects the finding in the DOM");
}

// ## 5. The Loom trace: every patch list reproduces the next SSR

ok(ui && ui.schema === "scry.source.ui/1", "the trace names its schema");
// The `route:` steps are entry points from the initial page (a shared link), not part
// of the chained interaction sequence; each is applied to `ui.initial` below.
const chained = traceSteps().filter((s) => !s.name.startsWith("route:"));
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
ok(traceSteps().some((s) => s.name.startsWith("route:")) &&
  traceSteps().filter((s) => s.name.startsWith("route:")).every((s) =>
    run(ui.initial, s.patches) === s.html),
  "every route step is an entry point from the initial page");
ok(traceSteps().some((s) => s.name === "select:" + taint.id),
  "the trace selects the taint finding");

// The hover step's DOM: the card shows the rule and the span.
const hoverStep = traceSteps().find((s) => s.name === "hover:" + taint.id);
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
const infoStep = traceSteps().find((s) => s.name === "info:" + taint.id);
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
  const step = traceSteps().find((s) => s.name === "select:" + xss.id);
  ok(!!step, "the trace has the xss.c select step");
  if (step) {
    ok(!step.html.includes("<script>alert("), "the source's <script> is escaped");
    ok(step.html.includes("&lt;script&gt;"), "the escaped form is on the page");
  }
}

} // `if (taint)`: the C fixture's finding drives sections 2-6.

// ## 7. The host payload

const restored = JSON.parse(bundlePayload(bundle));
ok(restored.schema === "scry.source.bundle-ui/1" &&
  restored.files.length === filesJson.files.length &&
  restored.findings.length === findings.length &&
  (!isC || restored.facts.length > 0),
  "the host payload carries the three tables",
  restored.files.length + "/" + restored.findings.length + "/" + restored.facts.length);

// ## Done

console.log(failed === 0 ? "source static: all checks passed"
  : `source static: ${failed} failure(s)`);
process.exit(failed === 0 ? 0 : 1);
