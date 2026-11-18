// End-to-end test of the playground's output pane as a Loom component
// (lib/Web/Playground.wiz): take the JSON web/playground_loom_gen.wiz printed, parse
// the "empty" SSR with minidom.mjs, apply each patch list with runtime.js, and require
// the serialized result to equal the next state's SSR exactly. Also pins the `#count`
// text and the classes the page's CSS expects, and checks the value grammar against
// web/playground-values.js (the oracle the page used before the grammar moved to Wiz).
//
// No Wasm and no browser: the pane is pure presentation, so its HTML and its diff are
// the whole contract.
//
//   node web/playground_loom_test.mjs FIXTURE.json
"use strict";
import { readFileSync } from "node:fs";
import { applyPatches } from "./framework/runtime.js";
import { parse, serialize } from "./framework/minidom.mjs";
import { isValue, renderValue } from "./playground-values.js";

const fixture = JSON.parse(readFileSync(process.argv[2], "utf-8"));
let failed = 0;
const ok = (cond, what, detail = "") => {
  if (cond) console.log("ok: " + what);
  else { failed++; console.log("FAIL: " + what + (detail ? "\n  " + detail : "")); }
};

const run = (oldHtml, patchesJson) => {
  const root = parse(oldHtml);
  applyPatches(root, JSON.parse(patchesJson), parse);
  return serialize(root);
};

ok(run(fixture.empty, fixture.emptyToOk) === fixture.ok,
  "an empty pane to two lines reproduces the new SSR",
  "got  " + run(fixture.empty, fixture.emptyToOk) + "\nwant " + fixture.ok);
ok(run(fixture.ok, fixture.okToBad) === fixture.bad,
  "two lines to two errors reproduces the new SSR",
  "got  " + run(fixture.ok, fixture.okToBad) + "\nwant " + fixture.bad);
ok(run(fixture.bad, fixture.badToEmpty) === fixture.empty,
  "two errors back to empty reproduces the new SSR",
  "got  " + run(fixture.bad, fixture.badToEmpty) + "\nwant " + fixture.empty);

// The page's `#count` text, verbatim.
ok(fixture.emptyCount === "0 lines", "an empty pane counts 0 lines", fixture.emptyCount);
ok(fixture.okCount === "2 lines", "two lines count as 2 lines", fixture.okCount);
ok(fixture.badCount === "2 lines · 2 errors", "two errors say so", fixture.badCount);
ok(fixture.single === "1 line", "one line is singular", fixture.single);
ok(fixture.oneErr === "1 line · 1 error", "one error is singular", fixture.oneErr);
ok(fixture.failureCount === "exit code 3", "a failure shows its count text", fixture.failureCount);
ok(fixture.failureStatus === "failed /error", "a failure sets the status pair", fixture.failureStatus);

// The classes the stylesheet hangs off (`web/playground.css`).
ok(fixture.bad.split('class="line err"').length - 1 === 2, "both error lines are `err`", fixture.bad);
ok(fixture.marked.includes('class="line val"'), "a value line keeps the kind it was given", fixture.marked);
ok(!fixture.nasty.includes("<script>"), "output text is escaped", fixture.nasty);
ok(fixture.empty.includes('id="output"') && fixture.empty.includes('aria-live="polite"'),
  "the pane keeps the page's id and aria-live", fixture.empty);

// The value grammar, against web/playground-values.js: `Line.ofText` (Wiz) must decide
// the same kinds and friendly forms as `isValue`/`renderValue` (the page's old
// implementation) for every shape in the corpus.
const oracle = (raw) => {
  const isErrLine = raw.startsWith("error:") || raw.startsWith("parse error");
  if (isErrLine) return { text: raw, kind: "err", title: "" };
  if (!isValue(raw)) return { text: raw, kind: "", title: "" };
  const shown = renderValue(raw);
  return shown === null ? { text: raw, kind: "val raw", title: raw } : { text: shown, kind: "val", title: raw };
};
for (const row of fixture.values) {
  const want = oracle(row.raw);
  ok(row.text === want.text && row.kind === want.kind && row.title === want.title,
    "the value grammar agrees with the oracle: " + JSON.stringify(row.raw),
    `want ${JSON.stringify(want)}\n  got  ${JSON.stringify(row)}`);
  ok(row.cls === (want.kind ? "line " + want.kind : "line"),
    "its class is the page's: " + JSON.stringify(row.raw), row.cls);
}

console.log(failed === 0 ? "playground loom: all checks passed" : `playground loom: ${failed} failure(s)`);
process.exit(failed === 0 ? 0 : 1);
