// The playground's startup failure path (web/playground.js): when the runtime cannot
// start there is no second UI. The mount point gets a plain text message — the reason,
// and where the build is documented — and nothing is constructed in it.
//
//   node web/playground_start_test.mjs
"use strict";
import { startPage } from "./playground.js";
import { parse, serialize } from "./framework/minidom.mjs";

let failed = 0;
const ok = (cond, what, detail = "") => {
  if (cond) console.log("ok: " + what);
  else { failed++; console.log("FAIL: " + what + (detail ? "\n  " + detail : "")); }
};
const isElement = (n) => !!n.tagName;

// ## A module that is not a Loom runtime: refused before the page is touched
const mismatch = parse("");
const started = await startPage({ root: mismatch, module: async () => ({ not: "a runtime" }) });
ok(started === false, "a foreign module does not start the page");
ok(mismatch.childNodes.length === 1 && !isElement(mismatch.childNodes[0]),
  "no UI is built: the mount point holds text only", serialize(mismatch));
const text = mismatch.textContent;
ok(text.includes("could not start"), "the message says the runtime could not start", text);
ok(text.includes("wiz_loom_init"), "and gives the ABI reason", text);
ok(text.includes("docs/building.md"), "and points at the build documentation", text);
ok(!/<\/?[a-z]/i.test(serialize(mismatch)), "the message is escaped text, not markup",
  serialize(mismatch));

// ## A missing module (not built, or the network refused it): the same one failure path
const missing = parse("");
const started2 = await startPage({
  root: missing,
  module: async () => { throw new Error("wiz-playground-ui.mjs: not found"); },
});
ok(started2 === false, "a missing module does not start the page");
ok(missing.textContent.includes("could not start") &&
  missing.textContent.includes("wiz-playground-ui.mjs: not found"),
  "the message carries the loader's reason", missing.textContent);
ok(missing.childNodes.length === 1 && !isElement(missing.childNodes[0]),
  "and still constructs nothing", serialize(missing));

console.log(failed === 0 ? "playground start: all checks passed" : `playground start: ${failed} failure(s)`);
process.exit(failed === 0 ? 0 : 1);
