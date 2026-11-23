// The documentation page's static-complete form, without JavaScript.
//
// `wiz doc` renders a module page to HTML: the declaration's signature, its doc
// comment and the highlighted code are in the page, and the Wasm module only adds
// hover/selection. This test strips every `<script>` and `<style>` and requires the
// page's content to still be there; the browser half (`web/doc_chrome_test.mjs`) checks
// the interactive upgrade.
//
//   node web/docs_static_test.mjs PAGE.html
"use strict";
import { readFileSync } from "node:fs";

const [pagePath] = process.argv.slice(2);
if (!pagePath) {
  console.error("usage: node web/docs_static_test.mjs PAGE.html");
  process.exit(2);
}
const html = readFileSync(pagePath, "utf-8");
const visible = html
  .replace(/<script\b[\s\S]*?<\/script>/gi, "")
  .replace(/<style\b[\s\S]*?<\/style>/gi, "");

let failed = 0;
const ok = (cond, what, detail = "") => {
  if (cond) console.log("ok: " + what);
  else { failed++; console.log("FAIL: " + what + (detail ? "\n  " + detail : "")); }
};

ok(html.length > 0, "the page is non-empty");
ok(/<link rel="stylesheet"/u.test(html), "the stylesheet is linked in the HTML");
for (const want of ["pick", "The colour.", "Nat"]) {
  ok(visible.includes(want), "the JS-off page has " + JSON.stringify(want));
}
ok(/<span class="sig-type" id="sig-\d+">/u.test(visible),
  "the signature is statically rendered (the Wasm module is an enhancement)");
ok(/<span class="sig-type" id="sig-\d+">[\s\S]*?<a href="/u.test(visible),
  "the static signature's constants are real links");
ok(!visible.includes("data-wiz-error"), "the JS-off page carries no mount error");
ok(!/<script\b[\s\S]*?<\/script>/i.test(visible), "the script blocks are stripped");

console.log(failed === 0 ? "docs static: all checks passed" : `docs static: ${failed} failure(s)`);
process.exit(failed === 0 ? 0 : 1);
