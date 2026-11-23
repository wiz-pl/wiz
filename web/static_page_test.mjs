// The playground's static-complete page, without a browser.
//
// `web/build-playground.sh` renders `Page.initial` with the same Loom renderer the
// runtime uses, fills `web/playground.html`'s `#app` island and writes the normalised
// tree hash as `data-wiz-ssr`. This test checks the artifact, not the template:
// the whole shell is present with the scripts removed, the island attributes and hash
// are there, the noscript line is outside the island, and nothing has been left as a
// placeholder or a mount error.
//
//   node web/static_page_test.mjs PAGE.html [FIXTURE.json] [TEMPLATE.html]
"use strict";
import { readFileSync } from "node:fs";

const [pagePath, fixturePath, templatePath] = process.argv.slice(2);
if (!pagePath) {
  console.error("usage: node web/static_page_test.mjs PAGE.html [FIXTURE.json] [TEMPLATE.html]");
  process.exit(2);
}
const page = readFileSync(pagePath, "utf-8");
let fixture = null;
if (fixturePath) fixture = JSON.parse(readFileSync(fixturePath, "utf-8"));
const template = templatePath ? readFileSync(templatePath, "utf-8") : null;

let failed = 0;
const ok = (cond, what, detail = "") => {
  if (cond) console.log("ok: " + what);
  else { failed++; console.log("FAIL: " + what + (detail ? "\n  " + detail : "")); }
};
const eq = (what, want, got) => ok(Object.is(got, want), what,
  `want ${JSON.stringify(want)}\n  got  ${JSON.stringify(got)}`);
const count = (s, re) => (s.match(re) || []).length;

// ## The island and its hash
const appOpen = /<div id="app" data-wiz-island="loom\/1" data-wiz-ssr="(t1-[0-9a-f]{8}-\d+-\d+)">/u.exec(page);
ok(!!appOpen, "the page has the #app island and a t1 normalised-tree hash");
if (appOpen && fixture) {
  eq("the server hash is the Wiz generator's hash", fixture.hash, appOpen[1]);
  ok(page.includes(fixture.html), "the island contains the generated Loom first paint");
}
ok(!page.includes("<!--wiz-static-->"), "the static placeholder is filled");
ok(!page.includes("<!--wiz-ssr-->"), "the SSR placeholder is filled");
ok(!page.includes("data-wiz-error"), "the artifact carries no mount error");

// ## The static-complete form: every pane, control and label is in the HTML
const appStart = page.indexOf('<div id="app"');
const noscript = page.indexOf("<noscript>");
const app = appStart >= 0 ? page.slice(appStart, noscript > appStart ? noscript : page.length) : "";
for (const want of ["<header", "<main", "<footer", 'id="editor"', 'id="run"',
  'id="count"', 'id="preset"', 'id="status"', 'id="output"', 'id="goals"',
  'id="engine"', 'class="toolbar"']) {
  ok(app.includes(want), "the static island has " + want, app.slice(0, 120));
}
ok(!/<script[\s>]/i.test(app), "the island contains no script (it is data, not code)");
ok(count(page, /<noscript>/g) === 1, "the page has one noscript line");
ok(noscript > appStart, "the noscript line is outside the island");
ok(/<div id="app"[\s\S]*<\/div>\s*<noscript>/u.test(page),
  "the island closes before the noscript line");
ok(/<noscript>[^<]*needs JavaScript/u.test(page), "the noscript line says JavaScript is needed");

// ## JS off: the same page, with every script removed, still has the product
const visible = page
  .replace(/<script\b[\s\S]*?<\/script>/gi, "")
  .replace(/<style\b[\s\S]*?<\/style>/gi, "");
for (const want of ["Playground", "Example", "Share", "Save", "Reset", "Clear",
  "Output", "Goals", "Run", "the self-hosted checker"]) {
  ok(visible.includes(want), "the JS-off text has " + want);
}
ok(/<textarea[^>]*id="editor"[^>]*>[\s\S]*?def /u.test(visible),
  "the JS-off editor contains the default program");
ok(/<link rel="stylesheet" href="playground\.css">/u.test(page),
  "the stylesheet is linked in the HTML, not injected by a script");
ok(count(page, /<script type="module">/g) === 1, "exactly one module script mounts the runtime");
ok(/startPage\(\)/.test(page), "the module script calls startPage()");

// ## The template is only a template
if (template) {
  ok(template.includes("<!--wiz-static-->"), "the source template has the static placeholder");
  ok(template.includes("<!--wiz-ssr-->"), "the source template has the hash placeholder");
  ok(!template.includes('data-wiz-ssr="t1-'), "the source template has no pre-filled hash");
  ok(!/<header[ >]/.test(template), "the source template has no hand-written page shell");
}

console.log(failed === 0 ? "static page: all checks passed" : `static page: ${failed} failure(s)`);
process.exit(failed === 0 ? 0 : 1);
