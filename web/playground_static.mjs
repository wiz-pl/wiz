// Fill the static-complete playground template from the Wiz generator's JSON.
//
// The generator (`web/playground_static_gen.wiz`) is the same Loom renderer the runtime
// uses: `html` is `Page.initial`'s first paint and `hash` is `Loom.LiveApp.ssrHash`, the
// normalised-tree identity the runtime exports as `wiz_loom_ssr_hash`. This script only
// substitutes the two placeholders; it does not render or hash anything itself.
//
//   node web/playground_static.mjs TEMPLATE FIXTURE.json OUT.html
"use strict";
import { readFileSync, writeFileSync } from "node:fs";

const [templatePath, fixturePath, outPath] = process.argv.slice(2);
if (!templatePath || !fixturePath || !outPath) {
  console.error("usage: node web/playground_static.mjs TEMPLATE FIXTURE.json OUT.html");
  process.exit(2);
}

const template = readFileSync(templatePath, "utf-8");
const fixture = JSON.parse(readFileSync(fixturePath, "utf-8"));
const fail = (message) => { console.error("playground-static: " + message); process.exit(1); };

if (typeof fixture.html !== "string" || fixture.html === "") fail("the fixture has no html");
if (typeof fixture.hash !== "string" || !/^t1-[0-9a-f]{8}-\d+-\d+$/.test(fixture.hash)) {
  fail("the fixture has no normalised tree hash (t1-<fnv8>-<length>-<nodes>)");
}
if (!template.includes("<!--wiz-static-->")) fail("the template has no <!--wiz-static--> placeholder");
if (!template.includes("<!--wiz-ssr-->")) fail("the template has no <!--wiz-ssr--> placeholder");
if (!/^[A-Za-z0-9._:-]+$/.test(fixture.hash)) fail("the hash is not safe in an attribute");

const page = template
  .replace("<!--wiz-ssr-->", () => fixture.hash)
  .replace("<!--wiz-static-->", () => fixture.html);
if (/<!--wiz-(?:static|ssr)-->/u.test(page)) fail("a placeholder was not replaced");
if (!page.includes("data-wiz-island") || !page.includes('id="app"')) {
  fail("the generated page has no island mount point");
}
writeFileSync(outPath, page);
console.log("playground-static: " + outPath + " (" + fixture.nodes + " nodes, " + fixture.hash + ")");
