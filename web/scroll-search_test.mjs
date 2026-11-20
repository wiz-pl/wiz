// (11s) The search box's ranking and result rendering, without a browser: the fixture
// `web/search_gen.wiz` renders `lib/Web/Search.wiz` from a two-row index, then the checks
// are the same ones the old JavaScript renderer had.
//   usage: node web/scroll-search_test.mjs FIXTURE.json
import { readFileSync } from "node:fs";
const fixture = JSON.parse(readFileSync(process.argv[2], "utf-8"));
let failed = 0;
function want(name, condition, detail) {
  if (condition) console.log(`ok: ${name}`);
  else { failed++; console.log(`FAIL: ${name}${detail ? "\n  " + detail : ""}`); }
}
want("a name match", fixture.name.includes("Shapes.html#Point"), fixture.name);
want("a doc-comment match", fixture.docs.includes("Shapes.html#Point"), fixture.docs);
want("a signature match", fixture.signature.includes("Shapes.html#area"), fixture.signature);
want("the matched field is shown", fixture.docs.includes('class="where">docs'), fixture.docs);
want("the empty result", fixture.miss.includes("No declarations"), fixture.miss);
if (failed) { console.log(`scroll-search: ${failed} check(s) failed`); process.exit(1); }
console.log("scroll-search: all checks passed");
