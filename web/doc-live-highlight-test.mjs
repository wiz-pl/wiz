// The P1 highlight consumer: `Web.InfoTree`'s `wiz.hover/1` and `wiz.highlight/1`
// models, `Hover.card`'s span assembly, and the docs panel's use of the page data.
//   usage: wiz run -I lib web/doc-live-gen.wiz > fixture.json
//          node web/doc-live-highlight-test.mjs fixture.json
import { readFileSync } from "node:fs";
const f = JSON.parse(readFileSync(process.argv[2], "utf-8"));
let failed = 0;
function check(name, cond, detail) {
  if (cond) console.log(`ok: ${name}`);
  else { failed++; console.log(`FAIL: ${name}${detail ? "\n  " + detail : ""}`); }
}
const has = (x, s) => typeof x === "string" && x.includes(s);

check("payload: the Markdown ladder", f.answer === "```wiz\nf : Nat\n```\n\n---\n\nA definition.", f.answer);
check("payload: the card", has(f.payload, 'class="wiz-hover"'), f.payload.slice(0, 300));
check("payload: a const span", has(f.payload, '<span class="hl-const">f</span>'), f.payload);
check("payload: a second const span", has(f.payload, '<span class="hl-const">Nat</span>'), f.payload);
check("payload: the doc text", has(f.payload, "A definition."), f.payload);
check("bad class: whole block plain", !has(f.bad, "hl-") && has(f.bad, "f : Nat"), f.bad);
check("unknown schema: no card", f.wrongSchema === "", f.wrongSchema);
check("panel: the page's spans are used", has(f.panel, '<span class="hl-const">f</span>'), f.panel.slice(0, 500));
check("panel: the code line", has(f.panel, '<pre class="sig">'), f.panel);
check("panel: a section heading", has(f.panel, "Type and documentation"), f.panel);
check("panel: the goals section", has(f.panel, ">Goals<"), f.panel);
check("panel: the diagnostics section", has(f.panel, "Diagnostics"), f.panel);
if (failed) { console.log(`doc-live highlight: ${failed} check(s) failed`); process.exit(1); }
console.log("doc-live highlight: all checks passed");
