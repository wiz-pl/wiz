// The normalised SSR tree hash (`Loom.ssrHash` in Wiz, `wiz_loom_ssr_hash`) under Node:
// the fixture is rendered and hashed by the Wiz compiler (web/framework/hash_gen.wiz),
// and this test pins the identity rules the adopt contract depends on.
//
//   node web/framework/hash_test.mjs FIXTURE.json
//
// Attribute order and white-space spelling are not identity; a real attribute/text
// change is, a key is (it is what a keyed `move` matches), and child order is. A hash
// with the right digest but a different length/node-count witness is a collision and
// must replace, never adopt. The exact `hashHtml` fallback stays exact.
"use strict";
import { readFileSync } from "node:fs";
import { hashHtml, decideAdopt } from "./adopt.js";
import { parse, document as minidom } from "./minidom.mjs";

const fixture = JSON.parse(readFileSync(process.argv[2], "utf-8"));
let failed = 0;
const ok = (cond, what, detail = "") => {
  if (cond) console.log("ok: " + what);
  else { failed++; console.log("FAIL: " + what + (detail ? "\n  " + detail : "")); }
};
const eq = (what, want, got) => ok(Object.is(got, want), what,
  `want ${JSON.stringify(want)}\n  got  ${JSON.stringify(got)}`);

const TREE = /^t1-([0-9a-f]{8})-(\d+)-(\d+)$/;
const match = TREE.exec(fixture.hashA || "");
ok(!!match, "the Wiz hash has the documented t1 form", fixture.hashA);
const [, digest, length, nodes] = match || [];
eq("the witness's node count matches the tree", String(fixture.nodesA), nodes);

// ## Normalisation: the spelling of the same tree is not identity
ok(fixture.htmlA !== fixture.htmlB, "the two fixtures really render differently",
  fixture.htmlA + " vs " + fixture.htmlB);
eq("attribute order and white-space runs collapse to one hash", fixture.hashA, fixture.hashB);
ok(hashHtml(fixture.htmlA) !== hashHtml(fixture.htmlB),
  "the exact hash would have forced a replace (why the tree hash exists)");
ok(String(fixture.canonicalA).includes("A5:class") &&
   String(fixture.canonicalA).includes("A2:id") &&
   String(fixture.canonicalA).indexOf("A5:class") < String(fixture.canonicalA).indexOf("A2:id"),
  "the canonical form sorts attributes by name", fixture.canonicalA);
ok(String(fixture.canonicalA).includes("t3:a b"),
  "the canonical form collapses white space in a text node", fixture.canonicalA);

// ## Real changes differ
ok(fixture.hashA !== fixture.hashC, "a changed attribute/text is a different hash",
  fixture.hashA);
eq("the same keys render the same HTML", fixture.htmlKeyA, fixture.htmlKeyB);
ok(fixture.hashKeyA !== fixture.hashKeyB,
  "a different element key is a different identity (a keyed move matches it)");
ok(fixture.hashOrderAB !== fixture.hashOrderBA,
  "a keyed reorder is a different tree");

// ## The adopt decision: one hash, one decision, never a partial adopt
function island(ssr, html) {
  const root = minidom().createElement("div");
  root.setAttribute("data-wiz-island", "loom/1");
  root.setAttribute("data-wiz-ssr", ssr);
  const frag = parse(html);
  for (const c of [...frag.childNodes]) root.appendChild(c);
  return root;
}

{
  const root = island(fixture.hashA, "<div class=\"x\" id=\"y\">a   b</div>");
  const decision = decideAdopt({ root, html: fixture.htmlA, runtimeHash: fixture.hashA });
  eq("the matching normalised hash adopts", "adopt", decision.mode);
  eq("the reason is hash-match", "hash-match", decision.reason);
}

{
  // Same FNV digest and canonical length, different node count: the witness catches a
  // collision the digest alone would have made an adopt.
  const collision = ["t1", digest, length, String(Number(nodes) + 1)].join("-");
  const root = island(collision, "<div class=\"x\" id=\"y\">a   b</div>");
  const warnings = [];
  const decision = decideAdopt({ root, html: fixture.htmlA, runtimeHash: fixture.hashA,
    warn: (m) => warnings.push(m) });
  eq("a collision in the digest field replaces", "replace", decision.mode);
  eq("the reason is hash-collision", "hash-collision", decision.reason);
  ok(/collides/.test(warnings[0] || ""), "the warning names the collision", warnings[0]);
}

{
  const root = island(fixture.hashA, "<div class=\"x\" id=\"y\">a   b</div>");
  const warnings = [];
  const decision = decideAdopt({ root, html: fixture.htmlA, runtimeHash: fixture.hashC,
    warn: (m) => warnings.push(m) });
  eq("a real change replaces", "replace", decision.mode);
  eq("the reason is hash-mismatch", "hash-mismatch", decision.reason);
}

{
  // A coincidentally equal digest is not enough either when the server and client
  // distances differ in the other witness field.
  const otherLength = ["t1", digest, String(Number(length) + 1), nodes].join("-");
  const root = island(otherLength, "<div class=\"x\" id=\"y\">a   b</div>");
  const decision = decideAdopt({ root, html: fixture.htmlA, runtimeHash: fixture.hashA });
  eq("a length witness collision replaces", "replace", decision.mode);
  eq("the reason is hash-collision", "hash-collision", decision.reason);
}

console.log(failed === 0 ? "normalised hash: all checks passed"
  : `normalised hash: ${failed} failure(s)`);
process.exit(failed === 0 ? 0 : 1);
