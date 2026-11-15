// (11s) The search box's ranking and result rendering, without a browser: loads
// web/scroll-search.js with a tiny DOM stub and a two-row index, then checks that a
// name, a doc comment and a signature each find their declaration, and that a miss says
// so. Used by web/test.sh (no emcc or Chromium needed for this part).
import { readFileSync } from "node:fs";
import vm from "node:vm";

const listeners = {};
const box = { value: "", addEventListener: (k, f) => { listeners["box:" + k] = f; } };
const out = { hidden: true, innerHTML: "", contains: () => false };
const document = {
  getElementById: (id) => (id === "search" ? box : id === "results" ? out : null),
  addEventListener: (k, f) => { listeners["doc:" + k] = f; },
  activeElement: null,
};
const window = {
  wizSearchIndex: [
    { n: "Point", m: "Shapes", k: "structure", d: "A point in the *plane*.", s: "Type", u: "Shapes.html#Point" },
    { n: "area", m: "Shapes", k: "def", d: "The area of a circle.", s: "Circle → Nat", u: "Shapes.html#area" },
  ],
};
vm.runInContext(readFileSync(new URL("./scroll-search.js", import.meta.url), "utf8"),
  vm.createContext({ window, document, location: { href: "" } }));
const search = (q) => { box.value = q; listeners["box:input"](); return out.innerHTML; };
const want = (cond, what) => {
  if (!cond) { console.error("scroll-search: " + what); process.exit(1); }
};
want(search("point").includes("Shapes.html#Point"), "a name match");
want(search("plane").includes("Shapes.html#Point"), "a doc-comment match");
want(search("Circle").includes("Shapes.html#area"), "a signature match");
want(search("plane").includes('class="where">docs'), "the matched field is shown");
want(search("zzz").includes("No declarations"), "the empty result");
console.log("scroll-search: all checks passed");
