/* Run the built `examples/js-loom/loom.wiz` against the fake DOM and assert the
 * operations the Wiz code performed: the elements it created, the attributes and text
 * it set, the listener it registered, and the patch lists it applied on navigation.
 *
 *   wiz build examples/js-loom/loom.wiz --target js -o /tmp/loom.mjs
 *   node examples/js-loom/run.mjs /tmp/loom.mjs
 *
 * Exit code 0 means every assertion passed; a broken route, handler or patch list
 * makes one fail and the exit code 1 (the `=js` test group builds a deliberately
 * broken variant to show that).
 */

import { pathToFileURL } from "node:url";
import { resolve } from "node:path";
import { install, allElements } from "./fake-dom.mjs";

const file = process.argv[2];
if (!file) {
  console.error("usage: node examples/js-loom/run.mjs BUILT.mjs");
  process.exit(2);
}

const dom = install();
const mod = await import(pathToFileURL(resolve(file)).href);

const failures = [];
function expect(cond, what) {
  if (cond) {
    console.log("PASS " + what);
  } else {
    console.log("FAIL " + what);
    failures.push(what);
  }
}

await mod.main();

const els = allElements(dom.root);
const byTag = (t) => els.filter((e) => e.tag === t);
const container = byTag("div")[0];
const nav = byTag("nav")[0];
const main = byTag("main")[0];
const links = byTag("a");

expect(dom.creates.join(",") === "div,nav,a,a,main", "mount created div, nav, two links and main");
expect(container && container.attrs.get("id") === "app", "mount set the container's id to app");
expect(container && container.children.length === 2, "the container has nav and main");
expect(links.length === 2, "mount created two links");
expect(links.every((l) => l.attrs.has("data-path")), "each link has a data-path attribute");
expect(
  links[0].attrs.get("data-path") === "/" && links[1].attrs.get("data-path") === "/about",
  "the links point at / and /about",
);
expect(nav && nav.listeners.length === 1 && nav.listeners[0].event === "click",
  "one delegated click listener is registered on nav");
expect(main && main.text === "Home" && main.attrs.get("data-view") === "home",
  "the initial patch list renders Home");

function click(target) {
  /* the listener is the Wiz closure `fun target => handleClick content target`; applying
   * it to the target and the world runs the IO action (an over-application, which
   * `wizApply` handles) */
  mod.wizApply(nav.listeners[0].fn, [target, 0]);
}

const about = links.find((l) => l.attrs.get("data-path") === "/about");
click(about);
expect(main.text === "About" && main.attrs.get("data-view") === "about",
  "clicking /about applies its patch list");

const missing = {
  tag: "a",
  attrs: new Map([["data-path", "/missing"]]),
  getAttribute(k) {
    return this.attrs.has(k) ? this.attrs.get(k) : "";
  },
};
click(missing);
expect(main.text === "Not found" && main.attrs.get("data-view") === "404",
  "an unknown route applies the 404 patch list");

const patchOps = dom.ops.filter((o) => (o[0] === "text" || o[0] === "attr") && o[1] === "main");
expect(patchOps.length === 6, "three patch lists of two operations each reached main");

if (failures.length > 0) {
  console.log("FAIL loom demo: " + failures.length + " assertion(s) failed");
  process.exitCode = 1;
} else {
  console.log("PASS loom demo: mount, route and patch are Wiz");
}
