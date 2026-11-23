// The migration's contract test: the playground's entry point (web/playground.js) points
// at an element and calls mount; it never touches the runtime's ABI. Every call into the
// runtime goes through mount's `call`, and the runtime module's exports are the driver's
// and the mount's business, not the page's.
//
// There is no second page: `?ui` is gone, no hand-written fallback exists, and the one
// failure path is a text message in the mount point (web/playground_start_test.mjs runs
// it). The page ships a **static-complete** form instead: `#app` is an island filled at
// build time from the same Loom renderer, with `data-wiz-ssr` matching
// `wiz_loom_ssr_hash`; JavaScript adopts it. The behavioural half (the page's SSR,
// steps and patches) is web/playground_page_test.mjs; the mount contract itself is
// web/framework/mount_test.mjs.
//
// This is a source-level check on purpose: it is the one property a page is not allowed
// to erode as features move, and it fails at the first `_wiz_loom_show(...)` that creeps
// back into a page.
//
//   node web/playground_entry_test.mjs
"use strict";
import { readFileSync } from "node:fs";

let failed = 0;
const ok = (cond, what, detail = "") => {
  if (cond) console.log("ok: " + what);
  else { failed++; console.log("FAIL: " + what + (detail ? "\n  " + detail : "")); }
};

const entry = readFileSync(new URL("./playground.js", import.meta.url), "utf-8");
const mount = readFileSync(new URL("./framework/mount.js", import.meta.url), "utf-8");
const html = readFileSync(new URL("./playground.html", import.meta.url), "utf-8");

// ## The entry point is the mount contract
ok(/from "\.\/framework\/mount\.js"/.test(entry),
  "the entry imports the mount contract");
ok(/await mount\(/.test(entry), "and uses it");
ok(!/_wiz_loom_/.test(entry),
  "the entry has no direct ABI calls (all go through mount.call)");
ok(!/stringToNewUTF8|UTF8ToString|\._free\(/.test(entry),
  "the entry does no string marshalling of its own");
ok(!/document\.createElement|replaceChildren|appendChild|innerHTML/.test(entry),
  "the entry builds no DOM (the runtime's patches do)");
ok(/call\("wiz_loom_/.test(entry),
  "its effects use mount's `call`, not the module object");
ok(/getElementById\("widget-list"\)/.test(entry) && /widgetPane/.test(entry),
  "the goals pane hands #widget-list to the widget host");
const exports = [...entry.matchAll(/^export (?:async )?function (\w+)/gm)].map((m) => m[1]);
ok(exports.length === 1 && exports[0] === "startPage",
  "the entry exports exactly one function (startPage)", exports.join(","));
ok(/startPage\(\)/.test(html), "the page's HTML mounts it with startPage()");
ok(/getElementById\("app"\)/.test(entry), "startPage mounts the #app island");

// ## One page, one runtime, with a static-complete first paint
ok(!/playground-static/.test(entry) && !/playground-static\.js/.test(html),
  "there is no hand-written fallback page");
ok(/<div id="app" data-wiz-island=/.test(html),
  "the mount point is an island with a data-wiz-island attribute");
ok(/data-wiz-ssr="<!--wiz-ssr-->"|data-wiz-ssr="t1-/.test(html),
  "the island carries the SSR hash placeholder (or the generated hash)");
ok(/<!--wiz-static-->|<header[ >]/.test(html),
  "the island carries the static render placeholder (or the generated tree)");
ok(/<noscript>/.test(html) && !/<noscript>[\s\S]*id="app"/.test(html),
  "the noscript line is outside the island (it cannot shift a child-index path)");
ok(!/ui=loom|useLoom|params\.get\("ui"\)/.test(entry),
  "there is no ?ui switch (the runtime is the page)");
ok(!/function wireEditor|presetSelect|localStorage/.test(entry),
  "the entry carries none of the old page's state");

// ## The failure path is text in the mount point, not a second UI
ok(/function cannotStart\(root, e\)/.test(entry) &&
  /root\.textContent\s*=/.test(entry),
  "a startup failure is a text message on the mount point");
ok(/could not start/.test(entry) && /docs\/building\.md/.test(entry),
  "the message says what failed and points at the build docs");

// ## mount is the only export (the contract's shape)
const mountExports = [...mount.matchAll(/^export (?:async )?function (\w+)/gm)].map((m) => m[1]);
ok(mountExports.length === 1 && mountExports[0] === "mount",
  "mount.js exports exactly one function", mountExports.join(","));

// ## The runtime's ABI is the documented three exports, plus the page's effect hooks
for (const name of ["_wiz_loom_init", "_wiz_loom_html", "_wiz_loom_step"]) {
  ok(mount.includes(name), `mount expects ${name}`);
}

console.log(failed === 0 ? "playground entry: all checks passed" : `playground entry: ${failed} failure(s)`);
process.exit(failed === 0 ? 0 : 1);
