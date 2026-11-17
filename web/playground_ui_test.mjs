// The playground's React UI (?ui=react) under Node, in two halves:
//
//   1. The Wiz half: web/test-playground-ui.sh rendered three models with `wiz run`
//      (web/playground-ui-fixture.wiz) and printed their HTML and the patch list between
//      the first two. Applying the patches to the first HTML with web/framework/runtime.js
//      and minidom must reproduce the second exactly — SSR, the Wiz diff and the browser's
//      patch applier agreeing.
//   2. The page half: web/framework/driver.js's `startModel` and web/playground-react.js's
//      `createPageUi`, driven by a fake Wasm module that answers with the same fixture
//      strings. No Emscripten and no browser, but the same code the page runs.
//
//   usage: node web/playground_ui_test.mjs FIXTURE.json
"use strict";
import { readFileSync } from "node:fs";
import { applyPatches } from "./framework/runtime.js";
import { document as minidoc, parse, serialize } from "./framework/minidom.mjs";
import { startModel } from "./framework/driver.js";
import {
  startPageUi, createPageUi, reactUiAvailable, emptyModel, normalizeModel, mergeModel, UI_EXPORTS,
} from "./playground-react.js";

const fixture = JSON.parse(readFileSync(process.argv[2], "utf-8"));
let failed = 0;
function check(name, got, want) {
  const a = JSON.stringify(got), b = JSON.stringify(want);
  if (a === b) console.log(`ok: ${name}`);
  else { failed++; console.log(`FAIL: ${name}\n  want: ${b}\n  got:  ${a}`); }
}
function checkThat(name, condition, detail) {
  if (condition) console.log(`ok: ${name}`);
  else { failed++; console.log(`FAIL: ${name}${detail ? "\n  " + detail : ""}`); }
}

// A Wasm module double: the driver's whole surface is `stringToNewUTF8`, `UTF8ToString`,
// `_free` and the two exports. Strings are kept in a table (a pointer is a key) so the
// argument a Wiz function receives can be inspected. `html` may be a function of the model
// or a queue of answers consumed in call order.
function fakeWasm({ html = () => "", patches = null } = {}) {
  const strings = new Map();
  let next = 0x1000;
  const put = (s) => { const p = next++; strings.set(p, String(s)); return p; };
  const get = (p) => (strings.has(Number(p)) ? strings.get(Number(p)) : null);
  const queue = Array.isArray(html) ? html.slice() : null;
  const wasm = {
    htmlCalls: [],
    patchCalls: [],
    stringToNewUTF8: put,
    UTF8ToString: get,
    _free(p) { strings.delete(Number(p)); },
    _wiz_ui_html(p) {
      const model = get(p);
      wasm.htmlCalls.push(model);
      const answer = queue ? (queue.length ? queue.shift() : "") : html(model);
      return put(answer === undefined || answer === null ? "" : answer);
    },
  };
  if (patches !== null) {
    wasm._wiz_ui_patch = (a, b) => {
      wasm.patchCalls.push([get(a), get(b)]);
      return put(typeof patches === "function" ? patches(get(a), get(b)) : patches);
    };
  }
  return wasm;
}

// ## 1. The Wiz fixture: SSR + patches + the browser's applier

{
  const root = parse(fixture.html0);
  applyPatches(root, JSON.parse(fixture.patches), parse);
  check("fixture: the patches reproduce the next SSR", serialize(root), fixture.html1);
  checkThat("fixture: the first paint has the pane", fixture.html0.includes('class="react-ui"'));
  checkThat("fixture: the goals panel is embedded as HTML", fixture.html0.includes('class="nothing"'));
  checkThat("fixture: the output lines", fixture.html0.includes('class="line val"') && fixture.html0.includes("42"));
  checkThat("fixture: the count is in the output's pane head", fixture.html0.includes("2 lines"));
  checkThat("fixture: the changed goal markup arrives", fixture.html1.includes('class="lsp-view"'));
  checkThat("fixture: an error line's class", fixture.html1.includes('class="line err"'));
  checkThat("fixture: a line that looks like markup is escaped",
    fixture.escaped.includes("&lt;script&gt;") && !fixture.escaped.includes("<script>"), fixture.escaped);
  checkThat("fixture: an empty model is an empty pane", fixture.empty.includes('class="output"'));
  checkThat("fixture: the patch list is not empty", JSON.parse(fixture.patches).length > 0);
}

// ## 2. driver.startModel: mount, then patch

{
  const wasm = fakeWasm({ patches: fixture.patches, html: [fixture.html0, fixture.html1] });
  const root = parse("");
  const driver = startModel(wasm, root, { model: fixture.model0, parse });
  checkThat("driver: mounted", !!driver);
  check("driver: the first paint is the SSR", serialize(root), fixture.html0);
  driver.render(fixture.model1);
  check("driver: a patch reaches the next SSR", serialize(root), fixture.html1);
  check("driver: the model is kept", driver.model(), fixture.model1);
  check("driver: the model passed to Wiz is the page's", wasm.patchCalls, [[fixture.model0, fixture.model1]]);
  check("driver: an unchanged model does not render again", driver.render(fixture.model1), fixture.html1);
  check("driver: renders counted", driver.renders(), 2);
}

// A module with no `wiz_ui_patch` still works: a full mount instead of patches.
{
  const wasm = fakeWasm({ html: (m) => (m === fixture.model1 ? fixture.html1 : fixture.html0) });
  const root = parse("");
  const driver = startModel(wasm, root, { model: fixture.model0, parse });
  driver.render(fixture.model1);
  check("driver: without a patch export, a full mount", serialize(root), fixture.html1);
}
check("driver: no html export, no driver", startModel({}, parse(""), {}), null);

// ## 3. The page's model

check("model: empty", emptyModel(), { count: "", lines: [], goals: "" });
check("model: fields are strings", normalizeModel({ count: 3, lines: [{ kind: "err", text: "x" }], goals: null }),
  { count: "3", lines: [{ kind: "err", text: "x" }], goals: "" });
check("model: lines without text are dropped",
  normalizeModel({ lines: [{ kind: "err" }, { text: "kept" }, null] }).lines, [{ kind: "", text: "kept" }]);
check("model: merge keeps the other fields",
  mergeModel({ count: "1 line", lines: [], goals: "g" }, { goals: "h" }),
  { count: "1 line", lines: [], goals: "h" });
check("model: merge replaces the lines",
  mergeModel({ count: "", lines: [{ kind: "", text: "a" }], goals: "" }, { lines: [{ kind: "val", text: "b" }] }).lines,
  [{ kind: "val", text: "b" }]);
check("model: a bad model is the empty one", normalizeModel(null), emptyModel());

// ## 4. createPageUi: the handle the page holds

{
  const wasm = fakeWasm({
    patches: fixture.patches,
    html: (m) => (m.includes("error: unknown identifier") ? fixture.html1 : fixture.html0),
  });
  const root = parse("");
  const page = createPageUi({
    wasm, root, parse, document: minidoc(), model: { count: "2 lines", lines: [{ kind: "val", text: "42" }], goals: "" },
  });
  checkThat("page: created", !!page);
  page.update({ count: "3 lines · 1 error", lines: [{ kind: "err", text: "error: unknown identifier nope" }] });
  check("page: the model merged", page.model().count, "3 lines · 1 error");
  check("page: the goals were kept", page.model().goals, "");
  check("page: the DOM is the next SSR", serialize(root), fixture.html1);
}

// Without the export the page keeps its DOM path.
check("page: no ui module, no page ui", startPageUi({ wasm: {}, root: parse("") }), null);
check("page: reactUiAvailable", reactUiAvailable({ _wiz_ui_html() {} }), true);
check("page: reactUiAvailable, absent", reactUiAvailable({}), false);
check("page: the export names", UI_EXPORTS, { html: "_wiz_ui_html", patch: "_wiz_ui_patch" });

if (failed) {
  console.log(`playground ui: ${failed} check(s) failed`);
  process.exit(1);
}
console.log("playground ui: all checks passed");
