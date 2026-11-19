// The playground's editor as a Loom component (lib/Web/Editor.wiz), end to end without a
// browser: take the JSON web/playground_editor_gen.wiz printed, parse the initial SSR
// with minidom.mjs, apply the patches runtime.js applies in the page, and require the
// serialized result to equal the next state's SSR. Also pins the driver's event strings
// (the handlers' indices and the payloads they carry), the escaping, and the Run state.
//
//   node web/playground_editor_test.mjs FIXTURE.json
"use strict";
import { readFileSync } from "node:fs";
import { applyPatches } from "./framework/runtime.js";
import { parse, serialize } from "./framework/minidom.mjs";

const fixture = JSON.parse(readFileSync(process.argv[2], "utf-8"));
let failed = 0;
const ok = (cond, what, detail = "") => {
  if (cond) console.log("ok: " + what);
  else { failed++; console.log("FAIL: " + what + (detail ? "\n  " + detail : "")); }
};
const run = (oldHtml, patchesJson) => {
  const root = parse(oldHtml);
  applyPatches(root, JSON.parse(patchesJson), parse);
  return serialize(root);
};

// ## The patches reproduce the next SSR
ok(run(fixture.initial, fixture.initialToTyped) === fixture.typed,
  "typing reproduces the new SSR",
  "got  " + run(fixture.initial, fixture.initialToTyped) + "\nwant " + fixture.typed);
ok(run(fixture.initial, fixture.initialToEnabled) === fixture.enabled,
  "enabling Run reproduces the new SSR",
  "got  " + run(fixture.initial, fixture.initialToEnabled) + "\nwant " + fixture.enabled);

// ## The page's markup (web/playground.html, web/playground.css)
ok(fixture.initial.includes('<section class="pane">'), "the editor is the page's .pane section");
ok(fixture.initial.includes('id="editor"') && fixture.initial.includes('spellcheck="false"'),
  "the textarea keeps its id and spellcheck");
ok(fixture.initial.includes('data-wiz-on-input="0"'),
  "the textarea's input is handler 0 (the driver sends its value to it)", fixture.initial.slice(0, 400));
ok(fixture.initial.includes('data-wiz-on-click="1"'),
  "the Run button's click is handler 1", fixture.initial.slice(0, 400));
ok(fixture.initial.includes("Ctrl/⌘+Enter runs"), "the hint text is unchanged");
ok(fixture.initial.includes('id="run"') && fixture.initial.includes(">Run</button>"),
  "the Run button is there");
ok(fixture.initial.includes('id="count"') && fixture.initial.includes('class="dim"'),
  "the count place is there");
ok(fixture.initial.includes('disabled="disabled"'),
  "Run starts disabled (the engine is not ready)");
ok(!fixture.enabled.includes('disabled="disabled"'), "the page can enable Run");
ok(fixture.counted.includes("2 lines · 1 error"), "the count text is shown verbatim", fixture.counted);

// ## The text (the event's payload) round-trips
ok(fixture.typedText.includes("\ndef twice (n : Nat) : Nat := n + n"),
  "the input payload is the whole text", fixture.typedText);
ok(fixture.multilineText === "a\nb\nc", "a payload's newlines survive", JSON.stringify(fixture.multilineText));
ok(fixture.multiline.includes("a\nb\nc"), "and reach the textarea's text", fixture.multiline);
ok(fixture.escaped.includes("&lt;/textarea&gt;") && !fixture.escaped.includes("</textarea><script>"),
  "the text is escaped, so it cannot close the textarea", fixture.escaped);

// ## Run and stale events
ok(fixture.disabledRuns === "0", "a disabled Run does nothing", fixture.disabledRuns);
ok(fixture.clickRuns === "1", "a click on Run is one request", fixture.clickRuns);
ok(fixture.twiceRuns === "2", "two clicks are two requests", fixture.twiceRuns);
ok(fixture.staleIndexRuns === "0" && fixture.staleIndexText.includes("import Prelude"),
  "a stale handler index cannot click the button", fixture.staleIndexText.slice(0, 80));
ok(fixture.staleEventText.includes("import Prelude"),
  "a stale event name cannot overwrite the text", fixture.staleEventText.slice(0, 80));

console.log(failed === 0 ? "playground editor: all checks passed" : `playground editor: ${failed} failure(s)`);
process.exit(failed === 0 ? 0 : 1);
