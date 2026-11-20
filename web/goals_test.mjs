// The Wiz goals pane, hover card and status line against the fixtures `web/goals_gen.wiz`
// renders. The oracle (`web/framework/goals.mjs`, `framework/hover.mjs`) is what the
// Node transport tests use; this checks the runtime's markup for the same answers.
//   usage: node web/goals_test.mjs FIXTURE.json
import { readFileSync } from "node:fs";
const fixture = JSON.parse(readFileSync(process.argv[2], "utf-8"));
let failed = 0;
function check(name, condition, detail) {
  if (condition) console.log(`ok: ${name}`);
  else { failed++; console.log(`FAIL: ${name}${detail ? "\n  " + detail : ""}`); }
}
const want = (name, text, xs) => check(name, xs.every((x) => text.includes(x)), text.slice(0, 400));

check("status: open", fixture.statusOpen === "connected to ws://127.0.0.1:8765 · wiz 0.1 · wiz infoview v1", fixture.statusOpen);
check("status: idle", fixture.statusIdle === "no language server", fixture.statusIdle);
want("goals: a hypothesis name", fixture.goals, ['class="names"', "n", "b"]);
want("goals: the turnstile", fixture.goals, ["⊢ "]);
want("goals: a tagged constant", fixture.goals, ["tt k-const", "data-ref=", "data-idx="]);
want("goals: a source span", fixture.goals, ['data-span="2:8-2:11"', 'data-span="1:28-4:9"']);
want("goals: the expected type", fixture.goals, ["Expected type", "Nat"]);
want("goals: the diagnostics", fixture.goals, ["mock: unknown identifier", "sev-error", 'data-span="0:0-0:3"']);
want("goals: the handlers", fixture.goals, ["data-wiz-on-click=", "data-wiz-on-keydown="]);
want("goals: a tagged click asks for its span and subterm", fixture.clicked,
  ['"kind":"reveal"', '"payload":"2:8-2:11"', '"kind":"subterm"', '"payload":"5"']);
want("hover: the signature", fixture.hover, ["Nat.add : Nat → Nat → Nat", "Adds two Nats."]);
want("hover: the rule", fixture.hover, ["<hr>"]);
want("hover: a definition label", fixture.hoverLabel, ["Prelude.wiz:7:1"]);
if (failed) { console.log(`goals: ${failed} check(s) failed`); process.exit(1); }
console.log("goals: all checks passed");
