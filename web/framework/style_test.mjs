// The browser-free contract test for `web/framework/style.js`.
//
// The model is the CSS DSL design note (`loom-css-dsl.md`, in the workspace notes) and
// `docs/notes/loom-wire-protocol.md`; the wire/adopt rows that this file does *not* test
// are `web/framework/wire_test.mjs`'s. Here we pin:
//
//   * the FNV-1a-32 class-name vectors and the key/slug/public-name refusals;
//   * the typed-value encoder, canonical declaration order, pseudo/media attachments,
//     and the one sorted `class` attribute;
//   * the raw-value refusal fixture, whole-value (never repaired);
//   * the wire/adopt serialisation: a state change is one `setAttr "class"` on the
//     existing patch path, never a second HTML string protocol.
//
//   node web/framework/style_test.mjs
"use strict";
import { readFileSync } from "node:fs";
import {
  SHEET_SCHEMA, CLASS_PREFIX, HL_CLASSES, StyleError,
  fnv1a32, hex8, className, slugOf, Class, Value, Media, Style, Styled, VALIDATION,
} from "./style.js";
import { WIRE_VALIDATION_IDS } from "./wire.js";
import { applyPatches } from "./runtime.js";
import { parse, serialize, document as minidom } from "./minidom.mjs";

let failed = 0;
const ok = (cond, what, detail = "") => {
  if (cond) console.log("ok: " + what);
  else { failed++; console.log("FAIL: " + what + (detail ? "\n  " + detail : "")); }
};
const eq = (what, want, got) => ok(Object.is(got, want), what,
  `want ${JSON.stringify(want)}\n  got  ${JSON.stringify(got)}`);
const eqJson = (what, want, got) => ok(JSON.stringify(got) === JSON.stringify(want), what,
  `want ${JSON.stringify(want)}\n  got  ${JSON.stringify(got)}`);

function throws(what, fn, code) {
  let err = null;
  try { fn(); } catch (e) { err = e; }
  ok(err instanceof StyleError && (code === undefined || err.code === code), what,
    err ? `code ${err.code}: ${err.message}` : "no error");
  return err;
}

const decls = (pairs) => pairs.reduce((s, [p, v]) => Style.merge(s, Style.set(p, v)), Style.empty);

// ## Class names: the pinned function, key shape, public names

eq("FNV-1a-32 of the empty string is the offset basis", "811c9dc5", hex8(fnv1a32("")));
eq("the button golden vector", "lz-button-root-362f3fa2", className("loom/button/root"));
eq("the disabled golden vector", "lz-button-root-8dc21167", className("loom/button/root/disabled"));
eq("the overlay golden vector", "lz-overlay-layer-4becf5f5", className("loom/overlay/layer"));
eq("the goal-row golden vector", "lz-goal-row-03f18365", className("loom/goal/row"));
eq("the selected golden vector", "lz-goal-row-6b73c047", className("loom/goal/row/selected"));
eq("a package key differs only by its hash", "lz-button-root-6150e3c9", className("acme/button/root"));
eq("the slug drops the package and the state", "goal-row", slugOf("loom/goal/row/selected"));
eq("the name is a pure function of the key", className("loom/goal/row"),
  Class.name(Class.of("loom/goal/row")));
// The class is a function of the key, not of the declarations. Two `Styled` values with
// the same key and *different* declarations must render the same class (and their CSS
// must differ, so the declarations really changed); a rename must render a different one.
const quietRow = Styled.of(Class.of("loom/goal/row"), Style.set("color", Value.var("lz-fg")));
const loudRow = Styled.of(Class.of("loom/goal/row"), Style.set("color", Value.var("lz-accent")));
const quietCss = Style.sheet([{ pkg: "loom", styles: [quietRow] }]);
const loudCss = Style.sheet([{ pkg: "loom", styles: [loudRow] }]);
ok(quietCss !== loudCss, "the two declarations really differ", quietCss);
eq("a declaration change does not rename the class",
  Class.name(quietRow.cls), Class.name(loudRow.cls));
ok(Class.name(Class.of("loom/goal/row")) !== Class.name(Class.of("loom/goal/cell")),
  "a rename does change the class");

throws("a key needs a package, component and slot", () => Class.of("loom/button"), "key");
throws("a key's segments are lower-case identifiers", () => Class.of("Loom/button/root"), "key");
throws("a key has at most one state segment", () => Class.of("loom/button/root/extra/more"), "key");
throws("an over-long slug is refused, not truncated",
  () => Class.of("loom/this-component-is-too-long/root"), "slug");
throws("a package cannot claim another package's key",
  () => Class.of("acme/button/root", { pkg: "loom" }), "key-prefix");

eq("a fixed highlight name is literal", "hl-kw", Class.fixed("hl-kw").name);
eq("a payload namespace name is literal", "wz-acme-chart", Class.fixed("wz-acme-chart").name);
for (const name of HL_CLASSES) eq("all eight highlight names are public", name, Class.fixed(name).name);
throws("an unknown hl- name is refused", () => Class.fixed("hl-nope"), "fixed-name");
throws("a scoped name cannot be published as fixed", () => Class.fixed("lz-button-root-362f3fa2"), "fixed-name");
throws("host chrome is not a payload name", () => Class.fixed("wiz-widget-card"), "fixed-name");
throws("an empty wz- suffix is refused", () => Class.fixed("wz-"), "fixed-name");
throws("a wz- suffix is lower-case", () => Class.fixed("wz-Plot"), "fixed-name");

// ## The one sorted class attribute

const row = Class.of("loom/goal/row");
const selected = Class.of("loom/goal/row/selected");
const disabled = Class.of("loom/button/root/disabled");

eqJson("the class attribute sorts rendered names",
  ["class", `${row.name} ${selected.name}`], Class.attr([selected, row]));
eqJson("a list of one is unchanged", ["class", row.name], Class.attr([row]));
eqJson("duplicates by key are dropped", ["class", row.name], Class.attr([row, row]));
eq("Class.if is a list or nothing", 0, Class.if(false, row).length);
eq("Class.all puts the base first", row, Class.all(row, Class.if(true, selected))[0]);
throws("a payload string is never a class", () => Class.attr(["goal"]), "class");

// ## The typed encoder

const button = Styled.of(Class.of("loom/button/root"),
  Style.merge(
    decls([
      ["padding", Value.seq(Value.px(4), Value.px(16))],
      ["border", Value.border(Value.px(1), "solid", Value.var("lz-line"))],
      ["radius", Value.var("lz-r1")],
      ["background", Value.var("lz-panel")],
      ["color", Value.var("lz-fg")],
      ["cursor", Value.keyword("pointer")],
    ]),
    Style.merge(
      Style.hover(Style.set("color", Value.var("lz-accent"))),
      Style.media(Media.reducedMotion, Style.set("transition", Value.keyword("none"))))));

const sheet = Style.sheet([{ pkg: "loom", styles: [button] }]);
const css = sheet.slice(sheet.indexOf("\n") + 1);
eq("the sheet header carries schema, profile and class count",
  `/* generated by web/framework/style.js schema=${SHEET_SCHEMA} profile=web classes=1 */`,
  sheet.split("\n")[0]);
ok(css.startsWith(
  ".lz-button-root-362f3fa2{padding:4px 16px;color:var(--lz-fg);background:var(--lz-panel);" +
  "border:1px solid var(--lz-line);border-radius:var(--lz-r1);cursor:pointer}\n"),
  "declarations are canonical (property order, typed values)", css);
ok(css.includes(".lz-button-root-362f3fa2:hover{color:var(--lz-accent)}"), "a pseudo attaches to the class", css);
ok(css.includes("@media (prefers-reduced-motion:reduce){.lz-button-root-362f3fa2{transition:none}}"),
  "a media query wraps the rule", css);
ok(!/url\s*\(/i.test(sheet) && !sheet.includes("@import") && !sheet.includes("style="),
  "generated CSS has no url(), @import or style=");
eq("one class is one block", 3, css.trim().split("\n").length);

const reordered = Styled.of(Class.of("loom/button/root"),
  Style.merge(
    Style.merge(
      Style.media(Media.reducedMotion, Style.set("transition", Value.keyword("none"))),
      Style.hover(Style.set("color", Value.var("lz-accent")))),
    decls([
      ["cursor", Value.keyword("pointer")],
      ["color", Value.var("lz-fg")],
      ["background", Value.var("lz-panel")],
      ["radius", Value.var("lz-r1")],
      ["border", Value.border(Value.px(1), "solid", Value.var("lz-line"))],
      ["padding", Value.seq(Value.px(4), Value.px(16))],
    ])));
eq("merge's source order does not change the base rule bytes",
  css.split("\n")[0],
  Style.sheet([{ pkg: "loom", styles: [reordered] }]).split("\n")[1]);

// The same property set twice is last-wins, not two declarations.
const lastWins = Styled.of(Class.of("loom/goal/row"),
  Style.merge(Style.set("color", Value.var("lz-fg")), Style.set("color", Value.var("lz-accent"))));
const lastCss = Style.sheet([{ pkg: "loom", styles: [lastWins] }]);
ok(lastCss.includes(".lz-goal-row-03f18365{color:var(--lz-accent)}"), "a later property wins", lastCss);
ok(!lastCss.includes("color:var(--lz-fg)"), "the earlier duplicate is not emitted", lastCss);

const safeRaw = Styled.of(Class.of("loom/overlay/layer"), Style.raw("filter", "blur(2px)"));
ok(Style.sheet([{ pkg: "loom", styles: [safeRaw] }]).includes("filter:blur(2px)"),
  "Style.raw permits a checked declaration shape");

throws("an unknown property is refused", () => Style.set("colour", Value.var("lz-fg")), "prop");
throws("an unknown token prefix is refused", () => Value.var("panel"), "value");
throws("a negative length is refused", () => Value.px(-1), "value");

// ## The refusal fixture: whole value, never repaired

const refused = JSON.parse(readFileSync(new URL("./style_refused.json", import.meta.url), "utf8"));
for (const c of refused.cases) {
  throws("refused: " + c.name, () => Style.raw(c.prop, c.value), c.code);
}

// ## The collision gate (a real FNV-1a pair, pinned)

const collideA = Class.of("loom/g/c/d97n283fsw");
const collideB = Class.of("loom/g/c/cstn367og1");
eq("the pinned pair really collides", "lz-g-c-1262fe8a", Class.name(collideA));
eq("the second key names the same class", Class.name(collideA), Class.name(collideB));
throws("the generator refuses two keys with one name", () => Style.sheet([{
  pkg: "loom",
  styles: [Styled.of(collideA, Style.empty), Styled.of(collideB, Style.empty)],
}]), "collision");
throws("the generator checks a group's package prefix", () => Style.sheet([{
  pkg: "loom",
  styles: [Styled.of(Class.of("acme/button/root"), Style.empty)],
}]), "key-prefix");

// ## The wire/adopt path: one class attribute, one setAttr, no HTML protocol

eq("a sorted class attribute is the SSR value", `${row.name} ${selected.name}`,
  Class.attrValue([selected, row]));
eq("the same state produces no patch", null, Class.patch("0", [row, selected], [selected, row]));
const patch = Class.patch("0", [row], [row, selected]);
eq("a state change is one setAttr", "setAttr", patch.op);
eq("it names the class attribute", "class", patch.name);
eq("its value is the sorted SSR attribute", `${row.name} ${selected.name}`, patch.value);

const root = minidom().createElement("div");
const buttonEl = parse(`<button class="${row.name}" type="button">Run</button>`).childNodes[0];
root.appendChild(buttonEl);
const beforeHtml = serialize(root);
applyPatches(root, [patch], parse);
eq("the class patch updates the existing element", `${row.name} ${selected.name}`,
  buttonEl.getAttribute("class"));
eq("the patch does not replace the node", true, root.childNodes[0] === buttonEl);
eq("the patch does not touch the text", "Run", buttonEl.textContent);
ok(beforeHtml !== serialize(root), "the adopt hash input changes with the class attribute");

// ## The validation table: row 11 only, not a copy of the wire's rows

eq("style.js owns exactly validation row 11", "11", VALIDATION.map((r) => r.id).join(","));
ok(!WIRE_VALIDATION_IDS.includes(11), "row 11 is not duplicated by wire.js");
ok(VALIDATION[0].impl.includes("style.js"), "row 11 names the executable reference");
ok(CLASS_PREFIX === "lz-", "the scoped prefix is lz-");

if (failed) {
  console.log(`\n${failed} failure${failed === 1 ? "" : "s"}`);
  process.exitCode = 1;
} else {
  console.log("\nall style tests passed");
}
