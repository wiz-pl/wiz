// The widget host (`web/widgets.js`) under Node: the two producers' payloads as
// fixtures (`web/fixtures/plot-widget.json`, `web/fixtures/scry-analysis-widget.json`),
// the safety rules, the fallback for an unknown kind, and the DOM mount the standalone
// infoview's widget pane uses. The LSP transport is not involved here; it is stubbed in
// `web/playground_lsp_test.mjs`.
//
//   node web/widgets_test.mjs
"use strict";
import { readFileSync } from "node:fs";
import { document as minidoc } from "./framework/minidom.mjs";
import {
  WIDGET_PREFIX, WIDGET_SCHEMA, parseWidgetPayload, sanitizeWidgetMarkup, renderWidget,
  renderWidgets, widgetCards, widgetCount, mountWidgets,
} from "./widgets.js";

let failed = 0;
function check(name, got, want) {
  if (Object.is(got, want)) console.log(`ok: ${name}`);
  else {
    failed++;
    console.log(`FAIL: ${name}\n  want: ${JSON.stringify(want)}\n  got:  ${JSON.stringify(got)}`);
  }
}
function checkThat(name, condition, detail) {
  if (condition) console.log(`ok: ${name}`);
  else { failed++; console.log(`FAIL: ${name}${detail ? "\n  " + detail : ""}`); }
}

const fixture = (name) => JSON.parse(readFileSync(new URL(`./fixtures/${name}`, import.meta.url), "utf-8"));
const plotBundle = fixture("plot-widget.json");
const scryBundle = fixture("scry-analysis-widget.json");
const plotPayload = WIDGET_PREFIX + JSON.stringify(plotBundle);
const scryPayload = WIDGET_PREFIX + JSON.stringify(scryBundle);
const widget = (text, title = "widget") => ({ kind: "widget", title, text });

const walk = (node, pred, out = []) => {
  if (pred(node)) out.push(node);
  for (const child of node.childNodes || []) walk(child, pred, out);
  return out;
};
const classes = (node) => String((node.getAttribute && node.getAttribute("class")) || "").split(/\s+/);
const byClass = (root, name) => walk(root, (n) => n.getAttribute && classes(n).includes(name));
const textOf = (node) => (node.textContent === undefined ? "" : node.textContent);
const tag = (root, name) => walk(root, (n) => n.tagName === name);

// ## 1. Parsing: the prefix, the schema, and what is not a widget

check("parse: the prefix is stripped", parseWidgetPayload(plotPayload).ok, true);
check("parse: the schema is wiz.widget/1", parseWidgetPayload(plotPayload).bundle.schema, WIDGET_SCHEMA);
check("parse: a bare bundle still parses", parseWidgetPayload(JSON.stringify(plotBundle)).ok, true);
check("parse: an unknown schema is refused",
  parseWidgetPayload(JSON.stringify({ schema: "wiz.widget/2", kind: "plot" })).ok, false);
check("parse: malformed JSON is refused", parseWidgetPayload("WIZ_WIDGET:{no").ok, false);
check("parse: empty text is refused", parseWidgetPayload("").ok, false);

// ## 2. The plot producer: the HTML figure, its title and summary

const plotHtml = renderWidgets([widget(plotPayload, "plot")]);
checkThat("plot: a widget grid", plotHtml.includes('class="wiz-widget-grid"'));
checkThat("plot: the payload's figure is drawn", plotHtml.includes('<figure class="wiz-plot">'));
checkThat("plot: the SVG is inline", plotHtml.includes("<svg"));
checkThat("plot: the title is shown", plotHtml.includes(">Sales</span>"));
checkThat("plot: the kind is shown", plotHtml.includes(">plot</span>"));
checkThat("plot: the summary is shown", plotHtml.includes("plot: Sales (1 series"));
checkThat("plot: no script", !/<script/i.test(plotHtml));
checkThat("plot: no external reference", !/\b(?:href|src)\s*=/i.test(plotHtml));

// An `image/svg+xml` payload with no `html` body is still drawn.
const svgOnly = JSON.stringify({
  schema: WIDGET_SCHEMA, kind: "plot", mimeType: "image/svg+xml", title: "Dot",
  svg: '<svg xmlns="http://www.w3.org/2000/svg" width="8" height="8"><circle cx="4" cy="4" r="3"/></svg>',
});
const svgHtml = renderWidgets([widget(WIDGET_PREFIX + svgOnly, "plot")]);
checkThat("svg: an svg-only payload is drawn", svgHtml.includes("<circle"));
checkThat("svg: the title is the card's", svgHtml.includes('data-widget-title="Dot"'));

// A `text/html` payload is drawn through the same allowlist.
const textHtml = JSON.stringify({
  schema: WIDGET_SCHEMA, kind: "note", mimeType: "text/html", title: "Note",
  html: '<div class="note">hello <strong>world</strong></div>',
});
checkThat("html: a text/html payload is drawn",
  renderWidgets([widget(WIDGET_PREFIX + textHtml)]).includes("<strong>world</strong>"));

// ## 3. Safety: scripts, handlers, external references and styles are refused

const bad = (body) => renderWidgets([widget(WIDGET_PREFIX + JSON.stringify({
  schema: WIDGET_SCHEMA, kind: "plot", title: "bad", html: body,
}))]);
const blocked = (name, body, forbidden) => {
  const html = bad(body);
  const violates = forbidden instanceof RegExp ? forbidden.test(html) : html.includes(forbidden);
  checkThat(name, html.includes("wiz-widget-blocked") && !violates, html);
  checkThat(name + " (kind named)", html.includes(">plot<"));
};
blocked("safety: a script is refused", "<figure><script>alert(1)</script></figure>", /<script/i);
blocked("safety: an event handler is refused", '<svg onload="alert(1)"></svg>', /onload\s*=/i);
blocked("safety: an image src is refused", '<img src="https://example.invalid/x.png">', /example\.invalid/);
blocked("safety: a link href is refused", '<a href="https://example.invalid/">x</a>', /example\.invalid/);
blocked("safety: a style attribute is refused", '<div style="background:url(https://example.invalid/x)">x</div>', /style\s*=/i);
blocked("safety: a script URL is refused", '<div class="javascript:alert(1)">x</div>', /javascript:/i);
blocked("safety: a data URL is refused", '<svg><rect width="1" height="1" fill="data:image/png,x"/></svg>', /data:/i);
blocked("safety: a non-SVG foreignObject is refused", "<svg><foreignObject><div>x</div></foreignObject></svg>", /<foreignObject/i);

// The sanitizer itself: a benign fragment round-trips with entities intact.
const safe = sanitizeWidgetMarkup('<figure class="wiz-plot"><figcaption>A &amp; B</figcaption></figure>');
check("sanitize: a figure is allowed", safe.ok, true);
check("sanitize: entities are not double-escaped", safe.nodes[0].children[0].children[0].text, "A & B");
check("sanitize: an unclosed element is refused", sanitizeWidgetMarkup("<div><span>x</div>").ok, false);
check("sanitize: an unknown element is refused", sanitizeWidgetMarkup("<marquee>x</marquee>").ok, false);
check("sanitize: a url() fill is refused", sanitizeWidgetMarkup('<svg><rect fill="url(#g)"/></svg>').ok, false);
check("sanitize: the SVG namespace is allowed",
  sanitizeWidgetMarkup('<svg xmlns="http://www.w3.org/2000/svg"></svg>').ok, true);
check("sanitize: another namespace is refused",
  sanitizeWidgetMarkup('<svg xmlns="http://example.invalid/"></svg>').ok, false);

// ## 4. The scry producer: the claim, findings and graph counts

const scryHtml = renderWidgets([widget(scryPayload, "scry")]);
checkThat("scry: the claim status is drawn", scryHtml.includes("wiz-scry-refuted") && scryHtml.includes("refuted"));
checkThat("scry: the claim summary is drawn", scryHtml.includes("1 of 2 call_expression"));
checkThat("scry: the finding names its file and node", scryHtml.includes("beta.c") && scryHtml.includes("node 7"));
checkThat("scry: the graph counts are drawn", scryHtml.includes("nodes: 9") && scryHtml.includes("edges: 5"));
checkThat("scry: the bundle's inert button HTML is not inserted", !scryHtml.includes("<button"));
checkThat("scry: no script", !/<script/i.test(scryHtml));

// ## 5. A kind nobody can draw: the fallback names it

const unknown = renderWidgets([widget(WIDGET_PREFIX + JSON.stringify({ schema: WIDGET_SCHEMA, kind: "slider" }), "slider")]);
checkThat("fallback: the kind is named", unknown.includes("cannot render") && unknown.includes("slider"));
checkThat("fallback: the card is marked blocked", unknown.includes("wiz-widget-blocked"));
checkThat("fallback: no body is invented", !unknown.includes("<svg"));

// Two widgets are side by side in one grid (the CSS makes the columns).
const many = renderWidgets([widget(plotPayload, "plot"), widget(scryPayload, "scry")]);
check("many: two cards", (many.match(/class="wiz-widget-card/g) || []).length, 2);
check("many: one grid", (many.match(/class="wiz-widget-grid"/g) || []).length, 1);
check("many: one svg", (many.match(/<svg/g) || []).length, 1);

// ## 6. The DOM pane (`mountWidgets`)

const doc = minidoc();
const pane = doc.createElement("div");
check("dom: two widgets mount", mountWidgets(pane, [widget(plotPayload, "plot"), widget(scryPayload, "scry")], doc), 2);
check("dom: the count attribute", pane.getAttribute("data-widget-count"), "2");
check("dom: two cards", byClass(pane, "wiz-widget-card").length, 2);
check("dom: one SVG element", tag(pane, "svg").length, 1);
checkThat("dom: the plot's title", textOf(pane).includes("Sales"));
checkThat("dom: the claim's status", textOf(pane).includes("refuted"));
checkThat("dom: no script element", tag(pane, "script").length === 0);

// A second cursor replaces the first cursor's widgets.
check("dom: a second mount replaces them", mountWidgets(pane, [widget(plotPayload, "plot")], doc), 1);
check("dom: the old scry card is gone", textOf(pane).includes("beta.c"), false);
check("dom: the new count", pane.getAttribute("data-widget-count"), "1");

// A refused payload mounts as a card, never as script: the pane cannot execute it.
const badPane = doc.createElement("div");
mountWidgets(badPane, [widget(WIDGET_PREFIX + JSON.stringify({
  schema: WIDGET_SCHEMA, kind: "plot", title: "bad",
  html: '<figure><script>alert(1)</script><img src="https://example.invalid/x.png"></figure>',
}))], doc);
check("dom: the refused payload is one card", byClass(badPane, "wiz-widget-card").length, 1);
checkThat("dom: no script element", tag(badPane, "script").length === 0);
checkThat("dom: no image element", tag(badPane, "img").length === 0);
checkThat("dom: no external URL", !textOf(badPane).includes("example.invalid"));

// Empty: the pane says so.
const empty = doc.createElement("div");
check("dom: no widgets", mountWidgets(empty, [], doc), 0);
checkThat("dom: the empty message", textOf(empty).includes("No widgets at the cursor"));

// `renderWidget` is the single-payload form the tests and other clients can use.
check("renderWidget: plot ok", renderWidget(plotPayload).ok, true);
check("renderWidget: unknown kind refused", renderWidget(WIDGET_PREFIX + JSON.stringify({ schema: WIDGET_SCHEMA, kind: "slider" })).ok, false);
check("cards: non-widget items are ignored", widgetCards([{ kind: "message", title: "info", text: "hello" }]).length, 0);
check("count: two widget items", widgetCount([widget(plotPayload), { kind: "message" }, widget(scryPayload)]), 2);

if (failed) {
  console.log(`widgets: ${failed} check(s) failed`);
  process.exit(1);
}
console.log("widgets: all checks passed");
