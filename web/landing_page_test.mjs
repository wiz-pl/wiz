// The landing page's build-time contract, without a browser or a compiler.
//
// The page must be *made of* the snippet files: each panel's code is the file (after
// the build's span wrappers), each "run in the playground" link decodes back to the
// file's bytes, the tabs and panels point at each other, exactly one tab is selected,
// the copy buttons are a progressive enhancement (`hidden`), and no template
// placeholder or old invented token class survives. The page keeps every destination
// the old landing had.
//
//   usage: node web/landing_page_test.mjs SITE/index.html [ROOT]
"use strict";
import { readFileSync } from "node:fs";
import { dirname, join, resolve } from "node:path";
import { fileURLToPath } from "node:url";

const here = dirname(fileURLToPath(import.meta.url));
const pagePath = process.argv[2];
const root = resolve(process.argv[3] || join(here, ".."));
if (!pagePath) {
  console.error("usage: node web/landing_page_test.mjs SITE/index.html [ROOT]");
  process.exit(2);
}
const html = readFileSync(pagePath, "utf-8");
const manifest = JSON.parse(readFileSync(join(root, "web/landing/snippets.json"), "utf-8"));

let failed = 0;
const ok = (cond, what, detail = "") => {
  if (cond) console.log("ok: " + what);
  else { failed++; console.log("FAIL: " + what + (detail ? "\n  " + detail : "")); }
};

// The page's own entity decoding, used to compare a panel's text with its file.
function decode(text) {
  return text.replace(/&#39;/g, "'").replace(/&quot;/g, '"')
    .replace(/&lt;/g, "<").replace(/&gt;/g, ">").replace(/&amp;/g, "&");
}
const textOf = (fragment) => decode(fragment.replace(/<[^>]*>/g, ""));

function between(text, start, end) {
  const i = text.indexOf(start);
  if (i < 0) return "";
  const j = text.indexOf(end, i + start.length);
  return j < 0 ? "" : text.slice(i + start.length, j);
}
function attr(tag, name) {
  const m = new RegExp("\\b" + name + '="([^"]*)"').exec(tag);
  return m ? m[1] : null;
}

// ## Every snippet is a file, and the page is that file
const panels = new Map();
for (const entry of manifest.snippets) {
  const source = readFileSync(join(root, "web/landing/snippets", entry.file), "utf-8").replace(/\n$/, "");
  const panelId = "/s/" + entry.name;
  const article = between(html, 'id="' + panelId + '"', "</article>");
  panels.set(entry.name, article);
  ok(article.length > 0, entry.name + ": the panel " + panelId + " is on the page");
  if (!article) continue;
  ok(article.includes('role="tabpanel"') && article.includes('aria-labelledby="tab-' + entry.name + '"'),
    entry.name + ": the panel is a tabpanel labelled by its tab");
  const code = between(article, '<code class="language-wiz">', "</code>");
  ok(code.length > 0, entry.name + ": the panel has a wiz code block");
  ok(textOf(code) === source, entry.name + ": the code block is the snippet file, byte for byte",
    textOf(code).slice(0, 120) + " … vs … " + source.slice(0, 120));
  const run = /<a class="run" href="([^"]+)"/u.exec(article);
  ok(!!run, entry.name + ": the panel links to the playground");
  if (run) {
    const url = run[1];
    const m = /^playground\/#code=([A-Za-z0-9_-]+)$/u.exec(url);
    ok(!!m, entry.name + ": the playground link carries #code= (a draft fragment)");
    if (m) {
      const bytes = Buffer.from(m[1].replace(/-/g, "+").replace(/_/g, "/"), "base64");
      ok(bytes.toString("utf-8") === source,
        entry.name + ": the playground link decodes to the snippet file");
    }
  }
  const copy = /<button[^>]*class="copy"[^>]*>/u.exec(article);
  ok(!!copy && /\bdata-copy="\/s\//u.test(copy[0]) && /\bhidden\b/u.test(copy[0]),
    entry.name + ": copy is a hidden progressive enhancement");
  // The tabs: one link per panel, pointing at this panel.
  const tab = new RegExp('<a class="tab"[^>]*id="tab-' + entry.name + '"[^>]*>', "u").exec(html);
  ok(!!tab, entry.name + ": the tab is present");
  if (tab) {
    ok(attr(tab[0], "href") === "#" + panelId, entry.name + ": the tab href is #" + panelId,
      attr(tab[0], "href"));
    ok(attr(tab[0], "aria-controls") === panelId,
      entry.name + ": the tab controls " + panelId);
    ok(attr(tab[0], "role") === "tab", entry.name + ": the tab has role=tab");
  }
}

// ## One selection, one live region, no placeholder
const selected = html.match(/aria-selected="true"/g) || [];
ok(selected.length === 1, "exactly one tab is aria-selected", String(selected.length));
ok(/id="carousel"[^>]*aria-label="Wiz code snippets"/u.test(html),
  "the carousel is a labelled region");
ok(/id="carousel-status"[^>]*aria-live="polite"/u.test(html),
  "the carousel has one polite live region");
ok(!html.includes("<!--wiz-"), "no template placeholder survives the build");
ok(!/\btok-(keyword|number|string|comment)\b/u.test(html),
  "the old invented token classes are gone");
ok(!html.includes("data-wiz-error"), "the static page carries no mount error");

// ## The island, when the build made one
const island = /<div id="quantity-app"([^>]*)>/u.exec(html);
if (island) {
  ok(/data-wiz-island="loom\/1"/u.test(island[1]), "the quantity island is an island");
  ok(/data-wiz-ssr="t1-[0-9a-f]{8}-\d+-\d+"/u.test(island[1]),
    "the island carries a normalised-tree hash", island[1]);
  const inner = between(html, '<div id="quantity-app"', '</section>');
  ok(inner.includes('id="q-select"'), "the island's SSR has the quantity select");
  const qpanels = (html.match(/class="q-panel"/g) || []).length;
  ok(qpanels === 3, "the island's SSR has all three quantity panels", String(qpanels));
} else {
  ok(html.includes('class="q-app q0"'), "without the island JSON the quantity section is the static explainer");
}
ok(/<noscript>[\s\S]*?panels[\s\S]*?<\/noscript>/u.test(html),
  "the noscript line is outside the island and explains the panels");
ok(!/<noscript>[\s\S]*?id="quantity-app"/u.test(html),
  "the noscript line is not inside the island");

// ## Headings and the destinations the page must keep
ok((html.match(/<h1\b/g) || []).length === 1, "exactly one h1");
ok((html.match(/<h2\b/g) || []).length >= 5, "the page has its section h2s");
for (const href of ["docs/", "guide/docs/index.html", "bench/", "playground/",
  "https://github.com/wiz-pl/wiz", "licenses/", "guide/docs/tour.html",
  "guide/docs/install.html"]) {
  ok(html.includes('href="' + href + '"'), "the page keeps the link " + href);
}
ok(/<script src="landing\/carousel\.js" defer><\/script>/u.test(html),
  "the carousel enhancement is loaded with defer");
ok(/<script type="module" src="landing\/app\.js"><\/script>/u.test(html),
  "the island mount is a module script");
// The page's two scripts are the Loom boundary restated: one mount call, no direct
// ABI calls, and no DOM construction in either script.
const appJs = readFileSync(join(root, "web/landing/app.js"), "utf-8");
ok(/import \{ mount \} from "\.\/framework\/mount\.js"/u.test(appJs),
  "app.js imports the mount contract");
ok(/await mount\(el, \{/u.test(appJs), "app.js mounts the island with mount(el, { module })");
ok(!/_wiz_loom_|createElement|innerHTML|appendChild|insertAdjacentHTML/u.test(appJs),
  "app.js calls no ABI directly and builds no DOM");
const carouselJs = readFileSync(join(root, "web/landing/carousel.js"), "utf-8");
ok(!/createElement|innerHTML|appendChild|insertAdjacentHTML/u.test(carouselJs),
  "carousel.js builds no DOM (attributes and focus only)");
ok(html.includes("tower default nightly"), "the install command is on the page");
ok(html.includes("sha256sum -c -"), "the install command still checks its checksum");

console.log(failed === 0 ? "landing page: all checks passed"
  : `landing page: ${failed} failure(s)`);
process.exit(failed === 0 ? 0 : 1);
