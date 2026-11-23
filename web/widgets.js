// The widget host: `WIZ_WIDGET:` payloads (the Loom schema `wiz.widget/1`) as DOM,
// for the standalone infoview's widget pane and the playground's goals panel.
//
// A payload is a JSON object with a `schema` of `wiz.widget/1`. The two producers in
// the tree today are:
//
//   * `#plot expr` (`lib/Plot.wiz` `Plot.widget`): `kind: "plot"`,
//     `mimeType: "image/svg+xml"`, a self-contained `svg` and an `html` figure;
//   * `Scry.analysisDisplay` (`scry/src/Scry/AnalysisFile.wiz`): `kind:
//     "scry.analysis"`, `mimeType: "text/html"`, plus a `scry.analysis/1` extension
//     (`claim`, `findings`, `graph`) that this module draws as a claim card.
//
// **Safety.** Payload text is never assigned to `innerHTML` and no payload string is
// inserted verbatim. The markup is parsed into a tiny tree, checked against an
// allowlist of elements and attributes, and rebuilt from that tree with `createElement`
// / `createElementNS` / `createTextNode` (or serialized back for the panel's string
// API). Refused outright: scripts, styles, iframes/objects/embeds, form controls,
// foreignObject/image/use, event handlers (`on*`), `href`/`src`/`style` attributes,
// `url(...)`, `javascript:`, `vbscript:`, `data:`, and anything not on the allowlist.
// A payload that cannot be drawn becomes a card naming its kind and the reason.
//
// **A new kind.** A producer only has to emit `schema: "wiz.widget/1"`, a `kind` and
// either an `html`/`svg` body (drawn by this host) or a structured extension that a
// renderer here knows how to draw (as `scry.analysis/1` is). Add the renderer in
// `renderWidget` below, a fixture under `web/fixtures/`, and a case in
// `web/widgets_test.mjs`; no page or transport changes are needed.
"use strict";

export const WIDGET_PREFIX = "WIZ_WIDGET:";
export const WIDGET_SCHEMA = "wiz.widget/1";
export const SVG_NS = "http://www.w3.org/2000/svg";

// ## Text and trees

export function escapeHtml(value) {
  return String(value === null || value === undefined ? "" : value)
    .replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;")
    .replace(/"/g, "&quot;").replace(/'/g, "&#39;");
}

const escapeAttr = escapeHtml;

const text = (value) => ({ type: "text", text: String(value === null || value === undefined ? "" : value) });
const element = (tag, attrs = [], children = [], options = {}) => ({
  type: "el", tag, attrs, children, svg: !!options.svg,
});

// Serialize a checked tree (the panel's string API). Text and attribute values are
// escaped here, so a node's text is always data, never markup.
export function serializeNodes(nodes) {
  const out = [];
  const write = (node) => {
    if (!node) return;
    if (node.type === "text") { out.push(escapeHtml(node.text)); return; }
    out.push("<" + node.tag);
    for (const [name, value] of node.attrs) out.push(" " + name + "=\"" + escapeAttr(value) + "\"");
    out.push(">");
    // The host only emits these as void HTML elements; SVG's self-closing elements are
    // written with an explicit close, which is valid SVG and valid HTML.
    if (node.tag === "br" || node.tag === "hr") return;
    for (const child of node.children) write(child);
    out.push("</" + node.tag + ">");
  };
  for (const node of nodes) write(node);
  return out.join("");
}

// Append a checked tree to a real (or test-double) DOM. SVG elements go in the SVG
// namespace when the document can make one; `web/framework/minidom.mjs` cannot, so the
// tests get plain elements with the same tag names and attributes.
export function appendNodes(doc, parent, nodes) {
  for (const node of nodes) {
    if (node.type === "text") { parent.appendChild(doc.createTextNode(node.text)); continue; }
    const el = node.svg && typeof doc.createElementNS === "function"
      ? doc.createElementNS(SVG_NS, node.tag)
      : doc.createElement(node.tag);
    for (const [name, value] of node.attrs) {
      if (typeof el.setAttribute === "function") el.setAttribute(name, value);
    }
    if (node.children.length) appendNodes(doc, el, node.children);
    parent.appendChild(el);
  }
  return parent;
}

// ## Parsing and sanitising markup

const HTML_TAGS = new Set([
  "figure", "figcaption", "div", "span", "p", "h1", "h2", "h3", "h4", "ul", "ol",
  "li", "dl", "dt", "dd", "table", "thead", "tbody", "tfoot", "tr", "th", "td",
  "pre", "code", "strong", "em", "b", "i", "br", "hr", "section", "article",
  "header", "footer", "small", "sub", "sup", "details", "summary", "blockquote",
]);

const SVG_TAGS = new Set([
  "svg", "g", "defs", "symbol", "path", "rect", "circle", "ellipse", "line",
  "polyline", "polygon", "text", "tspan", "title", "desc", "clippath",
  "lineargradient", "radialgradient", "stop", "pattern", "mask", "marker",
]);

// Attribute names are lower-cased for the check (SVG's `viewBox` is emitted as written).
const ATTRS = new Set([
  "class", "id", "role", "aria-label", "aria-hidden", "aria-describedby",
  "width", "height", "viewbox", "preserveaspectratio", "x", "y", "x1", "y1", "x2",
  "y2", "cx", "cy", "r", "rx", "ry", "d", "points", "fill", "fill-opacity",
  "fill-rule", "stroke", "stroke-width", "stroke-linejoin", "stroke-linecap",
  "stroke-dasharray", "stroke-dashoffset", "stroke-opacity", "opacity", "transform",
  "font-family", "font-size", "font-weight", "font-style", "text-anchor",
  "dominant-baseline", "alignment-baseline", "letter-spacing", "word-spacing",
  "stop-color", "stop-opacity", "offset", "gradientunits", "gradienttransform",
  "marker-start", "marker-mid", "marker-end", "xmlns",
]);

const URL_ATTRS = new Set([
  "fill", "stroke", "marker-start", "marker-mid", "marker-end", "clip-path", "mask",
]);

const SELF_CLOSABLE_HTML = new Set(["br", "hr"]);

const decodeEntities = (value) => String(value).replace(
  /&(#x[0-9a-fA-F]+|#[0-9]+|[a-zA-Z]+);/g,
  (match, body) => {
    if (body[0] === "#") {
      const n = body[1] === "x" ? parseInt(body.slice(2), 16) : parseInt(body.slice(1), 10);
      return Number.isFinite(n) ? String.fromCodePoint(n) : match;
    }
    const named = { amp: "&", lt: "<", gt: ">", quot: "\"", apos: "'", nbsp: "\u00a0" };
    return Object.prototype.hasOwnProperty.call(named, body) ? named[body] : match;
  });

const CLEAN_CONTROL = /[\u0000-\u0008\u000b\u000c\u000e-\u001f]/g;

function tagEnd(markup, at) {
  let quote = null;
  for (let i = at; i < markup.length; i++) {
    const c = markup[i];
    if (quote) { if (c === quote) quote = null; }
    else if (c === "\"" || c === "'") quote = c;
    else if (c === ">") return i;
  }
  return -1;
}

// Parse a fragment into checked `{type: "text"}` / `{type: "el"}` nodes. On anything
// outside the allowlist it returns `{ok: false, error}` and no nodes: refusing is safer
// than trying to repair a hostile payload.
export function sanitizeWidgetMarkup(markup) {
  if (typeof markup !== "string" || !markup.trim()) return { ok: false, error: "empty payload" };
  if (markup.length > 2000000) return { ok: false, error: "payload is too large" };
  const root = [];
  const stack = [{ tag: null, svg: false, children: root }];
  const top = () => stack[stack.length - 1];
  let i = 0;

  const fail = (error) => ({ ok: false, error });

  while (i < markup.length) {
    if (markup[i] !== "<") {
      let j = markup.indexOf("<", i);
      if (j < 0) j = markup.length;
      const data = decodeEntities(markup.slice(i, j)).replace(CLEAN_CONTROL, "");
      if (data) top().children.push(text(data));
      i = j;
      continue;
    }
    if (markup.startsWith("<!--", i)) {
      const j = markup.indexOf("-->", i + 4);
      if (j < 0) return fail("unterminated comment");
      i = j + 3;
      continue;
    }
    if (markup[i + 1] === "!" || markup[i + 1] === "?") return fail("declarations are not allowed");
    if (markup[i + 1] === "/") {
      const end = markup.indexOf(">", i);
      if (end < 0) return fail("unterminated close tag");
      const tag = markup.slice(i + 2, end).trim().toLowerCase();
      if (stack.length <= 1 || !top().tag) return fail("close tag without an open element");
      if (top().tag.toLowerCase() !== tag) return fail("close tag does not match <" + top().tag + ">");
      stack.pop();
      i = end + 1;
      continue;
    }
    const end = tagEnd(markup, i + 1);
    if (end < 0) return fail("unterminated tag");
    let body = markup.slice(i + 1, end);
    i = end + 1;
    const selfClose = /\/\s*$/.test(body);
    if (selfClose) body = body.replace(/\/\s*$/, "");
    const nameMatch = /^([A-Za-z][A-Za-z0-9:_-]*)/.exec(body);
    if (!nameMatch) return fail("bad tag");
    const rawTag = nameMatch[1];
    const lower = rawTag.toLowerCase();
    if (lower === "foreignobject" || lower === "image" || lower === "script" ||
        lower === "style" || lower === "iframe" || lower === "object" ||
        lower === "embed" || lower === "use" || lower === "a" ||
        lower === "form" || lower === "input" || lower === "button" ||
        lower === "textarea" || lower === "select" || lower === "option" ||
        lower === "link" || lower === "meta" || lower === "base" ||
        lower === "audio" || lower === "video" || lower === "source" ||
        lower === "animate" || lower === "animatemotion" ||
        lower === "animatetransform" || lower === "set") {
      return fail("element <" + rawTag + "> is not allowed");
    }
    if (!HTML_TAGS.has(lower) && !SVG_TAGS.has(lower)) {
      return fail("element <" + rawTag + "> is not allowed");
    }
    const attrs = [];
    const rest = body.slice(nameMatch[0].length);
    const attrRe = /([^\s"'=<>\/]+)(?:\s*=\s*("([^"]*)"|'([^']*)'|([^\s"'=<>`]+)))?/g;
    let a;
    while ((a = attrRe.exec(rest))) {
      const name = a[1];
      const lname = name.toLowerCase();
      const value = decodeEntities(a[3] !== undefined ? a[3]
        : a[4] !== undefined ? a[4] : a[5] !== undefined ? a[5] : "").replace(CLEAN_CONTROL, "");
      if (lname.startsWith("on")) return fail("event handler " + name + " is not allowed");
      if (lname === "href" || lname === "src" || lname === "srcset" ||
          lname === "xlink:href" || lname === "style" || lname === "action" ||
          lname === "formaction" || lname === "background" || lname === "poster" ||
          lname === "xml:base" || lname === "xmlns:xlink") {
        return fail("attribute " + name + " is not allowed");
      }
      if (lname !== "xmlns" && !ATTRS.has(lname) && !lname.startsWith("data-") &&
          !lname.startsWith("aria-")) {
        return fail("attribute " + name + " is not allowed");
      }
      if (lname === "xmlns" && value !== SVG_NS) return fail("only the SVG namespace is allowed");
      const compact = value.replace(/[\s\u0000-\u001f]+/g, " ").toLowerCase();
      if (compact.includes("javascript:") || compact.includes("vbscript:")) {
        return fail("a script URL is not allowed");
      }
      if (URL_ATTRS.has(lname) && (compact.includes("url(") || compact.includes("data:"))) {
        return fail("an external reference is not allowed");
      }
      attrs.push([name, value]);
    }
    if (rest.replace(attrRe, "").trim()) return fail("bad attributes in <" + rawTag + ">");
    const svg = top().svg || lower === "svg";
    const node = element(lower === "svg" ? "svg" : rawTag, attrs, [], { svg });
    top().children.push(node);
    if (!selfClose && !SELF_CLOSABLE_HTML.has(lower)) {
      stack.push({ tag: lower === "svg" ? "svg" : rawTag, svg, children: node.children });
    }
  }
  if (stack.length !== 1) return fail("unclosed <" + top().tag + ">");
  return { ok: true, nodes: root };
}

// ## The payload

export function parseWidgetPayload(value) {
  let source = typeof value === "string" ? value : "";
  if (source.startsWith(WIDGET_PREFIX)) source = source.slice(WIDGET_PREFIX.length);
  if (!source.trim()) return { ok: false, error: "empty payload" };
  let bundle;
  try { bundle = JSON.parse(source); } catch (_) {
    return { ok: false, error: "payload is not JSON" };
  }
  if (!bundle || typeof bundle !== "object" || Array.isArray(bundle)) {
    return { ok: false, error: "payload is not an object" };
  }
  const schema = typeof bundle.schema === "string" ? bundle.schema : "";
  if (schema !== WIDGET_SCHEMA) {
    return { ok: false, error: "unsupported schema" + (schema ? " \"" + schema + "\"" : ""), bundle };
  }
  return { ok: true, bundle };
}

const kindOf = (bundle, item) => {
  if (bundle && typeof bundle.kind === "string" && bundle.kind) return bundle.kind;
  if (bundle && bundle.scry && bundle.scry.schema === "scry.analysis/1") return "scry.analysis";
  return (item && typeof item.title === "string" && item.title) || "widget";
};

const titleOf = (bundle, item) => {
  if (bundle && typeof bundle.title === "string" && bundle.title) return bundle.title;
  if (bundle && bundle.scry && bundle.scry.claim) {
    const claim = bundle.scry.claim;
    if (typeof claim.name === "string" && claim.name) {
      return "claim " + claim.name + (typeof claim.status === "string" ? ": " + claim.status : "");
    }
  }
  return (item && typeof item.title === "string" && item.title) || kindOf(bundle, item);
};

const summaryOf = (bundle) => {
  if (bundle && typeof bundle.summary === "string" && bundle.summary) return bundle.summary;
  if (bundle && bundle.scry && bundle.scry.claim && typeof bundle.scry.claim.summary === "string") {
    return bundle.scry.claim.summary;
  }
  return "";
};

const safeClass = (value) => String(value || "unknown").toLowerCase().replace(/[^a-z0-9_-]/g, "") || "unknown";

// The `scry.analysis/1` extension: the claim, its findings and the graph's counts.
// Everything is a checked node, so a hostile claim string stays text.
function scryWidget(bundle, item) {
  const ext = bundle.scry && typeof bundle.scry === "object" ? bundle.scry : {};
  const claim = ext.claim && typeof ext.claim === "object" ? ext.claim : {};
  const findings = Array.isArray(ext.findings) ? ext.findings
    : (Array.isArray(claim.findings) ? claim.findings : []);
  const graph = ext.graph && typeof ext.graph === "object" ? ext.graph : {};
  const status = typeof claim.status === "string" && claim.status ? claim.status : "unknown";
  const title = titleOf(bundle, item);
  const summary = summaryOf(bundle);
  const counts = [];
  for (const key of ["nodes", "edges", "relationRows"]) {
    if (typeof graph[key] === "number" && Number.isFinite(graph[key])) {
      counts.push(element("span", [["class", "wiz-scry-count"]], [
        text(key + ": " + Math.trunc(graph[key])),
      ]));
    }
  }
  const body = [
    element("p", [["class", "wiz-scry-line"]], [
      element("span", [["class", "wiz-scry-status wiz-scry-" + safeClass(status)]], [text(status)]),
      text(" "),
      element("span", [["class", "wiz-scry-summary"]], [text(summary)]),
    ]),
  ];
  if (counts.length) {
    body.push(element("p", [["class", "wiz-scry-graph"]], counts.flatMap((n, i) =>
      i === 0 ? [n] : [text(" · "), n])));
  }
  body.push(findings.length
    ? element("ul", [["class", "wiz-findings"]], findings.map((finding) => {
      const f = finding && typeof finding === "object" ? finding : {};
      return element("li", [["class", "wiz-finding"]], [
        element("code", [["class", "wiz-finding-file"]], [text(typeof f.file === "string" ? f.file : "?")]),
        text(" node "),
        element("span", [["class", "wiz-finding-node"]], [text(typeof f.node === "number" ? String(f.node) : "?")]),
        text(" — "),
        text(typeof f.message === "string" ? f.message : ""),
      ]);
    }))
    : element("p", [["class", "wiz-nothing"]], [text("no findings")]));
  return { ok: true, kind: "scry.analysis", title, summary, body, text: summary };
}

// A card names the kind it could not draw, and why: a client always has something to
// show, even for a widget kind this host has never heard of.
function fallbackWidget(parsed, item, error) {
  const bundle = parsed && parsed.bundle ? parsed.bundle : null;
  const kind = kindOf(bundle, item);
  return {
    ok: false,
    kind,
    title: titleOf(bundle, item),
    summary: summaryOf(bundle),
    error,
    body: [element("div", [["class", "wiz-widget-fallback"]], [
      text("cannot render "),
      element("code", [], [text(kind)]),
      text(": " + error),
    ])],
  };
}

function bodyOf(bundle) {
  // `html` is the display fragment (a plot's figure around its SVG); `svg` is the
  // image on its own. Either may be absent; the first one that sanitises is used.
  const candidates = [];
  if (typeof bundle.html === "string" && bundle.html.trim()) candidates.push(bundle.html);
  if (typeof bundle.svg === "string" && bundle.svg.trim()) candidates.push(bundle.svg);
  if (!candidates.length) return { ok: false, error: "no html or svg body" };
  let reason = "no drawable body";
  for (const candidate of candidates) {
    const checked = sanitizeWidgetMarkup(candidate);
    if (checked.ok) return checked;
    reason = checked.error;
  }
  return { ok: false, error: reason };
}

// Render one `wiz/interactiveInfo` item (an object with `kind`, `title`, `text`) or a
// payload string. The result is `{ok, kind, title, summary, body, error?}` with `body`
// a checked node list.
export function renderWidget(item) {
  const source = typeof item === "string" ? { text: item } : (item && typeof item === "object" ? item : {});
  const parsed = parseWidgetPayload(source.text);
  if (!parsed.ok) return fallbackWidget(parsed, source, parsed.error);
  const bundle = parsed.bundle;
  if (bundle.scry && bundle.scry.schema === "scry.analysis/1") return scryWidget(bundle, source);
  const drawn = bodyOf(bundle);
  if (!drawn.ok) return fallbackWidget(parsed, source, drawn.error);
  return {
    ok: true,
    kind: kindOf(bundle, source),
    title: titleOf(bundle, source),
    summary: summaryOf(bundle),
    body: drawn.nodes,
    text: summaryOf(bundle),
  };
}

const isWidgetItem = (item) => {
  if (!item || typeof item !== "object") return false;
  if (item.kind === "widget") return true;
  return typeof item.text === "string" && item.text.startsWith(WIDGET_PREFIX);
};

// The cards for a list of items (non-widget items are ignored). Exported for the DOM
// pane and the panel's string renderer.
export function widgetCards(items) {
  const list = Array.isArray(items) ? items.filter(isWidgetItem) : [];
  return list.map((item) => {
    const rendered = renderWidget(item);
    const head = element("figcaption", [["class", "wiz-widget-head"]], [
      element("span", [["class", "wiz-widget-title"]], [text(rendered.title)]),
      element("span", [["class", "wiz-widget-kind"]], [text(rendered.kind)]),
    ]);
    const children = [head, element("div", [["class", "wiz-widget-body"]], rendered.body)];
    if (rendered.summary && rendered.summary !== rendered.title) {
      children.push(element("p", [["class", "wiz-widget-summary"]], [text(rendered.summary)]));
    }
    return element("figure", [
      ["class", "wiz-widget-card" + (rendered.ok ? "" : " wiz-widget-blocked")],
      ["data-widget-kind", rendered.kind],
      ["data-widget-title", rendered.title],
      ["data-widget-rendered", rendered.ok ? "true" : "false"],
    ], children);
  });
}

// The whole grid as HTML (the goals panel's string API). Empty when there are no
// widget items, so the caller can leave its `Widgets` heading out.
export function renderWidgets(items) {
  const cards = widgetCards(items);
  if (!cards.length) return "";
  return serializeNodes([element("div", [["class", "wiz-widget-grid"]], cards)]);
}

export function widgetCount(items) {
  return widgetCards(items).length;
}

// Mount into an element (the standalone page's widget pane). Clears the previous
// cursor's widgets first, and shows a plain "nothing here" line when there are none.
export function mountWidgets(container, items, doc, options = {}) {
  if (!container || !doc) return 0;
  while (container.childNodes && container.childNodes.length) {
    container.removeChild(container.childNodes[0]);
  }
  const cards = widgetCards(items);
  const nodes = cards.length
    ? [element("div", [["class", "wiz-widget-grid"]], cards)]
    : [element("div", [["class", "nothing"]], [text(options.emptyText || "No widgets at the cursor")])];
  appendNodes(doc, container, nodes);
  if (typeof container.setAttribute === "function") {
    container.setAttribute("data-widget-count", String(cards.length));
  }
  return cards.length;
}
