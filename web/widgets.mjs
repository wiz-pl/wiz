// A minimal client for the `widgets` of a `wiz/interactiveGoals` result (stage 11af).
// The raw protocol is unchanged: a widget is {title, html, goals}. The trust boundary is
// the widget: Wiz code chooses `title` and `html`, so a client must treat both as
// untrusted. Here `html` is sanitised again (the server already removes the obvious
// escapes) and rendered in an iframe with `sandbox` and a `default-src 'none'` content
// security policy: no scripts, no event handlers, no javascript:/data:text/html links,
// and no way to reach the infoview's own DOM.
"use strict";

const escapeHtml = (s) =>
  String(s ?? "").replace(/[&<>"']/g, (c) =>
    ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" })[c]);

// Elements that can run code, load content or restyle the page. Removed with their
// content (the server's Wiz/Infoview.lean removes the same set, plus a few more).
const BANNED = ["script", "style", "iframe", "object", "embed", "meta", "link", "base",
                "form", "noscript", "template", "svg", "math"];

// Sanitise untrusted widget HTML for the sandboxed body. Defence in depth: the iframe
// would block scripts and the CSP would block the rest, but a client that inserts
// widget HTML into a page must not rely on only one of them.
export function sanitizeWidgetHtml(html) {
  let s = String(html ?? "");
  s = s.replace(/<!--[\s\S]*?-->/g, "");
  for (const name of BANNED) {
    s = s.replace(new RegExp(`<${name}\\b[^>]*>[\\s\\S]*?<\\/${name}\\s*>`, "gi"), "");
    s = s.replace(new RegExp(`<${name}\\b[^>]*\\/?>`, "gi"), "");
    s = s.replace(new RegExp(`<\\/${name}\\s*>`, "gi"), "");
  }
  // Event-handler and embedding attributes, quoted or unquoted.
  s = s.replace(/\son[a-z0-9_-]+\s*=\s*(?:"[^"]*"|'[^']*'|[^\s>]+)/gi, "");
  s = s.replace(/\sstyle\s*=\s*(?:"[^"]*"|'[^']*'|[^\s>]+)/gi, "");
  s = s.replace(/\s(?:srcdoc|formaction)\s*=\s*(?:"[^"]*"|'[^']*'|[^\s>]+)/gi, "");
  // URL attributes with an active scheme are dropped whole.
  s = s.replace(/\s(?:href|src|action|xlink:href)\s*=\s*(?:"[^"]*"|'[^']*'|[^\s>]+)/gi,
    (m) => /(?:javascript|vbscript|data\s*:\s*text\/html)/i.test(m) ? "" : m);
  // A last sweep, including text (defence in depth).
  s = s.replace(/\b(?:javascript|vbscript)\s*:/gi, "");
  s = s.replace(/data\s*:\s*text\/html/gi, "");
  return s;
}

// One widget: escaped title, the sanitised body in a sandboxed iframe, the goal snapshot.
export function widgetHtml(w) {
  const body = sanitizeWidgetHtml(w && w.html);
  const doc = "<!doctype html><meta http-equiv=\"Content-Security-Policy\" " +
    "content=\"default-src 'none'\">" + body;
  const goals = (w && Array.isArray(w.goals) ? w.goals : [])
    .map((g) => `<pre class="widget-goal">${escapeHtml(g)}</pre>`).join("");
  return `<div class="widget"><div class="widget-title">${escapeHtml(w && w.title)}</div>` +
    `<iframe class="widget-body" sandbox srcdoc="${escapeHtml(doc)}"></iframe>` +
    (goals ? `<div class="widget-goals">${goals}</div>` : "") + `</div>`;
}

// Replace `root`'s content with the widgets, in emission order.
export function renderWidgets(root, widgets) {
  root.innerHTML = (Array.isArray(widgets) ? widgets : []).map(widgetHtml).join("");
}

// The page's sample: one ordinary widget, and one that tries every escape hatch.
export const sampleWidgets = [
  { title: "Panel", html: "<b>n + 0 = n</b>", goals: ["n : Nat\n⊢ Nat"] },
  { title: "Danger (sanitised)",
    html: "<script>window.pwned = 1</script><style>body { display: none }</style>" +
      "<b onclick=\"window.pwned = 2\">ok</b>" +
      "<a href=\"javascript:window.pwned = 3\">no</a>" +
      "<img src=x onerror=\"window.pwned = 4\">" +
      "<iframe src=\"data:text/html,<script>alert(1)</script>\"></iframe>",
    goals: [] },
];

if (typeof document !== "undefined") {
  const root = document.getElementById("widgets");
  if (root) renderWidgets(root, sampleWidgets);
}
