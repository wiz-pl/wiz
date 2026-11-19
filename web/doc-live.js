// The documentation server's live panel (`wiz doc --serve --lsp PORT`).
//
// A page made with `--serve` carries `#wiz-doc-serve` (its module, the URL of its source
// on the documentation server, and the language server's endpoint) and this module.
// With an endpoint, hovering or clicking a declaration asks `wiz lsp --ws` for the real
// type and doc (textDocument/hover) and for the goals, expected type and diagnostics at
// that position, and shows them in a panel:
//
//   * the client is `web/lsp-client.js`, exactly the playground's (no second client);
//   * the goals, expected type and diagnostics are rendered by `web/goals.js`, the same
//     functions the playground's panel uses;
//   * the document is the module's source, fetched from the server (`sources/A.B.wiz`)
//     and opened with `textDocument/didOpen`, so the positions the server answers about
//     are the ones the page's declarations were generated from.
//
// No endpoint (no `--lsp`, or `?lsp=off`): this module does nothing at all — no socket,
// no fetch, no panel. The page is then the static documentation, readable without JS.
// `?lsp=PORT` (or a `ws://` URL) overrides the endpoint the page was made with.
// `?token=T` is the language server's token (#430: `wiz lsp --ws` prints it, and refuses
// a connection without it); the page never carries it itself.
"use strict";
import { LspClient, endpointFromSearch } from "./lsp-client.js";
import { escapeHtml, readGoalState, renderDiagnostics, renderGoalResult, renderTermResult } from "./goals.js";

// The page's serve data, or null (a page made without --serve carries no such script).
function serveData() {
  const el = document.getElementById("wiz-doc-serve");
  if (!el) return null;
  try { return JSON.parse(el.textContent || "null"); } catch (_) { return null; }
}

// `?lsp=` wins when present (`?lsp=off` disables); otherwise the page's `--lsp` port.
// `?token=` goes into the socket's URL either way.
function endpointOf(data) {
  const search = typeof location !== "undefined" ? location.search : "";
  return endpointFromSearch(search, "lsp", data && data.lsp);
}

// ## Hover contents (Markdown, as `textDocument/hover` returns it)

function hoverValue(result) {
  const c = result && result.contents;
  if (!c) return "";
  if (typeof c === "string") return c;
  if (Array.isArray(c)) {
    return c.map((x) => (typeof x === "string" ? x : (x && x.value) || "")).join("\n\n");
  }
  return c.value || "";
}

// `---` separates the declaration from its doc comment (Wiz's hover); keep it as a line.
function hoverHtml(result) {
  const value = hoverValue(result);
  if (!value.trim()) return `<div class="nothing">no hover information</div>`;
  return markdownHtml(value);
}

function inlineHtml(text) {
  let h = escapeHtml(text);
  h = h.replace(/`([^`\n]+)`/g, "<code>$1</code>");
  h = h.replace(/\*\*([^*\n]+)\*\*/g, "<strong>$1</strong>");
  h = h.replace(/(^|[^*])\*([^*\n]+)\*/g, "$1<em>$2</em>");
  return h;
}

function paragraphsHtml(text) {
  const t = text.trim();
  if (!t) return "";
  return t.split(/\n\s*\n/).map((p) => `<p>${inlineHtml(p).replace(/\n/g, " ")}</p>`).join("");
}

// Markdown with the pieces a hover uses (fenced code with a language, paragraphs,
// `code`, emphasis). Everything is escaped before any tag is added.
function markdownHtml(md) {
  const out = [];
  let rest = String(md || "");
  for (;;) {
    const open = rest.indexOf("```");
    if (open < 0) { out.push(paragraphsHtml(rest)); break; }
    out.push(paragraphsHtml(rest.slice(0, open)));
    const after = rest.slice(open + 3);
    const nl = after.indexOf("\n");
    if (nl < 0) { out.push(`<pre class="sig">${escapeHtml(after)}</pre>`); break; }
    const lang = after.slice(0, nl).trim();
    const body = after.slice(nl + 1);
    const close = body.indexOf("```");
    if (close < 0) { out.push(`<pre class="sig">${escapeHtml(body)}</pre>`); break; }
    const cls = lang === "wiz" ? "sig wiz" : "sig";
    out.push(`<pre class="${cls}">${escapeHtml(body.slice(0, close))}</pre>`);
    rest = body.slice(close + 3);
  }
  return out.join("");
}

// ## The panel

function createPanel() {
  const el = document.createElement("aside");
  el.id = "doc-live";
  el.className = "doc-live";
  el.setAttribute("aria-live", "polite");
  el.setAttribute("aria-label", "live documentation");
  document.body.appendChild(el);
  return el;
}

function statusText(state) {
  if (state === "open") return "connected";
  if (state === "connecting") return "connecting…";
  if (state === "closed") return "disconnected";
  if (state === "failed") return "no server";
  return state || "";
}

function render(panel, view) {
  const state = view.state || "idle";
  const open = state === "open";
  const server = view.serverInfo && view.serverInfo.name
    ? ` · ${escapeHtml(view.serverInfo.name)}` : "";
  const endpoint = view.endpoint ? ` <code>${escapeHtml(view.endpoint)}</code>` : "";
  const pin = view.pinned ? `<span class="pin">pinned · Esc unpins</span>` : "";
  const where = view.position
    ? `line ${view.position.line + 1}, col ${view.position.character + 1}` : "";
  let body = "";
  if (!open) {
    const why = view.message ? `<p class="reason">${escapeHtml(view.message)}</p>` : "";
    body = `${why}<p class="hint">Start a language server with ` +
      `<code>wiz lsp --ws PORT --no-stdio</code>, from the module root (so its imports ` +
      `resolve), make the pages with <code>--lsp PORT</code>, and open them with ` +
      `<code>?token=T</code>, where T is the token the server prints.</p>` +
      `<p><button type="button" data-live-reconnect>reconnect</button></p>`;
  } else {
    const why = view.message ? `<p class="reason">${escapeHtml(view.message)}</p>` : "";
    body = why + `<h3>Type and documentation</h3>` +
      (view.hover ? hoverHtml(view.hover) : `<div class="nothing">hover a signature</div>`) +
      `<h3>Goals</h3>` +
      (view.goals
        ? renderGoalResult(view.goals.goals, view.goals.goalsKind)
        : `<div class="nothing">hover a signature</div>`) +
      `<h3>Expected type</h3>` +
      (view.goals
        ? renderTermResult(view.goals.term, view.goals.termKind)
        : `<div class="nothing">hover a signature</div>`) +
      `<h3>Diagnostics</h3>` + renderDiagnostics(view.diagnostics);
  }
  panel.innerHTML =
    `<div class="doc-live-head"><span class="dot ${escapeHtml(state)}"></span>` +
    `<span class="title">live docs</span>` +
    `<span class="status">${statusText(state)}${server}${endpoint}</span>${pin}</div>` +
    (where ? `<div class="where">${escapeHtml(where)}</div>` : "") +
    `<div class="doc-live-body">${body}</div>`;
}

// ## Asking the server about a declaration

function positionOf(el) {
  const line = Number(el.getAttribute("data-doc-line"));
  const character = Number(el.getAttribute("data-doc-col"));
  return { line: isFinite(line) ? line : 0, character: isFinite(character) ? character : 0 };
}

function start() {
  const data = serveData();
  const endpoint = endpointOf(data);
  // No endpoint: the page is the static documentation, and nothing here runs.
  if (!data || !endpoint) return;

  const panel = createPanel();
  const view = {
    state: "connecting", endpoint: endpoint.label || endpoint.url, serverInfo: null,
    hover: null, goals: null, diagnostics: [], message: null,
    pinned: false, position: null,
  };
  let client = null;
  let hoverEl = null;
  let activeEl = null;
  let hoverTimer = null;
  let generation = 0;
  const uri = `file:///wiz-doc/${data.module || "module"}.wiz`;

  const renderNow = () => render(panel, view);

  function mark(el) {
    if (activeEl === el) return;
    if (activeEl) activeEl.classList.remove("doc-live-active");
    activeEl = el;
    if (el) el.classList.add("doc-live-active");
  }

  function schedule(el) {
    if (!el || el === hoverEl || view.pinned) return;
    hoverEl = el;
    mark(el);
    clearTimeout(hoverTimer);
    hoverTimer = setTimeout(() => ask(el, false), 120);
  }

  async function ask(el, pin) {
    if (!client || client.state !== "open" || !el) return;
    const position = positionOf(el);
    const token = ++generation;
    view.position = position;
    if (pin) view.pinned = true;
    mark(el);
    renderNow();
    try {
      let hover = null;
      const errors = [];
      try {
        hover = await client.request("textDocument/hover", {
          textDocument: { uri }, position,
        });
      } catch (e) {
        errors.push(e && e.message ? e.message : String(e));
      }
      const goals = await readGoalState(client, uri, position);
      if (token !== generation) return;
      view.hover = hover;
      view.goals = goals;
      const stored = client.diagnostics && client.diagnostics.get(uri);
      view.diagnostics = (stored && stored.diagnostics) || [];
      view.message = errors.concat(goals.errors).join("; ") || null;
      renderNow();
    } catch (e) {
      if (token !== generation) return;
      view.message = e && e.message ? e.message : String(e);
      renderNow();
    }
  }

  function watched(node) {
    return node && node.closest ? node.closest("[data-doc-line]") : null;
  }

  document.addEventListener("mouseover", (e) => schedule(watched(e.target)));
  document.addEventListener("click", (e) => {
    const el = watched(e.target);
    if (!el || (e.target.closest && e.target.closest("a"))) return; // links still navigate
    clearTimeout(hoverTimer);
    hoverEl = el;
    ask(el, true);
  });
  document.addEventListener("keydown", (e) => {
    if (e.key === "Escape" && view.pinned) {
      view.pinned = false;
      renderNow();
    }
  });
  panel.addEventListener("click", (e) => {
    if (e.target.closest && e.target.closest("[data-live-reconnect]")) connect();
  });

  function waitDiagnostics(c, ms) {
    if (c.diagnostics.has(uri)) return Promise.resolve();
    return new Promise((resolve) => {
      let done = false;
      const finish = () => { if (!done) { done = true; off(); resolve(); } };
      const off = c.on("diagnostics", (d) => { if (d.uri === uri) finish(); });
      setTimeout(finish, ms);
    });
  }

  async function connect() {
    if (client) { try { client.close(); } catch (_) { /* already gone */ } }
    view.state = "connecting";
    view.message = null;
    renderNow();
    try {
      const response = await fetch(data.src, { cache: "no-store" });
      if (!response.ok) throw new Error(`cannot read ${data.src}: HTTP ${response.status}`);
      const text = await response.text();
      const c = new LspClient({ url: endpoint.url, clientInfo: { name: "wiz-doc" } });
      client = c;
      c.openDocument(uri, text);
      c.on("state", (s) => {
        if (c !== client) return;
        view.state = s.state;
        if (s.state === "open") view.message = null;
        renderNow();
      });
      c.on("diagnostics", (d) => {
        if (c !== client || d.uri !== uri) return;
        view.diagnostics = d.diagnostics;
        renderNow();
      });
      await c.connect();
      view.serverInfo = c.serverInfo;
      view.state = c.state;
      renderNow();
      // The server elaborates the document on didOpen; hover before that is empty.
      await waitDiagnostics(c, 3000);
      const first = document.querySelector("[data-doc-line]");
      if (first) { hoverEl = first; ask(first, false); }
    } catch (e) {
      view.state = "failed";
      view.message = e && e.message ? e.message : String(e);
      renderNow();
    }
  }

  renderNow();
  connect();

  if (typeof window !== "undefined") {
    window.addEventListener("pagehide", () => {
      if (client) { try { client.close(); } catch (_) { /* already gone */ } }
    });
  }
}

start();
