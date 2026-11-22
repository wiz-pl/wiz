// The documentation server's live panel (`wiz doc --serve --lsp PORT`).
//
// The page carries `#wiz-doc-serve` (its module, the source's URL and the language
// server's endpoint) and this module. With an endpoint, hovering or clicking a
// declaration asks `wiz lsp --ws` for its hover, goals, expected type and diagnostics,
// and the runtime (`wiz-doc-live-ui.mjs`, `lib/Web/DocLive.wiz`) draws the panel. This
// file keeps the transport: the source's fetch, the WebSocket (`web/lsp-client.js`),
// the debounce and the pin. No DOM is built here except the panel's mount point; no
// Markdown is interpreted here (that is `Web.Hover`).
//
// No endpoint (no `--lsp`, or `?lsp=off`): nothing runs and the page stays the static
// documentation. `?lsp=PORT` (or a `ws://` URL) overrides the page's endpoint;
// `?token=T` is the server's token (#430).
"use strict";
import { mount } from "./framework/mount.js";
import { LspClient, endpointFromSearch } from "./lsp-client.js";

const runtimeModule = () => import("./wiz-doc-live-ui.mjs");

function serveData() {
  const el = document.getElementById("wiz-doc-serve");
  if (!el) return null;
  try { return JSON.parse(el.textContent || "null"); } catch (_) { return null; }
}

function endpointOf(data) {
  const search = typeof location !== "undefined" ? location.search : "";
  return endpointFromSearch(search, "lsp", data && data.lsp);
}

function positionOf(el) {
  const line = Number(el.getAttribute("data-doc-line"));
  const character = Number(el.getAttribute("data-doc-col"));
  return { line: isFinite(line) ? line : 0, character: isFinite(character) ? character : 0 };
}

// One interactive answer, with the plain method as the fallback.
async function answer(client, uri, position, method, plain) {
  const errors = [];
  try {
    return { value: await client[method](uri, position), kind: "interactive", errors };
  } catch (e) {
    errors.push(e && e.message ? e.message : String(e));
    try {
      return { value: await client[plain](uri, position), kind: "plain", errors };
    } catch (e2) {
      errors.push(e2 && e2.message ? e2.message : String(e2));
      return null;
    }
  }
}

function start() {
  const data = serveData();
  const endpoint = endpointOf(data);
  if (!data || !endpoint) return;

  const panel = document.createElement("aside");
  panel.id = "doc-live";
  panel.className = "doc-live";
  panel.setAttribute("aria-live", "polite");
  panel.setAttribute("aria-label", "live documentation");
  document.body.appendChild(panel);

  let handle = null;
  let client = null;
  let hoverEl = null;
  let activeEl = null;
  let hoverTimer = null;
  let generation = 0;
  let pinned = false;
  let connectGeneration = 0;
  const uri = `file:///wiz-doc/${data.module || "module"}.wiz`;
  const effect = (kind, a = "", b = "") => {
    if (handle) handle.call("wiz_loom_effect", kind, a, b);
  };

  function mark(el) {
    if (activeEl === el) return;
    if (activeEl) activeEl.classList.remove("doc-live-active");
    activeEl = el;
    if (el) el.classList.add("doc-live-active");
  }

  function schedule(el) {
    if (!el || el === hoverEl || pinned) return;
    hoverEl = el;
    mark(el);
    clearTimeout(hoverTimer);
    hoverTimer = setTimeout(() => ask(el, false), 120);
  }

  async function ask(el, pin) {
    if (!client || client.state !== "open" || !el) return;
    const position = positionOf(el);
    const token = ++generation;
    pinned = pin || pinned;
    mark(el);
    // One hover is seven fields of one state: send them as one `batch`, so the runtime
    // renders the panel once instead of once per field (and patches the DOM once).
    const pending = [
      { kind: "pinned", a: pinned ? "1" : "0", b: "" },
      { kind: "position", a: `line ${position.line + 1}, col ${position.character + 1}`, b: "" },
    ];
    const status = [];
    let hover = null;
    try {
      hover = await client.request("textDocument/hover", { textDocument: { uri }, position });
    } catch (e) {
      status.push(e && e.message ? e.message : String(e));
    }
    const goals = await answer(client, uri, position, "interactiveGoals", "plainGoal");
    const term = await answer(client, uri, position, "interactiveTermGoal", "plainTermGoal");
    if (token !== generation) return;
    pending.push({ kind: "hover", a: hover ? JSON.stringify(hover) : "", b: "" });
    pending.push({ kind: "goals", a: goals ? JSON.stringify(goals.value) : "", b: goals ? goals.kind : "" });
    pending.push({ kind: "term", a: term ? JSON.stringify(term.value) : "", b: term ? term.kind : "" });
    const stored = client.diagnostics && client.diagnostics.get(uri);
    pending.push({ kind: "diagnostics", a: JSON.stringify((stored && stored.diagnostics) || []), b: "" });
    pending.push({ kind: "message",
      a: status.concat(goals ? goals.errors : [], term ? term.errors : []).join("; "), b: "" });
    effect("batch", JSON.stringify(pending));
  }

  function watched(node) {
    return node && node.closest ? node.closest("[data-doc-line]") : null;
  }

  document.addEventListener("mouseover", (e) => schedule(watched(e.target)));
  document.addEventListener("click", (e) => {
    const el = watched(e.target);
    if (!el || (e.target.closest && e.target.closest("a"))) return;
    clearTimeout(hoverTimer);
    hoverEl = el;
    ask(el, true);
  });
  document.addEventListener("keydown", (e) => {
    if (e.key === "Escape" && pinned) {
      pinned = false;
      effect("pinned", "0");
    }
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
    const mine = ++connectGeneration;
    if (client) { try { client.close(); } catch (_) { /* already gone */ } }
    effect("state", "connecting", endpoint.label || endpoint.url);
    effect("message", "");
    try {
      const response = await fetch(data.src, { cache: "no-store" });
      if (!response.ok) throw new Error(`cannot read ${data.src}: HTTP ${response.status}`);
      const text = await response.text();
      const c = new LspClient({ url: endpoint.url, clientInfo: { name: "wiz-doc" } });
      client = c;
      c.openDocument(uri, text);
      c.on("state", (s) => {
        if (c !== client || mine !== connectGeneration) return;
        effect("state", s.state, endpoint.label || endpoint.url);
        if (s.state === "open") effect("message", "");
      });
      c.on("diagnostics", (d) => {
        if (c !== client || d.uri !== uri) return;
        effect("diagnostics", JSON.stringify(d.diagnostics || []));
      });
      await c.connect();
      if (mine !== connectGeneration) return;
      effect("server", c.serverInfo && c.serverInfo.name ? c.serverInfo.name : "");
      effect("state", c.state, endpoint.label || endpoint.url);
      await waitDiagnostics(c, 3000);
      const first = document.querySelector("[data-doc-line]");
      if (first) { hoverEl = first; ask(first, false); }
    } catch (e) {
      if (mine !== connectGeneration) return;
      effect("state", "failed", endpoint.label || endpoint.url);
      effect("message", e && e.message ? e.message : String(e));
    }
  }

  mount(panel, {
    module: runtimeModule,
    transport: { lsp: endpoint },
    events: ["click"],
    onRequest: (kind) => { effect("ack", kind); if (kind === "reconnect") connect(); },
  }).then((mounted) => {
    handle = mounted;
    connect();
  }).catch((e) => console.warn("wiz doc: live docs need the runtime (" + e + ")"));

  if (typeof window !== "undefined") {
    window.addEventListener("pagehide", () => {
      if (client) { try { client.close(); } catch (_) { /* already gone */ } }
    });
  }
}

start();
