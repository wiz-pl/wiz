// The browser half of the web infoview: a WebSocket to the language server
// (`wiz lsp --ws PORT`, which web/bridge.sh starts), the Wiz program compiled to WebAssembly (web/Web.wiz), and the page.
// Everything the infoview decides is in Wiz; this file only moves events in and HTML
// out. Every event is a step of the Wiz program (its export `wiz_web_step`, stage 9g),
// which calls back js_send and js_set_html (web/js.c).
"use strict";
// (11s) The parts the documentation's pages use too are web/tagged.js.
import { loadWasm, stepper, delegate } from "./tagged.js";

const params = new URLSearchParams(location.search);
const port = params.get("port") || "8765";
// (#430) the server's token (`wiz lsp` prints the page's URL with it; `wiz/browserInfoview`
// puts it there): the WebSocket presents it, or the server refuses the connection
const token = params.get("token") || "";
// (one server serves every page, and documents are shared: a URI of our own)
const uri = params.get("uri") || `file:///scratch-${Math.random().toString(36).slice(2, 10)}.wiz`;

// Events for Wiz: each is a step `state = wiz_web_step(state, event)`. The state is a
// Wiz value (a reference the page owns, passed back in); the event's text is copied by
// Wiz. Events before the module is loaded wait in `early`.
let step = null;
const early = [];
function post(kind, payload) {
  const ev = kind + "\n" + payload;
  if (step) step(ev); else early.push(ev);
}

// Messages to and from the server. Wiz frames its stream with Content-Length, as on
// stdio; the WebSocket carries one JSON-RPC message per text frame (protocol §8.2), so
// outgoing frames are cut out of the stream here, and incoming ones get their header.
let sock = null;
const outbox = [];
const encoder = new TextEncoder();
const decoder = new TextDecoder("utf-8");
let pending = new Uint8Array(0);   // bytes from Wiz not yet a whole message
function sendMessage(text) {
  if (sock && sock.readyState === WebSocket.OPEN) sock.send(text); else outbox.push(text);
}
globalThis.wizSend = (text) => {
  const more = encoder.encode(text);
  const buf = new Uint8Array(pending.length + more.length);
  buf.set(pending); buf.set(more, pending.length);
  let at = 0;
  for (;;) {
    let end = -1;   // the blank line after the headers
    for (let i = at; i + 3 < buf.length; i++)
      if (buf[i] === 13 && buf[i + 1] === 10 && buf[i + 2] === 13 && buf[i + 3] === 10) { end = i; break; }
    if (end < 0) break;
    const m = /Content-Length:\s*(\d+)/i.exec(decoder.decode(buf.subarray(at, end)));
    const len = m ? Number(m[1]) : 0;
    if (end + 4 + len > buf.length) break;
    sendMessage(decoder.decode(buf.subarray(end + 4, end + 4 + len)));
    at = end + 4 + len;
  }
  pending = buf.slice(at);
};
// (11w) `?follow=1`: no editor of our own; show the editor's cursor (wiz.nvim's
// :WizInfoviewBrowser opens the page so), as the server announces it
const follow = params.get("follow") === "1";
function received(text) {
  if (follow) {
    try {
      const m = JSON.parse(text);
      if (m.method === "wiz/infoview/cursor") {
        const p = m.params || {};
        post("follow", (p.textDocument || {}).uri || "");
        post("cursor", `${(p.position || {}).line || 0} ${(p.position || {}).character || 0}`);
        return;
      }
    } catch (e) { /* not JSON: Wiz reports it */ }
  }
  post("net", `Content-Length: ${encoder.encode(text).length}\r\n\r\n${text}`);
}
globalThis.wizSetHtml = (id, html) => {
  const el = document.getElementById(id);
  if (el) el.innerHTML = html;
};

function setStatus(text) { document.getElementById("status").textContent = text; }

function connect() {
  sock = new WebSocket(`ws://127.0.0.1:${port}/` + (token ? `?token=${encodeURIComponent(token)}` : ""));
  sock.onopen = () => {
    setStatus("connected");
    for (const b of outbox.splice(0)) sock.send(b);
  };
  sock.onmessage = (m) => received(m.data);
  sock.onclose = () => setStatus(token ? "disconnected (is `wiz lsp --ws` running?)"
    : "disconnected (no ?token= in this page's URL: use the URL `wiz lsp --ws` printed)");
  sock.onerror = () => setStatus("cannot connect to ws://127.0.0.1:" + port);
}

// The editor: a textarea. Its cursor as an LSP position (0-based, in characters).
const editor = document.getElementById("editor");
function cursor() {
  const before = Array.from(editor.value.slice(0, editor.selectionStart));
  let line = 0, col = 0;
  for (const c of before) { if (c === "\n") { line++; col = 0; } else col++; }
  return [line, col];
}
let lastPos = "";
let opened = false;   // (cursor moves before the document is open would ask about nothing)
function onCursor() {
  if (!opened) return;
  const [l, c] = cursor();
  const key = l + " " + c;
  if (key === lastPos) return;
  lastPos = key;
  document.getElementById("pos").textContent = `${l + 1}:${c + 1}`;
  post("cursor", key);
}
let changeTimer = null;
editor.addEventListener("input", () => {
  clearTimeout(changeTimer);
  changeTimer = setTimeout(() => { if (!opened) return; post("change", editor.value); lastPos = ""; onCursor(); }, 300);
});
for (const ev of ["keyup", "click", "select"]) editor.addEventListener(ev, onCursor);

// The infoview: clicks select a subterm (event delegation: one listener for every
// tag Wiz renders), the innermost tag under the mouse is highlighted, arrows navigate.
delegate(document.getElementById("goals"), {
  click: (t) => post("click", t.dataset.idx),
  key: (k) => post("key", k),
});

// Start: load the Wasm module (Emscripten's loader, web/build.sh), open the document.
async function start() {
  setStatus("loading");
  const wasm = await loadWasm();
  step = stepper(wasm, "_wiz_web_init", "_wiz_web_step");
  for (const ev of early.splice(0)) step(ev);
  connect();
  if (follow) {
    editor.style.display = "none";
    setStatus("following the editor");
    return;
  }
  post("open", uri + "\n" + editor.value);
  opened = true;
  onCursor();
}
start().catch((e) => setStatus("failed: " + e));
