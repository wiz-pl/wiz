// The standalone web infoview page (`web/infoview.html`, served by `wiz lsp --ws` via
// web/bridge.sh). The pane itself is the playground's (`web/playground-lsp.js`, built on
// `web/lsp-client.js` and `web/goals.js`): one implementation of the browser infoview
// for both pages and for both transports.
//
// This file only wires the page up:
//
//   * `?port=PORT` is a local server (`ws://127.0.0.1:PORT`, the default 8765 — what
//     `wiz lsp --ws` prints); `?lsp=` names one like the playground's (`ws://host:port`,
//     a bare port, or `off`), so the same pane works either way.
//   * The editor is its own document by default. `?follow=1` (what
//     `wiz/browserInfoview` opens) hides it and shows the cursor of the editor that owns
//     the server instead, from the server's `wiz/infoview/cursor` notification.
//   * `#status` mirrors the connection state and `#pos` the cursor (`line:col`, 1-based);
//     `#info` is the selected subterm, outside the goals panel as before.
//
// Nothing in this page is Wasm: the infoview's language client is JavaScript now, so the
// page needs no `wiz-infoview.mjs` of its own (the documentation's pages still do).
"use strict";
import { startInfoview } from "./playground-lsp.js";
import { parseEndpoint } from "./lsp-client.js";

// The server the page's URL names: `?lsp=` wins (the playground's spelling, `off` turns
// the pane into "no server"), else `?port=` (this page's old parameter), else 8765.
export function endpointOf(search) {
  const params = new URLSearchParams(search || "");
  const lsp = params.get("lsp");
  if (lsp !== null) return parseEndpoint(lsp);
  return parseEndpoint(params.get("port") || "8765");
}

// The page's `#status` text for a view (the standalone page has no engine status).
export function statusText(view, follow) {
  switch (view.state) {
    case "open": return "connected";
    case "connecting": return follow ? "following the editor" : "connecting";
    case "closed": return "disconnected (is `wiz lsp --ws` running?)";
    case "failed": return "cannot connect to " + (view.endpoint || "the language server");
    default: return "no server";
  }
}

// Mount the page on `doc` (a Document) at `loc` (a Location). Exported for the Node test;
// `start()` below is the browser's call.
export function startPage(doc = globalThis.document, loc = globalThis.location) {
  if (!doc) return null;
  const params = new URLSearchParams(loc ? loc.search : "");
  const follow = params.get("follow") === "1";
  const editor = doc.getElementById("editor");
  const panel = doc.getElementById("goals");
  const info = doc.getElementById("info");
  const status = doc.getElementById("status");
  const pos = doc.getElementById("pos");
  if (follow && editor) editor.style.display = "none";

  const app = startInfoview({
    editor,
    panel,
    info,
    config: endpointOf(loc ? loc.search : ""),
    follow,
    // Following: the document is the editor's, not ours; the server announces it.
    uri: follow ? null : undefined,
    onRender(view) {
      if (status) status.textContent = statusText(view, follow);
      if (pos && view.position) {
        pos.textContent = `${view.position.line + 1}:${view.position.character + 1}`;
      }
    },
  });

  if (app && follow) {
    const client = app.client();
    // The server moves the cursor (`wiz/infoview/cursor`, protocol §8.4); the pane asks
    // for the state there. Documents stay the editor's: we never open or change one.
    if (client) {
      client.on("wiz/infoview/cursor", (params) => {
        if (!params || !params.textDocument || !params.position) return;
        app.goTo(params.textDocument.uri, params.position);
      });
    }
  }
  return app;
}

if (typeof document !== "undefined") startPage();
