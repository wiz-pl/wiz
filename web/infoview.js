// The standalone web infoview page (`web/infoview.html`, served by `wiz lsp --ws` via
// web/bridge.sh). It mounts the page's runtime (`wiz-infoview-ui.mjs`, built from
// `web/infoview-ui.wiz` and `lib/Web/InfoviewPage.wiz`) and keeps only the endpoint
// rule, the language server's socket and the editor's caret. The pane and the hover
// card are `lib/Web/{Goals,Hover}.wiz`; the same transport as the playground
// (`web/playground-lsp.js`) drives both.
//
// `?port=PORT` is a local server (default 8765, what `wiz lsp --ws` prints); `?lsp=`
// names one like the playground's. `?follow=1` (what `wiz/browserInfoview` opens) shows
// the cursor of the editor that owns the server instead of its own document.
"use strict";
import { mount } from "./framework/mount.js";
import { startInfoview } from "./playground-lsp.js";
import { endpointFromSearch } from "./lsp-client.js";

// The server the page's URL names: `?lsp=` wins, else `?port=`, else 8765.
export function endpointOf(search) {
  const params = new URLSearchParams(search || "");
  return params.has("lsp") ? endpointFromSearch(search)
    : endpointFromSearch(search, "port", "8765");
}

const runtimeModule = () => import("./wiz-infoview-ui.mjs");

// Mount the page on `doc` at `loc`. Exported for the Node test; `start()` below is the
// browser's call.
export async function startPage({ doc = globalThis.document, loc = globalThis.location,
  module = runtimeModule } = {}) {
  if (!doc || !doc.body) return null;
  const params = new URLSearchParams(loc ? loc.search : "");
  const follow = params.get("follow") === "1";
  const endpoint = endpointOf(loc ? loc.search : "");
  let app = null;
  let handle = null;

  const effect = (kind, a = "", b = "") => {
    if (handle) handle.call("wiz_loom_effect", kind, a, b);
  };
  // The editor's pure rules are the runtime's (`Web.EditorModel`), read through `ask`.
  const rules = {
    position: (text, offset) =>
      JSON.parse(handle.ask("wiz_loom_editor_position", text, String(offset))),
    segments: (text, diagnostics) =>
      JSON.parse(handle.ask("wiz_loom_editor_segments", text, JSON.stringify(diagnostics || []), "0")),
  };
  const onRequest = (kind, payload) => {
    effect("ack", kind);
    if (app) app.request(kind, payload);
  };

  handle = await mount(doc.body, {
    module,
    transport: { lsp: endpoint },
    events: ["click", "input", "change", "keydown"],
    onRequest,
  });
  // Follow mode hides the local editor; normal mode keeps the runtime's default text.
  effect("page", "init", JSON.stringify({ follow }));
  const editor = follow ? null : doc.getElementById("editor");
  app = startInfoview({
    editor,
    follow,
    config: endpoint,
    uri: follow ? null : undefined,
    squiggles: false,
    completions: false,
    rules,
    document: doc,
    update: (kind, a, b) => effect("panel", kind, b === "" ? a : b),
    onRender: (view) => {
      if (view.position) {
        effect("page", "position",
          `${view.position.line + 1}:${view.position.character + 1}`);
      }
    },
  });
  if (app && follow) {
    const client = app.client();
    if (client) {
      client.on("wiz/infoview/cursor", (p) => {
        if (!p || !p.textDocument || !p.position) return;
        app.goTo(p.textDocument.uri, p.position);
      });
    }
  }
  return app;
}

if (typeof document !== "undefined") startPage();
