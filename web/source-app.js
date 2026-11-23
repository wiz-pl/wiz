// The static bundle's bootstrap: load `data/`, mount the Loom runtime on the SSR the
// export wrote into `#app`, answer the runtime's requests from the bundle, and forward
// hash routes to it.
//
// With `?lsp=PORT` (or `?lsp=ws://HOST:PORT`) the same module is mounted by the live
// host (`source-live.js`): it asks `wiz lsp --ws` for hover and definition on the
// bundle's Wiz files and falls back to the bundle's answers for everything else. The
// static page is unchanged either way: the SSR is the first paint, `app.js` works with
// no server at all, and a failed connection is one note in the footer, not an error page.
"use strict";
import { loadBundle, mountSource } from "./source-static.js";
import { writeError } from "./framework/adopt.js";

const el = document.getElementById("app");
const reason = (e) => "source reader: " + (e && e.message ? e.message : String(e));

// `?lsp=` / `?lspRoot=`; `off`, `none`, `no`, `0` and `false` mean the static page, as
// `web/lsp-client.js` decides for the playground.
function liveEndpoint(search) {
  try {
    const params = new URLSearchParams(search || "");
    const value = params.get("lsp");
    if (value === null || /^\s*(off|none|no|0|false)\s*$/i.test(value)) return null;
    return {
      endpoint: value.trim(),
      token: params.get("token"),
      root: params.get("lspRoot"),
    };
  } catch (_) {
    return null;
  }
}

try {
  // A relative URL keeps the bundle servable from any prefix (`file://` needs the
  // single-file build, which is P2).
  const bundle = await loadBundle("data/");
  const live = liveEndpoint(globalThis.location && globalThis.location.search);
  if (live) {
    const { mountLive } = await import("./source-live.js");
    await mountLive(el, {
      module: () => import("./wiz-source-ui.mjs"),
      bundle,
      endpoint: live.endpoint,
      token: live.token,
      root: live.root,
      env: globalThis,
    });
  } else {
    await mountSource(el, {
      module: () => import("./wiz-source-ui.mjs"),
      bundle,
      env: globalThis,
    });
  }
  el.removeAttribute("data-wiz-error");
} catch (e) {
  if (el) {
    writeError(el, document, reason(e));
    console.warn(reason(e));
  }
}
