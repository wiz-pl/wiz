// The static bundle's bootstrap: load `data/`, mount the Loom runtime on the SSR the
// export wrote into `#app`, answer the runtime's requests from the bundle, and forward
// hash routes to it.
//
// The SSR in `index.html` is the first paint. If the runtime module is missing (a data
// export without `--ui`) or fails to start, the SSR stays and this writes one plain
// reason into the mount point, as the adopt contract asks; it never draws a second UI.
"use strict";
import { loadBundle, mountSource } from "./source-static.js";
import { writeError } from "./framework/adopt.js";

const el = document.getElementById("app");
const reason = (e) => "source reader: " + (e && e.message ? e.message : String(e));

try {
  // A relative URL keeps the bundle servable from any prefix (`file://` needs the
  // single-file build, which is P2).
  const bundle = await loadBundle("data/");
  await mountSource(el, {
    module: () => import("./wiz-source-ui.mjs"),
    bundle,
    env: globalThis,
  });
  el.removeAttribute("data-wiz-error");
} catch (e) {
  if (el) {
    writeError(el, document, reason(e));
    console.warn(reason(e));
  }
}
