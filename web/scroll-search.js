// The documentation's search box: the index is `search.js`'s (`window.wizSearchIndex`),
// the matching and the hits are `lib/Web/Search.wiz` (mounted here), and this file keeps
// the input, Enter/Escape and the `location`. A classic script so it works from
// `file://`; the runtime is a module it loads when the page is interactive.
"use strict";
(function () {
  const box = document.getElementById("search");
  const out = document.getElementById("results");
  if (!box || !out) return;
  let handle = null;
  let failed = false;

  function search(q) {
    if (!handle) return;
    handle.call("wiz_loom_effect", "search", "query", q);
    out.hidden = q.trim() === "";
  }

  import("./framework/mount.js").then(async ({ mount }) => {
    handle = await mount(out, { module: () => import("./wiz-docs-ui.mjs") });
    handle.call("wiz_loom_effect", "search", "index", JSON.stringify(window.wizSearchIndex || []));
    box.addEventListener("input", () => search(box.value));
    box.addEventListener("keydown", (e) => {
      if (e.key === "Enter") { const a = out.querySelector("a"); if (a) location.href = a.href; }
      if (e.key === "Escape") { box.value = ""; search(""); }
    });
    document.addEventListener("click", (e) => {
      if (!out.contains(e.target) && e.target !== box) out.hidden = true;
    });
    document.addEventListener("keydown", (e) => {
      if (e.key === "/" && document.activeElement !== box) { e.preventDefault(); box.focus(); }
    });
  }).catch((e) => {
    failed = true;
    console.warn("wiz doc: search needs the runtime (" + e + ")");
  });
})();
