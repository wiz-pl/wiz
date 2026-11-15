// The search box of a documentation page (`wiz doc`, stage 11s): the index is
// search.js (`window.wizSearchIndex`: name, module, kind, doc summary, signature text
// and target of every module and declaration). A classic script, so that it works from
// file:// too.
"use strict";
(function () {
  const box = document.getElementById("search");
  const out = document.getElementById("results");
  if (!box || !out) return;
  const esc = (s) => String(s).replace(/[&<>"']/g, (c) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" }[c]));
  // a snippet around the match, so a hit in a long doc comment or signature shows why
  const around = (s, q, n = 150) => {
    s = String(s || "");
    const i = s.toLowerCase().indexOf(q);
    if (i < 0) return s.length > n ? s.slice(0, n - 1).trimEnd() + "…" : s;
    const start = Math.max(0, i - 45);
    return (start > 0 ? "…" : "") + s.slice(start, start + n).trim() + (start + n < s.length ? "…" : "");
  };
  // a name matches first by the last component, then by a prefix, then anywhere
  function score(name, q) {
    const n = name.toLowerCase();
    const last = n.slice(n.lastIndexOf(".") + 1);
    if (last === q) return 0;
    if (n === q) return 0;
    if (last.startsWith(q)) return 1;
    if (n.startsWith(q)) return 2;
    if (n.includes(q)) return 3;
    return -1;
  }
  // then the doc comment, then the signature: the same answer with a lower rank and
  // the text that matched (`where`, `text`)
  function content(e, q) {
    const d = (e.d || "").toLowerCase();
    if (d.includes(q)) return ["docs", e.d, 4];
    const s = (e.s || "").toLowerCase();
    if (s.includes(q)) return ["signature", e.s, 5];
    return null;
  }
  function href(e) {
    // a module is its own page; a declaration is an anchor on it
    return e.u || (e.k === "module" ? `${e.m}.html` : `${e.m}.html#${e.n}`);
  }
  function search(q) {
    q = q.trim().toLowerCase();
    if (!q) { out.hidden = true; out.innerHTML = ""; return; }
    const hits = [];
    for (const e of window.wizSearchIndex || []) {
      const s = score(e.n, q);
      if (s >= 0) { hits.push([s, e, null, ""]); continue; }
      const c = content(e, q);
      if (c) hits.push([c[2], e, c[0], c[1]]);
    }
    hits.sort((a, b) => a[0] - b[0] || a[1].n.length - b[1].n.length || a[1].n.localeCompare(b[1].n));
    out.innerHTML = hits.slice(0, 50).map(([, e, where, text]) => {
      const detail = where
        ? `<div class="summary"><span class="where">${esc(where)}</span> ${esc(around(text, q))}</div>`
        : `<div class="summary">${esc(around(e.d, q))}</div>`;
      return `<a class="hit" href="${esc(href(e))}"><span class="kind">${esc(e.k)}</span> <code>${esc(e.n)}</code>` +
        ` <span class="mod">${esc(e.m)}</span>${detail}</a>`;
    }).join("") || `<div class="nothing">No declarations, docs or signatures match.</div>`;
    out.hidden = false;
  }
  box.addEventListener("input", () => search(box.value));
  box.addEventListener("keydown", (e) => {
    if (e.key === "Enter") { const a = out.querySelector("a"); if (a) location.href = a.href; }
    if (e.key === "Escape") { box.value = ""; search(""); }
  });
  document.addEventListener("click", (e) => { if (!out.contains(e.target) && e.target !== box) out.hidden = true; });
  document.addEventListener("keydown", (e) => {
    if (e.key === "/" && document.activeElement !== box) { e.preventDefault(); box.focus(); }
  });
})();
