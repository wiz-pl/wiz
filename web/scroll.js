// The interactive half of a documentation page (`wiz doc`, stage 11s). The page is
// complete without it; with it, the Wasm module the web infoview uses (web/Web.wiz,
// `wiz_doc_step`; its model is `DocPage` in lib/Tagged.wiz) renders each signature as
// tagged text, from the page's JSON (`#wiz-doc-data`): hovering a subterm shows its type
// and where it is defined, clicking a constant goes to its definition, clicking anything
// else selects it (arrows then move the selection, as in the infoview).
"use strict";
import { loadWasm, stepper, delegate } from "./tagged.js";

const data = JSON.parse(document.getElementById("wiz-doc-data").textContent);
const byId = new Map(data.decls.map((d) => [d.id, d]));
const info = document.getElementById("info");
const main = document.querySelector("main");
let anchor = null;   // the tag the box is shown at

function place() {
  const t = anchor && anchor.isConnected ? anchor : document.querySelector(".tt.sel");
  if (!t) return;
  const r = t.getBoundingClientRect();
  info.style.left = `${Math.max(8, Math.min(window.scrollX + r.left, window.scrollX + document.documentElement.clientWidth - info.offsetWidth - 8))}px`;
  info.style.top = `${window.scrollY + r.bottom + 6}px`;
}
globalThis.wizSetHtml = (id, html) => {
  if (id === "info") {
    info.innerHTML = html;
    info.hidden = html === "";
    if (!info.hidden) place();
    return;
  }
  const el = document.getElementById(id);
  if (el) el.innerHTML = html;
};
globalThis.wizGo = (url) => { location.href = url; };

async function start() {
  const wasm = await loadWasm();
  const step = stepper(wasm, "_wiz_doc_init", "_wiz_doc_step");
  document.body.classList.add("interactive");
  // the module links GMP's mini-gmp (LGPL v3+ / GPL v2+): say so where it runs
  const notice = document.createElement("p");
  notice.className = "wasm-notice";
  notice.innerHTML = 'The interactive signatures run a WebAssembly module that includes mini-gmp from GMP 6.3.0 (LGPL v3+ / GPL v2+): <a href="https://wiz-pl.github.io/wiz/licenses/">licences and source</a>.';
  document.body.append(notice);
  // a signature is handed to Wasm when it is (nearly) on screen
  const loaded = new Set();
  const load = (el) => {
    if (loaded.has(el.id)) return;
    loaded.add(el.id);
    const d = byId.get(el.id);
    if (d) step("decl\n" + JSON.stringify(d));
  };
  const sigs = document.querySelectorAll(".sig-type");
  if ("IntersectionObserver" in window) {
    const io = new IntersectionObserver((es) => {
      for (const e of es) if (e.isIntersecting) { load(e.target); io.unobserve(e.target); }
    }, { rootMargin: "400px" });
    for (const s of sigs) io.observe(s);
  } else for (const s of sigs) load(s);
  const declOf = (t) => t.closest(".sig-type").id;
  main.tabIndex = -1;
  delegate(main, {
    hover: (t) => { anchor = t; step(`hover\n${declOf(t)} ${t.dataset.idx}`); },
    leave: () => { anchor = null; step("leave\n"); },
    click: (t) => { anchor = null; main.focus({ preventScroll: true }); step(`click\n${declOf(t)} ${t.dataset.idx}`); },
    key: (k) => { anchor = null; step("key\n" + k); },
  });
}
start().catch((e) => console.warn("wiz doc: plain pages (" + e + ")"));
