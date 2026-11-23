// The real-DOM adapter: `globalThis.wiz.dom`, the namespace a `--target js` module's
// `extern "js.wiz.dom.…"` calls resolve to in a browser.
//
// The same entry names, with the same results, as `examples/js-loom/fake-dom.mjs`
// provides for the Node tests, so one Wiz module — the Loom-shaped demo, a page's DOM
// glue — runs unchanged against both. `install()` is the only call a page makes:
//
//   import { install } from "./dom-host.mjs";
//   const dom = install();          // publishes globalThis.wiz.dom, returns its root
//   await mount(el, { module: () => import("./app.mjs") });
//
// What is here and what is not. These are the DOM operations the *runtime* is allowed to
// perform: build elements, set text and attributes, move nodes, toggle classes, take the
// focus, read/write a control's selection. Everything that is the browser's — layout,
// geometry, scrolling, IME, the caret *policy* — stays in the host (mount.js's
// `wizHost`), because a Wiz program cannot own it (the ownership table is canonical in
// `docs/notes/loom-wire-protocol.md` §1).
//
// Values cross the FFI as the JS target's table says: a `Nat` arrives as a `BigInt`
// (`Number(…)` here), a `String` as a JavaScript string, an `Elem` as the element itself
// (a `foreign_type` handle), and a `Callback` as the Wiz closure — a callable that takes
// the callback's own arguments *and* the world, so a listener calls
// `fn(event.target, 0)` exactly as the C glue's trampoline would.
//
// The entries that return a value a Wiz type has no shape for (`selection`, `classList`)
// return a plain object/array as a `w` result: Wiz passes it back or ignores it.
"use strict";

const N = (x) => (typeof x === "bigint" ? Number(x) : Number(x));

// The element an event's target should be reported as: the deepest element the browser
// dispatched to, which is what delegation reads `data-*` from.
function targetOf(e, el) {
  const t = e && e.target;
  return t && t.nodeType === 1 ? t : el;
}

// Build the namespace over `doc` (the live document by default). `rootEl` is what
// `root()` returns: the element the app owns (default `document.body`).
export function domApi({ document: doc = globalThis.document, root: rootEl } = {}) {
  if (!doc || typeof doc.createElement !== "function") {
    throw new TypeError("dom-host: no document to adapt (pass { document })");
  }
  const theRoot = () => rootEl || doc.body || doc.documentElement;
  // `addEventListener` returns the wrapper it registered: the Wiz closure is not the
  // function the DOM holds (the DOM calls it with the event, the closure wants the
  // target and the world), so removing a listener needs this handle.
  return {
    root: theRoot,
    createElement: (tag) => doc.createElement(String(tag)),
    createTextNode: (text) => doc.createTextNode(String(text)),
    setAttribute: (el, name, value) => { el.setAttribute(String(name), String(value)); },
    // The fake DOM's rule, and the one the Wiz side was written against: "" when the
    // attribute is absent (`Element.getAttribute` would say null, which becomes "" at the
    // FFI boundary anyway).
    getAttribute: (el, name) => {
      const v = el.getAttribute(String(name));
      return v === null || v === undefined ? "" : String(v);
    },
    removeAttribute: (el, name) => { el.removeAttribute(String(name)); },
    setText: (el, text) => {
      el.textContent = String(text);
      // A textarea's text child is only its default value: once the user has typed, the
      // live value is what is shown. Keep the two in step, as runtime.js does.
      const parent = el.parentNode;
      if (parent && String(parent.tagName || "").toLowerCase() === "textarea") {
        try { if (parent.value !== String(text)) parent.value = String(text); } catch { /* a control that refuses a value */ }
      }
    },
    getText: (el) => el.textContent || "",
    appendChild: (el, child) => { el.appendChild(child); },
    // `index` is a `Nat` (a BigInt here): insert before the child at that index, or
    // append when the index is past the end.
    insertBefore: (el, child, ref) => {
      if (typeof ref === "number" || typeof ref === "bigint") {
        const at = N(ref);
        const kids = el.childNodes;
        el.insertBefore(child, at < kids.length ? kids[at] : null);
      } else {
        el.insertBefore(child, ref || null);
      }
    },
    removeChild: (el, child) => { el.removeChild(child); },
    replaceWith: (el, node) => { el.replaceWith(node); },
    focus: (el) => { if (typeof el.focus === "function") el.focus(); },
    blur: (el) => { if (typeof el.blur === "function") el.blur(); },
    // The class list, as the browser holds it (an SVG element's is an SVGAnimatedString,
    // so read the attribute rather than trusting `classList`).
    classList: (el) => String(el.getAttribute("class") || "").split(/\s+/).filter((c) => c !== ""),
    classAdd: (el, name) => {
      const names = String(el.getAttribute("class") || "").split(/\s+/).filter((c) => c !== "");
      if (!names.includes(String(name))) names.push(String(name));
      el.setAttribute("class", names.join(" "));
    },
    classRemove: (el, name) => {
      const names = String(el.getAttribute("class") || "").split(/\s+/).filter((c) => c !== "");
      el.setAttribute("class", names.filter((c) => c !== String(name)).join(" "));
    },
    classHas: (el, name) =>
      String(el.getAttribute("class") || "").split(/\s+/).includes(String(name)),
    // A text control's selection, in UTF-16 offsets (what `selectionStart` counts and what
    // the driver's payload carries). An element with no selection reports 0/0.
    selection: (el) => {
      const start = typeof el.selectionStart === "number" ? el.selectionStart : 0;
      const end = typeof el.selectionEnd === "number" ? el.selectionEnd : start;
      return { start, end };
    },
    setSelection: (el, start, end) => {
      const a = N(start);
      const b = end === undefined || end === null ? a : N(end);
      if (typeof el.setSelectionRange === "function") el.setSelectionRange(a, b);
      else { el.selectionStart = a; el.selectionEnd = b; }
    },
    // The listener: the DOM passes the event, the Wiz closure wants the target element
    // and the world (`Callback (Elem → IO Unit)` erased is `Elem → World → pair`).
    addEventListener: (el, type, fn) => {
      const listener = (e) => {
        try {
          fn(targetOf(e, el), 0);
        } catch (err) {
          // A Wiz runtime that throws must not break the page's other listeners.
          console.error("wiz.dom.addEventListener: " + (err && err.message ? err.message : err));
        }
      };
      el.addEventListener(String(type), listener, false);
      return listener;
    },
    removeEventListener: (el, type, listener) => { el.removeEventListener(String(type), listener, false); },
    // One delegated listener on the mount root: `data-wiz-on-EVENT` is the handler index,
    // and the closure gets the marked element and the event's payload text. The index is
    // read here rather than in Wiz because the attribute is the host's contract
    // (runtime.js `delegate` in the Wasm path).
    delegate: (el, type, fn) => {
      const attr = "data-wiz-on-" + String(type);
      const listener = (e) => {
        let t = targetOf(e, el);
        while (t && t !== el && !(typeof t.getAttribute === "function" && t.getAttribute(attr) !== null)) {
          t = t.parentNode;
        }
        if (!t || t === el || typeof t.getAttribute !== "function") return;
        const at = t.getAttribute(attr);
        if (at === null) return;
        fn(t, at, e);
      };
      el.addEventListener(String(type), listener, false);
      return listener;
    },
  };
}

// Install the namespace on `globalThis.wiz.dom` (the path `extern "js.wiz.dom.…"`
// resolves), and return the handle a page keeps: the api, its root element, and an
// `uninstall` that puts back what was there (a Node test that installs, unmounts, and
// installs the fake DOM again must not leak this one).
export function install(options = {}) {
  const api = domApi(options);
  const previous = globalThis.wiz;
  const hadDom = !!previous && Object.prototype.hasOwnProperty.call(previous, "dom");
  const oldDom = previous && previous.dom;
  globalThis.wiz = Object.assign({}, previous, { dom: api });
  return {
    api,
    root: api.root(),
    uninstall() {
      if (hadDom) globalThis.wiz.dom = oldDom;
      else if (globalThis.wiz) delete globalThis.wiz.dom;
    },
  };
}
