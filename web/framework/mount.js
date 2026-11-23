// The page's whole half of a Loom app: one function.
//
// The shared model — what the host, the Loom runtime, the SSR shell and the
// designer/builder each own, which data crosses which boundary, where it is validated,
// and the adopt contract — is canonical in `docs/notes/loom-wire-protocol.md`. This
// comment is only the mount API and the host capabilities; do not restate the model
// here.
//
// A page finds its element and calls
//
//   mount(el, { module, transport })
//
// and nothing else. `module` is the runtime (a Wasm module built from a `Web.Loom` app,
// or any object with the same three exports: `wiz_loom_init`, `wiz_loom_html`,
// `wiz_loom_step`); `transport` is whatever the runtime needs from outside (an engine,
// a language server's socket), and is handed to the module factory and published as
// `globalThis.wizTransport`. Everything the page can see of the runtime is this one
// call: the SSR is mounted into `el`, patches from `js_patch` land in `el`, DOM events
// on it become steps, and the page's effects go back through `call`.
//
// **What a runtime may ask the host for, and nothing more** (`globalThis.wizHost`, the
// browser APIs a Wiz program cannot reach itself):
//
//   * `clipboard(text)` — copy, as a promise of whether it worked;
//   * `download(name, text)` — save text as a file;
//   * `storage.get(key)` / `storage.set(key, value)` — `localStorage`, guarded;
//   * `url(href)` — `history.replaceState`, guarded (`file://`, an over-long URL);
//   * `tick(fn)` — run `fn` on the next animation frame (returns a cancel);
//   * `onResize(fn)` — run `fn` when `el`'s size changes (returns a disconnect);
//   * `edit({ insert, from, to })` — apply one text edit to the mount's text field:
//     replace `[from, to)` (UTF-16 offsets; the current selection when omitted) with
//     `insert`, put the caret after it, dispatch `input`, and return
//     `{ value, selectionStart, selectionEnd }`. It is the *primitive*, not a policy:
//     the runtime decides what to indent, and this only edits the control.
//
// The host object is the boundary: a capability that is not here is not in the runtime
// either. `env` (for the Node tests, and for a non-browser host) supplies the browser
// globals; it defaults to `globalThis`.
//
// **What is not here on purpose.** The textarea's value, selection and caret are the
// browser's text-input implementation: an IME, undo and accessibility are not something
// a Wiz program can own. The runtime *models* the text and the host applies edits
// (`host.edit`) rather than replacing the control; the ownership table and the reason
// are in the canonical note, not repeated here.
"use strict";
import { start } from "./driver.js";
import { islandInfo, islandProps, writeError } from "./adopt.js";

const big = (x) => (typeof x === "bigint" ? x : BigInt(x));   // wasm64: pointers are i64

// Take an owned UTF-8 string out of the module (the module allocated it; free it after
// copying).
function takeString(wasm, p) {
  if (!p) return "";
  const s = wasm.UTF8ToString(Number(p));
  wasm._free(p);
  return s;
}

// Find the mount point: an element, or a selector (a missing `#id` is created, so a
// page needs no placeholder); null when there is nothing to mount on.
function resolveTarget(target, doc) {
  if (target && typeof target === "object" && "childNodes" in target) return target;
  if (typeof target !== "string" || !doc) return null;
  const found = typeof doc.querySelector === "function" ? doc.querySelector(target) : null;
  if (found) return found;
  if (!target.startsWith("#") || typeof doc.createElement !== "function") return null;
  const el = doc.createElement("div");
  el.setAttribute("id", target.slice(1));
  const parent = doc.body || doc.documentElement || doc;
  if (parent && typeof parent.appendChild === "function") parent.appendChild(el);
  return el;
}

// The runtime: a factory (the dynamic import's default), a module object with
// `default`/`create`, or the factory itself. Its ABI is checked before the page is
// touched, so a module built by an older compiler cannot half-render one: `mount` throws
// and the page decides what to say.
async function instantiate(module, options) {
  const opts = {
    print: options.print || ((s) => console.log(s)),
    printErr: options.printErr || ((s) => console.warn(s)),
    transport: options.transport,
  };
  // A page passes either the factory or a loader (`() => import("./x-ui.mjs")`). A
  // loader resolves to the ES module namespace, whose `default` is the factory; without
  // this second step `mount` would call the loader as if it were the factory and see a
  // namespace with no ABI exports (the playground's "does not export" start failure).
  let wasm = typeof module === "function" ? await module(opts) : module;
  const factory = wasm && typeof wasm.default === "function" ? wasm.default
    : wasm && typeof wasm.create === "function" ? wasm.create
      : null;
  if (factory) wasm = await factory(opts);
  if (!wasm || typeof wasm._wiz_loom_init !== "function" ||
      typeof wasm._wiz_loom_html !== "function" || typeof wasm._wiz_loom_step !== "function") {
    throw new TypeError("mount: the runtime does not export wiz_loom_init/html/step");
  }
  return wasm;
}

// The text field inside the mount point: the element itself when it is one, else the
// first `<textarea>`/text input below it. A page has one editor; the runtime names no
// selector.
function textFieldOf(el) {
  const isField = (n) => {
    const tag = n && n.tagName ? String(n.tagName).toLowerCase() : "";
    if (tag === "textarea") return true;
    if (tag !== "input") return false;
    const type = typeof n.getAttribute === "function" ? n.getAttribute("type") : null;
    return !type || type === "text" || type === "search" || type === "url";
  };
  if (isField(el)) return el;
  const walk = (n) => {
    for (const c of (n.childNodes || [])) {
      if (isField(c)) return c;
      const found = walk(c);
      if (found) return found;
    }
    return null;
  };
  return el ? walk(el) : null;
}

// `host.edit`: one text edit on the field, no policy. `from`/`to` are UTF-16 offsets
// (the current selection when omitted); the caret lands after the inserted text; the
// `input` event is the page's normal "the text changed" path.
function applyEdit(el, doc, edit) {
  const field = textFieldOf(el);
  if (!field || typeof edit !== "object" || edit === null) return null;
  const value = typeof field.value === "string" ? field.value : "";
  const startSel = typeof field.selectionStart === "number" ? field.selectionStart : 0;
  const endSel = typeof field.selectionEnd === "number" ? field.selectionEnd : startSel;
  const clamp = (n) => Math.max(0, Math.min(value.length, Number.isFinite(n) ? Math.trunc(n) : 0));
  const from = edit.from === undefined ? startSel : clamp(edit.from);
  const to = edit.to === undefined ? (edit.from === undefined ? endSel : from) : clamp(edit.to);
  const insert = edit.insert === undefined ? "" : String(edit.insert);
  const next = value.slice(0, from) + insert + value.slice(Math.max(from, to));
  const caret = from + insert.length;
  field.value = next;
  try {
    if (typeof field.setSelectionRange === "function") field.setSelectionRange(caret, caret);
    else { field.selectionStart = caret; field.selectionEnd = caret; }
  } catch { /* a field that refuses a selection: the value still changed */ }
  // The page's own listeners (didChange, the squiggle refresh) see a normal edit.
  try {
    const EventImpl = (doc && doc.defaultView && doc.defaultView.Event) ||
      (typeof Event === "function" ? Event : null);
    if (EventImpl && typeof field.dispatchEvent === "function") {
      field.dispatchEvent(new EventImpl("input", { bubbles: true }));
    }
  } catch { /* no event implementation: the caller still gets the new value */ }
  return { value: next, selectionStart: caret, selectionEnd: caret };
}

// The browser capabilities, over `env`'s globals. Each is guarded: a private window, a
// full quota or a `file://` page loses the capability, not the page.
function browserHost(el, env) {
  const nav = env.navigator || {};
  const doc = env.document;
  const win = env.window || env;
  return {
    clipboard: async (text) => {
      try {
        if (nav.clipboard && typeof nav.clipboard.writeText === "function") {
          await nav.clipboard.writeText(text);
          return true;
        }
      } catch { /* no permission (plain HTTP): fall through */ }
      if (!doc || typeof doc.createElement !== "function") return false;
      let area = null;
      try {
        area = doc.createElement("textarea");
        area.value = text;
        area.setAttribute("readonly", "");
        area.style.position = "fixed";
        area.style.opacity = "0";
        (doc.body || doc.documentElement).appendChild(area);
        area.select();
        return typeof doc.execCommand === "function" ? !!doc.execCommand("copy") : false;
      } catch {
        return false;
      } finally {
        if (area && typeof area.remove === "function") area.remove();
      }
    },
    download: (name, text, type = "text/plain;charset=utf-8") => {
      try {
        const href = env.URL.createObjectURL(new env.Blob([text], { type }));
        const link = doc.createElement("a");
        link.href = href;
        link.download = name;
        (doc.body || doc.documentElement).appendChild(link);
        link.click();
        link.remove();
        win.setTimeout(() => env.URL.revokeObjectURL(href), 1000);
        return true;
      } catch {
        return false;
      }
    },
    storage: {
      get: (key) => {
        try { return env.localStorage.getItem(key); } catch { return null; }
      },
      set: (key, value) => {
        try { env.localStorage.setItem(key, value); return true; } catch { return false; }
      },
    },
    url: (href) => {
      try {
        env.history.replaceState(null, "", href);
        return true;
      } catch {
        return false;   // `file://`, a blocked History API, or an over-long URL
      }
    },
    tick: (fn) => {
      if (typeof win.requestAnimationFrame !== "function") return () => {};
      const id = win.requestAnimationFrame(fn);
      return () => { if (typeof win.cancelAnimationFrame === "function") win.cancelAnimationFrame(id); };
    },
    onResize: (fn) => {
      if (typeof env.ResizeObserver !== "function") return () => {};
      const ro = new env.ResizeObserver(fn);
      ro.observe(el);
      return () => ro.disconnect();
    },
    edit: (edit) => applyEdit(el, doc, edit),
  };
}

// Mount `module`'s runtime on `target`. Returns the handle a page needs for its own
// effects: `call(name, ...args)` invokes an exported entry point with the current state
// (the module consumes it and returns the next one), `ask(name, ...args)` invokes a
// read-only entry point that returns a string without touching the state (the editor's
// rules), and `state`/`html`/`setState` are the driver's. `onRequest(kind, payload)`
// receives the effects the runtime asked for (its `wiz_loom_requests` export, a JSON
// list); the page does them and acknowledges with
// `call("wiz_loom_effect", "ack", kind, "")`.
//
// An island (`data-wiz-island`, `data-wiz-ssr`, optionally `data-wiz-props`) is adopted
// when the hash matches and replaced when it does not; see `adopt.js` and the canonical
// note. A module/ABI failure on an island leaves the static tree and writes one plain
// text reason into `data-wiz-error`; elsewhere it still throws, as before.
export async function mount(target, { module, transport, env = globalThis, print, printErr,
  events, parse, onStep, onRequest, warn } = {}) {
  const doc = (target && target.ownerDocument) || env.document;
  const el = resolveTarget(target, doc);
  if (!el) throw new TypeError("mount: no element to mount on");
  const island = islandInfo(el);
  const props = islandProps(island, warn || ((m) => console.warn(m)));
  const runtimeTransport = props === null || !island.island
    ? transport
    : (transport && typeof transport === "object" && !Array.isArray(transport)
      ? { ...transport, props }
      : { transport, props });
  let wasm;
  try {
    wasm = await instantiate(module, { transport: runtimeTransport, print, printErr });
  } catch (e) {
    if (island.island) writeError(el, doc, "mount: " + (e && e.message ? e.message : String(e)));
    throw e;
  }
  const host = browserHost(el, env);
  // Publish the boundary before the first render: a runtime that asks for a capability
  // from `wiz_loom_init` must find it there.
  globalThis.wizHost = host;             // the capability boundary (see the header)
  globalThis.wizTransport = runtimeTransport;   // the runtime's outside world (engine, socket)
  globalThis.wizProps = props;           // the island's `data-wiz-props`, through the transport

  let app = null;
  let servicing = false;
  // The runtime's pending effects, in order. A request stays pending until the page
  // acknowledges it, so an effect that arrives while one is in flight is still seen
  // after the first; a request is never dropped because a step happened to coalesce it.
  const service = () => {
    if (!app || typeof onRequest !== "function" || servicing) return;
    let list;
    try { list = JSON.parse(app.requests() || "[]"); } catch { list = []; }
    if (!Array.isArray(list) || list.length === 0) return;
    servicing = true;
    try {
      for (const r of list) {
        try {
          onRequest(r && r.kind, (r && r.payload) || "");
        } catch (e) {
          console.error("mount: an effect request failed: " + (e && e.message ? e.message : e));
        }
      }
    } finally {
      servicing = false;
    }
  };

  try {
    app = start(wasm, el, {
      events, parse,
      warn,
      onStep: (state, event, index, payload) => {
        service();
        if (typeof onStep === "function") onStep(state, event, index, payload);
      },
    });
  } catch (e) {
    if (island.island) writeError(el, doc, "mount: " + (e && e.message ? e.message : String(e)));
    throw e;
  }

  // The runtime's own entry points (`wiz_loom_effect`, …): strings are allocated here
  // and freed after, numbers are wasm64 pointers, and the returned state is the next one.
  const call = (name, ...args) => {
    const fn = wasm["_" + name];
    if (typeof fn !== "function") throw new TypeError("mount: the runtime has no " + name);
    const pointers = [];
    const rest = args.map((a) => {
      if (typeof a === "string") {
        const p = wasm.stringToNewUTF8(a);
        pointers.push(p);
        return big(p);
      }
      return typeof a === "number" ? big(a) : a;
    });
    try {
      app.setState(fn(app.state(), ...rest));
    } finally {
      for (const p of pointers) wasm._free(p);
    }
    service();
  };

  // A read-only runtime query (the editor's pure rules, `wiz_loom_editor_*`): strings
  // in, an owned string out, no state and no effect. The page parses the JSON.
  const ask = (name, ...args) => {
    const fn = wasm["_" + name];
    if (typeof fn !== "function") throw new TypeError("mount: the runtime has no " + name);
    const pointers = [];
    const rest = args.map((a) => {
      if (typeof a === "string") {
        const p = wasm.stringToNewUTF8(a);
        pointers.push(p);
        return big(p);
      }
      return typeof a === "number" ? big(a) : a;
    });
    try {
      return takeString(wasm, fn(...rest));
    } finally {
      for (const p of pointers) wasm._free(p);
    }
  };

  service();
  return { ...app, call, ask, host, module: wasm };
}
