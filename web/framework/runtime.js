// The browser half of lib/Web/Loom.wiz: apply the patch list `Loom.patchesJson`
// produces, and turn DOM events into (event, handler-index) calls back into Wiz.
//
// This file is the DOM seam only. The shared model (host / Loom runtime / SSR shell /
// designer-builder), the data paths, the single validation table and the adopt contract
// are canonical in `docs/notes/loom-wire-protocol.md`; in particular `mount` here is the
// **replace** path, chosen by `adopt.js` when an island's SSR hash does not verify.
//
// The paths are child indices from the container: "" is the container, "0" its first
// child, "0.2" the third child of that. Text nodes count as children, as in the DOM.
// The pages this is used on are produced by the same renderer (SSR), so the index path
// addresses the same nodes; a page that a framework did not render needs a re-render
// (replace "") rather than a patch.
//
// No framework, no build step: an ES module, like tagged.js.
"use strict";

// Apply `patches` (the parsed JSON of Loom.patchesJson) to `root`. `parse(html)`
// returns a DocumentFragment (in a browser, `parseHtml` below). Each operation expects
// the DOM state left by the previous ones (the diff emits them in order).
export function applyPatches(root, patches, parse = parseHtml) {
  for (const p of patches) {
    switch (p.op) {
      case "replace": {
        const n = nodeAt(root, p.path);
        replace(n, parse(p.html));
        break;
      }
      case "text": {
        const n = nodeAt(root, p.path);
        n.textContent = p.text;
        // A textarea's text child is its *default* value: once the user has edited the
        // control (the HTML "dirty value flag"), replacing the child does not change the
        // live value. A page that sets a textarea's text means the value too. Only
        // assign when it differs, so a re-render during typing cannot move the caret.
        const parent = n.parentNode;
        if (parent && String(parent.tagName || "").toLowerCase() === "textarea" &&
            parent.value !== p.text) {
          try { parent.value = p.text; } catch { /* a test double without a value */ }
        }
        break;
      }
      case "setAttr": {
        const n = nodeAt(root, p.path);
        n.setAttribute(p.name, p.value);
        // A form control's `value` attribute is only its *default* value.  Once the
        // user has edited the control the live `value` property keeps what they chose
        // (the HTML "dirty value flag"), so a patch that only calls setAttribute
        // leaves a slider showing the old value.  Mirror the attribute into the
        // property; no minidom test double has one, so only a real DOM catches this.
        if (p.name === "value" && "value" in n) {
          try { n.value = p.value; } catch { /* file inputs refuse a non-empty value */ }
        }
        break;
      }
      case "removeAttr":
        nodeAt(root, p.path).removeAttribute(p.name);
        break;
      case "insert": {
        const parent = nodeAt(root, p.path);
        const frag = parse(p.html);
        const ref = parent.childNodes[p.index] || null;
        for (const c of Array.from(frag.childNodes)) parent.insertBefore(c, ref);
        break;
      }
      case "remove": {
        const parent = nodeAt(root, p.path);
        const n = parent.childNodes[p.index];
        if (n) parent.removeChild(n);
        break;
      }
      case "move": {
        const parent = nodeAt(root, p.path);
        const n = parent.childNodes[p.src];
        if (!n) break;
        parent.removeChild(n);
        parent.insertBefore(n, parent.childNodes[p.dst] || null);
        break;
      }
      default:
        throw new Error("unknown patch op: " + p.op);
    }
  }
  return root;
}

// The node at a child-index path ("" is `root`).
export function nodeAt(root, path) {
  if (path === "" || path == null) return root;
  let n = root;
  for (const part of String(path).split(".")) {
    n = n.childNodes[Number(part)];
    if (!n) throw new Error("no node at path " + path);
  }
  return n;
}

function replace(n, frag) {
  const parent = n.parentNode;
  if (!parent) {
    // The container itself: its children are the rendered tree.
    for (const c of Array.from(n.childNodes)) n.removeChild(c);
    for (const c of Array.from(frag.childNodes)) n.appendChild(c);
    return;
  }
  parent.insertBefore(frag, n);
  parent.removeChild(n);
}

function parseHtml(html) {
  return document.createRange().createContextualFragment(html);
}

// DOM event delegation: one listener per event type on `root`; the innermost element
// with `data-wiz-on-EVENT="index"` is found from the target up (one attribute per
// event, so an element can handle a click and a keydown), and `send(event, index,
// domEvent)` is called. `send` returns whether the event was handled; when it does,
// the default action is prevented (a button in a form should not submit) — unless the
// element also carries `data-wiz-prevent-EVENT` (`Loom.onPrevent`), in which case
// `consume(event, index, domEvent)` decides: a keydown on a textarea must not swallow
// typing, so the runtime prevents only the keys it consumed.
export function delegate(root, send, types = ["click", "input", "change", "submit", "keydown", "keyup"], consume = null) {
  for (const type of types) {
    const attr = "data-wiz-on-" + type;
    const marked = "data-wiz-prevent-" + type;
    root.addEventListener(type, (e) => {
      let t = e.target;
      while (t && t !== root && !(t.getAttribute && t.getAttribute(attr) != null)) t = t.parentNode;
      if (!t || t === root || !t.getAttribute) return;
      const at = t.getAttribute(attr);
      if (at == null) return;
      const handled = send(type, Number(at), e);
      if (!handled) return;
      const asks = t.getAttribute(marked) != null;
      if (!asks || typeof consume !== "function" || consume(type, Number(at), e)) e.preventDefault();
    }, false);
  }
}

// Mount a server-rendered tree: `html` is Loom.toHtml's output for the initial state.
export function mount(root, html, parse = parseHtml) {
  const frag = parse(html);
  for (const c of Array.from(root.childNodes)) root.removeChild(c);
  for (const c of Array.from(frag.childNodes)) root.appendChild(c);
}
