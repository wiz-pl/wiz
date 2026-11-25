// The browser half of lib/Web/Loom.wiz: apply the patch list `Loom.patchesJson`
// produces, and turn DOM events into (event, handler-index) calls back into Wiz.
//
// This file is the DOM seam only. The shared model (host / Loom runtime / SSR shell /
// designer-builder), the data paths, the single validation table and the adopt contract
// are canonical in `docs/notes/loom-wire-protocol.md`; in particular `mount` here is the
// **replace** path, chosen by `adopt.js` when an island's SSR hash does not verify. The
// keyed patch list is the fast path; `applyPatches` takes the `morph` path for a batch
// with an HTML-carrying `replace` while an element in the container has the focus, and
// morphs only the `replace` that would remove that element or one of its ancestors (see
// that note, §4.1).
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
//
// **The keyed patch list is the fast path.** The default loop below applies every op
// exactly as before. It is used unless the batch carries an HTML-carrying `replace`
// that removes the focused element (or an ancestor of it): then the same ops are
// applied through `morph`, which matches children by `id`/`data-key` and updates the
// existing nodes instead of re-parsing them. That keeps `document.activeElement`, its
// selection and a control's live value across a re-render. A `move` may name its child
// by `key` (`id`/`data-key`) instead of `src`; Loom's keyed diff still emits `src`/`dst`,
// and both forms keep the node's identity.
//
// A batch with no `replace`, or with no focused element in `root`, never pays for the
// morph. With both, the morph path checks each `replace` against the tree as the earlier
// ops left it and morphs only the subtree that contains the focus; an unrelated replace
// is still the plain fast replace. `options.activeElement` / `options.document` exist for
// a host without browser globals (the Node test double); a page passes neither.
export function applyPatches(root, patches, parse = parseHtml, options = {}) {
  const doc = options.document || (root && root.ownerDocument) ||
    (typeof document !== "undefined" ? document : null);
  const active = options.activeElement !== undefined ? options.activeElement
    : (doc ? doc.activeElement : null);
  // A batch with no HTML-carrying replace cannot remove the focused subtree, so it is
  // always the fast path. With one, the morph path decides per op against the tree as
  // the earlier ops left it (a path after a `remove` is not the initial tree's path).
  const hasReplace = patches.some((p) => p && p.op === "replace");
  if (!active || active === root || !contains(root, active) || !hasReplace) {
    return applyFast(root, patches, parse);
  }
  return applyMorph(root, patches, parse, active, doc);
}

function applyFast(root, patches, parse) {
  for (const p of patches) {
    switch (p.op) {
      case "replace": {
        const n = nodeAt(root, p.path);
        replace(n, parse(p.html));
        break;
      }
      case "text":
        setText(nodeAt(root, p.path), p.text);
        break;
      case "setAttr":
        setAttr(nodeAt(root, p.path), p.name, p.value);
        break;
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
      case "move":
        moveChild(nodeAt(root, p.path), p);
        break;
      default:
        throw new Error("unknown patch op: " + p.op);
    }
  }
  return root;
}

// A textarea's text child is its *default* value: once the user has edited the control
// (the HTML "dirty value flag"), replacing the child does not change the live value. A
// page that sets a textarea's text means the value too. Only assign when it differs, so
// a re-render during typing cannot move the caret.
function setText(n, text) {
  n.textContent = text;
  mirrorTextarea(n, text);
}

function mirrorTextarea(n, text) {
  const parent = n.parentNode;
  if (parent && String(parent.tagName || "").toLowerCase() === "textarea" &&
      parent.value !== text) {
    try { parent.value = text; } catch { /* a test double without a value */ }
  }
}

// A form control's `value` attribute is only its *default* value. Once the user has
// edited the control the live `value` property keeps what they chose (the HTML "dirty
// value flag"), so a patch that only calls setAttribute leaves a slider showing the old
// value. Mirror the attribute into the property; a test double without one is skipped.
function setAttr(n, name, value) {
  n.setAttribute(name, value);
  if (name === "value" && "value" in n) {
    try { n.value = value; } catch { /* file inputs refuse a non-empty value */ }
  }
}

function moveChild(parent, p) {
  let n = p.key != null && p.key !== "" ? findByKey(parent, String(p.key)) : null;
  if (!n) n = parent.childNodes[p.src];
  if (!n) return;
  parent.removeChild(n);
  parent.insertBefore(n, parent.childNodes[p.dst] || null);
}

// ## The morph fallback

function applyMorph(root, patches, parse, active, doc) {
  const saved = saveFocus(root, active, doc);
  for (const p of patches) {
    switch (p.op) {
      case "replace": {
        const n = nodeAt(root, p.path);
        const frag = parse(p.html);
        if (n === root) morphChildren(n, frag, doc);
        else if (n === active || contains(n, active)) morphNode(n, frag, doc);
        else replace(n, frag);
        break;
      }
      case "text":
        setTextMorph(nodeAt(root, p.path), p.text, doc);
        break;
      case "setAttr":
        setAttr(nodeAt(root, p.path), p.name, p.value);
        break;
      case "removeAttr":
        nodeAt(root, p.path).removeAttribute(p.name);
        break;
      case "insert": {
        // An insertion never removes the focused node; applying it normally keeps both
        // the node and the focus.
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
      case "move":
        moveChild(nodeAt(root, p.path), p);
        break;
      default:
        throw new Error("unknown patch op: " + p.op);
    }
  }
  restoreFocus(root, saved, doc);
  return root;
}

// Morph the single node `oldNode` towards the fragment `frag`. A same-tag element is
// updated in place; a text node is updated in place; anything else is a real replace.
function morphNode(oldNode, frag, doc) {
  const kids = Array.from(frag.childNodes || []);
  if (kids.length === 0) {
    if (oldNode.parentNode) oldNode.parentNode.removeChild(oldNode);
    return;
  }
  if (kids.length === 1 && isText(oldNode) && isText(kids[0])) {
    setTextMorph(oldNode, kids[0].data, doc);
    return;
  }
  if (kids.length === 1 && isElement(oldNode) && isElement(kids[0]) &&
      tag(oldNode) === tag(kids[0])) {
    morphElement(oldNode, kids[0], doc);
    return;
  }
  replace(oldNode, frag);
}

function morphElement(oldNode, newEl, doc) {
  syncAttributes(oldNode, newEl);
  morphChildren(oldNode, newEl, doc);
}

// Set the new attributes, remove the old ones that are gone, and leave every other
// attribute — and every live property the user owns (a dirty `value`, `checked`, a
// textarea's text, a `<details>`'s `open`) — alone unless the new tree changes it.
function syncAttributes(oldNode, newEl) {
  const oldNames = attrNames(oldNode);
  const newNames = attrNames(newEl);
  for (const name of newNames) {
    const value = newEl.getAttribute(name);
    if (oldNode.getAttribute(name) !== value) setAttr(oldNode, name, value);
  }
  for (const name of oldNames) {
    if (newEl.getAttribute(name) == null) oldNode.removeAttribute(name);
  }
}

function attrNames(node) {
  if (typeof node.getAttributeNames === "function") return node.getAttributeNames();
  if (node.attributes && typeof node.attributes.length === "number") {
    return Array.from(node.attributes, (a) => a.name);
  }
  return [];
}

// Reconcile `oldParent`'s children with `newParent`'s, reusing old nodes by key
// (`id`/`data-key`) first and by position otherwise. A keyed child that moved is moved,
// not re-created, so its focus/selection/value survive.
function morphChildren(oldParent, newParent, doc) {
  const oldKids = Array.from(oldParent.childNodes || []);
  const newKids = Array.from(newParent.childNodes || []);
  const byKey = new Map();
  for (const node of oldKids) {
    const key = keyOf(node);
    if (key && !byKey.has(key)) byKey.set(key, node);
  }
  const used = new Set();
  let cursor = oldParent.firstChild || null;
  for (let i = 0; i < newKids.length; i++) {
    const want = newKids[i];
    let reuse = null;
    const key = keyOf(want);
    if (key && byKey.has(key) && !used.has(byKey.get(key))) reuse = byKey.get(key);
    // Do not consume a keyed old node positionally when a later new child still names
    // its key: that would re-purpose the node and destroy the identity the key is for.
    const cursorKey = cursor ? keyOf(cursor) : "";
    const reserved = cursorKey !== "" && keyUsedLater(cursorKey, newKids, i + 1);
    if (!reuse && cursor && !used.has(cursor) && !reserved && compatible(cursor, want)) reuse = cursor;
    if (!reuse) {
      if (cursor && cursor.parentNode === oldParent) oldParent.insertBefore(want, cursor);
      else oldParent.appendChild(want);
      used.add(want);
      cursor = want.nextSibling;
      continue;
    }
    if (reuse !== cursor) {
      if (cursor && cursor.parentNode === oldParent) oldParent.insertBefore(reuse, cursor);
      else oldParent.appendChild(reuse);
    }
    used.add(reuse);
    const placed = morphNodeInPlace(reuse, want, doc);
    cursor = placed.parentNode === oldParent ? placed.nextSibling : null;
  }
  for (const node of oldKids) {
    if (!used.has(node) && node.parentNode === oldParent) oldParent.removeChild(node);
  }
}

// Returns the node now in the slot: `oldNode` when it was morphed in place, `want` when
// it had to be replaced.
function morphNodeInPlace(oldNode, want, doc) {
  if (isText(oldNode) && isText(want)) {
    setTextMorph(oldNode, want.data, doc);
    return oldNode;
  }
  if (isElement(oldNode) && isElement(want) && tag(oldNode) === tag(want)) {
    morphElement(oldNode, want, doc);
    return oldNode;
  }
  // Same key, different node kind: the key identifies the slot, not the node.
  if (oldNode.parentNode) {
    oldNode.parentNode.insertBefore(want, oldNode);
    oldNode.parentNode.removeChild(oldNode);
  }
  return want;
}

// A focused textarea keeps the text the user typed; its text child is only the default.
// Every other text update follows the normal rule (including the textarea default when
// the control is not focused).
function setTextMorph(n, text, doc) {
  const parent = n.parentNode;
  if (parent && String(parent.tagName || "").toLowerCase() === "textarea" &&
      doc && doc.activeElement === parent) {
    if (n.textContent !== text) n.textContent = text;
    return;
  }
  setText(n, text);
}

function keyOf(node) {
  if (!node || typeof node.getAttribute !== "function") return "";
  return node.getAttribute("id") || node.getAttribute("data-key") ||
    node.getAttribute("data-wiz-key") || "";
}

function findByKey(parent, key) {
  for (const node of Array.from(parent.childNodes || [])) {
    if (keyOf(node) === key) return node;
  }
  return null;
}

function keyUsedLater(key, kids, from) {
  for (let i = from; i < kids.length; i++) if (keyOf(kids[i]) === key) return true;
  return false;
}

function compatible(a, b) {
  if (isText(a) && isText(b)) return true;
  return isElement(a) && isElement(b) && tag(a) === tag(b);
}

// ## Focus/selection preservation

function saveFocus(root, active, doc) {
  if (!active || typeof active.tagName !== "string") return null;
  const id = attr(active, "id");
  const name = attr(active, "name");
  return {
    node: active,
    id,
    name,
    tag: tag(active),
    start: typeof active.selectionStart === "number" ? active.selectionStart : null,
    end: typeof active.selectionEnd === "number" ? active.selectionEnd : null,
    path: pathOf(root, active),
    doc,
  };
}

// After a morph the focused node usually survives by identity; when a keyed match could
// not reuse it, find the new node by id (then by path, then by tag/name) and focus it.
// A focus the page moved itself during the batch wins.
function restoreFocus(root, saved, doc) {
  if (!saved) return;
  let target = saved.node && contains(root, saved.node) ? saved.node : null;
  if (!target && saved.id) target = find(root, (n) => attr(n, "id") === saved.id);
  if (!target && saved.path) {
    try {
      const n = nodeAt(root, saved.path);
      if (n && tag(n) === saved.tag) target = n;
    } catch { /* the tree changed shape: try the name */ }
  }
  if (!target && saved.name) {
    target = find(root, (n) => tag(n) === saved.tag && attr(n, "name") === saved.name);
  }
  if (!target) return;
  const current = doc && doc.activeElement;
  const body = doc && doc.body;
  if (current && current !== saved.node && current !== target && current !== body) return;
  if (typeof target.focus === "function") {
    try { target.focus({ preventScroll: true }); } catch { try { target.focus(); } catch {} }
  }
  if (saved.start != null && typeof target.setSelectionRange === "function") {
    const length = typeof target.value === "string" ? target.value.length : saved.start;
    const start = Math.max(0, Math.min(length, saved.start));
    const end = Math.max(start, Math.min(length, saved.end == null ? start : saved.end));
    try { target.setSelectionRange(start, end); } catch { /* a field that refuses a selection */ }
  }
}

function pathOf(root, node) {
  const parts = [];
  let n = node;
  while (n && n !== root) {
    const parent = n.parentNode;
    if (!parent) return "";
    parts.push(Array.prototype.indexOf.call(parent.childNodes, n));
    n = parent;
  }
  return n === root ? parts.reverse().join(".") : "";
}

function find(root, pred) {
  if (pred(root)) return root;
  for (const c of Array.from(root.childNodes || [])) {
    const hit = find(c, pred);
    if (hit) return hit;
  }
  return null;
}

function contains(root, node) {
  for (let n = node; n; n = n.parentNode) if (n === root) return true;
  return false;
}

function isText(n) {
  return !!n && (n.nodeType === 3 || n.nodeType === 4) && typeof n.data === "string";
}

function isElement(n) {
  return !!n && typeof n.tagName === "string";
}

function tag(n) {
  return n && n.tagName ? String(n.tagName).toLowerCase() : "";
}

function attr(n, name) {
  if (!n || typeof n.getAttribute !== "function") return "";
  return n.getAttribute(name) || "";
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
