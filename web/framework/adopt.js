// The adopt-and-listen decision for a server-rendered Loom island.
//
// This is the *whole* hydration contract, and it is deliberately smaller than a
// hydration diff: the container carries a server-rendered tree and a hash of that tree;
// the client computes the hash of its own first render and either **adopts** (attaches
// listeners and state, touches no node) or **replaces** (today's `mount`). There is no
// node-by-node reconciliation and no partial adopt.
//
// The canonical model (host / Loom runtime / SSR shell / designer-builder, the data
// paths, the wire's role, the single validation table and this contract) is
// `docs/notes/loom-wire-protocol.md`. This file is the implementation of the contract's
// rows 13, 4 and the hash; it does not restate the model.
//
// ## The attributes
//
//   data-wiz-island   the container is an island (presence is what matters)
//   data-wiz-props    JSON for the runtime's initial props (through the transport)
//   data-wiz-ssr      the server's `hashHtml` (eight lower-case hex digits)
//
// ## The hash
//
// `hashHtml` is FNV-1a 32-bit over the UTF-8 bytes of the HTML string, including class
// attributes (they are part of the string). It is the working choice from the note while
// the owner's exact hash inputs are open; the same algorithm is `Wire.ssrHash` in Wiz so
// a runtime can export `wiz_loom_ssr_hash` instead of letting the host hash `html`.
"use strict";

export const ISLAND = "data-wiz-island";
export const PROPS = "data-wiz-props";
export const SSR = "data-wiz-ssr";
export const ERROR = "data-wiz-error";

const FNV_OFFSET = 0x811c9dc5;
const FNV_PRIME = 0x01000193;

// The UTF-8 bytes of one code point (a JS string is UTF-16, so a surrogate pair is one
// code point). The same four cases as `Draft.utf8Char` / `Wire.utf8Char`.
function utf8(cp, out) {
  if (cp < 0x80) out.push(cp);
  else if (cp < 0x800) out.push(0xc0 | (cp >>> 6), 0x80 | (cp & 0x3f));
  else if (cp < 0x10000) {
    out.push(0xe0 | (cp >>> 12), 0x80 | ((cp >>> 6) & 0x3f), 0x80 | (cp & 0x3f));
  } else {
    out.push(0xf0 | (cp >>> 18), 0x80 | ((cp >>> 12) & 0x3f),
      0x80 | ((cp >>> 6) & 0x3f), 0x80 | (cp & 0x3f));
  }
}

// FNV-1a 32 over the UTF-8 bytes of `html`, as eight lower-case hex digits. The result is
// a build/identity check, not a security hash: it catches a stale or different render,
// and a collision merely means a replace instead of an adopt.
export function hashHtml(html) {
  let h = FNV_OFFSET;
  for (const ch of String(html)) {
    const bytes = [];
    utf8(ch.codePointAt(0), bytes);
    for (const b of bytes) {
      h = Math.imul(h ^ b, FNV_PRIME) >>> 0;
    }
  }
  return h.toString(16).padStart(8, "0");
}

function attr(node, name) {
  if (!node || typeof node.getAttribute !== "function") return null;
  const v = node.getAttribute(name);
  return v == null ? null : String(v);
}

// What the container says about itself. `island` is presence, not a value: a page may
// write `data-wiz-island="loom/1"` today and a later ABI may use the value.
export function islandInfo(root) {
  const get = (name) => attr(root, name);
  const island = get(ISLAND);
  const props = get(PROPS);
  const ssr = get(SSR);
  return { island: island != null, value: island, props, ssr };
}

// Parse `data-wiz-props`; a malformed attribute is a warning and no props, not a failed
// mount (the static DOM still stands).
export function islandProps(info, warn = () => {}) {
  if (!info || info.props == null || info.props === "") return null;
  try {
    return JSON.parse(info.props);
  } catch (e) {
    try { warn("mount: data-wiz-props is not JSON: " + (e && e.message ? e.message : e)); } catch {}
    return null;
  }
}

// The adopt/replace decision, before the first message and before any node is touched.
//
//   { mode: "adopt",   reason: "hash-match", hash }
//   { mode: "replace", reason: "no-island" | "no-ssr-hash" | "hash-mismatch", hash,
//     expected }
//
// `hash` is the client's hash (`runtimeHash` when the runtime exports one, else
// `hashHtml(html)`), and `expected` is the server's `data-wiz-ssr`.
export function decideAdopt({ root, html, runtimeHash, warn = () => {} } = {}) {
  const info = islandInfo(root);
  if (!info.island) return { mode: "replace", reason: "no-island", hash: null };
  const hash = runtimeHash != null && runtimeHash !== "" ? String(runtimeHash) : hashHtml(html == null ? "" : html);
  if (!info.ssr) {
    safeWarn(warn, "mount: an island has no data-wiz-ssr; replacing it");
    return { mode: "replace", reason: "no-ssr-hash", hash };
  }
  if (info.ssr !== hash) {
    safeWarn(warn, "mount: the island's SSR hash does not match (" + info.ssr + " server, " +
      hash + " client); replacing it");
    return { mode: "replace", reason: "hash-mismatch", hash, expected: info.ssr };
  }
  // Equal hashes: adopt. Even an empty container is the server's tree; attaching the
  // listeners and the state is all that remains.
  return { mode: "adopt", reason: "hash-match", hash };
}

function safeWarn(warn, message) {
  try { warn(message); } catch {}
}

// The module/ABI failure path: leave the static DOM alone and write one plain-text
// reason into `data-wiz-error`. No retry, no second UI, no innerHTML.
export function writeError(root, doc, reason) {
  const document = doc || (root && root.ownerDocument) || (typeof globalThis !== "undefined" ? globalThis.document : null);
  if (!document || typeof document.createElement !== "function") return null;
  let found = null;
  const walk = (n) => {
    for (const c of (n.childNodes || [])) {
      if (c && typeof c.getAttribute === "function" && c.getAttribute(ERROR) != null) { found = c; return; }
      walk(c);
    }
  };
  walk(root);
  if (!found) {
    found = document.createElement("div");
    found.setAttribute(ERROR, "");
    if (root && typeof root.appendChild === "function") root.appendChild(found);
  }
  found.textContent = String(reason == null ? "the runtime could not start" : reason);
  return found;
}
