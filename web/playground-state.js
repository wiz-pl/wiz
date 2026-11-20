// (11ab) The playground's pure state: the editor's text, the selected example, and the
// two ways the page keeps them — a URL fragment and a localStorage draft. Nothing here
// touches the DOM, so web/playground-state_test.mjs can test the encoding under Node.
//
// A fragment is either
//
//   #preset=basics
//
// when the text is exactly an example, or
//
//   #code=<base64url of the UTF-8 text>
//
// otherwise. Base64url (RFC 4648 §5, no padding) keeps the fragment to one URL-safe
// parameter, including for Unicode, quotes, newlines and `&`/`#`/`%` in a program.
"use strict";
import {
  defaultPreset,
  defaultPresetId,
  findPreset,
  presetOf,
} from "./playground-presets.js";

const VERSION = 1;
const ALPHABET = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_";

// A source without an import gets the embedded Prelude, so a bare definition works
// as in `wiz check`. (The engine itself needs the import; the page's contract is
// tested in web/playground_test.mjs.)
export function withPrelude(text) {
  return /^\s*import\b/m.test(text) ? text : "import Prelude\n\n" + text;
}

export function base64UrlEncode(text) {
  const bytes = new TextEncoder().encode(String(text));
  let out = "";
  for (let i = 0; i < bytes.length; i += 3) {
    const a = bytes[i];
    const b = i + 1 < bytes.length ? bytes[i + 1] : undefined;
    const c = i + 2 < bytes.length ? bytes[i + 2] : undefined;
    out += ALPHABET[a >> 2];
    out += ALPHABET[((a & 0x03) << 4) | (b === undefined ? 0 : b >> 4)];
    if (b === undefined) break;
    out += ALPHABET[((b & 0x0f) << 2) | (c === undefined ? 0 : c >> 6)];
    if (c === undefined) break;
    out += ALPHABET[c & 0x3f];
  }
  return out;
}

export function base64UrlDecode(text) {
  const s = String(text);
  if (!/^[A-Za-z0-9_-]*$/.test(s)) return null;
  if (s.length % 4 === 1) return null;
  const bytes = [];
  let buffer = 0;
  let bits = 0;
  for (const ch of s) {
    const value = ALPHABET.indexOf(ch);
    if (value < 0) return null;
    buffer = (buffer << 6) | value;
    bits += 6;
    if (bits >= 8) {
      bits -= 8;
      bytes.push((buffer >> bits) & 0xff);
      buffer &= (1 << bits) - 1;
    }
  }
  // A canonical encoding has only zero padding bits; reject `abc`-style aliases.
  if (buffer !== 0) return null;
  try {
    return new TextDecoder("utf-8", { fatal: true }).decode(Uint8Array.from(bytes));
  } catch {
    return null;
  }
}

// `{ code, preset }` with `preset` set only when it is the example the text came from.
export function stateFor(code) {
  const text = typeof code === "string" ? code : "";
  const p = presetOf(text);
  return p ? { code: text, preset: p.id } : { code: text, preset: null };
}

export function defaultState() {
  return { code: defaultPreset().code, preset: defaultPresetId };
}

export function encodeFragment(state) {
  const code = state && typeof state.code === "string" ? state.code : "";
  const p = presetOf(code);
  if (p) return "#preset=" + encodeURIComponent(p.id);
  return "#code=" + base64UrlEncode(code);
}

export function decodeFragment(hash) {
  if (typeof hash !== "string") return null;
  const raw = hash.startsWith("#") ? hash.slice(1) : hash;
  if (raw === "") return null;
  let params;
  try {
    params = new URLSearchParams(raw);
  } catch {
    return null;
  }
  const preset = params.get("preset");
  if (preset !== null) {
    const p = findPreset(preset);
    return p ? { code: p.code, preset: p.id } : null;
  }
  if (params.has("code")) {
    const code = base64UrlDecode(params.get("code"));
    return code === null ? null : stateFor(code);
  }
  return null;
}

export function encodeShareUrl(href, state) {
  const url = new URL(href, "http://localhost/");
  url.hash = encodeFragment(state);
  return url.href;
}

export function decodeShareUrl(href) {
  try {
    return decodeFragment(new URL(href, "http://localhost/").hash);
  } catch {
    return null;
  }
}

// The draft is versioned JSON so a future change can refuse old data instead of
// guessing. A matching preset id is kept; a stale one is dropped.
export function serializeDraft(state) {
  const current = stateFor(state && state.code);
  return JSON.stringify({ version: VERSION, code: current.code, preset: current.preset });
}

export function parseDraft(raw) {
  if (typeof raw !== "string") return null;
  let value;
  try {
    value = JSON.parse(raw);
  } catch {
    return null;
  }
  if (value === null || typeof value !== "object") return null;
  if (value.version !== VERSION || typeof value.code !== "string") return null;
  return stateFor(value.code, value.preset);
}

// The example the text exactly matches, if any (for the select box).
export function matchedPresetId(code) {
  const p = presetOf(code);
  return p ? p.id : "";
}
