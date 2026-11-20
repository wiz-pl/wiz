// (11ab) The playground's state and URL encoding, under Node: no page, no Wasm. The
// pure module in web/playground-state.js is the contract the page and the share links
// rely on, so this checks its round trips, its canonical form, malformed input, and the
// examples' ids.
//   usage: node web/playground-state_test.mjs
import assert from "node:assert/strict";
import {
  base64UrlDecode,
  base64UrlEncode,
  decodeFragment,
  decodeShareUrl,
  defaultState,
  encodeFragment,
  encodeShareUrl,
  matchedPresetId,
  parseDraft,
  serializeDraft,
  stateFor,
  withPrelude,
} from "./playground-state.js";
import {
  defaultPreset,
  defaultPresetId,
  findPreset,
  presets,
  presetOf,
} from "./playground-presets.js";

let failed = 0;
function check(name, fn) {
  try {
    fn();
    console.log(`ok: ${name}`);
  } catch (e) {
    failed++;
    console.log(`FAIL: ${name}\n  ${e && e.message ? e.message : String(e)}`);
  }
}

check("examples have unique ids and text", () => {
  assert.ok(presets.length >= 5);
  assert.equal(new Set(presets.map((p) => p.id)).size, presets.length);
  assert.equal(new Set(presets.map((p) => p.code)).size, presets.length);
  for (const p of presets) {
    assert.equal(typeof p.title, "string");
    assert.ok(p.title.length > 0);
    assert.match(p.id, /^[a-z][a-z0-9-]*$/);
    assert.ok(p.code.trim().length > 0);
  }
});

check("the default example exists", () => {
  const p = defaultPreset();
  assert.ok(p);
  assert.equal(p.id, defaultPresetId);
  assert.equal(findPreset(defaultPresetId), p);
  assert.equal(findPreset("nope"), null);
  assert.equal(presetOf(p.code), p);
  assert.equal(matchedPresetId(p.code), p.id);
  assert.equal(matchedPresetId("custom"), "");
});

check("withPrelude adds the import only when there is none", () => {
  assert.equal(withPrelude("def one : Nat := 1"), "import Prelude\n\ndef one : Nat := 1");
  assert.equal(withPrelude("import Prelude\ndef one : Nat := 1"), "import Prelude\ndef one : Nat := 1");
  assert.equal(withPrelude("  import Std\ndef one : Nat := 1"), "  import Std\ndef one : Nat := 1");
});

check("base64url round-trips ASCII", () => {
  for (const text of ["", "a", "ab", "abc", "abcd", "hello world\n", "x&y#z%q?r=1+s=t"]) {
    assert.equal(base64UrlDecode(base64UrlEncode(text)), text);
  }
});

check("base64url round-trips UTF-8 and control characters", () => {
  const texts = [
    "def twice (n : Nat) : Nat := n + n\n#eval twice 21\n",
    "-- λ → ∀ 😀 🧙\n",
    "\u0000\u0001\u007f\n",
    "quote \" and backslash \\ and tab \t",
  ];
  for (const text of texts) {
    assert.equal(base64UrlDecode(base64UrlEncode(text)), text);
  }
});

check("base64url is URL-safe and unpadded", () => {
  const encoded = base64UrlEncode("π".repeat(100));
  assert.doesNotMatch(encoded, /[+/=]/);
  assert.match(encoded, /^[A-Za-z0-9_-]+$/);
});

check("base64url rejects malformed input", () => {
  assert.equal(base64UrlDecode("!"), null);
  assert.equal(base64UrlDecode("A"), null);
  assert.equal(base64UrlDecode("AB"), null);
  assert.equal(base64UrlDecode("AAAAA"), null);
});

check("a canonical state uses the short preset fragment", () => {
  const state = defaultState();
  assert.equal(encodeFragment(state), "#preset=basics");
  assert.deepEqual(decodeFragment("#preset=basics"), state);
  assert.deepEqual(decodeFragment("preset=basics"), state);
});

check("custom text round-trips through the code fragment", () => {
  const state = { code: "def one : Nat := 1\n#eval one & # %\n", preset: null };
  const fragment = encodeFragment(state);
  assert.match(fragment, /^#code=[A-Za-z0-9_-]+$/);
  assert.deepEqual(decodeFragment(fragment), state);
});

check("a code that matches an example is canonicalised to its preset", () => {
  const state = { code: defaultPreset().code, preset: null };
  assert.equal(encodeFragment(state), "#preset=basics");
  assert.deepEqual(stateFor(defaultPreset().code), defaultState());
});

check("the code fragment handles an empty program", () => {
  assert.equal(encodeFragment({ code: "" }), "#code=");
  assert.deepEqual(decodeFragment("#code="), { code: "", preset: null });
});

check("malformed fragments are ignored", () => {
  assert.equal(decodeFragment(""), null);
  assert.equal(decodeFragment("#"), null);
  assert.equal(decodeFragment("#preset=nope"), null);
  assert.equal(decodeFragment("#code=!!!!"), null);
  assert.equal(decodeFragment("#other=1"), null);
  assert.equal(decodeFragment(null), null);
});

check("a full share URL preserves origin, path and query", () => {
  const state = { code: "def x : Nat := 1\n", preset: null };
  const href = encodeShareUrl("https://example.test/play/playground.html?theme=dark#old", state);
  const url = new URL(href);
  assert.equal(url.origin, "https://example.test");
  assert.equal(url.pathname, "/play/playground.html");
  assert.equal(url.search, "?theme=dark");
  assert.deepEqual(decodeShareUrl(href), state);
});

check("relative share URLs decode with a document base", () => {
  const state = defaultState();
  const href = encodeShareUrl("/playground.html", state);
  assert.equal(href, "http://localhost/playground.html#preset=basics");
  assert.deepEqual(decodeShareUrl(href), state);
  assert.equal(decodeShareUrl("/playground.html#preset=nope"), null);
  assert.equal(decodeShareUrl("not a url"), null);
});

check("drafts round-trip and are canonicalised", () => {
  const state = { code: "def custom : Nat := 2\n", preset: null };
  const raw = serializeDraft(state);
  assert.deepEqual(parseDraft(raw), state);
  assert.deepEqual(parseDraft(serializeDraft(defaultState())), defaultState());
});

check("malformed and stale drafts are rejected or cleaned", () => {
  assert.equal(parseDraft("not json"), null);
  assert.equal(parseDraft("null"), null);
  assert.equal(parseDraft('{"version":2,"code":"x"}'), null);
  assert.equal(parseDraft('{"version":1,"code":3}'), null);
  assert.deepEqual(parseDraft('{"version":1,"code":"x","preset":"basics"}'), { code: "x", preset: null });
  assert.deepEqual(parseDraft('{"version":1,"code":"x"}'), { code: "x", preset: null });
});

if (failed) process.exit(1);
console.log("playground state: all checks passed");
