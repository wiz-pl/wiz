// The P0 typed style/class model: aliases for a hashed class name, the small typed
// declaration vocabulary, and the canonical encoder the build-time generator uses.
//
// The model is canonical in the CSS DSL design note (`loom-css-dsl.md`, in the
// workspace notes); the shared runtime model, validation table and adopt contract are
// canonical in `docs/notes/loom-wire-protocol.md`. In particular:
//
//   * a `Class` is a *key*, `pkg/component/slot[/state]`; its name is
//     `lz-<component>-<slot>-<fnv1a32(key)>` (lower-case eight hex digits) and never
//     depends on the declarations;
//   * a `Style` is a list of rules, each a declaration block with outer-to-inner
//     pseudo/media attachments; the sheet is emitted once at build time;
//   * a view carries only the sorted class attribute. The wire carries that value as an
//     ordinary `setAttr "class"` patch; there is no style message type and no second
//     HTML string protocol here.
//
// This module is the browser-free reference encoder/validator (the same role
// `web/framework/wire.js` has for the wire). The Wiz DSL lives in `lib/Web/Style.wiz`
// and `Loom.styled` is the bridge; the golden vectors are shared with
// `web/framework/style_test.mjs`. Validation row 11 of
// `docs/notes/loom-wire-protocol.md` names this file; the wire's own rows 3–7 and 10
// stay in `wire.js`.
//
// P0 deliberately has no theme engine, no vendor-prefix pass, no arbitrary selector,
// no `@supports`/container query and no descendant combinator. A new media kind or a
// property is a deliberate addition to the vocabulary below.
"use strict";

export const SHEET_SCHEMA = 1;
export const CLASS_PREFIX = "lz-";
export const WZ_PREFIX = "wz-";
export const HL_CLASSES = Object.freeze([
  "hl-kw", "hl-com", "hl-str", "hl-num", "hl-op", "hl-const", "hl-var", "hl-sort",
]);
const HL_SET = new Set(HL_CLASSES);

// One refusal type, so a caller can switch on `e.code` without parsing prose.
export class StyleError extends Error {
  constructor(code, message) {
    super(message);
    this.name = "StyleError";
    this.code = code;
  }
}

const fail = (code, message) => { throw new StyleError(code, message); };
const frozen = (o) => Object.freeze(o);

// ## Class names

// FNV-1a 32-bit over the UTF-8 bytes. The public vectors in `style_test.mjs` pin it;
// `Class.hash` in `lib/Web/Style.wiz` is the same function.
export function fnv1a32(value) {
  const bytes = typeof value === "string" ? new TextEncoder().encode(value) : value;
  let h = 2166136261 >>> 0;
  for (const b of bytes) {
    h = (h ^ b) >>> 0;
    h = Math.imul(h, 16777619) >>> 0;
  }
  return h >>> 0;
}

export function hex8(n) {
  return (n >>> 0).toString(16).padStart(8, "0");
}

// A key segment is non-empty, lower-case ASCII letters/digits/hyphens and does not
// start or end with a hyphen. Package names and component/slot/state names use it.
const SEGMENT = /^[a-z0-9](?:[a-z0-9-]*[a-z0-9])?$/;

function keyParts(key) {
  if (typeof key !== "string") fail("key", "a class key must be a string");
  const parts = key.split("/");
  if (parts.length < 3 || parts.length > 4 || !parts.every((p) => SEGMENT.test(p))) {
    fail("key", `the key ${JSON.stringify(key)} is not pkg/component/slot[/state]`);
  }
  return parts;
}

// `component-slot`, the part of the name a human reads. The package and the state are
// in the hash, not in the slug; an over-long slug is refused rather than truncated.
export function slugOf(key) {
  const parts = keyParts(key);
  const slug = parts[1] + "-" + parts[2];
  if (slug.length > 16) fail("slug", `the slug ${JSON.stringify(slug)} is longer than 16 characters`);
  return slug;
}

export function className(key) {
  return CLASS_PREFIX + slugOf(key) + "-" + hex8(fnv1a32(key));
}

// A `Class` stores its key, the rendered name and whether it is a public fixed name.
// `pkg` is the key's first segment (or the fixed name's namespace); the generator
// checks it against the owning profile.
function makeClass(key, fixed, pkg) {
  return frozen({ key, name: fixed ? key : className(key), fixed, pkg });
}

function assertClass(c) {
  if (!c || typeof c !== "object" || typeof c.name !== "string" ||
      typeof c.key !== "string" || typeof c.fixed !== "boolean") {
    fail("class", "a class attribute accepts Class values, never payload strings");
  }
  return c;
}

export const Class = frozen({
  // Scoped, hashed class. `opts.pkg` is the owning package (`grail.wiz` name); when
  // present the key's first segment must equal it.
  of(key, opts = {}) {
    const parts = keyParts(key);
    const pkg = opts.pkg === undefined ? parts[0] : opts.pkg;
    if (typeof pkg !== "string" || !SEGMENT.test(pkg)) fail("pkg", `bad package ${JSON.stringify(pkg)}`);
    if (parts[0] !== pkg) {
      fail("key-prefix", `package ${JSON.stringify(pkg)} cannot claim the key ${JSON.stringify(key)}`);
    }
    return makeClass(key, false, pkg);
  },

  // A public name: one of the eight fixed `hl-*` classes or a `wz-*` payload style.
  // Anything else (notably `lz-*`, `wiz-*`, an unknown `hl-*`) is refused.
  fixed(name) {
    if (typeof name !== "string") fail("fixed-name", "a fixed class name must be a string");
    if (HL_SET.has(name)) return makeClass(name, true, "hl");
    if (name.startsWith(WZ_PREFIX) && SEGMENT.test(name.slice(WZ_PREFIX.length))) {
      return makeClass(name, true, "wz");
    }
    fail("fixed-name", `the public class ${JSON.stringify(name)} is not hl-* or wz-*`);
  },

  name(c) { return assertClass(c).name; },

  // The one `class` attribute: dedupe by key, then sort the rendered names. Sorted
  // names make an adopt and a patch byte-identical for the same state.
  attr(classes) {
    if (!Array.isArray(classes)) fail("class", "Class.attr needs a list of Class values");
    const byKey = new Map();
    for (const c of classes) byKey.set(assertClass(c).key, c.name);
    return ["class", [...new Set(byKey.values())].sort().join(" ")];
  },

  attrValue(classes) { return Class.attr(classes)[1]; },

  all(base, extra = []) {
    assertClass(base);
    if (!Array.isArray(extra)) fail("class", "Class.all needs a list");
    return [base, ...extra];
  },

  if(ok, c) { return ok ? [assertClass(c)] : []; },

  // The wire/adopt serialisation: a state change is at most one `setAttr "class"` whose
  // value is exactly the SSR attribute. `null` means the attribute did not change.
  patch(path, before, after) {
    const value = Class.attrValue(after);
    if (Class.attrValue(before) === value) return null;
    return frozen({ op: "setAttr", path: String(path), name: "class", value });
  },
});

// ## Values

const IDENT = /^[a-z][a-z0-9-]*$/;
const TOKEN = /^(?:lz|hl)-[a-z0-9-]+$/;
const PROP = /^[a-z][a-z-]*$/;

// A value is a tagged union. The constructors are the vocabulary; there is no
// `Style.padding("4px 16px")` string form except `Style.raw`.
function makeValue(kind, props = {}) { return frozen({ kind, ...props }); }

function num(n, what) {
  if (!Number.isInteger(n) || n < 0) fail("value", `${what} must be a non-negative integer`);
  return n;
}

function validateValueText(text, code = "value") {
  if (typeof text !== "string" || text.length === 0) fail(code, "an empty value is refused");
  if (/[;{}@\\]/.test(text) || /url\s*\(/i.test(text)) {
    fail(code, `the value ${JSON.stringify(text)} contains a refused token`);
  }
  if (/[\u0000-\u001f\u007f]/.test(text)) fail(code, "a value may not contain a control character");
  return text;
}

const KEYWORDS = Object.freeze({
  inherit: "inherit", initial: "initial", unset: "unset",
  flex: "flex", grid: "grid", block: "block", inlineFlex: "inline-flex", inline: "inline",
  none: "none", auto: "auto", default: "default",
  fixed: "fixed", absolute: "absolute", relative: "relative", static: "static", sticky: "sticky",
  pointer: "pointer", column: "column", row: "row", wrap: "wrap", nowrap: "nowrap",
  preWrap: "pre-wrap", semibold: "600", bold: "700", italic: "italic",
  solid: "solid", dashed: "dashed", dotted: "dotted",
  hidden: "hidden", visible: "visible", scroll: "auto", clip: "hidden",
});

export const Value = frozen({
  keyword(k) {
    if (k && typeof k === "object" && k.kind === "keyword") return k;
    if (typeof k !== "string" || !(k in KEYWORDS)) fail("value", `unknown keyword ${JSON.stringify(k)}`);
    return makeValue("keyword", { css: KEYWORDS[k] });
  },
  px(n) { return makeValue("px", { n: num(n, "px") }); },
  rem(n) { return makeValue("rem", { n: num(n, "rem") }); },
  number(n) { return makeValue("number", { n: num(n, "number") }); },
  var(name) {
    if (typeof name !== "string" || !TOKEN.test(name)) {
      fail("value", `the token ${JSON.stringify(name)} is not lz-* or hl-*`);
    }
    return makeValue("var", { name });
  },
  // Space-separated components: `padding:4px 16px`, `border:1px solid var(--lz-line)`.
  seq(...parts) { return makeValue("seq", { parts: parts.flat().map(normalizeValue) }); },
  sparse(...parts) { return Value.seq(...parts); },
  comma(...parts) { return makeValue("comma", { parts: parts.flat().map(normalizeValue) }); },
  border(width, style = Value.keyword("solid"), color) {
    return Value.seq(width, Value.keyword(style), color);
  },
  outline(width, style = Value.keyword("solid"), color, offset) {
    const parts = [width, Value.keyword(style), color];
    if (offset !== undefined) parts.push(offset);
    return Value.seq(...parts);
  },
  // The closed shadow scale in `lib/Web/Style/Tokens.wiz`; at this layer it is a value
  // shape, still checked for `;{}@url(`.
  shadow(text) { return makeValue("raw", { text: validateValueText(text) }); },
  raw(text) { return makeValue("raw", { text: validateValueText(text) }); },
});

function normalizeValue(v) {
  if (v && typeof v === "object" && typeof v.kind === "string") return v;
  fail("value", "a declaration value is a Value, not a string");
}

// ## Properties and rules

const PROP_CSS = Object.freeze({
  display: "display", position: "position", inset: "inset", zIndex: "z-index",
  flexDirection: "flex-direction", flexWrap: "flex-wrap", flex: "flex",
  gap: "gap", margin: "margin", padding: "padding",
  alignItems: "align-items", justifyContent: "justify-content",
  width: "width", height: "height", minWidth: "min-width", maxWidth: "max-width",
  overflow: "overflow", overflowX: "overflow-x", overflowY: "overflow-y",
  color: "color", background: "background", backgroundColor: "background-color",
  border: "border", borderColor: "border-color", borderLeft: "border-left",
  radius: "border-radius", shadow: "box-shadow",
  font: "font", fontSize: "font-size", fontWeight: "font-weight", lineHeight: "line-height",
  whiteSpace: "white-space", textAlign: "text-align", textDecoration: "text-decoration",
  opacity: "opacity", pointerEvents: "pointer-events", cursor: "cursor",
  outline: "outline", outlineOffset: "outline-offset",
  transition: "transition", transform: "transform",
  content: "content", userSelect: "user-select",
});
const PROP_ORDER = Object.keys(PROP_CSS);
const PROP_INDEX = new Map(PROP_ORDER.map((k, i) => [PROP_CSS[k], i]));

function propName(prop) {
  if (prop && typeof prop === "object" && prop.kind === "raw") return prop.name;
  if (typeof prop !== "string" || !(prop in PROP_CSS)) {
    fail("prop", `unknown property ${JSON.stringify(prop)}`);
  }
  return PROP_CSS[prop];
}

function normalizeProp(prop) {
  if (prop && typeof prop === "object" && prop.kind === "raw") return prop;
  return propName(prop);
}

export const Media = frozen({
  colorScheme: frozen({ kind: "media", css: "(prefers-color-scheme:dark)" }),
  reducedMotion: frozen({ kind: "media", css: "(prefers-reduced-motion:reduce)" }),
  moreContrast: frozen({ kind: "media", css: "(prefers-contrast:more)" }),
  hoverNone: frozen({ kind: "media", css: "(hover:none)" }),
  maxWidth(px) { return frozen({ kind: "media", css: `(max-width:${num(px, "maxWidth")}px)` }); },
});

function assertMedia(m) {
  if (!m || typeof m !== "object" || m.kind !== "media" || typeof m.css !== "string") {
    fail("media", "a media query is one of the closed Media values");
  }
  return m;
}

function valueCss(v) {
  normalizeValue(v);
  switch (v.kind) {
    case "keyword": return v.css;
    case "px": return v.n + "px";
    case "rem": return v.n + "rem";
    case "number": return String(v.n);
    case "var": return `var(--${v.name})`;
    case "seq": return v.parts.map(valueCss).join(" ");
    case "comma": return v.parts.map(valueCss).join(",");
    case "raw": return validateValueText(v.text);
    default: fail("value", `unknown value kind ${JSON.stringify(v.kind)}`);
  }
}

function validateValue(v) {
  if (!v || typeof v !== "object") fail("value", "not a Value");
  switch (v.kind) {
    case "keyword":
      if (typeof v.css !== "string" || v.css.length === 0) fail("value", "bad keyword");
      return;
    case "px": case "rem": case "number": num(v.n, v.kind); return;
    case "var":
      if (typeof v.name !== "string" || !TOKEN.test(v.name)) fail("value", "bad token");
      return;
    case "seq": case "comma":
      if (!Array.isArray(v.parts) || v.parts.length === 0) fail("value", "empty value list");
      for (const p of v.parts) validateValue(p);
      return;
    case "raw": validateValueText(v.text); return;
    default: fail("value", `unknown value kind ${JSON.stringify(v.kind)}`);
  }
}

function makeRule(attaches, decls) { return { attaches, decls }; }
function makeStyle(rules) { return frozen({ rules }); }
function rule(attaches, decls) { return frozen(makeRule(attaches, decls)); }

const EMPTY = makeStyle([]);

function assertStyle(s) {
  if (!s || typeof s !== "object" || !Array.isArray(s.rules)) fail("style", "not a Style");
  for (const r of s.rules) {
    if (!Array.isArray(r.attaches) || !Array.isArray(r.decls)) fail("style", "bad rule");
    for (const a of r.attaches) {
      if (a.kind === "pseudo") {
        if (typeof a.name !== "string" || !/^[a-z][a-z0-9-]*$/.test(a.name)) fail("pseudo", "bad pseudo-class");
      } else if (a.kind === "media") assertMedia(a);
      else fail("attach", `unknown attachment ${JSON.stringify(a.kind)}`);
    }
    for (const d of r.decls) {
      normalizeProp(d.prop);
      validateValue(d.value);
    }
  }
  return s;
}

function withAttaches(s, f) {
  assertStyle(s);
  return makeStyle(s.rules.map((r) => rule(f(r.attaches), r.decls)));
}

export const Style = frozen({
  empty: EMPTY,

  // A base declaration. Setting the same property again is last-wins in the emitter.
  set(prop, value) {
    normalizeProp(prop);
    normalizeValue(value);
    return makeStyle([rule([], [{ prop, value }])]);
  },

  // Concatenate rules. The emitter keeps the last declaration per (attachment,
  // property), so `Style.merge a b` lets `b` win without depending on source order.
  merge(a, b) {
    assertStyle(a); assertStyle(b);
    return makeStyle([...a.rules, ...b.rules]);
  },

  when(ok, s) { return ok ? assertStyle(s) : EMPTY; },

  pseudo(name, s) {
    if (typeof name !== "string" || !/^[a-z][a-z0-9-]*$/.test(name)) fail("pseudo", "bad pseudo-class");
    return withAttaches(s, (as) => [...as, frozen({ kind: "pseudo", name })]);
  },
  hover(s) { return Style.pseudo("hover", s); },
  focusVisible(s) { return Style.pseudo("focus-visible", s); },
  active(s) { return Style.pseudo("active", s); },
  disabled(s) { return Style.pseudo("disabled", s); },

  // Outer-to-inner: media first, so `Style.media m (Style.hover s)` emits
  // `@media m{.x:hover{…}}`.
  media(m, s) {
    assertMedia(m);
    return withAttaches(s, (as) => [frozen({ kind: "media", ...m }), ...as]);
  },

  // The one escape hatch. The property is a CSS identifier and the value may not carry
  // `;`, `{`, `}`, `@`, `\`, `url(` or a control character. This refuses injection, not
  // CSS semantics; a bad colour is still the caller's bug.
  raw(prop, value) {
    if (typeof prop !== "string" || !PROP.test(prop)) {
      fail("raw", `the raw property ${JSON.stringify(prop)} is not a lower-case identifier`);
    }
    return makeStyle([rule([], [{
      prop: frozen({ kind: "raw", name: prop }),
      value: frozen({ kind: "raw", text: validateValueText(value, "raw") }),
    }])]);
  },

  sheet(groups, opts = {}) {
    const profile = opts.profile === undefined ? "web" : String(opts.profile);
    const styled = [];
    const seen = new Map();
    for (const g of groups) {
      if (!g || typeof g !== "object" || !Array.isArray(g.styles)) {
        fail("sheet", "a sheet group is {pkg, styles}");
      }
      const pkg = g.pkg;
      if (pkg !== undefined && (typeof pkg !== "string" || !SEGMENT.test(pkg))) {
        fail("pkg", `bad package ${JSON.stringify(pkg)}`);
      }
      for (const s of g.styles) {
        if (!s || typeof s !== "object") fail("sheet", "a group holds Styled values");
        const c = assertClass(s.cls);
        assertStyle(s.style);
        if (!c.fixed) {
          const parts = keyParts(c.key);
          if (pkg !== undefined && parts[0] !== pkg) {
            fail("key-prefix", `package ${JSON.stringify(pkg)} cannot claim ${JSON.stringify(c.key)}`);
          }
        }
        const prev = seen.get(c.name);
        if (prev !== undefined && prev !== c.key) {
          fail("collision", `the keys ${JSON.stringify(prev)} and ${JSON.stringify(c.key)} both name ${c.name}`);
        }
        seen.set(c.name, c.key);
        styled.push(s);
      }
    }

    styled.sort((a, b) => (a.cls.name < b.cls.name ? -1 : a.cls.name > b.cls.name ? 1 : 0));
    const lines = [];
    for (const s of styled) {
      for (const r of groupedRules(s.style)) lines.push(ruleCss(s.cls.name, r));
    }
    const body = lines.join("\n");
    const header = `/* generated by web/framework/style.js schema=${SHEET_SCHEMA} profile=${profile} classes=${styled.length} */`;
    return body === "" ? header + "\n" : header + "\n" + body + "\n";
  },

  // The browser-free validation row (11). Returns `null` or the first refusal, so a
  // generator can fail the build before bytes are written.
  check(style) {
    try { assertStyle(style); return null; }
    catch (e) { return e instanceof StyleError ? e : fail("style", String(e)); }
  },
});

function attachKey(attaches) {
  return attaches.map((a) => (a.kind === "pseudo" ? "p:" + a.name : "m:" + a.css)).join("|");
}

// `Style.merge` concatenates rules, so the same attachment chain can appear more than
// once. Grouping makes the block canonical and lets a later declaration win regardless
// of where the merge happened.
function groupedRules(style) {
  assertStyle(style);
  const order = [];
  const byKey = new Map();
  for (const r of style.rules) {
    const key = attachKey(r.attaches);
    if (!byKey.has(key)) {
      byKey.set(key, { attaches: r.attaches, decls: [] });
      order.push(key);
    }
    byKey.get(key).decls.push(...r.decls);
  }
  const mediaKey = (as) => {
    const m = as.find((a) => a.kind === "media");
    return m === undefined ? "" : m.css;
  };
  // Base rule first, then pseudo variants, then media blocks; the tie-break is the
  // selector text. The generated bytes therefore do not depend on merge order.
  return order.map((key) => byKey.get(key)).sort((a, b) => {
    const am = mediaKey(a.attaches), bm = mediaKey(b.attaches);
    if (am !== bm) return am < bm ? -1 : 1;
    const as = selector("", a.attaches), bs = selector("", b.attaches);
    return as < bs ? -1 : as > bs ? 1 : 0;
  });
}

function canonicalDecls(decls) {
  // Last-wins by property name; order by PROP_ORDER so a merge's source order cannot
  // change the bytes. Raw properties keep their position after the known ones.
  const last = new Map();
  for (const d of decls) last.set(propName(d.prop), d);
  const known = [...last.entries()]
    .filter(([name]) => PROP_INDEX.has(name))
    .sort((a, b) => PROP_INDEX.get(a[0]) - PROP_INDEX.get(b[0]));
  const raw = [...last.entries()].filter(([name]) => !PROP_INDEX.has(name));
  return [...known, ...raw].map(([, d]) => d);
}

function selector(name, attaches) {
  let suffix = "";
  for (const a of attaches) {
    if (a.kind === "pseudo") suffix += ":" + a.name;
  }
  return "." + name + suffix;
}

function wrapMedia(attaches, body) {
  // The list is outer-to-inner, so the first media wrapper is the outermost.
  let out = body;
  for (const a of [...attaches].reverse()) {
    if (a.kind === "media") out = `@media ${a.css}{${out}}`;
  }
  return out;
}

function ruleCss(name, r) {
  const decls = canonicalDecls(r.decls)
    .map((d) => `${propName(d.prop)}:${valueCss(d.value)}`).join(";");
  return wrapMedia(r.attaches, `${selector(name, r.attaches)}{${decls}}`);
}

// A `Styled` is the build-time pair. Splitting it from `Class` is what lets a runtime
// import keys only; the declarations stay in the generator.
export const Styled = frozen({
  of(cls, style) {
    assertClass(cls);
    assertStyle(style);
    return frozen({ cls, style });
  },
  fixed(name, style) { return Styled.of(Class.fixed(name), style); },
});

// The generator's validation row, and only that row. Rows 3–7 and 10 are `wire.js`'s;
// a copy here would be a second statement of the wire's table.
export const VALIDATION = Object.freeze([
  Object.freeze({
    id: 11,
    boundary: "CSS generator (build)",
    impl: "web/framework/style.js#Style.sheet",
    validates: "key prefix, collision gate, public names, raw declaration shape, no url(/@import/style=",
    doesNotValidate: "page composition, CSS semantics",
    failure: "build fails",
  }),
]);
