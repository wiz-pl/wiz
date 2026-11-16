// A minimal DOM for web/framework/test.mjs: enough of Element, Text, DocumentFragment
// and events to run runtime.js's patch applier and event delegation under Node, with
// the same HTML string in and out (so the round trip is exact). It is a test double,
// not a browser: no layout, no CSS, no scripts, no HTML error recovery.
"use strict";

const VOID = new Set(["area", "base", "br", "col", "embed", "hr", "img", "input",
  "link", "meta", "param", "source", "track", "wbr"]);

class Node {
  constructor() { this.parentNode = null; this.childNodes = []; this._ls = new Map(); }
  get textContent() { return this.childNodes.map((n) => n.textContent).join(""); }
  set textContent(v) {
    for (const c of this.childNodes) c.parentNode = null;
    this.childNodes = [];
    if (v !== "") this.appendChild(new Text(String(v)));
  }
  appendChild(n) {
    if (n.parentNode) n.parentNode.removeChild(n);
    n.parentNode = this;
    this.childNodes.push(n);
    return n;
  }
  insertBefore(n, ref) {
    if (n.parentNode) n.parentNode.removeChild(n);
    const i = ref == null ? this.childNodes.length : this.childNodes.indexOf(ref);
    if (i < 0) throw new Error("insertBefore: reference is not a child");
    n.parentNode = this;
    this.childNodes.splice(i, 0, n);
    return n;
  }
  removeChild(n) {
    const i = this.childNodes.indexOf(n);
    if (i < 0) throw new Error("removeChild: not a child");
    this.childNodes.splice(i, 1);
    n.parentNode = null;
    return n;
  }
  addEventListener(type, fn) {
    if (!this._ls.has(type)) this._ls.set(type, []);
    this._ls.get(type).push(fn);
  }
  dispatchEvent(e) {
    e.target = e.target || this;
    e.preventDefault = () => { e.defaultPrevented = true; };
    for (let n = this; n; n = n.parentNode) {
      for (const fn of n._ls.get(e.type) || []) fn(e);
    }
    return !e.defaultPrevented;
  }
}

class Text extends Node {
  constructor(data) { super(); this.data = String(data); }
  get textContent() { return this.data; }
  set textContent(v) { this.data = String(v); }
}

class Element extends Node {
  constructor(tagName) {
    super();
    this.tagName = tagName;
    this.attrs = new Map();
  }
  getAttribute(name) { return this.attrs.has(name) ? this.attrs.get(name) : null; }
  setAttribute(name, value) { this.attrs.set(String(name), String(value)); }
  removeAttribute(name) { this.attrs.delete(name); }
  get ownerDocument() { return doc; }
}

class DocumentFragment extends Node {}

const doc = {
  createElement: (tag) => new Element(tag),
  createTextNode: (s) => new Text(s),
  createRange: () => ({ createContextualFragment: (html) => parseFragment(html) }),
};

// ## Parsing

const NAMED = { amp: "&", lt: "<", gt: ">", quot: "\"", apos: "'", nbsp: "\u00a0" };

function decode(s) {
  return s.replace(/&(#x[0-9a-fA-F]+|#[0-9]+|[a-zA-Z]+);/g, (m, body) => {
    if (body[0] === "#") {
      const n = body[1] === "x" ? parseInt(body.slice(2), 16) : parseInt(body.slice(1), 10);
      return Number.isFinite(n) ? String.fromCodePoint(n) : m;
    }
    return body in NAMED ? NAMED[body] : m;
  });
}

function tagEnd(html, at) {
  let quote = null;
  for (let i = at; i < html.length; i++) {
    const c = html[i];
    if (quote) { if (c === quote) quote = null; }
    else if (c === "\"" || c === "'") quote = c;
    else if (c === ">") return i;
  }
  throw new Error("unterminated tag");
}

function parseFragment(html) {
  const root = new DocumentFragment();
  const stack = [root];
  const top = () => stack[stack.length - 1];
  let i = 0;
  while (i < html.length) {
    if (html[i] !== "<") {
      const j = html.indexOf("<", i);
      const end = j < 0 ? html.length : j;
      top().appendChild(new Text(decode(html.slice(i, end))));
      i = end;
      continue;
    }
    if (html.startsWith("<!--", i)) {
      const j = html.indexOf("-->", i + 4);
      i = j < 0 ? html.length : j + 3;
      continue;
    }
    if (html[i + 1] === "/") {
      const end = html.indexOf(">", i);
      if (end < 0) throw new Error("unterminated close tag");
      const tag = html.slice(i + 2, end).trim();
      if (stack.length > 1 && top().tagName === tag) stack.pop();
      else throw new Error("close tag </" + tag + "> does not match " + (top().tagName || "the root"));
      i = end + 1;
      continue;
    }
    const end = tagEnd(html, i + 1);
    let body = html.slice(i + 1, end);
    i = end + 1;
    const selfClose = body.endsWith("/");
    if (selfClose) body = body.slice(0, -1);
    const m = /^([A-Za-z0-9-]+)/.exec(body);
    if (!m) throw new Error("bad tag: <" + body + ">");
    const tag = m[1];
    const el = new Element(tag);
    const rest = body.slice(m[0].length);
    const re = /([^\s=]+)(?:\s*=\s*("([^"]*)"|'([^']*)'|([^\s"'>]+)))?/g;
    let a;
    while ((a = re.exec(rest))) {
      const value = a[3] !== undefined ? a[3] : a[4] !== undefined ? a[4] : a[5] !== undefined ? a[5] : "";
      el.setAttribute(a[1], decode(value));
    }
    top().appendChild(el);
    if (!selfClose && !VOID.has(tag.toLowerCase())) stack.push(el);
  }
  if (stack.length !== 1) throw new Error("unclosed <" + top().tagName + ">");
  return root;
}

// ## Serializing (the same escaping as Tagged.esc in lib/Tagged.wiz)

function esc(s) {
  return String(s).replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;")
    .replace(/"/g, "&quot;").replace(/'/g, "&#39;");
}

function write(n, out) {
  if (n instanceof Text) { out.push(esc(n.data)); return; }
  if (n instanceof DocumentFragment) { for (const c of n.childNodes) write(c, out); return; }
  out.push("<" + n.tagName);
  for (const [k, v] of n.attrs) out.push(" " + k + "=\"" + esc(v) + "\"");
  out.push(">");
  if (VOID.has(n.tagName.toLowerCase())) return;
  for (const c of n.childNodes) write(c, out);
  out.push("</" + n.tagName + ">");
}

export function serialize(n) {
  const out = [];
  write(n, out);
  return out.join("");
}

export function parse(html) { return parseFragment(html); }
export function document() { return doc; }
export { Element, Text, DocumentFragment };
