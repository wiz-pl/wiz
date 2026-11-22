/* A tiny fake DOM for `examples/js-loom/loom.wiz`.
 *
 * It implements only the operations the Wiz demo calls, and records every one so the
 * harness can assert what the Wiz code did. `document.createElement` is the real DOM
 * path; the rest are the `wiz.dom` adapter a browser host would install over
 * `Element`.
 */

export function install() {
  const ops = [];
  const creates = [];

  function makeElement(tag) {
    const el = {
      tag,
      attrs: new Map(),
      children: [],
      listeners: [],
      text: "",
      setAttribute(k, v) {
        el.attrs.set(k, v);
        ops.push(["attr", tag, k, v]);
      },
      getAttribute(k) {
        return el.attrs.has(k) ? el.attrs.get(k) : "";
      },
      appendChild(child) {
        el.children.push(child);
        ops.push(["append", tag, child.tag]);
      },
      addEventListener(event, fn) {
        el.listeners.push({ event, fn });
        ops.push(["listen", tag, event]);
      },
      setText(s) {
        el.text = s;
        ops.push(["text", tag, s]);
      },
    };
    return el;
  }

  const root = makeElement("#root");
  globalThis.document = {
    createElement(tag) {
      const el = makeElement(tag);
      creates.push(tag);
      ops.push(["create", tag]);
      return el;
    },
  };
  globalThis.wiz = {
    dom: {
      root: () => root,
      setAttribute: (el, k, v) => el.setAttribute(k, v),
      appendChild: (el, child) => el.appendChild(child),
      addEventListener: (el, event, fn) => el.addEventListener(event, fn),
      getAttribute: (el, k) => el.getAttribute(k),
      setText: (el, s) => el.setText(s),
    },
  };
  return { root, ops, creates };
}

export function allElements(root) {
  const out = [];
  const go = (el) => {
    out.push(el);
    for (const c of el.children) go(c);
  };
  go(root);
  return out;
}
