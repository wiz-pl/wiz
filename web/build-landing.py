#!/usr/bin/env python3
"""Assemble the landing page from its template and the snippet files.

The page's code blocks are **files**: every carousel panel is
`web/landing/snippets/<name>.wiz`, and the only bytes on the page are those bytes
(escaped, and highlighted at build time by `web/landing_highlight.py`). The
"run it in the playground" link carries the same bytes as `#code=<base64url>`, the
fragment `Web.Draft.decodeFragment` already understands, so the page never embeds a
second compiler or a second copy of the code.

    usage: web/build-landing.py --out FILE [--root DIR] [--island JSON]

`--island JSON` is `web/landing/static_gen.wiz`'s `{html, hash}`: the Loom app's first
paint and its normalised-tree hash. Without it (a docs-only build) the quantity section
is a static explainer with all three panels, which is also the no-JavaScript form.
"""

import argparse
import base64
import html
import json
import os
import sys

# The template's two insertion points (one line each, so a stale build leaves a
# recognisable marker rather than a half page).
CAROUSEL = "<!--wiz-carousel-->"
ISLAND = "<!--wiz-island-->"

# The static explainer, when no island JSON was built. It is the same three programs
# the Loom app renders; without JavaScript the app's own SSR is this stack anyway.
STATIC_ISLAND = """\
<div class="q-app q0" id="quantity-widget">
  <p class="q-intro">The same shape of definition under each quantity.</p>
  <section class="q-panel" data-for="0">
    <h4>0 — erased at run time</h4>
    <pre tabindex="0"><code class="language-wiz">def ignore {0 A : Type} (0 x : A) : Nat := 0</code></pre>
    <p>The argument is absent from the compiled code: it may be a type, a proof, or an
      index, and the body cannot use it.</p>
  </section>
  <section class="q-panel" data-for="1">
    <h4>1 — used exactly once</h4>
    <pre tabindex="0"><code class="language-wiz">def identity {0 A : Type} (1 x : A) : A := x</code></pre>
    <p>A linear value must be consumed once: a file handle, a token, or a proof that
      must not be duplicated or dropped.</p>
  </section>
  <section class="q-panel" data-for="w">
    <h4>ω — unrestricted</h4>
    <pre tabindex="0"><code class="language-wiz">def dup {0 A : Type} (ω x : A) : A × A := (x, x)</code></pre>
    <p>Ordinary data is unrestricted: the body may use it any number of times, including
      twice in the same pair.</p>
  </section>
</div>"""


def esc(text):
    return html.escape(text, quote=False)


def read(path):
    with open(path, encoding="utf-8") as f:
        return f.read()


def snippet_text(root, entry):
    """A snippet's bytes as shown: its file, minus the final newline only."""
    text = read(os.path.join(root, "web", "landing", "snippets", entry["file"]))
    return text.rstrip("\n")


def playground_href(root, code):
    data = base64.urlsafe_b64encode(code.encode("utf-8")).decode("ascii").rstrip("=")
    return "playground/#code=" + data


def carousel(root, snippets):
    tabs = []
    panels = []
    for i, s in enumerate(snippets):
        name = s["name"]
        panel_id = "/s/" + name
        first = i == 0
        tabs.append(
            '<a class="tab" role="tab" id="tab-{name}" href="#{pid}" '
            'aria-controls="{pid}" aria-selected="{sel}">{title}</a>'.format(
                name=esc(name), pid=esc(panel_id), sel="true" if first else "false",
                title=esc(s["title"])))
        code = snippet_text(root, s)
        panels.append(
            """\
<article class="slide" id="{pid}" role="tabpanel" aria-labelledby="tab-{name}" tabindex="0"{active}>
  <header class="slide-head">
    <h3>{title}</h3>
    <p class="slide-lede">{lede}</p>
  </header>
  <figure class="snippet">
    <figcaption class="snippet-chrome">
      <span class="snippet-lang">Wiz</span>
      <span class="snippet-file">snippets/{file}</span>
      <span class="snippet-actions">
        <button type="button" class="copy" data-copy="{pid}" hidden>Copy</button>
        <a class="run" href="{href}">Run it in the playground <span aria-hidden="true">→</span></a>
      </span>
    </figcaption>
    <pre tabindex="0"><code class="language-wiz">{code}</code></pre>
  </figure>
</article>""".format(
                pid=esc(panel_id), name=esc(name), active=" data-active" if first else "",
                title=esc(s["title"]), lede=esc(s["lede"]), file=esc(s["file"]),
                href=esc(playground_href(root, code)), code=esc(code)))
    return (
        '<div class="carousel" id="carousel" role="region" '
        'aria-roledescription="carousel" aria-label="Wiz code snippets">\n'
        '  <div class="carousel-tabs" role="tablist" aria-label="Snippets">\n    '
        + "\n    ".join(tabs) + "\n  </div>\n"
        '  <p class="sr-only" id="carousel-status" aria-live="polite" '
        'aria-atomic="true"></p>\n'
        '  <div class="carousel-panels">\n'
        + "\n".join(panels) + "\n  </div>\n</div>")


def island(root, path):
    if not path:
        return STATIC_ISLAND
    data = json.loads(read(path))
    tree = data["html"]
    digest = data["hash"]
    if not tree or not digest.startswith("t1-"):
        raise SystemExit("build-landing: island JSON has no html/hash")
    return (
        '<div id="quantity-app" data-wiz-island="loom/1" data-wiz-ssr="{hash}">\n'
        '{tree}\n</div>'.format(hash=esc(digest), tree=tree))


def main(argv):
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default=None)
    ap.add_argument("--out", required=True)
    ap.add_argument("--island", default=None)
    args = ap.parse_args(argv)
    root = os.path.abspath(args.root or os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))

    template = read(os.path.join(root, "web", "landing", "index.html"))
    snippets = json.loads(read(os.path.join(root, "web", "landing", "snippets.json")))["snippets"]
    if not snippets:
        raise SystemExit("build-landing: snippets.json has no snippets")
    if CAROUSEL not in template or ISLAND not in template:
        raise SystemExit("build-landing: the template is missing its placeholders")
    page = template.replace(CAROUSEL, carousel(root, snippets)).replace(ISLAND, island(root, args.island))
    os.makedirs(os.path.dirname(os.path.abspath(args.out)), exist_ok=True)
    with open(args.out, "w", encoding="utf-8") as f:
        f.write(page)
    print("build-landing: {n} snippets, island {kind} -> {out}".format(
        n=len(snippets), kind="Loom" if args.island else "static", out=args.out))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
