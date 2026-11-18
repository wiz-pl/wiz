#!/usr/bin/env python3
"""Crawl an assembled `doc-site` and fail on a link that cannot work.

Three rules, the ones the published site promises (docs/building.md, "Documentation
site"):

  a. no link points at a Markdown file. A link on the site resolves to a rendered page;
     the one exception is a page's own source link, because a rendered page may name the
     `.md` it came from. A source link is an `<a>` with class `src` or rel `source` and an
     absolute http(s) URL.
  b. every internal link resolves to a file in the tree (a directory means its
     `index.html`), and its fragment, if any, is an `id` on the target page. A link that
     starts with `/` is refused: it breaks the project-site prefix.
  c. every rendered page carries a source link (`.src`): a `docs/` module page (one with
     `class="decl"`), every page under `guide/`, and every page under `notebooks/`.

External links (http, https, mailto, data) are not fetched, but an http(s) link ending in
`.md` is still an error: it is a link to a repository Markdown file.

    usage: web/check-links.py [SITE] [--quiet]
"""

import os
import posixpath
import re
import sys
import urllib.parse

EXT = re.compile(r"^[a-z][a-z0-9+.-]*:", re.I)
TAG = re.compile(r"<(a|link|img|script|source)\b([^>]*)>", re.I | re.S)
ATTR = re.compile(r"""\b(href|src)\s*=\s*"([^"]*)\"""", re.I)
CLASS = re.compile(r"""\bclass\s*=\s*"([^"]*)\"""", re.I)
REL = re.compile(r"""\brel\s*=\s*"([^"]*)\"""", re.I)


def source_anchor(attrs):
    cls = CLASS.search(attrs)
    rel = REL.search(attrs)
    return bool(
        (cls and "src" in cls.group(1).split())
        or (rel and "source" in rel.group(1).split())
    )


def read(path):
    try:
        with open(path, encoding="utf-8", errors="replace") as f:
            return f.read()
    except OSError:
        return ""


def main(argv):
    args = [a for a in argv if not a.startswith("-")]
    quiet = "--quiet" in argv
    site = args[0] if args else "doc-site"
    if not os.path.isdir(site):
        print(f"check-links: {site} is not a directory", file=sys.stderr)
        return 2

    pages = []
    for base, dirs, names in os.walk(site):
        dirs[:] = sorted(d for d in dirs if not d.startswith("."))
        for n in sorted(names):
            if n.endswith(".html"):
                pages.append(os.path.relpath(os.path.join(base, n), site))
    pages.sort()

    errors = []
    ids = {}

    def page_ids(rel):
        if rel not in ids:
            ids[rel] = set(
                re.findall(
                    r"""\bid\s*=\s*"([^"]*)\"""",
                    read(os.path.join(site, rel)),
                )
            )
        return ids[rel]

    for rel in pages:
        text = read(os.path.join(site, rel))
        base = posixpath.dirname(rel)
        for tag in TAG.finditer(text):
            attrs = tag.group(2)
            cls = CLASS.search(attrs)
            is_src = (tag.group(1).lower() == "a" and source_anchor(attrs))
            for attr in ATTR.finditer(attrs):
                url = attr.group(2)
                if not url:
                    continue
                lower = url.lower()
                if lower.startswith(("mailto:", "data:", "javascript:", "#")):
                    continue
                # (a) A Markdown file is never a destination; only a page's own source
                # link may name the `.md` it came from.
                if url.split("#")[0].split("?")[0].lower().endswith(".md") and not is_src:
                    errors.append(f"{rel}: link to a Markdown file: {url}")
                    continue
                if lower.startswith("//"):
                    external = "https:" + url
                elif EXT.match(url):
                    external = url
                else:
                    external = None
                if external is not None:
                    continue
                path, _, frag = url.partition("#")
                path = path.split("?")[0]
                if not path:
                    target = rel
                else:
                    path = urllib.parse.unquote(path)
                    if path.startswith("/"):
                        errors.append(
                            f"{rel}: root-absolute link {url} (the tree must stay "
                            "relocatable)"
                        )
                        continue
                    target = posixpath.normpath(posixpath.join(base, path))
                    if target.startswith("../") or target == "..":
                        errors.append(f"{rel}: link escapes the site: {url}")
                        continue
                    if path.endswith("/") or os.path.isdir(
                        os.path.join(site, target)
                    ):
                        target = posixpath.join(target, "index.html")
                full = os.path.join(site, target)
                if not os.path.isfile(full):
                    errors.append(f"{rel}: {url} does not resolve ({target})")
                    continue
                if frag and target.endswith(".html"):
                    if urllib.parse.unquote(frag) not in page_ids(target):
                        errors.append(
                            f"{rel}: {url}: no id '{urllib.parse.unquote(frag)}' "
                            f"on {target}"
                        )

    # (c) a rendered page has a source link.
    for rel in pages:
        text = read(os.path.join(site, rel))
        module_page = rel.startswith("docs" + os.sep) and 'class="decl"' in text
        guide_page = rel.startswith("guide" + os.sep)
        notebook_page = rel.startswith("notebooks" + os.sep)
        if not (module_page or guide_page or notebook_page):
            continue
        if not any(
            source_anchor(t.group(2)) for t in TAG.finditer(text)
        ):
            errors.append(f"{rel}: no source link (a.src)")

    for e in errors:
        print(f"check-links: {e}", file=sys.stderr)
    if not quiet:
        print(
            f"check-links: {len(pages)} page{'s' if len(pages) != 1 else ''}, "
            f"{len(errors)} error{'s' if len(errors) != 1 else ''}"
        )
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
