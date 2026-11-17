#!/usr/bin/env python3
"""Render the repository's prose documentation into SITE/guide as HTML pages.

The published site must not send a reader to a repository Markdown file: a link on the
site resolves to a rendered page. `wiz doc` renders `lib/` (the API under SITE/docs);
this script renders the other half, the documents in the repository (`docs/**/*.md`,
`README.md`, `ROADMAP.md`, `CHANGELOG.md`, and the `.md` files they link to), into
`SITE/guide/<repo path>.html`, keeping the repository's relative layout. Relative links
between those files are rewritten from `.md` to `.html`; a link to any other file (a
`.wiz` source, a directory) becomes an absolute link to the repository, and an image is
copied next to the page. Every page carries one `.src` link: its Markdown source in the
repository, which is the one `.md` link a rendered page is allowed to have.

    usage: web/build-docs.py --site SITE [--root ROOT] [--source-url URL]
                             [--repo-url URL] [--check]

`--check` writes nothing and exits 1 if a page is missing or a link would not resolve.
The conversion covers the subset the repository uses: ATX headings, paragraphs, bullet
and numbered lists (nested), block quotes, fenced code, pipe tables, thematic breaks,
inline code, emphasis, links and images, and `<https://…>` autolinks. HTML in the input
is escaped, as the language's own `Wiz.Doc.Markdown` does.
"""

import argparse
import html
import os
import posixpath
import re
import shutil
import subprocess
import sys
import urllib.parse

# -- pages to render ------------------------------------------------------
# A page is anything the repository's documentation can reach. `docs/` is the whole
# documentation directory; the others are pages the README and the docs index link.
ENTRY_DIRS = ("docs/",)
ENTRY_FILES = ("README.md", "ROADMAP.md", "CHANGELOG.md")

SKIP_DIRS = {".git", ".lake", "node_modules", "doc-site", "web/out", "result"}


def tracked_markdown(root):
    """Every tracked `.md` file, repository-relative (posix)."""
    try:
        out = subprocess.check_output(
            ["git", "-C", root, "ls-files", "-z", "--cached", "--others",
             "--exclude-standard", "*.md"],
            stderr=subprocess.DEVNULL,
        )
        files = [f for f in out.decode("utf-8", "replace").split("\0") if f]
    except (OSError, subprocess.CalledProcessError):
        files = []
        for base, dirs, names in os.walk(root):
            dirs[:] = [d for d in dirs if d not in SKIP_DIRS and not d.startswith(".")]
            for n in names:
                if n.endswith(".md"):
                    files.append(os.path.relpath(os.path.join(base, n), root))
    return sorted(f.replace(os.sep, "/") for f in files)


LINK_RE = re.compile(r"!?\[[^\]]*\]\(([^)\s]+)(?:\s+\"[^\"]*\")?\)")


def reachable_pages(root, all_pages):
    """The pages to render: the entry points and every `.md` they link to.

    Rendering the closure rather than every tracked `.md` keeps unpublished notes and
    test fixtures out of the site, while a link from an entry point to one of them
    still resolves.
    """
    todo = [
        f
        for f in all_pages
        if f.startswith(ENTRY_DIRS) or f in ENTRY_FILES
    ]
    seen = set(todo)
    while todo:
        page = todo.pop()
        try:
            text = open(os.path.join(root, page), encoding="utf-8").read()
        except OSError:
            continue
        for m in LINK_RE.finditer(text):
            url = m.group(1)
            if url.startswith(("#", "http://", "https://", "mailto:", "data:")):
                continue
            path = urllib.parse.unquote(url.split("#")[0].split("?")[0])
            if not path.endswith(".md"):
                continue
            target = posixpath.normpath(
                posixpath.join(posixpath.dirname(page), path)
            )
            if target in all_pages and target not in seen:
                seen.add(target)
                todo.append(target)
    return sorted(seen)


# -- inline Markdown ------------------------------------------------------

INLINE = re.compile(
    r"(?P<code>`+)(?P<codebody>.+?)(?P=code)"
    r"|!\[(?P<alt>[^\]]*)\]\((?P<src>[^)\s]*)(?:\s+\"[^\"]*\")?\)"
    r"|\[(?P<label>[^\]]*)\]\((?P<href>[^)\s]*)(?:\s+\"[^\"]*\")?\)"
    r"|<(?P<auto>(?:https?|mailto):[^>\s]+)>"
    r"|\*\*(?P<strong>.+?)\*\*"
    r"|\*(?P<em>[^*\s][^*]*?)\*",
    re.S,
)


def escape(text):
    return html.escape(text, quote=False)


class Renderer:
    def __init__(self, page, pages, root, site, source_url, repo_url):
        self.page = page                # repo path of the Markdown file
        self.pages = pages              # repo paths of every rendered page
        self.root = root
        self.site = site
        self.source_url = source_url.rstrip("/")
        self.repo_url = repo_url.rstrip("/")
        self.errors = []
        self.headings = {}
        self.ids = set()

    # -- links ------------------------------------------------------------
    def target(self, url):
        """Classify a URL written in the Markdown.

        Returns (kind, value): `keep` (unchanged), `page` (rendered page), `file` (an
        absolute repository link), `image` (copied beside the page) or `error`.
        """
        if not url or url.startswith("#"):
            return "keep", url
        lower = url.lower()
        if lower.startswith(("http://", "https://", "//", "mailto:", "data:",
                             "javascript:", "tel:")):
            return "keep", url
        if re.match(r"^[a-z][a-z0-9+.-]*:", lower):
            return "keep", url
        path, sep, frag = url.partition("#")
        path, qsep, query = path.partition("?")
        if not path:
            return "keep", url
        path = urllib.parse.unquote(path)
        here = posixpath.dirname(self.page)
        repo_path = posixpath.normpath(posixpath.join(here, path))
        if repo_path.startswith("../") or repo_path == "..":
            return "error", url
        tail = sep + frag + qsep + query
        if path.endswith(".md"):
            if repo_path not in self.pages:
                return "error", url
            out = "guide/" + repo_path[:-3] + ".html"
            return "page", self.rel_to_site(out) + tail
        # An exported notebook is a page of the site (`/notebooks/`), not a repository
        # file to open on GitHub.
        if repo_path.startswith("docs/notebooks/") and repo_path.endswith(".html"):
            out = "notebooks/" + posixpath.basename(repo_path)
            return "page", self.rel_to_site(out) + tail
        full = os.path.join(self.root, repo_path)
        if os.path.isfile(full):
            if re.search(r"\.(png|jpe?g|gif|svg|webp)$", repo_path, re.I):
                out = "guide/" + repo_path
                return "image", self.rel_to_site(out), repo_path

            return "file", self.repo_url + "/blob/master/" + urllib.parse.quote(repo_path)
        if os.path.isdir(full):
            return "file", self.repo_url + "/tree/master/" + urllib.parse.quote(repo_path)
        return "error", url

    def rel_to_site(self, site_path):
        out_dir = posixpath.dirname("guide/" + self.page[:-3] + ".html")
        return posixpath.relpath(site_path, start=out_dir or ".")

    def href(self, url):
        kind, *rest = self.target(url)
        if kind == "error":
            self.errors.append(f"{self.page}: link '{url}' does not resolve")
            return url
        return rest[0]

    # -- headings ---------------------------------------------------------
    def slug(self, text):
        plain = re.sub(r"`+", "", text)
        plain = re.sub(r"!?\[([^\]]*)\]\([^)]*\)", r"\1", plain)
        plain = plain.lower()
        slug = "".join(
            c for c in plain if c.isalnum() or c in "-_ " or ord(c) > 127
        ).replace(" ", "-")
        slug = slug.strip("-") or "section"
        n = slug
        i = 1
        while n in self.ids:
            n = f"{slug}-{i}"
            i += 1
        self.ids.add(n)
        return n

    # -- inline -----------------------------------------------------------
    def inline(self, text):
        out = []
        pos = 0
        for m in INLINE.finditer(text):
            out.append(escape(text[pos:m.start()]))
            pos = m.end()
            if m.group("code") is not None:
                body = m.group("codebody").strip()
                out.append("<code>" + escape(body) + "</code>")
            elif m.group("alt") is not None:
                url = self.href(m.group("src"))
                out.append(
                    f'<img src="{escape(url)}" alt="{escape(m.group("alt"))}">'
                )
            elif m.group("label") is not None:
                url = self.href(m.group("href"))
                out.append(
                    f'<a href="{escape(url)}">{self.inline(m.group("label"))}</a>'
                )
            elif m.group("auto") is not None:
                url = m.group("auto")
                out.append(f'<a href="{escape(url)}">{escape(url)}</a>')
            elif m.group("strong") is not None:
                out.append("<strong>" + self.inline(m.group("strong")) + "</strong>")
            elif m.group("em") is not None:
                out.append("<em>" + self.inline(m.group("em")) + "</em>")
        out.append(escape(text[pos:]))
        return "".join(out)

    # -- blocks -----------------------------------------------------------
    def blocks(self, lines):
        out = []
        i = 0
        n = len(lines)
        while i < n:
            line = lines[i]
            if not line.strip():
                i += 1
                continue
            fence = re.match(r"^\s*(`{3,}|~{3,})\s*(.*?)\s*$", line)
            if fence:
                marker = fence.group(1)
                lang = fence.group(2).split()[0] if fence.group(2).split() else ""
                i += 1
                body = []
                while i < n and not re.match(
                    r"^\s*" + re.escape(marker[0]) + "{" + str(len(marker)) + r",}\s*$",
                    lines[i],
                ):
                    body.append(lines[i])
                    i += 1
                i += 1
                cls = f' class="language-{escape(lang)}"' if lang else ""
                out.append(
                    f"<pre><code{cls}>{escape(chr(10).join(body))}</code></pre>"
                )
                continue
            heading = re.match(r"^(#{1,6})\s+(.*?)\s*#*\s*$", line)
            if heading:
                level = len(heading.group(1))
                text = heading.group(2)
                out.append(
                    f'<h{level} id="{self.slug(text)}">{self.inline(text)}</h{level}>'
                )
                i += 1
                continue
            if re.match(r"^\s*((\*\s*){3,}|(-\s*){3,}|(_\s*){3,})$", line):
                out.append("<hr>")
                i += 1
                continue
            if "|" in line and i + 1 < n and is_table_rule(lines[i + 1]):
                i = self.table(lines, i, out)
                continue
            if line.lstrip().startswith(">"):
                quoted = []
                while i < n and lines[i].lstrip().startswith(">"):
                    quoted.append(re.sub(r"^\s*>\s?", "", lines[i]))
                    i += 1
                out.append("<blockquote>" + self.blocks(quoted) + "</blockquote>")
                continue
            if list_match(line):
                i = self.list(lines, i, out)
                continue
            para = []
            while i < n and lines[i].strip() and not block_start(lines[i], lines, i):
                para.append(lines[i].strip())
                i += 1
            if not para:  # defensive: never fail to advance
                para = [line.strip()]
                i += 1
            out.append("<p>" + self.inline(" ".join(para)) + "</p>")
        return "".join(out)

    def table(self, lines, i, out):
        header = split_row(lines[i])
        i += 2
        rows = []
        while i < len(lines) and lines[i].strip() and "|" in lines[i]:
            rows.append(split_row(lines[i]))
            i += 1
        head = "".join(f"<th>{self.inline(c)}</th>" for c in header)
        body = "".join(
            "<tr>" + "".join(f"<td>{self.inline(c)}</td>" for c in row) + "</tr>"
            for row in rows
        )
        out.append(
            f"<table><thead><tr>{head}</tr></thead><tbody>{body}</tbody></table>"
        )
        return i

    def list(self, lines, i, out):
        first = list_match(lines[i])
        indent = len(first.group(1))
        ordered = first.group(2)[0].isdigit()
        tag = "ol" if ordered else "ul"
        items = []
        while i < len(lines):
            m = list_match(lines[i])
            if (
                not m
                or len(m.group(1)) != indent
                or m.group(2)[0].isdigit() != ordered
            ):
                break
            item = [m.group(3)]
            i += 1
            while i < len(lines):
                ln = lines[i]
                if not ln.strip():
                    j = i
                    while j < len(lines) and not lines[j].strip():
                        j += 1
                    if j < len(lines) and indent_of(lines[j]) > indent:
                        item.append("")
                        i += 1
                        continue
                    break
                if list_match(ln) and len(list_match(ln).group(1)) == indent:
                    break
                if indent_of(ln) > indent:
                    item.append(ln)
                    i += 1
                    continue
                break
            items.append(self.item(item, indent))
            # blank lines between items
            j = i
            while j < len(lines) and not lines[j].strip():
                j += 1
            if j < len(lines):
                m2 = list_match(lines[j])
                if (
                    m2
                    and len(m2.group(1)) == indent
                    and m2.group(2)[0].isdigit() == ordered
                ):
                    i = j
        out.append(f"<{tag}>" + "".join(items) + f"</{tag}>")
        return i

    def item(self, item, indent):
        first = item[0].strip()
        rest = item[1:]
        # Hard-wrapped continuation of the item's first paragraph is one paragraph.
        k = 0
        while k < len(rest):
            ln = rest[k]
            if not ln.strip() or list_match(ln) or ln.lstrip().startswith((">", "```", "~~~")):
                break
            if re.match(r"^(#{1,6})\s+", ln):
                break
            if "|" in ln and k + 1 < len(rest) and is_table_rule(rest[k + 1]):
                break
            first += " " + ln.strip()
            k += 1
        rest = rest[k:]
        while rest and not rest[0].strip():
            rest = rest[1:]
        inner = ""
        if rest:
            cut = min(
                (indent_of(r) for r in rest if r.strip()), default=indent + 2
            )
            dedented = [r[cut:] if r.strip() else "" for r in rest]
            inner = self.blocks(dedented)
        if inner:
            return f"<li>{self.inline(first)}{inner}</li>"
        return f"<li>{self.inline(first)}</li>"

    # -- document ---------------------------------------------------------
    def render(self, text):
        # HTML comments are not part of the page (the semantics matrix's generated-file
        # note is one); they only occur outside code fences in this repository.
        text = re.sub(r"<!--.*?-->", "", text, flags=re.S)
        body = self.blocks(text.splitlines())
        return body

    def page_html(self, body, title):
        out_path = "guide/" + self.page[:-3] + ".html"
        out_dir = posixpath.dirname(out_path)
        style = posixpath.relpath("guide/guide.css", start=out_dir or ".")
        home = posixpath.relpath("index.html", start=out_dir or ".")
        api = posixpath.relpath("docs/index.html", start=out_dir or ".")
        guide = posixpath.relpath("guide/docs/index.html", start=out_dir or ".")
        playground = posixpath.relpath("playground/index.html", start=out_dir or ".")
        source = self.source_url + "/" + urllib.parse.quote(self.page)
        return (
            "<!doctype html>\n<html lang=\"en\"><head><meta charset=\"utf-8\">"
            "<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">"
            f"<title>{escape(title)}</title>"
            f"<link rel=\"stylesheet\" href=\"{escape(style)}\"></head><body>"
            "<header><a class=\"brand\" href=\"%s\">Wiz</a>"
            "<nav><a href=\"%s\">Guide</a><a href=\"%s\">API</a>"
            "<a href=\"%s\">Playground</a>"
            "<a class=\"src\" rel=\"source\" href=\"%s\">source</a></nav></header>\n"
            "<main>%s</main>\n"
            "<footer><p>This page is generated from the repository's Markdown by "
            "<code>web/build-docs.py</code>; the "
            "<a class=\"src\" rel=\"source\" href=\"%s\">source</a> is the file of "
            "record.</p></footer>\n</body></html>\n"
            % (home, guide, api, playground, source, body, source)
        )


# -- block helpers --------------------------------------------------------

LIST_RE = re.compile(r"^(\s*)([-*+]|\d+[.)])\s+(.*)$")


def list_match(line):
    return LIST_RE.match(line)


def indent_of(line):
    return len(line) - len(line.lstrip(" "))


def is_table_rule(line):
    return bool(
        re.match(r"^\s*\|?\s*:?-{2,}:?\s*(\|\s*:?-{2,}:?\s*)+\|?\s*$", line)
    )


def block_start(line, lines, i):
    if re.match(r"^\s*(`{3,}|~{3,})", line):
        return True
    if re.match(r"^(#{1,6})\s+", line):
        return True
    if re.match(r"^\s*((\*\s*){3,}|(-\s*){3,}|(_\s*){3,})$", line):
        return True
    if line.lstrip().startswith(">"):
        return True
    if list_match(line):
        return True
    if "|" in line and i + 1 < len(lines) and is_table_rule(lines[i + 1]):
        return True
    return False


def split_row(line):
    """Split a pipe-table row, honouring `\\|` and pipes inside code spans."""
    line = line.strip()
    if line.startswith("|"):
        line = line[1:]
    if line.endswith("|") and not line.endswith("\\|"):
        line = line[:-1]
    cells, cur, code, i = [], [], False, 0
    while i < len(line):
        c = line[i]
        if c == "\\" and i + 1 < len(line) and line[i + 1] == "|":
            cur.append("|")
            i += 2
            continue
        if c == "`":
            code = not code
            cur.append(c)
        elif c == "|" and not code:
            cells.append("".join(cur).strip())
            cur = []
        else:
            cur.append(c)
        i += 1
    cells.append("".join(cur).strip())
    return cells


# -- driver ---------------------------------------------------------------

HEADER = """\
:root { color-scheme: light dark; --ink:#1b1b1a; --bg:#fdfdfb; --muted:#5b5b57;
  --rule:#dcdcd5; --code:#f2f2ec; --link:#0b5cad; }
@media (prefers-color-scheme: dark) {
  :root { --ink:#e8e8e2; --bg:#161614; --muted:#a3a39c; --rule:#33332f;
    --code:#232320; --link:#7db4ef; } }
* { box-sizing: border-box; }
body { margin:0; background:var(--bg); color:var(--ink); line-height:1.6;
  font:16px/1.6 system-ui, -apple-system, "Segoe UI", sans-serif; }
header { display:flex; gap:1rem; align-items:center; flex-wrap:wrap;
  padding:.7rem 1.2rem; border-bottom:1px solid var(--rule); font-size:.95rem; }
header .brand { font-weight:700; text-decoration:none; color:var(--ink); margin-right:auto; }
header nav { display:flex; gap:1rem; flex-wrap:wrap; }
header a, main a { color:var(--link); }
header a.src { color:var(--muted); }
main { max-width:62rem; margin:0 auto; padding:1.2rem 1.2rem 3rem; }
h1,h2,h3,h4,h5,h6 { line-height:1.25; margin:1.8em 0 .5em; }
h1 { font-size:2rem; margin-top:.6rem; }
h2 { font-size:1.45rem; border-bottom:1px solid var(--rule); padding-bottom:.2rem; }
h3 { font-size:1.2rem; }
code { background:var(--code); padding:.08em .25em; border-radius:4px;
  font-family:ui-monospace, SFMono-Regular, Menlo, monospace; font-size:.92em; }
pre { background:var(--code); padding:.8rem 1rem; overflow:auto; border-radius:6px; }
pre code { background:none; padding:0; }
blockquote { margin:.6rem 0; padding:.1rem 1rem; border-left:3px solid var(--rule);
  color:var(--muted); }
table { border-collapse:collapse; margin:.8rem 0; width:100%; display:block;
  overflow-x:auto; }
th, td { border:1px solid var(--rule); padding:.35rem .6rem; text-align:left;
  vertical-align:top; }
th { background:var(--code); }
img { max-width:100%; height:auto; }
footer { max-width:62rem; margin:0 auto; padding:1.5rem 1.2rem 3rem;
  border-top:1px solid var(--rule); color:var(--muted); font-size:.9rem; }
"""


def title_of(text, path):
    for line in text.splitlines():
        m = re.match(r"^#\s+(.*?)\s*#*\s*$", line)
        if m:
            return re.sub(r"[`*]", "", m.group(1))
    return posixpath.basename(path)[:-3]


def rewrite_notebooks(site, pages, errors, root, repo_url, source_url):
    """Point a copied notebook's `.md` links at the rendered guide pages.

    The notebook pages in docs/notebooks/ keep repository-relative Markdown links (so
    they work on GitHub); the site's copy is under /notebooks/, so the same target is
    `../guide/<path>.html`.
    """
    nb_dir = os.path.join(site, "notebooks")
    if not os.path.isdir(nb_dir):
        return
    for name in sorted(os.listdir(nb_dir)):
        if not name.endswith(".html"):
            continue
        path = os.path.join(nb_dir, name)

        def fix(m):
            url = m.group(1)
            if not url or url.startswith(("#", "http://", "https://", "mailto:", "data:")):
                return m.group(0)
            raw, sep, frag = url.partition("#")
            path_part, qsep, query = raw.partition("?")
            tail = qsep + query + sep + frag
            # A link to another page of this directory (index.html, example.html) stays.
            if os.path.isfile(os.path.join(nb_dir, path_part)):
                return m.group(0)
            repo_path = posixpath.normpath(
                posixpath.join("docs/notebooks", urllib.parse.unquote(path_part))
            )
            if path_part.endswith(".md"):
                if repo_path not in pages:
                    errors.append(f"notebooks/{name}: link '{url}' does not resolve")
                    return m.group(0)
                return 'href="../guide/' + repo_path[:-3] + ".html" + tail + '"'
            full = os.path.join(root, repo_path)
            if os.path.isdir(full):
                return f'href="{repo_url}/tree/master/{repo_path}{tail}"'
            if os.path.isfile(full):
                return f'href="{repo_url}/blob/master/{repo_path}{tail}"'
            errors.append(f"notebooks/{name}: link '{url}' does not resolve")
            return m.group(0)

        text = open(path, encoding="utf-8").read()
        new = re.sub(r'href="([^"]*)"', fix, text)
        # A published page names its source; a notebook's is the `.ipynb` it was
        # exported from (the hand-written index names itself).
        if 'class="src"' not in new:
            src_name = name[:-5] + ".ipynb"
            if not os.path.isfile(os.path.join(root, "docs/notebooks", src_name)):
                src_name = name
            src_url = source_url.rstrip("/") + "/docs/notebooks/" + src_name
            new = new.replace(
                "</body>",
                f'<footer><p>Exported from the repository by '
                f'<code>web/build-site.sh</code>; the '
                f'<a class="src" rel="source" href="{src_url}">source</a> is the '
                f'file of record.</p></footer></body>',
            )
        if new != text:
            with open(path, "w", encoding="utf-8") as f:
                f.write(new)


def main(argv):
    ap = argparse.ArgumentParser()
    ap.add_argument("--site", required=True)
    ap.add_argument("--root", default=None)
    ap.add_argument(
        "--source-url",
        default=os.environ.get(
            "WIZ_SOURCE_URL", "https://github.com/wiz-pl/wiz/blob/master"
        ),
        help="the repository's blob URL prefix for the source link",
    )
    ap.add_argument("--repo-url", default="https://github.com/wiz-pl/wiz")
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args(argv)

    root = os.path.abspath(
        args.root or os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
    )
    pages = reachable_pages(root, tracked_markdown(root))
    errors = []
    rendered = {}

    for page in pages:
        src = os.path.join(root, page)
        try:
            text = open(src, encoding="utf-8").read()
        except OSError as e:
            errors.append(f"{page}: {e}")
            continue
        r = Renderer(page, pages, root, args.site, args.source_url, args.repo_url)
        body = r.render(text)
        rendered[page] = r.page_html(body, title_of(text, page))
        errors.extend(r.errors)

    if args.check:
        for page in pages:
            out = os.path.join(args.site, "guide", page[:-3] + ".html")
            if not os.path.isfile(out):
                errors.append(f"guide/{page[:-3]}.html is missing")
    else:
        guide = os.path.join(args.site, "guide")
        for page, text in rendered.items():
            out = os.path.join(guide, page[:-3] + ".html")
            os.makedirs(os.path.dirname(out), exist_ok=True)
            with open(out, "w", encoding="utf-8") as f:
                f.write(text)
        with open(os.path.join(guide, "guide.css"), "w", encoding="utf-8") as f:
            f.write(HEADER)
        # Images a page links to, copied so the page works without the network.
        for page in pages:
            r = Renderer(page, pages, root, args.site, args.source_url, args.repo_url)
            text = open(os.path.join(root, page), encoding="utf-8").read()
            for m in INLINE.finditer(text):
                if m.group("src") is not None:
                    kind, *rest = r.target(m.group("src"))
                    if kind == "image":
                        repo_path = rest[1]
                        dst = os.path.join(guide, repo_path)
                        os.makedirs(os.path.dirname(dst), exist_ok=True)
                        shutil.copyfile(os.path.join(root, repo_path), dst)
        rewrite_notebooks(args.site, pages, errors, root, args.repo_url, args.source_url)

    for e in errors:
        print(f"build-docs: {e}", file=sys.stderr)
    if errors:
        return 1
    if args.check:
        print(f"build-docs: ok ({len(pages)} pages under {args.site}/guide)")
    else:
        print(f"build-docs: {len(pages)} pages under {args.site}/guide")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
