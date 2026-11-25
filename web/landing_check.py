#!/usr/bin/env python3
"""Compile the landing snippets and check the build-time highlighter.

Two properties, both about the same files (`web/landing/snippets/*.wiz`):

1. **They are real programs.** Each file is checked by the toolchain
   (`wiz check -I lib`), so a snippet that stops compiling fails here rather than
   teaching the wrong thing on the page.
2. **The highlighter is the documentation's.** The snippets are rendered through
   `wiz doc` as `wiz` fences; `Wiz.Doc.Highlight` scans them with the parser's own
   token table. The landing build's `web/landing_highlight.py` must produce exactly
   the same ignored-tag HTML. A keyword invented by the Python file (or one it
   misses) changes the bytes and fails. A second probe requires every word in
   `KEYWORDS` to be highlighted by `wiz doc`, so the set cannot drift either.

    usage: web/landing_check.py [--root DIR] [--wiz PATH]

Exit status: 0 clean, 1 a failed check, 2 usage.
"""

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import landing_highlight as highlight  # noqa: E402

BLOCK = re.compile(r'<pre><code class="language-wiz">([\s\S]*?)</code></pre>')
CLASSES = re.compile(r'class="(hl-[a-z]+)"')


def read(path):
    with open(path, encoding="utf-8") as f:
        return f.read()


def snippets(root):
    manifest = json.loads(read(os.path.join(root, "web", "landing", "snippets.json")))
    out = []
    for entry in manifest["snippets"]:
        path = os.path.join(root, "web", "landing", "snippets", entry["file"])
        out.append((entry, path, read(path).rstrip("\n")))
    return out


def run(cmd, root):
    return subprocess.run(cmd, cwd=root, capture_output=True, text=True)


def check_compiles(wiz, root, items):
    failed = 0
    for entry, path, _ in items:
        rel = os.path.relpath(path, root)
        result = run([wiz, "check", "-I", os.path.join(root, "lib"), path], root)
        if result.returncode != 0:
            failed += 1
            print(f"landing: {rel} does not compile", file=sys.stderr)
            for line in (result.stdout + result.stderr).splitlines()[:8]:
                print("  " + line, file=sys.stderr)
        else:
            print(f"ok: {rel} compiles")
    return failed


def doc_probe(wiz, root, items, tmp):
    """Run `wiz doc` over a module whose doc comment holds one fence per snippet."""
    src = os.path.join(tmp, "src")
    os.makedirs(src, exist_ok=True)
    parts = ["import Prelude", "", "/-!"]
    for _, _, code in items:
        parts += ["```wiz", code, "```", ""]
    parts += ["-/", "", "def landing_probe : Nat := 0", ""]
    with open(os.path.join(src, "LandingProbe.wiz"), "w", encoding="utf-8") as f:
        f.write("\n".join(parts))
    site = os.path.join(tmp, "site")
    result = run([wiz, "doc", os.path.join(src, "LandingProbe.wiz"), "-o", site], root)
    if result.returncode != 0:
        print("landing: wiz doc failed on the highlight probe", file=sys.stderr)
        print(result.stdout + result.stderr, file=sys.stderr)
        return None
    page = os.path.join(site, "LandingProbe.html")
    return read(page) if os.path.isfile(page) else None


def check_highlight(root, items, page):
    failed = 0
    blocks = BLOCK.findall(page)
    if len(blocks) != len(items):
        print(f"landing: wiz doc rendered {len(blocks)} blocks, want {len(items)}",
              file=sys.stderr)
        return 1
    for (entry, path, code), want in zip(items, blocks):
        got = highlight.highlight(code)
        if got != want:
            failed += 1
            print(f"landing: {entry['name']}: the build highlighter disagrees with "
                  f"wiz doc", file=sys.stderr)
            for i, (a, b) in enumerate(zip(got, want)):
                if a != b:
                    print("  first difference at byte " + str(i) +
                          "\n  landing: " + repr(got[max(0, i - 40):i + 60]) +
                          "\n  wiz doc: " + repr(want[max(0, i - 40):i + 60]),
                          file=sys.stderr)
                    break
            if len(got) != len(want):
                print(f"  lengths: landing {len(got)}, wiz doc {len(want)}",
                      file=sys.stderr)
        else:
            print(f"ok: {entry['name']}: highlighting matches wiz doc")
    classes = set(CLASSES.findall(page))
    extra = classes - {"hl-kw", "hl-com", "hl-str", "hl-num"}
    if extra:
        failed += 1
        print("landing: wiz doc emitted classes outside the four: " +
              ", ".join(sorted(extra)), file=sys.stderr)
    return failed


def check_keywords(wiz, root, tmp):
    """Every word the highlighter calls reserved must be reserved to the parser."""
    words = sorted(highlight.KEYWORDS)
    src = os.path.join(tmp, "kw")
    os.makedirs(src, exist_ok=True)
    parts = ["import Prelude", "", "/-!", "```wiz"] + words + ["hello_world", "```",
             "-/", "", "def keyword_probe : Nat := 0", ""]
    with open(os.path.join(src, "KeywordProbe.wiz"), "w", encoding="utf-8") as f:
        f.write("\n".join(parts))
    site = os.path.join(tmp, "kw-site")
    result = run([wiz, "doc", os.path.join(src, "KeywordProbe.wiz"), "-o", site], root)
    if result.returncode != 0:
        print("landing: wiz doc failed on the keyword probe", file=sys.stderr)
        print(result.stdout + result.stderr, file=sys.stderr)
        return 1
    page = read(os.path.join(site, "KeywordProbe.html"))
    found = set(re.findall(r'<span class="hl-kw">([^<]*)</span>', page))
    missing = [w for w in words if w not in found]
    failed = 0
    if missing:
        failed += 1
        print("landing: KEYWORDS has words the parser does not reserve: " +
              ", ".join(missing), file=sys.stderr)
    if "hello_world" in found:
        failed += 1
        print("landing: the keyword probe's control word was highlighted",
              file=sys.stderr)
    if not failed:
        print(f"ok: all {len(words)} keywords are reserved atoms the parser highlights")
    return failed


def main(argv):
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default=os.path.join(HERE, ".."))
    ap.add_argument("--wiz", default=os.environ.get("WIZ", "wiz"))
    args = ap.parse_args(argv)
    root = os.path.abspath(args.root)
    wiz = shutil.which(args.wiz) or args.wiz
    if not os.path.isfile(wiz) or not os.access(wiz, os.X_OK):
        print(f"landing: no wiz at {args.wiz} (set WIZ)", file=sys.stderr)
        return 2
    items = snippets(root)
    if not items:
        print("landing: no snippets", file=sys.stderr)
        return 2
    failed = check_compiles(wiz, root, items)
    with tempfile.TemporaryDirectory(prefix="wiz-landing-") as tmp:
        page = doc_probe(wiz, root, items, tmp)
        if page is None:
            failed += 1
        else:
            failed += check_highlight(root, items, page)
        failed += check_keywords(wiz, root, tmp)
    if failed:
        print(f"landing check: {failed} failure(s)", file=sys.stderr)
        return 1
    print("landing check: all checks passed")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
