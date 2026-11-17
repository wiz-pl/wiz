#!/usr/bin/env python3
"""Check the links in Wiz's documentation without a build or the network.

The checker reads `docs/**/*.md`, `docs/**/*.html` and the root `*.md` files,
extracts every link and image (inline, reference-style, angle-bracket autolink
and HTML `href`/`src`), and resolves it the way a reader would:

  relative path   resolved against the linking file's directory.  The target
                  must exist in the checkout; a link that leaves the checkout
                  is reported.
  #anchor         resolved against the heading slugs and explicit HTML ids of
                  the target file (GitHub-flavoured: lowercase, spaces become
                  `-`, punctuation is dropped, repeated slugs get `-1`, `-2`).
  http(s) URL     reported as an external link.  It is not fetched unless
                  `--fetch` is given, so CI never depends on the network.
  wiz-notes/...   an external note: the notes live outside the repository, so
                  the target is reported as "external note, not checked" and
                  never counts as broken.

Code is not prose: fenced code blocks, inline code spans and HTML comments are
masked before links are read, so an example link in a code block is ignored.

Usage
  scripts/check-doc-links.py                 check this checkout
  scripts/check-doc-links.py --self-test     run the built-in fixtures
  scripts/check-doc-links.py --root DIR      check another checkout
  scripts/check-doc-links.py --quiet         problems and the summary only
  scripts/check-doc-links.py --fetch         also fetch http(s) links
  scripts/check-doc-links.py --timeout SECS  per-URL timeout for --fetch (5)

Exit status: 0 clean, 1 a broken relative link or anchor (or a failing
self-test), 2 usage error.  A dead external site is reported but is not a
failure unless it was fetched with `--fetch`.
"""

from __future__ import annotations

import argparse
import html
import posixpath
import re
import sys
import tempfile
import urllib.error
import urllib.parse
import urllib.request
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass, field
from pathlib import Path

ROOT_FILES = ("README.md", "ROADMAP.md", "CHANGELOG.md")

FENCE_RE = re.compile(r"^( {0,3})(`{3,}|~{3,})(.*)$")
ATX_RE = re.compile(r"^ {0,3}(#{1,6})(?:[ \t]+|$)(.*)$")
SETEXT_RE = re.compile(r"^ {0,3}(=+|-+)[ \t]*$")
DEF_RE = re.compile(r"^ {0,3}\[([^\]]+)\]:[ \t]*(.+)$")
AUTOLINK_RE = re.compile(r"<([A-Za-z][A-Za-z0-9+.-]*:[^<>\s]+)>")
ATTR_RE = re.compile(
    r"""\b(?:href|src)\s*=\s*(?:"([^"]*)"|'([^']*)')""", re.IGNORECASE
)
ID_RE = re.compile(r"""\bid\s*=\s*(?:"([^"]*)"|'([^']*)')""", re.IGNORECASE)
NAME_RE = re.compile(r"""<a\b[^>]*\bname\s*=\s*(?:"([^"]*)"|'([^']*)')""", re.IGNORECASE)
NOTE_REF_RE = re.compile(
    r"(?<![\w/.-])(?:\.\./)*wiz-notes/[A-Za-z0-9._/-]+"
)
SCHEME_RE = re.compile(r"^[A-Za-z][A-Za-z0-9+.-]*:")


@dataclass(frozen=True)
class Target:
    """One link destination found in a document."""

    path: str  # repository-relative path of the document
    line: int
    target: str  # the destination as written
    label: str  # link text, for the report


@dataclass
class Stats:
    files: int = 0
    links: int = 0
    anchors: int = 0
    external_links: int = 0
    external_notes: int = 0


@dataclass
class Report:
    stats: Stats = field(default_factory=Stats)
    problems: list[str] = field(default_factory=list)
    notes: list[str] = field(default_factory=list)


# --- masking ----------------------------------------------------------------------


def mask_comments(text: str) -> str:
    """Replace HTML comment bodies with spaces, keeping line structure."""
    def blank(match: re.Match[str]) -> str:
        return re.sub(r"[^\n]", " ", match.group(0))

    return re.sub(r"<!--.*?-->", blank, text, flags=re.DOTALL)


def mask_code_span(line: str) -> str:
    """Replace inline code spans with spaces (a link in `code` is not a link)."""
    out = list(line)
    index = 0
    while index < len(line):
        if line[index] != "`":
            index += 1
            continue
        end = index
        while end < len(line) and line[end] == "`":
            end += 1
        width = end - index
        probe = end
        close = -1
        while probe < len(line):
            if line[probe] != "`":
                probe += 1
                continue
            run_end = probe
            while run_end < len(line) and line[run_end] == "`":
                run_end += 1
            if run_end - probe == width:
                close = run_end
                break
            probe = run_end
        if close < 0:
            index = end
        else:
            for pos in range(index, close):
                out[pos] = " "
            index = close
    return "".join(out)


def strip_code_delimiters(line: str) -> str:
    """Drop backtick runs but keep their contents (for a heading's slug)."""
    return re.sub(r"`+", "", line)


# --- inline link parsing ----------------------------------------------------------


def match_bracket(line: str, start: int) -> int:
    """Index of the `]` matching the `[` at `start`, or -1."""
    depth = 0
    index = start
    while index < len(line):
        char = line[index]
        if char == "\\":
            index += 2
            continue
        if char == "[":
            depth += 1
        elif char == "]":
            depth -= 1
            if depth == 0:
                return index
        index += 1
    return -1


def match_paren(line: str, start: int) -> int:
    """Index of the `)` matching the `(` at `start`, or -1.

    Angle-bracketed destinations and quoted titles may contain parentheses.
    """
    depth = 0
    quote = ""
    angle = False
    index = start
    while index < len(line):
        char = line[index]
        if char == "\\":
            index += 2
            continue
        if angle:
            if char == ">":
                angle = False
        elif quote:
            if char == quote:
                quote = ""
        elif char == "<" and depth == 1:
            angle = True
        elif char in "\"'":
            quote = char
        elif char == "(":
            depth += 1
        elif char == ")":
            depth -= 1
            if depth == 0:
                return index
        index += 1
    return -1


def parse_destination(body: str) -> str:
    """The destination of an inline link's `(body)` (titles are dropped)."""
    body = body.strip()
    if not body:
        return ""
    if body.startswith("<"):
        end = body.find(">")
        if end > 0:
            return body[1:end]
    depth = 0
    index = 0
    while index < len(body):
        char = body[index]
        if char == "\\":
            index += 2
            continue
        if char == "(":
            depth += 1
        elif char == ")":
            depth = max(0, depth - 1)
        elif char.isspace() and depth == 0:
            break
        index += 1
    return body[:index]


def unescape_destination(target: str) -> str:
    """Undo Markdown backslash escapes in a destination."""
    return re.sub(r"\\([\\`*_{}\[\]()#+\-.!<>])", r"\1", target)


def normal_label(label: str) -> str:
    return re.sub(r"\s+", " ", label).strip().casefold()


def link_targets(path: str, text: str) -> tuple[list[Target], list[tuple[int, str]]]:
    """Links in a Markdown document, and its reference definitions.

    The second list is (line, destination) for each `[label]: target`; callers
    check those even when nothing uses the label, because a definition with a
    bad path is still a broken link.
    """
    lines = mask_comments(text).splitlines()
    masked: list[str] = []
    fenced: list[bool] = []
    fence_char = ""
    fence_len = 0
    for line in lines:
        fence = FENCE_RE.match(line)
        if fence_char:
            fenced.append(True)
            masked.append("")
            if (
                fence
                and fence.group(2)[0] == fence_char
                and len(fence.group(2)) >= fence_len
                and not fence.group(3).strip()
            ):
                fence_char = ""
                fence_len = 0
            continue
        if fence:
            fence_char = fence.group(2)[0]
            fence_len = len(fence.group(2))
            fenced.append(True)
            masked.append("")
            continue
        fenced.append(False)
        masked.append(mask_code_span(line))

    definitions: dict[str, str] = {}
    definition_lines: set[int] = set()
    for index, line in enumerate(masked):
        match = DEF_RE.match(line)
        if match is None:
            continue
        destination = parse_destination(match.group(2))
        if not destination:
            continue
        definitions.setdefault(normal_label(match.group(1)), destination)
        definition_lines.add(index)

    found: list[Target] = []
    definitions_out: list[tuple[int, str]] = []
    for index, line in enumerate(masked):
        if fenced[index]:
            continue
        if index in definition_lines:
            match = DEF_RE.match(line)
            if match is not None:
                destination = parse_destination(match.group(2))
                if destination:
                    definitions_out.append((index + 1, destination))
            continue

        pos = 0
        while pos < len(line):
            if line[pos] != "[" or (pos > 0 and line[pos - 1] == "\\"):
                pos += 1
                continue
            close = match_bracket(line, pos)
            if close < 0:
                pos += 1
                continue
            label = line[pos + 1 : close]
            after = close + 1
            if after < len(line) and line[after] == "(":
                end = match_paren(line, after)
                if end < 0:
                    pos = close + 1
                    continue
                destination = unescape_destination(
                    parse_destination(line[after + 1 : end])
                )
                if destination:
                    found.append(Target(path, index + 1, destination, label))
                pos = end + 1
                continue
            if after < len(line) and line[after] == "[":
                ref_close = match_bracket(line, after)
                if ref_close < 0:
                    pos = close + 1
                    continue
                ref = line[after + 1 : ref_close] or label
                destination = definitions.get(normal_label(ref))
                if destination is not None:
                    found.append(Target(path, index + 1, destination, label))
                pos = ref_close + 1
                continue
            # A shortcut reference is only a link when its label is defined.
            destination = definitions.get(normal_label(label))
            if destination is not None and label.strip():
                found.append(Target(path, index + 1, destination, label))
            pos = close + 1

        for match in AUTOLINK_RE.finditer(line):
            found.append(Target(path, index + 1, match.group(1), match.group(1)))

    return found, definitions_out


# --- anchors ----------------------------------------------------------------------


def heading_plain(text: str) -> str:
    """A heading's text with inline Markdown removed, as GitHub slugs it."""
    text = strip_code_delimiters(text)
    text = re.sub(r"!\[([^\]]*)\]\([^)]*\)", r"\1", text)
    text = re.sub(r"\[([^\]]*)\]\([^)]*\)", r"\1", text)
    text = re.sub(r"\[([^\]]*)\]\[[^\]]*\]", r"\1", text)
    text = re.sub(r"<[^>]+>", "", text)
    text = re.sub(r"[*~]", "", text)
    return html.unescape(text)


def slugify(text: str) -> str:
    """The GitHub heading slug: lowercase, spaces to `-`, punctuation dropped."""
    text = text.strip().lower()
    out: list[str] = []
    for char in text:
        if char.isspace():
            out.append("-")
        elif char.isalnum() or char in "-_":
            out.append(char)
    return "".join(out)


def markdown_anchors(text: str) -> set[str]:
    """Heading slugs and explicit HTML ids of a Markdown document."""
    lines = mask_comments(text).splitlines()
    text_lines: list[str] = []
    ignored: list[bool] = []
    fence_char = ""
    fence_len = 0
    for line in lines:
        fence = FENCE_RE.match(line)
        if fence_char:
            text_lines.append("")
            ignored.append(True)
            if (
                fence
                and fence.group(2)[0] == fence_char
                and len(fence.group(2)) >= fence_len
                and not fence.group(3).strip()
            ):
                fence_char = ""
                fence_len = 0
            continue
        if fence:
            fence_char = fence.group(2)[0]
            fence_len = len(fence.group(2))
            text_lines.append("")
            ignored.append(True)
            continue
        text_lines.append(line)
        ignored.append(False)

    anchors: set[str] = set()
    slugs: dict[str, int] = {}

    def add_heading(raw: str) -> None:
        base = slugify(heading_plain(raw))
        if not base:
            return
        count = slugs.get(base, 0)
        slugs[base] = count + 1
        anchors.add(base if count == 0 else f"{base}-{count}")

    for index, line in enumerate(text_lines):
        if ignored[index]:
            continue
        match = ATX_RE.match(line)
        if match is not None:
            body = re.sub(r"[ \t]+#+[ \t]*$", "", match.group(2)).strip()
            add_heading(body)
            continue
        if (
            index + 1 < len(text_lines)
            and SETEXT_RE.match(text_lines[index + 1]) is not None
            and line.strip()
            and not ignored[index + 1]
            and ATX_RE.match(line) is None
        ):
            add_heading(line)

    for raw in text_lines:
        for pattern in (ID_RE, NAME_RE):
            for match in pattern.finditer(raw):
                value = match.group(1) if match.group(1) is not None else match.group(2)
                if value:
                    anchors.add(value)
    return anchors


def html_anchors(text: str) -> set[str]:
    anchors: set[str] = set()
    text = re.sub(r"<!--.*?-->", "", text, flags=re.DOTALL)
    for pattern in (ID_RE, NAME_RE):
        for match in pattern.finditer(text):
            value = match.group(1) if match.group(1) is not None else match.group(2)
            if value:
                anchors.add(value)
    return anchors


def html_targets(path: str, text: str) -> list[Target]:
    text = re.sub(r"<!--.*?-->", lambda m: "\n" * m.group(0).count("\n"), text,
                  flags=re.DOTALL)
    found: list[Target] = []
    for match in ATTR_RE.finditer(text):
        value = match.group(1) if match.group(1) is not None else match.group(2)
        if not value:
            continue
        line = text.count("\n", 0, match.start()) + 1
        found.append(Target(path, line, html.unescape(value), match.group(0)))
    return found


# --- the checker ------------------------------------------------------------------


class Checker:
    def __init__(self, root: Path, fetch: bool = False, timeout: float = 5.0) -> None:
        self.root = root
        self.fetch = fetch
        self.timeout = timeout
        self._anchors: dict[Path, set[str]] = {}
        self.report = Report()

    def files(self) -> list[Path]:
        files = [
            self.root / name
            for name in ROOT_FILES
            if (self.root / name).is_file()
        ]
        docs = self.root / "docs"
        if docs.is_dir():
            files.extend(
                path
                for path in docs.rglob("*")
                if path.is_file() and path.suffix in (".md", ".html")
            )
        return sorted(set(files), key=lambda path: path.as_posix())

    def anchors_for(self, path: Path) -> set[str] | None:
        if path in self._anchors:
            return self._anchors[path]
        try:
            text = path.read_text(encoding="utf-8")
        except (OSError, UnicodeDecodeError):
            return None
        anchors = html_anchors(text) if path.suffix == ".html" else markdown_anchors(text)
        self._anchors[path] = anchors
        return anchors

    def add_note(self, message: str) -> None:
        self.report.stats.external_notes += 1
        self.report.notes.append(message)

    def check_target(self, target: Target) -> None:
        raw = html.unescape(target.target.strip())
        stats = self.report.stats
        if not raw:
            return

        if raw.startswith("//") or SCHEME_RE.match(raw):
            scheme = raw.split(":", 1)[0].lower() if ":" in raw else "http"
            if scheme in ("http", "https"):
                stats.external_links += 1
                self.report.notes.append(
                    f"{target.path}:{target.line}: external link, not checked: {raw}"
                )
            elif scheme == "mailto":
                self.report.notes.append(
                    f"{target.path}:{target.line}: mailto link, not checked: {raw}"
                )
            else:
                self.report.notes.append(
                    f"{target.path}:{target.line}: {scheme}: link, not checked: {raw}"
                )
            return

        path_part, hash_mark, fragment = raw.partition("#")
        path_part = path_part.split("?", 1)[0]
        path_part = urllib.parse.unquote(path_part)
        fragment = urllib.parse.unquote(fragment)
        stats.links += 1

        if not path_part:
            resolved = self.root / target.path
            if not fragment:
                return
            stats.anchors += 1
            self.check_anchor(target, resolved, fragment)
            return

        # Notes live outside the repository.  Report them, never as broken.
        segments = [part for part in path_part.replace("\\", "/").split("/") if part]
        if "wiz-notes" in segments:
            self.add_note(
                f"{target.path}:{target.line}: external note, not checked: {raw}"
            )
            return

        if path_part.startswith("/"):
            resolved = (self.root / path_part.lstrip("/")).resolve()
            relative = resolved.relative_to(self.root) if self._inside(resolved) else None
        else:
            resolved = (self.root / target.path).parent.joinpath(path_part)
            resolved = Path(posixpath.normpath(resolved.as_posix()))
            relative = None
            try:
                resolved.relative_to(self.root)
            except ValueError:
                self.report.problems.append(
                    f"{target.path}:{target.line}: broken link: {raw} "
                    "(leaves the repository)"
                )
                return

        if not resolved.exists():
            shown = relative.as_posix() if relative is not None else path_part
            self.report.problems.append(
                f"{target.path}:{target.line}: broken link: {raw} "
                f"(no such file: {shown})"
            )
            return

        if not fragment:
            return
        stats.anchors += 1
        if resolved.is_dir():
            self.add_note(
                f"{target.path}:{target.line}: anchor in a directory, not checked: {raw}"
            )
            return
        self.check_anchor(target, resolved, fragment)

    def check_anchor(self, target: Target, resolved: Path, fragment: str) -> None:
        if resolved.suffix not in (".md", ".html"):
            self.add_note(
                f"{target.path}:{target.line}: anchor in a non-Markdown/HTML file, "
                f"not checked: {target.target}"
            )
            return
        anchors = self.anchors_for(resolved)
        if anchors is None:
            self.report.problems.append(
                f"{target.path}:{target.line}: broken link: {target.target} "
                f"(cannot read {resolved.relative_to(self.root).as_posix()})"
            )
            return
        if fragment not in anchors:
            self.report.problems.append(
                f"{target.path}:{target.line}: broken anchor: {target.target} "
                f"(no heading or id '#{fragment}' in "
                f"{resolved.relative_to(self.root).as_posix()})"
            )

    def _inside(self, path: Path) -> bool:
        try:
            path.relative_to(self.root.resolve())
            return True
        except ValueError:
            return False

    def fetch_external(self) -> None:
        urls: list[str] = []
        for note in self.report.notes:
            marker = "external link, not checked: "
            if marker in note:
                url = note.split(marker, 1)[1]
                if url not in urls:
                    urls.append(url)
        if not urls:
            return

        def reachable(url: str) -> tuple[str, str]:
            request = urllib.request.Request(
                url,
                method="HEAD",
                headers={"User-Agent": "wiz-check-doc-links/1"},
            )
            try:
                with urllib.request.urlopen(request, timeout=self.timeout):
                    return url, ""
            except urllib.error.HTTPError as exc:
                if exc.code in (403, 405, 501):
                    request = urllib.request.Request(
                        url,
                        headers={"User-Agent": "wiz-check-doc-links/1"},
                    )
                    try:
                        with urllib.request.urlopen(request, timeout=self.timeout):
                            return url, ""
                    except Exception as inner:  # noqa: BLE001 - report it
                        return url, str(inner)
                return url, f"HTTP {exc.code}"
            except Exception as exc:  # noqa: BLE001 - report it
                return url, str(exc)

        with ThreadPoolExecutor(max_workers=8) as pool:
            for url, error in pool.map(reachable, urls):
                if error:
                    self.report.problems.append(
                        f"broken external link: {url} ({error})"
                    )

    def run(self) -> Report:
        files = self.files()
        self.report.stats.files = len(files)
        for path in files:
            relpath = path.relative_to(self.root).as_posix()
            try:
                text = path.read_text(encoding="utf-8")
            except UnicodeDecodeError as exc:
                self.report.problems.append(f"{relpath}: not UTF-8: {exc}")
                continue
            if path.suffix == ".html":
                targets = html_targets(relpath, text)
                definitions: list[tuple[int, str]] = []
            else:
                targets, definitions = link_targets(relpath, text)
            for target in targets:
                self.check_target(target)
            for line, destination in definitions:
                self.check_target(Target(relpath, line, destination, "definition"))
            if path.suffix == ".md":
                self.scan_notes(relpath, text, targets)

        if self.fetch:
            self.fetch_external()
        return self.report

    def scan_notes(self, relpath: str, text: str, targets: list[Target]) -> None:
        """Bare `wiz-notes/...` references, including ones in inline code."""
        seen = {(target.line, target.target) for target in targets}
        lines = mask_comments(text).splitlines()
        fence_char = ""
        fence_len = 0
        for index, line in enumerate(lines):
            fence = FENCE_RE.match(line)
            if fence_char:
                if (
                    fence
                    and fence.group(2)[0] == fence_char
                    and len(fence.group(2)) >= fence_len
                    and not fence.group(3).strip()
                ):
                    fence_char = ""
                    fence_len = 0
                continue
            if fence:
                fence_char = fence.group(2)[0]
                fence_len = len(fence.group(2))
                continue
            for match in NOTE_REF_RE.finditer(line):
                reference = match.group(0)
                if (index + 1, reference) in seen:
                    continue
                seen.add((index + 1, reference))
                self.add_note(
                    f"{relpath}:{index + 1}: external note, not checked: {reference}"
                )


def run(
    root: Path,
    *,
    quiet: bool = False,
    fetch: bool = False,
    timeout: float = 5.0,
    out=sys.stdout,
    err=sys.stderr,
) -> int:
    if not (root / "README.md").is_file() or not (root / "docs").is_dir():
        print(
            f"check-doc-links: {root} is not a Wiz checkout "
            "(README.md or docs/ is missing)",
            file=err,
        )
        return 2

    checker = Checker(root.resolve(), fetch=fetch, timeout=timeout)
    report = checker.run()
    stats = report.stats

    if not quiet:
        for note in report.notes:
            print(note, file=out)
    for problem in report.problems:
        print(problem, file=out)

    summary = (
        f"{stats.files} file(s), {stats.links} link(s), "
        f"{stats.anchors} anchor(s), {stats.external_notes} external note(s), "
        f"{stats.external_links} external link(s)"
    )
    if report.problems:
        print(
            f"\ncheck-doc-links: {len(report.problems)} broken "
            f"({summary})",
            file=err,
        )
        return 1
    print(f"check-doc-links: clean ({summary})", file=out)
    return 0


# --- self-test --------------------------------------------------------------------

FIXTURE_README = """\
# Fixture

[ok](docs/index.md)
[ok anchor](docs/index.md#details)
[bad](docs/missing.md)
[bad anchor](docs/index.md#nope)
`[inline code](missing-inline.md)`

```md
[fenced](missing-fence.md)
```

<https://example.com>
<mailto:someone@example.com>
"""

FIXTURE_DOCS_INDEX = """\
# Fixture docs

## Details

[back](../README.md)
### 4.1 Lifting (`ulift`, q4)
[slug](#41-lifting-ulift-q4)
[reference][ref]
[broken reference][dead]

[ref]: ../README.md
[dead]: missing-ref.md

`wiz-notes/outside.md` is an external note.
[external note](wiz-notes/also-outside.md)
"""

FIXTURE_HTML = """\
<!doctype html>
<html><body>
<a href="../README.md">ok</a>
<a href="missing.html">bad</a>
<a href="../docs/index.md#details">ok anchor</a>
<a href="../docs/index.md#gone">bad anchor</a>
</body></html>
"""


def self_test() -> int:
    with tempfile.TemporaryDirectory(prefix="wiz-doc-links-selftest-") as tmp:
        root = Path(tmp)
        (root / "docs").mkdir()
        (root / "README.md").write_text(FIXTURE_README, encoding="utf-8")
        (root / "docs" / "index.md").write_text(FIXTURE_DOCS_INDEX, encoding="utf-8")
        (root / "docs" / "page.html").write_text(FIXTURE_HTML, encoding="utf-8")

        import io

        out = io.StringIO()
        err = io.StringIO()
        status = run(root, quiet=False, out=out, err=err)
        text = out.getvalue() + err.getvalue()
        expected = [
            "docs/missing.md",
            "docs/index.md#nope",
            "missing-ref.md",
            "missing.html",
            "docs/index.md#gone",
        ]
        failures = [item for item in expected if item not in text]
        if status != 1:
            failures.append(f"expected exit 1, got {status}")
        for forbidden in (
            "missing-inline.md",
            "missing-fence.md",
            "outside.md",
            "also-outside.md",
        ):
            if forbidden in "\n".join(
                line for line in text.splitlines() if "broken" in line
            ):
                failures.append(f"reported {forbidden}, which is not a broken link")
        if "external note, not checked: wiz-notes/outside.md" not in text:
            failures.append("bare wiz-notes reference was not reported as an external note")

        clean = Path(tmp) / "clean"
        (clean / "docs").mkdir(parents=True)
        (clean / "README.md").write_text(
            "# Clean\n\n[docs](docs/index.md#top)\n", encoding="utf-8"
        )
        (clean / "docs" / "index.md").write_text(
            "# Top\n\n[home](../README.md)\n", encoding="utf-8"
        )
        out = io.StringIO()
        err = io.StringIO()
        status = run(clean, quiet=True, out=out, err=err)
        if status != 0:
            failures.append(f"clean fixture exited {status}: {err.getvalue()}")

        if failures:
            print("check-doc-links self-test: FAIL", file=sys.stderr)
            for failure in failures:
                print(f"  {failure}", file=sys.stderr)
            return 1
        print("check-doc-links self-test: ok (2 fixtures)")
        return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Check the links in Wiz's documentation.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
    )
    parser.add_argument("--root", default=str(Path(__file__).resolve().parent.parent),
                        help="the checkout to check (default: this script's checkout)")
    parser.add_argument("--quiet", action="store_true",
                        help="print problems and the summary only")
    parser.add_argument("--self-test", action="store_true",
                        help="run the built-in fixtures")
    parser.add_argument("--fetch", action="store_true",
                        help="fetch http(s) links (off by default: no network in CI)")
    parser.add_argument("--timeout", type=float, default=5.0,
                        help="per-URL timeout for --fetch (default: 5 seconds)")
    args = parser.parse_args(argv)

    if args.self_test:
        return self_test()
    return run(Path(args.root), quiet=args.quiet, fetch=args.fetch,
               timeout=args.timeout)


if __name__ == "__main__":
    sys.exit(main())
