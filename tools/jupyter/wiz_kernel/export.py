"""Static, deterministic export of a Wiz notebook.

A notebook is a JSON file of cells and *stored outputs*.  This module turns
that file into one self-contained HTML page or one plain Markdown file: no
Jupyter, no kernel, no network, no timestamp.  Running it twice on the same
notebook produces the same bytes, so the result can be checked in and diffed;
``--check`` re-renders in memory and fails when the committed file differs.

Usage::

    python3 -m wiz_kernel.export export FILE.ipynb [--to html|md]
        [--out FILE] [--check]

The kernel is not needed to export: the notebook already contains its outputs.
What is lost is everything that was *not* in the file: the running kernel, the
definitions it held, and the interactive state of widgets (see the notes below).

Widgets
-------

A widget's state lives in a kernel, not in the notebook, so a widget view
cannot be reproduced.  The exporter handles the two useful cases instead of
emitting a broken frame:

* ``application/vnd.wiz.widget+json`` (the infoview's ``{title, html, goals}``
  protocol) is exported as its static HTML, with the title and goal snapshot.
* a Jupyter widget view (``application/vnd.jupyter.widget-view+json``) is
  replaced by a note that says it is interactive-only, unless the same bundle
  carries a ``text/html`` fallback, which is exported.

HTML in an output is untrusted just as it is in a notebook viewer: scripts,
styles, frames, event handlers and active URLs are removed.  A widget frame
with ``srcdoc`` is unwrapped (its body is sanitised and inlined), not kept as a
frame; other frames become a note.
"""

from __future__ import annotations

import argparse
import base64
import difflib
import html
import json
import os
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path

__all__ = ["NotebookError", "Notebook", "Cell", "load_notebook",
           "render_html", "render_markdown", "render", "main"]


class NotebookError(Exception):
    """The file is not a notebook, or is one this exporter cannot read."""


# -- the model -----------------------------------------------------------

@dataclass
class Cell:
    kind: str                       # markdown, code, raw
    source: str
    execution_count: int | None = None
    outputs: list[dict] = field(default_factory=list)
    metadata: dict = field(default_factory=dict)


@dataclass
class Notebook:
    path: Path
    cells: list[Cell]
    metadata: dict
    title: str
    title_from: str                 # "metadata", "heading" or "stem"


def _text(value, what: str, where: str) -> str:
    """A notebook string field: a string, or the list of lines v4 also allows."""
    if isinstance(value, str):
        return value
    if isinstance(value, list) and all(isinstance(part, str) for part in value):
        return "".join(value)
    raise NotebookError(f"{where}: {what} must be a string or a list of strings")


def _mapping(value, what: str, where: str) -> dict:
    if not isinstance(value, dict):
        raise NotebookError(f"{where}: {what} must be an object")
    return value


def _traceback_text(value, where: str) -> str:
    """A traceback is a list of lines (often newline-terminated), not one string."""
    if value is None:
        return ""
    if isinstance(value, str):
        return value
    if isinstance(value, list) and all(isinstance(part, str) for part in value):
        return "".join(part if part.endswith("\n") else part + "\n"
                       for part in value)
    raise NotebookError(f'{where}: "traceback" must be a string or a list of strings')


def load_notebook(path: str | os.PathLike[str]) -> Notebook:
    """Read and validate a v4 notebook.  Raises :class:`NotebookError`."""
    file = Path(path)
    try:
        raw = file.read_text(encoding="utf-8")
    except OSError as exc:
        raise NotebookError(f"{file}: cannot read: {exc.strerror or exc}") from None
    try:
        document = json.loads(raw)
    except json.JSONDecodeError as exc:
        raise NotebookError(
            f"{file}: not valid JSON: line {exc.lineno} column {exc.colno}: {exc.msg}"
        ) from None
    if not isinstance(document, dict):
        raise NotebookError(f"{file}: not a Jupyter notebook: the top level is not an object")
    cells_value = document.get("cells")
    if not isinstance(cells_value, list):
        raise NotebookError(f'{file}: not a Jupyter notebook: no "cells" list')
    metadata = document.get("metadata")
    if metadata is None:
        metadata = {}
    if not isinstance(metadata, dict):
        raise NotebookError(f'{file}: "metadata" must be an object')

    cells: list[Cell] = []
    for index, value in enumerate(cells_value, 1):
        where = f"{file}: cell {index}"
        cell = _mapping(value, "cell", where)
        kind = cell.get("cell_type")
        if not isinstance(kind, str):
            raise NotebookError(f'{where}: "cell_type" must be a string')
        if kind not in ("markdown", "code", "raw"):
            raise NotebookError(f"{where}: unknown cell type {kind!r} "
                                "(expected markdown, code or raw)")
        source = _text(cell.get("source", ""), '"source"', where)
        count = cell.get("execution_count")
        if count is not None and not isinstance(count, int):
            raise NotebookError(f'{where}: "execution_count" must be an integer or null')
        outputs_value = cell.get("outputs", [])
        if not isinstance(outputs_value, list):
            raise NotebookError(f'{where}: "outputs" must be a list')
        outputs: list[dict] = []
        for out_index, output in enumerate(outputs_value, 1):
            out_where = f"{where}: output {out_index}"
            output = _mapping(output, "output", out_where)
            output_type = output.get("output_type")
            if not isinstance(output_type, str):
                raise NotebookError(f'{out_where}: "output_type" must be a string')
            if output_type == "update_display_data":
                output_type = "display_data"
                output = dict(output, output_type=output_type)
            if output_type == "stream":
                name = output.get("name", "stdout")
                if name not in ("stdout", "stderr"):
                    raise NotebookError(f"{out_where}: stream name {name!r} "
                                        "is not stdout or stderr")
                output["text"] = _text(output.get("text", ""), '"text"', out_where)
            elif output_type == "error":
                for key in ("ename", "evalue"):
                    if not isinstance(output.get(key, ""), str):
                        raise NotebookError(f'{out_where}: "{key}" must be a string')
                trace = output.get("traceback", [])
                output["traceback"] = _traceback_text(trace, out_where)
            elif output_type in ("execute_result", "display_data"):
                data = output.get("data", {})
                if not isinstance(data, dict):
                    raise NotebookError(f'{out_where}: "data" must be an object')
                output["data"] = data
            else:
                raise NotebookError(f"{out_where}: unknown output type {output_type!r}")
            outputs.append(output)
        cell_metadata = cell.get("metadata") or {}
        if not isinstance(cell_metadata, dict):
            raise NotebookError(f'{where}: "metadata" must be an object')
        cells.append(Cell(kind, source, count, outputs, cell_metadata))

    title, title_from = _notebook_title(cells, metadata, file)
    return Notebook(file, cells, metadata, title, title_from)


def _first_heading(cells: list[Cell]) -> str | None:
    """The text of the first markdown cell's leading H1, if it has one."""
    for cell in cells:
        if cell.kind != "markdown":
            continue
        for line in cell.source.splitlines():
            if not line.strip():
                continue
            match = re.match(r"^\s{0,3}#\s+(.+?)\s*#*\s*$", line)
            return _plain(match.group(1)) if match else None
    return None


def _notebook_title(cells: list[Cell], metadata: dict, file: Path) -> tuple[str, str]:
    value = metadata.get("title")
    if isinstance(value, str) and value.strip():
        return _plain(value.strip()), "metadata"
    heading = _first_heading(cells)
    if heading:
        return heading, "heading"
    return file.stem, "stem"


def _plain(value: str) -> str:
    """Drop the little inline Markdown a title may carry (for plain-text places)."""
    value = re.sub(r"`([^`]+)`", r"\1", value)
    value = re.sub(r"[*_]{1,2}([^*_]+)[*_]{1,2}", r"\1", value)
    value = re.sub(r"\[([^\]]+)\]\([^)]*\)", r"\1", value)
    return value.strip()


# -- escaping and sanitising --------------------------------------------

_ACTIVE_TAGS = ("script", "style", "iframe", "object", "embed", "form",
                "noscript", "template", "svg", "math", "base", "link", "meta",
                "frame", "frameset", "applet")
_IFRAME_RE = re.compile(r"<iframe\b([^>]*)>(.*?)</iframe\s*>", re.I | re.S)
_IFRAME_EMPTY_RE = re.compile(r"<iframe\b([^>]*)/\s*>", re.I | re.S)
_SRCDOC_RE = re.compile(r"\bsrcdoc\s*=\s*(\"([^\"]*)\"|'([^']*)'|([^\s>]+))",
                        re.I | re.S)
_URL_ATTR_RE = re.compile(r"\s(href|src|action|xlink:href)\s*=\s*"
                          r"(\"[^\"]*\"|'[^']*'|[^\s>]+)", re.I)
_EVENT_ATTR_RE = re.compile(r"\son[a-z0-9_-]+\s*=\s*(\"[^\"]*\"|'[^']*'|[^\s>]+)",
                            re.I)
_STYLE_ATTR_RE = re.compile(r"\sstyle\s*=\s*(\"[^\"]*\"|'[^']*'|[^\s>]+)", re.I)
_ACTIVE_ATTR_RE = re.compile(r"\s(?:srcdoc|formaction)\s*=\s*"
                             r"(\"[^\"]*\"|'[^']*'|[^\s>]+)", re.I)
_DATA_IMAGE_RE = re.compile(r"^data:image/(?:png|jpeg|gif|webp|svg\+xml);base64,",
                            re.I)


def _unwrap_frames(value: str, depth: int = 0) -> str:
    """Replace a frame's ``srcdoc`` body with the body itself; other frames with a note."""
    def replace(match: re.Match[str]) -> str:
        attrs = match.group(1)
        srcdoc = _SRCDOC_RE.search(attrs)
        if srcdoc is not None and depth < 4:
            body = srcdoc.group(2) or srcdoc.group(3) or srcdoc.group(4) or ""
            return _unwrap_frames(html.unescape(body), depth + 1)
        return ('<div class="widget-note">An embedded frame was not exported: '
                'it is interactive-only.</div>')

    value = _IFRAME_RE.sub(replace, value)
    return _IFRAME_EMPTY_RE.sub(replace, value)


def sanitize_html(value: object) -> str:
    """Static HTML with the active parts removed (scripts, frames, handlers, bad URLs)."""
    text = str(value)
    text = re.sub(r"<!--.*?-->", "", text, flags=re.S)
    text = _unwrap_frames(text)
    for tag in _ACTIVE_TAGS:
        text = re.sub(rf"<{tag}\b[^>]*>.*?</{tag}\s*>", "", text, flags=re.I | re.S)
        text = re.sub(rf"<{tag}\b[^>]*/\s*>", "", text, flags=re.I)
        text = re.sub(rf"</{tag}\s*>", "", text, flags=re.I)
    text = _EVENT_ATTR_RE.sub("", text)
    text = _STYLE_ATTR_RE.sub("", text)
    text = _ACTIVE_ATTR_RE.sub("", text)

    def url(match: re.Match[str]) -> str:
        name = match.group(1).lower()
        raw = html.unescape(match.group(2).strip().strip("\"'"))
        if name == "src":
            return match.group(0) if _DATA_IMAGE_RE.match(raw) else ""
        if re.match(r"(?is)^(?:javascript|vbscript|data\s*:\s*text/html)", raw):
            return ""
        return match.group(0)

    text = _URL_ATTR_RE.sub(url, text)
    text = re.sub(r"(?i)\b(?:javascript|vbscript)\s*:", "", text)
    text = re.sub(r"(?i)data\s*:\s*text/html", "", text)
    return text


# -- Markdown (a small, deterministic subset) ---------------------------

_FENCE_RE = re.compile(r"^(\s*)(`{3,}|~{3,})(.*)$")
_HEADING_RE = re.compile(r"^\s{0,3}(#{1,6})\s+(.*?)\s*#*\s*$")
_HR_RE = re.compile(r"^\s{0,3}([-*_])(?:\s*\1){2,}\s*$")
_BULLET_RE = re.compile(r"^\s*[-*+]\s+(.*)$")
_ORDERED_RE = re.compile(r"^\s*\d+[.)]\s+(.*)$")
_QUOTE_RE = re.compile(r"^\s*>\s?(.*)$")
_CODE_SPAN_RE = re.compile(r"(`+)(.+?)\1", re.S)
_IMAGE_RE = re.compile(r"!\[([^\]]*)\]\(([^)\s]+)\)")
_LINK_RE = re.compile(r"\[([^\]]+)\]\(([^)\s]+)\)")
_BOLD_RE = re.compile(r"\*\*(.+?)\*\*", re.S)
_ITALIC_RE = re.compile(r"(?<!\*)\*(?!\*)(.+?)(?<!\*)\*(?!\*)", re.S)


def _safe_url(escaped: str, *, image: bool = False) -> str | None:
    raw = html.unescape(escaped).strip()
    if not raw:
        return None
    lower = raw.lower()
    if lower.startswith(("javascript:", "vbscript:", "data:")):
        if image and _DATA_IMAGE_RE.match(raw):
            return html.escape(raw, quote=True)
        return None
    if image and lower.startswith(("http://", "https://", "//")):
        return None  # the exported page must be self-contained
    return html.escape(raw, quote=True)


def inline_markdown(text: str) -> str:
    placeholders: list[str] = []

    def stash(match: re.Match[str]) -> str:
        code = html.escape(match.group(2).strip(), quote=True)
        placeholders.append(f"<code>{code}</code>")
        return f"\x00{len(placeholders) - 1}\x00"

    text = _CODE_SPAN_RE.sub(stash, text)
    text = html.escape(text, quote=True)

    def image(match: re.Match[str]) -> str:
        alt = match.group(1)
        url = _safe_url(match.group(2), image=True)
        return f'<img src="{url}" alt="{alt}">' if url else alt

    def link(match: re.Match[str]) -> str:
        label = match.group(1)
        url = _safe_url(match.group(2))
        return f'<a href="{url}">{label}</a>' if url else label

    text = _IMAGE_RE.sub(image, text)
    text = _LINK_RE.sub(link, text)
    text = _BOLD_RE.sub(lambda m: f"<strong>{m.group(1)}</strong>", text)
    text = _ITALIC_RE.sub(lambda m: f"<em>{m.group(1)}</em>", text)
    for index, code in enumerate(placeholders):
        text = text.replace(f"\x00{index}\x00", code)
    return text


def markdown_to_html(source: str) -> str:
    lines = source.splitlines()
    out: list[str] = []
    index = 0
    while index < len(lines):
        line = lines[index]
        if not line.strip():
            index += 1
            continue
        fence = _FENCE_RE.match(line)
        if fence:
            marker = fence.group(2)
            language = fence.group(3).strip()
            index += 1
            body: list[str] = []
            closing = re.compile(rf"^\s*{re.escape(marker[0])}{{{len(marker)},}}\s*$")
            while index < len(lines) and not closing.match(lines[index]):
                body.append(lines[index])
                index += 1
            index += 1  # the closing fence (or the end of the cell)
            attribute = (f' class="language-{html.escape(language, quote=True)}"'
                         if language else "")
            out.append('<pre class="markdown-code"><code' + attribute + ">"
                       + html.escape("\n".join(body), quote=False)
                       + "</code></pre>")
            continue
        heading = _HEADING_RE.match(line)
        if heading:
            level = len(heading.group(1))
            out.append(f"<h{level}>{inline_markdown(heading.group(2))}</h{level}>")
            index += 1
            continue
        if _HR_RE.match(line):
            out.append("<hr>")
            index += 1
            continue
        if _QUOTE_RE.match(line):
            quoted: list[str] = []
            while index < len(lines):
                quote = _QUOTE_RE.match(lines[index])
                if quote is None:
                    break
                quoted.append(quote.group(1))
                index += 1
            out.append("<blockquote>" + markdown_to_html("\n".join(quoted))
                       + "</blockquote>")
            continue
        bullet = _BULLET_RE.match(line)
        ordered = _ORDERED_RE.match(line)
        if bullet or ordered:
            pattern = _BULLET_RE if bullet else _ORDERED_RE
            tag = "ul" if bullet else "ol"
            items: list[str] = []
            current: list[str] = []
            while index < len(lines):
                match = pattern.match(lines[index])
                if match is not None:
                    if current:
                        items.append(" ".join(current))
                    current = [match.group(1)]
                    index += 1
                elif lines[index].strip() and not _is_block_start(lines[index]):
                    current.append(lines[index].strip())
                    index += 1
                else:
                    break
            if current:
                items.append(" ".join(current))
            out.append(f"<{tag}>" + "".join(f"<li>{inline_markdown(item)}</li>"
                                            for item in items) + f"</{tag}>")
            continue
        # A paragraph: consecutive lines that do not start another block.
        paragraph: list[str] = []
        while index < len(lines):
            candidate = lines[index]
            if not candidate.strip() or _is_block_start(candidate):
                break
            paragraph.append(candidate.strip())
            index += 1
        if paragraph:
            out.append("<p>" + inline_markdown(" ".join(paragraph)) + "</p>")
        else:  # defensive: never fail to advance
            out.append("<p>" + inline_markdown(line.strip()) + "</p>")
            index += 1
    return "\n".join(out)


def _is_block_start(line: str) -> bool:
    return bool(_FENCE_RE.match(line) or _HEADING_RE.match(line)
                or _HR_RE.match(line) or _QUOTE_RE.match(line)
                or _BULLET_RE.match(line) or _ORDERED_RE.match(line))


# -- output rendering ---------------------------------------------------

_WIDGET_VIEW = "application/vnd.jupyter.widget-view+json"
_WIDGET_WIZ = "application/vnd.wiz.widget+json"


def _note(message: str) -> str:
    return f'<div class="output-note"><p>{message}</p></div>'


def _escaped_text(value: object) -> str:
    return html.escape(str(value), quote=False)


def _bundle_html(data: dict) -> str:
    """The static representation of one MIME bundle."""
    if _WIDGET_WIZ in data:
        widget = data[_WIDGET_WIZ]
        if isinstance(widget, dict):
            body = widget.get("html")
            title = widget.get("title")
            goals = widget.get("goals")
            if isinstance(body, str):
                parts = ['<div class="output-html wiz-widget">']
                if isinstance(title, str) and title.strip():
                    parts.append(f'<div class="widget-title">{_escaped_text(title)}</div>')
                parts.append(sanitize_html(body))
                if isinstance(goals, list):
                    for goal in goals:
                        if isinstance(goal, str):
                            parts.append(f'<pre class="widget-goal">{_escaped_text(goal)}</pre>')
                parts.append("</div>")
                return "".join(parts)
        return _note("<strong>Interactive widget not exported.</strong> "
                     "The widget has no static HTML body; its state lived in the kernel.")

    if _WIDGET_VIEW in data:
        if isinstance(data.get("text/html"), str):
            return ('<div class="output-html wiz-widget">'
                    + sanitize_html(data["text/html"])
                    + '</div><p class="output-caption">Static fallback of an interactive '
                      'widget; the widget state is not exported.</p>')
        return _note("<strong>Interactive widget not exported.</strong> "
                     "A Jupyter widget view needs a live kernel; only its notebook "
                     "state remains, and that is not a static page.")

    if isinstance(data.get("text/html"), str):
        return ('<div class="output-html">'
                + sanitize_html(data["text/html"]) + "</div>")
    if isinstance(data.get("text/markdown"), str):
        return ('<div class="output output-markdown">'
                + markdown_to_html(data["text/markdown"]) + "</div>")
    if isinstance(data.get("image/svg+xml"), str):
        payload = base64.b64encode(data["image/svg+xml"].encode("utf-8")).decode("ascii")
        return (f'<div class="output-image"><img alt="output" '
                f'src="data:image/svg+xml;base64,{payload}"></div>')
    for mime, label in (("image/png", "png"), ("image/jpeg", "jpeg"),
                        ("image/gif", "gif"), ("image/webp", "webp")):
        value = data.get(mime)
        if isinstance(value, str) and value.strip():
            payload = re.sub(r"\s+", "", value)
            if not re.fullmatch(r"[A-Za-z0-9+/=]+", payload):
                return _note(f"An embedded {label} image was not valid base64 and was "
                             "not exported.")
            return (f'<div class="output-image"><img alt="output" '
                    f'src="data:image/{label};base64,{payload}"></div>')
    if isinstance(data.get("text/plain"), str):
        return ('<pre class="output-text">'
                + html.escape(data["text/plain"], quote=False) + "</pre>")
    if "application/json" in data:
        try:
            payload = json.dumps(data["application/json"], indent=2, sort_keys=True,
                                 ensure_ascii=False)
        except (TypeError, ValueError):
            payload = json.dumps(data["application/json"], sort_keys=True,
                                 ensure_ascii=False, default=str)
        return ('<pre class="output-json">'
                + html.escape(payload, quote=False) + "</pre>")
    keys = ", ".join(sorted(data)) or "an empty bundle"
    return _note(f"An output with no static representation ({_escaped_text(keys)}) "
                 "was not exported.")


def _outputs_html(outputs: list[dict]) -> str:
    parts: list[str] = []
    index = 0
    while index < len(outputs):
        output = outputs[index]
        kind = output["output_type"]
        if kind == "stream":
            name = output.get("name", "stdout")
            text = output.get("text", "")
            index += 1
            while (index < len(outputs) and outputs[index]["output_type"] == "stream"
                   and outputs[index].get("name", "stdout") == name):
                text += outputs[index].get("text", "")
                index += 1
            if text:
                parts.append(f'<pre class="output stream stream-{name}">'
                             + html.escape(text, quote=False) + "</pre>")
            continue
        if kind == "error":
            ename = output.get("ename", "Error")
            evalue = output.get("evalue", "")
            traceback = output.get("traceback", "")
            parts.append('<div class="output output-error">'
                         f'<p class="error-name">{_escaped_text(ename)}: '
                         f'{_escaped_text(evalue)}</p>')
            if traceback:
                parts.append('<pre class="traceback">'
                             + html.escape(str(traceback), quote=False) + "</pre>")
            parts.append("</div>")
            index += 1
            continue
        count = output.get("execution_count")
        bundle = _bundle_html(output.get("data") or {})
        if kind == "execute_result":
            prompt = f"Out&nbsp;[{count if count is not None else '&nbsp;'}]:"
            parts.append('<div class="output output-result">'
                         f'<span class="prompt out-prompt">{prompt}</span>'
                         + bundle + "</div>")
        else:  # display_data
            parts.append('<div class="output output-display">' + bundle + "</div>")
        index += 1
    return "\n".join(parts)


# -- documents ----------------------------------------------------------

_STYLE = """\
:root { color-scheme: light dark; --paper: #fdfdfb; --ink: #1d1d1b;
  --muted: #666; --line: #d9d9d4; --code: #f4f4ef; --accent: #7a3e00;
  --error: #a11; --error-bg: #fff3f2; }
@media (prefers-color-scheme: dark) {
  :root { --paper: #1d1d1b; --ink: #fdfdfb; --muted: #aaa; --line: #3a3a36;
    --code: #262622; --accent: #ffb86b; --error: #ff8a80; --error-bg: #3a2020; }
}
* { box-sizing: border-box; }
body { margin: 0; background: var(--paper); color: var(--ink);
  font: 16px/1.55 system-ui, -apple-system, "Segoe UI", sans-serif; }
main.notebook { max-width: 58rem; margin: 0 auto; padding: 2rem 1.25rem 4rem; }
.notebook-header { border-bottom: 1px solid var(--line); margin-bottom: 1.5rem; }
.notebook-header h1 { margin: 0 0 .25rem; font-size: 1.9rem; line-height: 1.2; }
.notebook-subtitle { color: var(--muted); margin: 0 0 1.25rem; font-size: .92rem; }
.cell { margin: 0 0 1.4rem; }
.cell-code { border-left: 3px solid var(--line); padding-left: 1rem; }
.prompt { color: var(--muted); font: .8rem/1.4 ui-monospace, monospace;
  user-select: none; }
.cell-input { display: grid; grid-template-columns: 5.5rem 1fr; gap: .25rem;
  align-items: start; }
.cell-input .prompt { padding-top: .45rem; text-align: right; }
pre { margin: .45rem 0; overflow-x: auto; background: var(--code);
  border-radius: .25rem; padding: .65rem .75rem; }
pre code { font: .88rem/1.45 ui-monospace, SFMono-Regular, Menlo, monospace;
  white-space: pre; }
.code { margin: 0; }
.cell-outputs { margin-left: 5.75rem; }
.output { margin: .4rem 0; }
.output-result { display: grid; grid-template-columns: 4.5rem 1fr; gap: .5rem;
  align-items: start; }
.output-result .out-prompt { text-align: right; padding-top: .2rem; }
.output-text, .output-json, .stream, .traceback { font: .85rem/1.45 ui-monospace,
  SFMono-Regular, Menlo, monospace; }
.stream-stderr { border-left: 3px solid var(--accent); }
.output-error { background: var(--error-bg); border-left: 3px solid var(--error);
  border-radius: .25rem; padding: .55rem .75rem; }
.error-name { color: var(--error); font-weight: 600; margin: 0 0 .3rem; }
.output-note { color: var(--muted); border-left: 3px solid var(--line);
  padding: .2rem .75rem; }
.output-caption { color: var(--muted); font-size: .85rem; margin: .2rem 0; }
.output-html table { border-collapse: collapse; margin: .4rem 0; }
.output-html th, .output-html td { border: 1px solid var(--line);
  padding: .25rem .5rem; text-align: left; }
.output-image img { max-width: 100%; height: auto; }
.wiz-widget { border: 1px solid var(--line); border-radius: .3rem;
  padding: .5rem .75rem; }
.widget-title { font-weight: 600; margin-bottom: .3rem; }
.widget-goal { font-size: .85rem; }
.cell-raw pre { border: 1px dashed var(--line); }
blockquote { margin: .5rem 0; padding-left: .9rem; border-left: 3px solid
  var(--line); color: var(--muted); }
.markdown-code { background: var(--code); }
a { color: var(--accent); }
@media print { .cell { break-inside: avoid; } }
"""

_NOTEBOOK_NOTE = ("Static export: code and stored outputs are reproduced; the kernel, "
                  "its definitions and any interactive output are not.")


def _html_document(notebook: Notebook) -> str:
    heading = _first_heading(notebook.cells)
    parts = [
        "<!doctype html>",
        '<html lang="en">',
        "<head>",
        '<meta charset="utf-8">',
        '<meta name="viewport" content="width=device-width, initial-scale=1">',
        '<meta name="generator" content="wiz nb export">',
        f"<title>{_escaped_text(notebook.title)}</title>",
        f"<style>\n{_STYLE}</style>",
        "</head>",
        "<body>",
        '<main class="notebook">',
        '<header class="notebook-header">',
    ]
    # When the notebook's own first cell starts with this heading, that heading is
    # the title: do not repeat it above the cell.
    if heading != notebook.title:
        parts.append(f"<h1>{_escaped_text(notebook.title)}</h1>")
    parts.append(
        f'<p class="notebook-subtitle">Exported from <code>'
        f"{_escaped_text(notebook.path.name)}</code>. {_escaped_text(_NOTEBOOK_NOTE)}</p>")
    parts.append("</header>")
    for index, cell in enumerate(notebook.cells, 1):
        if cell.kind == "markdown":
            parts.append(f'<section class="cell cell-markdown" id="cell-{index}">')
            parts.append(markdown_to_html(cell.source))
            parts.append("</section>")
        elif cell.kind == "raw":
            parts.append(f'<section class="cell cell-raw" id="cell-{index}">')
            parts.append('<pre class="raw">' + html.escape(cell.source, quote=False)
                         + "</pre>")
            parts.append("</section>")
        else:
            count = cell.execution_count
            prompt = f"In&nbsp;[{count if count is not None else '&nbsp;'}]:"
            parts.append(f'<section class="cell cell-code" id="cell-{index}">')
            parts.append('<div class="cell-input">'
                         f'<span class="prompt in-prompt">{prompt}</span>'
                         '<pre class="code"><code class="language-wiz">'
                         + html.escape(cell.source, quote=False)
                         + "</code></pre></div>")
            if cell.outputs:
                parts.append('<div class="cell-outputs">')
                parts.append(_outputs_html(cell.outputs))
                parts.append("</div>")
            parts.append("</section>")
    parts += ["</main>", "</body>", "</html>", ""]
    return "\n".join(parts)


def _markdown_document(notebook: Notebook) -> str:
    lines = [f"<!-- wiz nb export: {notebook.path.name} -->", ""]
    if _first_heading(notebook.cells) != notebook.title:
        lines += [f"# {notebook.title}", ""]
    for index, cell in enumerate(notebook.cells, 1):
        if cell.kind == "markdown":
            lines += [cell.source.rstrip(), ""]
        elif cell.kind == "raw":
            lines += [f"<!-- cell {index}: raw -->", "```text",
                      cell.source.rstrip(), "```", ""]
        else:
            count = cell.execution_count
            label = count if count is not None else " "
            lines += [f"<!-- In [{label}]: -->", "```wiz",
                      cell.source.rstrip(), "```", ""]
            for output in cell.outputs:
                kind = output["output_type"]
                if kind == "stream":
                    name = output.get("name", "stdout")
                    text = output.get("text", "")
                    if text:
                        lines += [f"<!-- {name} -->", "```text",
                                  text.rstrip(), "```", ""]
                elif kind == "error":
                    ename = output.get("ename", "Error")
                    evalue = output.get("evalue", "")
                    lines += [f"**{_plain(str(ename))}**: {evalue}", ""]
                    trace = str(output.get("traceback", ""))
                    if trace:
                        lines += ["```text", trace.rstrip(), "```", ""]
                else:
                    bundle = output.get("data") or {}
                    if _WIDGET_VIEW in bundle or _WIDGET_WIZ in bundle:
                        body = _widget_markdown(bundle)
                        lines += [body, ""]
                    elif isinstance(bundle.get("text/html"), str):
                        lines += ["<!-- html output -->",
                                  sanitize_html(bundle["text/html"]), ""]
                    elif isinstance(bundle.get("text/markdown"), str):
                        lines += [bundle["text/markdown"].rstrip(), ""]
                    elif isinstance(bundle.get("image/svg+xml"), str):
                        payload = base64.b64encode(
                            bundle["image/svg+xml"].encode("utf-8")).decode("ascii")
                        lines += [f"![output](data:image/svg+xml;base64,{payload})", ""]
                    elif any(isinstance(bundle.get(mime), str)
                             for mime in ("image/png", "image/jpeg",
                                          "image/gif", "image/webp")):
                        mime = next(mime for mime in ("image/png", "image/jpeg",
                                                      "image/gif", "image/webp")
                                    if isinstance(bundle.get(mime), str))
                        payload = re.sub(r"\s+", "", bundle[mime])
                        lines += [f"![output](data:{mime};base64,{payload})", ""]
                    elif isinstance(bundle.get("text/plain"), str):
                        prefix = "**Out[%s]**" % (output.get("execution_count")
                                                  if output.get("execution_count") is not None
                                                  else " ")
                        lines += [prefix, "", "```text",
                                  bundle["text/plain"].rstrip(), "```", ""]
                    elif "application/json" in bundle:
                        lines += ["```json",
                                  json.dumps(bundle["application/json"], indent=2,
                                             sort_keys=True, ensure_ascii=False),
                                  "```", ""]
                    else:
                        lines += ["<!-- an output with no static text was not exported -->", ""]
    return "\n".join(lines).rstrip() + "\n"


def _widget_markdown(bundle: dict) -> str:
    if _WIDGET_WIZ in bundle:
        widget = bundle[_WIDGET_WIZ]
        if isinstance(widget, dict) and isinstance(widget.get("html"), str):
            title = widget.get("title")
            body = (f"**{_plain(str(title))}**\n\n" if isinstance(title, str)
                    and title.strip() else "")
            body += sanitize_html(widget["html"])
            goals = widget.get("goals")
            if isinstance(goals, list):
                for goal in goals:
                    if isinstance(goal, str):
                        body += "\n\n```text\n" + goal + "\n```"
            return body
    if _WIDGET_VIEW in bundle and isinstance(bundle.get("text/html"), str):
        return sanitize_html(bundle["text/html"])
    return ("> **Interactive output not exported.** A widget needs the kernel that "
            "created it; its state is not in the notebook file.")


def render_html(notebook: Notebook) -> str:
    return _html_document(notebook)


def render_markdown(notebook: Notebook) -> str:
    return _markdown_document(notebook)


def render(notebook: Notebook, fmt: str = "html") -> str:
    if fmt == "html":
        return render_html(notebook)
    if fmt in ("md", "markdown"):
        return render_markdown(notebook)
    raise ValueError(f"unknown format {fmt!r} (html or md)")


# -- the command --------------------------------------------------------

def _output_path(notebook: Path, out: str | None, fmt: str) -> Path:
    if out:
        return Path(out)
    suffix = ".md" if fmt == "md" else ".html"
    return notebook.with_suffix(suffix)


def _fmt_from_args(args: argparse.Namespace) -> str:
    fmt = args.to
    if args.out and args.out != "-" and args.out != "":
        suffix = Path(args.out).suffix.lower()
        inferred = {"md": "md", "markdown": "md", "html": "html", "htm": "html"}.get(
            suffix.lstrip("."))
        if fmt is None:
            fmt = inferred
        elif inferred is not None and inferred != fmt:
            raise ValueError(f"--to {fmt} does not match the suffix of --out {args.out}")
    return fmt or "html"


def main(argv: list[str] | None = None) -> int:
    argv = list(sys.argv[1:] if argv is None else argv)
    if argv and argv[0] == "nb":
        argv = argv[1:]
    if argv and argv[0] == "export":
        argv = argv[1:]
    parser = argparse.ArgumentParser(
        prog="wiz nb export",
        description="Export a Wiz notebook to a self-contained HTML page or Markdown.")
    parser.add_argument("notebook", metavar="FILE.ipynb")
    parser.add_argument("--to", choices=("html", "md"), dest="to",
                        help="output format (default: html, or from --out's suffix)")
    parser.add_argument("--out", metavar="FILE",
                        help="output file (default: the notebook's name with .html/.md)")
    parser.add_argument("--check", action="store_true",
                        help="render in memory and fail if the committed output differs")
    args = parser.parse_args(argv)

    try:
        fmt = _fmt_from_args(args)
    except ValueError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2

    try:
        notebook = load_notebook(args.notebook)
    except NotebookError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2

    output = _output_path(notebook.path, args.out, fmt)
    text = render(notebook, fmt)

    if args.out == "-":
        sys.stdout.write(text)
        return 0

    if args.check:
        try:
            committed = output.read_text(encoding="utf-8")
        except FileNotFoundError:
            print(f"error: {output}: exported output is missing; run "
                  f"`wiz nb export {args.notebook}` first", file=sys.stderr)
            return 1
        except OSError as exc:
            print(f"error: {output}: cannot read: {exc.strerror or exc}", file=sys.stderr)
            return 2
        if committed == text:
            print(f"{output}: up to date")
            return 0
        print(f"error: {output}: exported output is out of date; regenerate with "
              f"`wiz nb export {args.notebook}`", file=sys.stderr)
        diff = difflib.unified_diff(committed.splitlines(), text.splitlines(),
                                    fromfile=str(output), tofile="generated",
                                    lineterm="")
        for number, line in enumerate(diff):
            if number >= 40:
                print("… diff truncated …", file=sys.stderr)
                break
            print(line, file=sys.stderr)
        return 1

    try:
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(text, encoding="utf-8")
    except OSError as exc:
        print(f"error: {output}: cannot write: {exc.strerror or exc}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
