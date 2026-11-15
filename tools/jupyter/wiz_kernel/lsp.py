"""A small Language Server Protocol client for the Jupyter kernel.

The kernel's ``complete_request`` and ``inspect_request`` are answered by the
Wiz language server (``wiz lsp``), not by a second implementation of inference:
this module speaks LSP 3.17 over **stdio** (``Content-Length`` framed JSON-RPC,
one ``wiz lsp`` child per kernel, started lazily and stopped with the kernel).

The notebook has no file, but the server wants a document.  :class:`Notebook`
composes the accumulated source — an ``import Prelude`` (unless a cell already
imports it), then every executed cell, then the cell being completed — exactly
as the batch driver composes a notebook, and maps the cell's cursor into it.
The mapping is the rule that matters:

    compose the document the server sees, take the *code-point* prefix up to
    the cursor, count lines, and convert the last line to **UTF-16 code units**
    (LSP's default ``positionEncoding``).  Never add UTF-16 widths across cells.

Everything degrades to a value, not an exception: :func:`completion_answer`
returns an empty list and :func:`hover_answer` ``found: False`` when there is
no server, and the reason travels in the reply's metadata.
"""

from __future__ import annotations

import json
import os
import queue
import re
import shlex
import subprocess
import threading
import time
from dataclasses import dataclass, field
from pathlib import Path

PRELUDE = "import Prelude\n"
"""What the batch driver prepends to a notebook that does not import it."""


class LspError(Exception):
    """A JSON-RPC error, a timeout, or a dead server."""


class LspUnavailable(LspError):
    """The server could not be started (no binary, no ``lsp`` subcommand, …)."""


# -- positions ----------------------------------------------------------

def utf16_units(text: str) -> int:
    """The length of ``text`` in UTF-16 code units (LSP's ``character``)."""
    return sum(2 if ord(ch) > 0xFFFF else 1 for ch in text)


def offset_to_position(text: str, offset: int) -> tuple[int, int]:
    """A Python string offset (a code-point index) as an LSP ``(line, character)``.

    Lines are 0-based and separated by ``\\n``; the character is UTF-16 code
    units in its line, so an astral character counts two.
    """
    offset = max(0, min(int(offset), len(text)))
    before = text[:offset]
    line = before.count("\n")
    line_start = before.rfind("\n") + 1
    return line, utf16_units(before[line_start:])


def position_to_offset(text: str, line: int, character: int) -> int:
    """An LSP ``(line, character)`` as a Python string offset.

    A character inside a surrogate pair maps to the start of that character:
    a Python string cannot split one.
    """
    line = max(0, int(line))
    character = max(0, int(character))
    start = 0
    for _ in range(line):
        newline = text.find("\n", start)
        if newline < 0:
            return len(text)
        start = newline + 1
    units = 0
    index = start
    while index < len(text) and text[index] != "\n":
        width = 2 if ord(text[index]) > 0xFFFF else 1
        if units + width > character:
            break
        units += width
        index += 1
    return index


def word_start(code: str, cursor: int) -> int:
    """Where the dotted word ending at ``cursor`` starts (a Python offset)."""
    index = max(0, min(int(cursor), len(code)))
    while index > 0:
        char = code[index - 1]
        if not (char.isalnum() or char in "_'."):
            break
        index -= 1
    return index


# -- the notebook document ---------------------------------------------

class Notebook:
    """The executed cells, and the document they make with the current one."""

    def __init__(self, cells: list[str] | None = None):
        self.cells: list[str] = list(cells or [])

    def append(self, code: str) -> None:
        self.cells.append(code)

    def clear(self) -> None:
        self.cells.clear()

    def compose(self, current: str) -> tuple[str, int]:
        """The document for ``current`` and the code-point offset where it starts."""
        cells = self.cells + [current]
        needs_prelude = not any(re.search(r"^\s*import\s+Prelude\b", cell, re.MULTILINE)
                                for cell in cells)
        prefix = PRELUDE if needs_prelude else ""
        prior = "".join(cell if cell.endswith("\n") else cell + "\n"
                        for cell in self.cells)
        head = prefix + prior
        return head + current, len(head)

    def position(self, current: str, cursor: int) -> tuple[str, int, int, int]:
        """``(document, cell_start, line, character)`` for a cursor in ``current``."""
        document, start = self.compose(current)
        cursor = max(0, min(int(cursor), len(current)))
        line, character = offset_to_position(document, start + cursor)
        return document, start, line, character

    def cell_offset(self, document: str, start: int, line: int, character: int) -> int:
        """An LSP position in ``document`` as a Python offset in the current cell."""
        return max(0, position_to_offset(document, line, character) - start)


# -- completion and hover replies ---------------------------------------

@dataclass
class CompletionAnswer:
    items: list[dict] = field(default_factory=list)
    cursor_start: int = 0
    cursor_end: int = 0
    is_incomplete: bool = False
    available: bool = True
    reason: str | None = None


@dataclass
class HoverAnswer:
    found: bool = False
    data: dict = field(default_factory=dict)
    available: bool = True
    reason: str | None = None


# LSP CompletionItemKind -> the type names Jupyter frontends know.
_JUPYTER_KINDS = {
    1: "text",        # Text
    2: "method",      # Method
    3: "function",    # Function
    4: "function",    # Constructor (a value; Jupyter has no constructor type)
    5: "property",    # Field
    6: "text",        # Variable (a local; not a callable)
    7: "class",       # Class
    8: "class",       # Interface
    9: "module",      # Module
    10: "property",   # Property
    11: "text",       # Unit
    12: "text",       # Value
    13: "class",      # Enum
    14: "keyword",    # Keyword
    15: "text",       # Snippet
    16: "text",       # Color
    17: "path",       # File
    18: "text",       # Reference
    19: "path",       # Folder
    20: "text",       # EnumMember
    21: "text",       # Constant
    22: "class",      # Struct
    23: "text",       # Event
    24: "text",       # Operator
    25: "class",      # TypeParameter
}


def _markup(value) -> str:
    """Flatten LSP ``MarkupContent``/``MarkedString``/string documentation."""
    if isinstance(value, str):
        return value
    if isinstance(value, dict):
        if isinstance(value.get("value"), str):
            language = value.get("language")
            if isinstance(language, str) and language:
                return f"```{language}\n{value['value']}\n```"
            return value["value"]
        return ""
    if isinstance(value, list):
        return "\n\n".join(part for part in (_markup(v) for v in value) if part)
    return ""


def completion_answer(result, *, text: str, code: str, cursor: int,
                      cell_start: int) -> CompletionAnswer:
    """Map a ``textDocument/completion`` result to a Jupyter completion reply.

    ``text`` is the document the request named, ``code`` the cell, ``cursor``
    the offset in the cell and ``cell_start`` the cell's offset in ``text``.
    """
    if isinstance(result, list):
        items, incomplete = result, False
    elif isinstance(result, dict):
        items = result.get("items") or []
        incomplete = bool(result.get("isIncomplete", False))
    else:
        items, incomplete = [], False

    matches: list[dict] = []
    starts: list[int] = []
    ends: list[int] = []
    for item in items:
        if not isinstance(item, dict):
            continue
        edit = item.get("textEdit") if isinstance(item.get("textEdit"), dict) else {}
        new_text = edit.get("newText")
        if not isinstance(new_text, str):
            new_text = item.get("insertText")
        if not isinstance(new_text, str):
            new_text = item.get("label")
        if not isinstance(new_text, str):
            continue
        rng = edit.get("range") if isinstance(edit.get("range"), dict) else None
        if rng is not None:
            start = rng.get("start") or {}
            end = rng.get("end") or start
            try:
                start_offset = position_to_offset(
                    text, int(start.get("line", 0)), int(start.get("character", 0)))
                end_offset = position_to_offset(
                    text, int(end.get("line", 0)), int(end.get("character", 0)))
            except (TypeError, ValueError):
                pass
            else:
                starts.append(max(0, start_offset - cell_start))
                ends.append(max(0, end_offset - cell_start))
        label_details = item.get("labelDetails")
        if isinstance(item.get("detail"), str):
            signature = item["detail"]
        elif isinstance(label_details, dict) and isinstance(label_details.get("detail"), str):
            signature = label_details["detail"]
        else:
            signature = ""
        matches.append({
            "text": new_text,
            "type": _JUPYTER_KINDS.get(item.get("kind"), "text"),
            "signature": signature,
            "documentation": _markup(item.get("documentation")),
        })

    if starts:
        start = min(starts)
        # The item whose edit starts at the shared start decides where the
        # replacement ends (Jupyter has one cursor range for the whole list).
        end = ends[starts.index(start)]
    else:
        start, end = word_start(code, cursor), cursor
    cursor = max(0, min(int(cursor), len(code)))
    start = max(0, min(start, cursor))
    end = max(start, min(max(end, cursor), len(code)))
    return CompletionAnswer(matches, start, end, incomplete)


def hover_answer(result) -> HoverAnswer:
    """Map a ``textDocument/hover`` result to Jupyter's ``found``/``data``."""
    if not isinstance(result, dict):
        return HoverAnswer(False, {})
    contents = result.get("contents")
    if contents is None:
        return HoverAnswer(False, {})
    markdown = ""
    plain = ""

    def visit(value) -> None:
        nonlocal markdown, plain
        if isinstance(value, str):
            plain = plain + ("\n\n" if plain else "") + value
        elif isinstance(value, dict):
            kind = value.get("kind")
            text = value.get("value")
            if not isinstance(text, str):
                return
            if kind == "markdown":
                markdown = markdown + ("\n\n" if markdown else "") + text
            elif kind == "plaintext":
                plain = plain + ("\n\n" if plain else "") + text
            else:
                plain = plain + ("\n\n" if plain else "") + _markup(value)
        elif isinstance(value, list):
            for part in value:
                visit(part)

    visit(contents)
    text = markdown or plain
    if not text.strip():
        return HoverAnswer(False, {})
    data = {"text/plain": text}
    if markdown:
        data["text/markdown"] = markdown
    return HoverAnswer(True, data)


# -- the client ---------------------------------------------------------

def encode_message(message: dict) -> bytes:
    body = json.dumps(message, ensure_ascii=False).encode("utf-8")
    return b"Content-Length: %d\r\n\r\n" % len(body) + body


def read_message(stream) -> dict | None:
    """One LSP message from a binary stream, or ``None`` at end of file."""
    headers: dict[bytes, bytes] = {}
    while True:
        line = stream.readline()
        if not line:
            return None
        line = line.strip()
        if not line:
            break
        try:
            name, value = line.split(b":", 1)
        except ValueError:
            continue
        headers[name.strip().lower()] = value.strip()
    try:
        length = int(headers.get(b"content-length", b"0"))
    except ValueError:
        return None
    if length < 0 or length > (64 << 20):
        return None
    body = stream.read(length)
    if len(body) != length:
        return None
    try:
        message = json.loads(body.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError):
        return None
    return message if isinstance(message, dict) else None


_EOF = object()


class LspClient:
    """One ``wiz lsp`` child, over stdio.  Start it, then ask questions."""

    def __init__(self, command: list[str], *, cwd: str | None = None,
                 root_uri: str | None = None, timeout: float = 15.0,
                 start_timeout: float = 30.0, env: dict | None = None,
                 name: str = "wiz-jupyter-kernel"):
        self.command = [str(part) for part in command]
        self.cwd = os.path.abspath(cwd or os.getcwd())
        self.root_uri = root_uri or Path(self.cwd).as_uri()
        self.timeout = timeout
        self.start_timeout = start_timeout
        self.env = env
        self.name = name
        self.proc: subprocess.Popen | None = None
        self._messages: queue.Queue = queue.Queue()
        self._write_lock = threading.Lock()
        self._next_id = 0
        self._reader: threading.Thread | None = None
        self._stderr: threading.Thread | None = None
        self._stderr_tail: list[str] = []
        self._dead = False
        self._initialized = False
        self._uri: str | None = None
        self._text: str | None = None
        self._version = 0

    # -- lifecycle ------------------------------------------------------

    @property
    def alive(self) -> bool:
        return (self.proc is not None and not self._dead
                and self.proc.poll() is None)

    def start(self) -> "LspClient":
        if self.proc is not None:
            return self
        self._messages = queue.Queue()
        self._dead = False
        self._initialized = False
        self._uri = None
        self._text = None
        self._version = 0
        self._stderr_tail = []
        try:
            self.proc = subprocess.Popen(
                self.command, cwd=self.cwd, stdin=subprocess.PIPE,
                stdout=subprocess.PIPE, stderr=subprocess.PIPE, bufsize=0,
                env=self.env)
        except OSError as exc:
            raise LspUnavailable(f"cannot run {self.command[0]}: {exc}") from exc
        self._reader = threading.Thread(
            target=self._read_loop, name="wiz-kernel-lsp-reader", daemon=True)
        self._reader.start()
        self._stderr = threading.Thread(
            target=self._stderr_loop, name="wiz-kernel-lsp-stderr", daemon=True)
        self._stderr.start()
        params = {
            "processId": None,
            "clientInfo": {"name": self.name},
            "rootUri": self.root_uri,
            "workspaceFolders": [{"uri": self.root_uri,
                                  "name": os.path.basename(self.cwd) or "wiz"}],
            "capabilities": {
                "general": {"positionEncodings": ["utf-16"]},
                "workspace": {"workspaceFolders": True, "configuration": False},
                "window": {"workDoneProgress": False},
                "textDocument": {
                    "synchronization": {"dynamicRegistration": False,
                                        "willSave": False, "didSave": False},
                    "hover": {"contentFormat": ["markdown", "plaintext"]},
                    "completion": {
                        "completionItem": {
                            "snippetSupport": False,
                            "documentationFormat": ["markdown", "plaintext"],
                        },
                    },
                },
                "experimental": {"wizElaborated": True},
            },
        }
        try:
            self._request("initialize", params, timeout=self.start_timeout)
        except LspError as exc:
            detail = self._stderr_detail()
            self.close()
            raise LspUnavailable(
                f"`{' '.join(self.command)}` did not initialize: {exc}"
                + (f" ({detail})" if detail else "")) from exc
        self._initialized = True
        self.notify("initialized", {})
        return self

    def close(self) -> None:
        proc = self.proc
        if proc is None:
            return
        try:
            if proc.poll() is None and not self._dead:
                try:
                    if self._uri is not None:
                        self.notify("textDocument/didClose",
                                    {"textDocument": {"uri": self._uri}})
                    self._request("shutdown", None, timeout=2.0)
                    self.notify("exit", None)
                except LspError:
                    pass
        finally:
            self.proc = None
            try:
                if proc.stdin is not None:
                    proc.stdin.close()
            except (OSError, ValueError):
                pass
            try:
                proc.wait(timeout=3)
            except subprocess.TimeoutExpired:
                proc.terminate()
                try:
                    proc.wait(timeout=3)
                except subprocess.TimeoutExpired:
                    proc.kill()
                    try:
                        proc.wait(timeout=3)
                    except subprocess.TimeoutExpired:
                        pass
            if self._reader is not None:
                self._reader.join(timeout=1)
            if self._stderr is not None:
                self._stderr.join(timeout=1)
            self._dead = True

    def __enter__(self) -> "LspClient":
        return self.start()

    def __exit__(self, *exc) -> None:
        self.close()

    # -- transport ------------------------------------------------------

    def _stderr_loop(self) -> None:
        stream = self.proc.stderr if self.proc is not None else None
        if stream is None:
            return
        try:
            for raw in iter(stream.readline, b""):
                text = raw.decode("utf-8", "replace").rstrip()
                if len(self._stderr_tail) < 8:
                    self._stderr_tail.append(text)
        except (OSError, ValueError):
            pass

    def _read_loop(self) -> None:
        stream = self.proc.stdout if self.proc is not None else None
        try:
            while stream is not None:
                message = read_message(stream)
                if message is None:
                    break
                if "method" in message and "id" in message:
                    self._method_not_found(message)
                    continue
                self._messages.put(message)
        except (OSError, ValueError):
            pass
        finally:
            self._dead = True
            self._messages.put(_EOF)

    def _send(self, message: dict) -> None:
        if self.proc is None or self.proc.stdin is None or self._dead:
            raise LspError("the language server is not running")
        try:
            with self._write_lock:
                data = memoryview(encode_message(message))
                while data:
                    written = self.proc.stdin.write(data)
                    if not written:
                        raise OSError("short write to the language server")
                    data = data[written:]
                self.proc.stdin.flush()
        except (OSError, ValueError) as exc:
            self._dead = True
            raise LspError(f"cannot write to the language server: {exc}") from exc

    def _method_not_found(self, message: dict) -> None:
        try:
            self._send({"jsonrpc": "2.0", "id": message.get("id"),
                        "error": {"code": -32601,
                                  "message": f"method not supported by the Wiz kernel: "
                                             f"{message.get('method')}"}})
        except LspError:
            pass

    def notify(self, method: str, params) -> None:
        message = {"jsonrpc": "2.0", "method": method}
        if params is not None:
            message["params"] = params
        self._send(message)

    def _request(self, method: str, params, *, timeout: float | None = None):
        self._next_id += 1
        ident = self._next_id
        message = {"jsonrpc": "2.0", "id": ident, "method": method}
        if params is not None:
            message["params"] = params
        self._send(message)
        deadline = (timeout if timeout is not None else self.timeout)
        end = time.monotonic() + deadline
        while True:
            remaining = end - time.monotonic()
            if remaining <= 0:
                self._dead = True
                raise LspError(f"{method} timed out after {deadline:.0f}s")
            try:
                answer = self._messages.get(timeout=remaining)
            except queue.Empty:
                self._dead = True
                raise LspError(f"{method} timed out after {deadline:.0f}s")
            if answer is _EOF:
                detail = self._stderr_detail()
                raise LspError(f"the language server exited"
                               + (f": {detail}" if detail else ""))
            if not isinstance(answer, dict) or answer.get("id") != ident:
                continue
            if "error" in answer:
                error = answer.get("error") or {}
                code = error.get("code")
                text = error.get("message") or "language server error"
                raise LspError(f"{method}: {text}" + (f" ({code})" if code else ""))
            return answer.get("result")

    def _stderr_detail(self) -> str:
        lines = [line for line in self._stderr_tail if line.strip()]
        if not lines:
            return ""
        return " / ".join(lines[-3:])[:240]

    # -- documents ------------------------------------------------------

    def ensure_document(self, uri: str, text: str) -> None:
        """``didOpen``/``didChange`` as needed; full text, as the protocol says."""
        if self._uri != uri:
            if self._uri is not None:
                try:
                    self.notify("textDocument/didClose",
                                {"textDocument": {"uri": self._uri}})
                except LspError:
                    pass
            self._uri, self._text, self._version = uri, text, 1
            self.notify("textDocument/didOpen", {
                "textDocument": {"uri": uri, "languageId": "wiz",
                                 "version": self._version, "text": text}})
        elif self._text != text:
            self._version += 1
            self._text = text
            self.notify("textDocument/didChange", {
                "textDocument": {"uri": uri, "version": self._version},
                "contentChanges": [{"text": text}]})

    def completion(self, uri: str, text: str, line: int, character: int):
        self.ensure_document(uri, text)
        return self._request("textDocument/completion", {
            "textDocument": {"uri": uri},
            "position": {"line": int(line), "character": int(character)},
            "context": {"triggerKind": 1},
        })

    def hover(self, uri: str, text: str, line: int, character: int):
        self.ensure_document(uri, text)
        return self._request("textDocument/hover", {
            "textDocument": {"uri": uri},
            "position": {"line": int(line), "character": int(character)},
        })


# -- discovery ----------------------------------------------------------

def lsp_command(executable: str, toolchain_args: list[str] | None,
                cwd: str) -> list[str]:
    """The command line for the language server: ``wiz … -I CWD lsp`` (stdio)."""
    return [executable, *(toolchain_args or []), "-I", os.path.abspath(cwd), "lsp"]


def command_from_spec(spec: str | list[str] | None) -> list[str] | None:
    """A user-supplied command line (``--lsp-command`` or ``$WIZ_KERNEL_LSP``)."""
    if spec is None:
        return None
    if isinstance(spec, list):
        return [str(part) for part in spec]
    try:
        parsed = shlex.split(spec)
    except ValueError as exc:
        raise LspUnavailable(f"cannot parse the language server command: {exc}") from exc
    return parsed or None


def notebook_uri(cwd: str) -> str:
    """A stable ``file://`` URI for the virtual notebook (it need not exist).

    It lives in the kernel's working directory so that ``include_str`` in a
    cell resolves against the same directory as a file opened by an editor.
    """
    return Path(cwd, ".wiz-kernel-notebook.wiz").resolve().as_uri()
