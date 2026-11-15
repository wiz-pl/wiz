"""A mock language server for the kernel's tests (``--self-test``, unittest).

It speaks the same stdio LSP framing as the kernel's client and answers with
fixed completions and hover text, so the client's cursor translation and its
empty-result paths can be exercised without building Wiz::

    python -m wiz_kernel.mock_lsp [--log FILE]

Every request and notification is appended to ``--log`` as one JSON object per
line (``{"method": …, "params": …}``), which is how the self-test checks the
exact ``position`` the client sent.  A document containing ``MOCK_NONE`` gets no
completions and no hover; one containing ``MOCK_INCOMPLETE`` reports an
incomplete completion list.
"""

from __future__ import annotations

import argparse
import json
import sys

from .lsp import encode_message, offset_to_position, position_to_offset, read_message, word_start


def _log(handle, message: dict) -> None:
    if handle is None:
        return
    handle.write(json.dumps(message, ensure_ascii=False) + "\n")
    handle.flush()


def _text_edit(document: str, position: dict, new_text: str) -> dict:
    end = position_to_offset(document, int(position.get("line", 0)),
                             int(position.get("character", 0)))
    start = word_start(document, end)
    return {
        "range": {"start": _pos(document, start), "end": _pos(document, end)},
        "newText": new_text,
    }


def _pos(document: str, offset: int) -> dict:
    line, character = offset_to_position(document, offset)
    return {"line": line, "character": character}


def _completion(text: str, position: dict) -> dict:
    if "MOCK_NONE" in text:
        return {"isIncomplete": False, "items": []}
    items = []
    for label, kind, detail, documentation in (
            ("mockValue", 6, "Nat", {"kind": "markdown", "value": "The mock value."}),
            ("mockFunction", 3, "Nat → Nat", "A function from the mock.")):
        items.append({
            "label": label,
            "kind": kind,
            "detail": detail,
            "documentation": documentation,
            "textEdit": _text_edit(text, position, label),
        })
    return {"isIncomplete": "MOCK_INCOMPLETE" in text, "items": items}


def _hover(text: str) -> dict | None:
    if "MOCK_NONE" in text:
        return None
    return {"contents": {"kind": "markdown",
                         "value": "```wiz\nmockHover : Nat\n```\n\nMock documentation."}}


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(prog="python -m wiz_kernel.mock_lsp")
    parser.add_argument("--log", metavar="FILE", help="append every message as JSON lines")
    args = parser.parse_args(argv)

    documents: dict[str, str] = {}
    log = open(args.log, "w", encoding="utf-8") if args.log else None
    output = sys.stdout.buffer

    def send(message: dict) -> None:
        output.write(encode_message(message))
        output.flush()

    def reply(ident, result) -> None:
        send({"jsonrpc": "2.0", "id": ident, "result": result})

    def error(ident, code: int, text: str) -> None:
        send({"jsonrpc": "2.0", "id": ident,
              "error": {"code": code, "message": text}})

    def notify(method: str, params) -> None:
        send({"jsonrpc": "2.0", "method": method, "params": params})

    try:
        while True:
            message = read_message(sys.stdin.buffer)
            if message is None:
                return 0
            method = message.get("method")
            params = message.get("params") or {}
            _log(log, message)
            ident = message.get("id")
            if method == "initialize":
                reply(ident, {
                    "capabilities": {
                        "textDocumentSync": 1,
                        "completionProvider": {"triggerCharacters": ["."]},
                        "hoverProvider": True,
                    },
                    "serverInfo": {"name": "wiz-kernel-mock-lsp"},
                })
            elif method == "initialized":
                pass
            elif method == "shutdown":
                reply(ident, None)
            elif method == "exit":
                return 0
            elif method in ("textDocument/didOpen", "textDocument/didChange"):
                uri = (params.get("textDocument") or {}).get("uri", "")
                if method == "textDocument/didOpen":
                    text = (params.get("textDocument") or {}).get("text", "")
                else:
                    changes = params.get("contentChanges") or []
                    text = changes[-1].get("text", "") if changes else documents.get(uri, "")
                documents[uri] = text
                notify("textDocument/publishDiagnostics", {"uri": uri, "diagnostics": []})
            elif method == "textDocument/didClose":
                documents.pop((params.get("textDocument") or {}).get("uri", ""), None)
            elif method == "textDocument/completion":
                uri = (params.get("textDocument") or {}).get("uri", "")
                text = documents.get(uri, "")
                reply(ident, _completion(text, params.get("position") or {}))
            elif method == "textDocument/hover":
                uri = (params.get("textDocument") or {}).get("uri", "")
                text = documents.get(uri, "")
                reply(ident, _hover(text))
            elif ident is not None:
                error(ident, -32601, f"method not found: {method}")
    finally:
        if log is not None:
            log.close()


if __name__ == "__main__":
    sys.exit(main())
