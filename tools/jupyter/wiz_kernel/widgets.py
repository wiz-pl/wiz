"""Notebook widgets: display bundles and Jupyter comms.

`lib/Web/Widget.wiz`'s `Widget.display` returns a pure string:

    WIZ_WIDGET:{"schema":"wiz.widget/1","html":"…","widgets":[…],"count":N}

The kernel recognises the prefix, turns it into a MIME bundle
(``application/vnd.wiz.widget+json`` plus the same fragment as ``text/html`` for
progressive enhancement) and opens **one comm per display** with target
``wiz.widgets``.  The widget descriptors carry a *callback expression* — Wiz source
naming a ``Widget.Callback`` — which is all the registry needs:

    comm_id -> {bundle, callbacks: widget id -> callback expression}

A front end sends ``{method: "event", widget_id, event, value}`` on the comm.  The
kernel evaluates, **in the notebook's own session**,

    #eval Widget.handle (<callback>) "<previous bundle>" "<widget id>" "<event>" "<value>"

which re-renders the old and new widget lists and diffs them with
``Loom.Rendered.diff``.  The resulting bundle (with ``patches``) goes back on the
same comm, and the browser applies it with ``web/framework/runtime.js``.

The only source that is spliced into the session is ``callback``: it comes from the
notebook author's own ``Widget.display`` call, so it has the authority of a cell.
Every value that comes back from the browser is quoted with :func:`wiz_literal` and
cannot become source.
"""

from __future__ import annotations

import json
import uuid
from dataclasses import dataclass, field

PREFIX = "WIZ_WIDGET:"
SCHEMA = "wiz.widget/1"
TARGET = "wiz.widgets"
MIME = "application/vnd.wiz.widget+json"


class WidgetError(Exception):
    """A comm message the kernel cannot honour (unknown comm or widget, bad value)."""


def _control(ch: str) -> str:
    """A Wiz `\\u{H}` escape for a control character."""
    return f"\\u{{{ord(ch):x}}}"


def wiz_literal(text: str) -> str:
    """`text` as a Wiz string literal.

    Wiz supports ``\\\\``, ``\\"``, ``\\n``, ``\\r``, ``\\t`` and ``\\u{H}`` escapes.
    Everything that comes from the browser goes through here; it is never spliced as
    source.
    """
    out = ['"']
    for ch in text:
        if ch == "\\":
            out.append("\\\\")
        elif ch == '"':
            out.append('\\"')
        elif ch == "\n":
            out.append("\\n")
        elif ch == "\r":
            out.append("\\r")
        elif ch == "\t":
            out.append("\\t")
        elif ord(ch) < 0x20:
            out.append(_control(ch))
        else:
            out.append(ch)
    out.append('"')
    return "".join(out)


def decode_eval_text(text: str | None) -> str | None:
    """The Wiz value of a ``#eval`` info line.

    The toolchain prints a `String` as a quoted, escaped literal (``"a\\"b"``), which
    is JSON for the ASCII escapes it emits; a non-string result is returned as-is.
    """
    if text is None:
        return None
    text = text.strip()
    if text.startswith('"'):
        try:
            return json.loads(text)
        except json.JSONDecodeError:
            return text
    return text


def parse_display(text: str | None) -> dict | None:
    """The bundle in a ``WIZ_WIDGET:`` display string (with or without the prefix)."""
    if text is None:
        return None
    text = text.strip()
    if not text.startswith(PREFIX):
        return None
    try:
        bundle = json.loads(text[len(PREFIX):])
    except json.JSONDecodeError:
        return None
    if not isinstance(bundle, dict) or bundle.get("schema") != SCHEMA:
        return None
    return bundle


def plain_summary(bundle: dict) -> str:
    """A terminal-friendly one-liner for the MIME bundle's `text/plain`."""
    widgets = bundle.get("widgets") or []
    if not widgets:
        return "no Wiz widgets"
    parts = [f"{w.get('id', '?')} ({w.get('kind', '?')})" for w in widgets]
    return f"{len(parts)} Wiz widget{'s' if len(parts) != 1 else ''}: " + ", ".join(parts)


def html_fragment(bundle: dict, comm_id: str) -> str:
    """The SSR fragment, wrapped so the loader can find it and its comm.

    The html is the renderer's own output (`Loom.toHtml`), which escapes every text
    and attribute; the wrapper adds only a hex comm id.
    """
    return (f'<div class="wiz-widget-fragment" data-wiz-widget-comm="{comm_id}">'
            f'{bundle.get("html", "")}</div>')


def mime_bundle(bundle: dict) -> dict:
    """The notebook data for one display (the bundle already carries `comm_id`)."""
    return {
        MIME: bundle,
        "text/html": html_fragment(bundle, bundle.get("comm_id", "")),
        "text/plain": plain_summary(bundle),
    }


@dataclass
class WidgetComm:
    comm_id: str
    bundle: dict
    callbacks: dict[str, str] = field(default_factory=dict)
    #: The callback used for a widget that did not declare one.
    default_callback: str = ""


class WidgetManager:
    """The comm registry and the event→evaluation round trip."""

    def __init__(self, backend) -> None:
        self.backend = backend
        self.comms: dict[str, WidgetComm] = {}

    # -- registry -------------------------------------------------------

    def open(self, bundle: dict) -> dict:
        """Register a display and give its bundle a fresh comm id.

        The returned dict is the bundle with ``comm_id`` added; the caller publishes
        ``comm_open`` with it and uses it as the ``execute_result`` data.
        """
        comm_id = uuid.uuid4().hex
        callbacks = {
            str(w.get("id", "")): str(w.get("callback", ""))
            for w in bundle.get("widgets") or []
            if isinstance(w, dict) and w.get("id")
        }
        self.comms[comm_id] = WidgetComm(comm_id=comm_id, bundle=bundle, callbacks=callbacks)
        return {**bundle, "comm_id": comm_id}

    def adopt(self, comm_id: str, bundle: dict) -> None:
        """Re-register a comm the front end opened (a reconnected notebook)."""
        if not comm_id or not isinstance(bundle, dict):
            return
        callbacks = {
            str(w.get("id", "")): str(w.get("callback", ""))
            for w in bundle.get("widgets") or []
            if isinstance(w, dict) and w.get("id")
        }
        existing = self.comms.get(comm_id)
        if existing is not None:
            existing.bundle = bundle
            existing.callbacks = callbacks
        else:
            self.comms[comm_id] = WidgetComm(comm_id, bundle, callbacks)

    def close(self, comm_id: str) -> None:
        self.comms.pop(comm_id, None)

    def info(self) -> dict:
        return {cid: {"target_name": TARGET} for cid in self.comms}

    # -- events ---------------------------------------------------------

    def event(self, comm_id: str, data: dict) -> dict:
        """Run one widget event and return the new bundle (with `patches`)."""
        entry = self.comms.get(comm_id)
        if entry is None:
            raise WidgetError(f"unknown comm {comm_id!r}")
        method = str(data.get("method", "event"))
        if method != "event":
            raise WidgetError(f"unknown comm method {method!r}")
        widget_id = str(data.get("widget_id", ""))
        event = str(data.get("event", ""))
        value = str(data.get("value", ""))
        if not widget_id:
            raise WidgetError("the event names no widget")
        callback = entry.callbacks.get(widget_id) or entry.default_callback
        if not callback:
            raise WidgetError(f"widget {widget_id!r} has no callback; it is display-only")
        previous = json.dumps(entry.bundle, separators=(",", ":"), ensure_ascii=False)
        expression = (
            f"Widget.handle ({callback}) {wiz_literal(previous)} "
            f"{wiz_literal(widget_id)} {wiz_literal(event)} {wiz_literal(value)}"
        )
        text = self.backend.eval_string(expression)
        bundle = parse_display(decode_eval_text(text))
        if bundle is None:
            detail = (text or "").strip()
            if len(detail) > 400:
                detail = detail[:397] + "..."
            raise WidgetError(
                "the widget callback did not return a display bundle"
                + (f": {detail}" if detail else " (is the callback in scope?)"))
        entry.bundle = {k: v for k, v in bundle.items() if k not in ("patches", "previous")}
        return bundle
