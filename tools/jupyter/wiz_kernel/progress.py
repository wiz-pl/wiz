"""Progress for long cells: a comm channel, or `stdout` streams.

A two-minute ``scry taint --progress`` run must not look like a frozen notebook,
so a cell magic forwards each progress line *as it arrives*, while the cell is
still running.  There are two transports:

* **comm** — a kernel-initiated ``comm_open`` with target ``wiz.progress`` and
  one ``comm_msg`` per line.  Kernel-initiated comms need no client support to
  send, but a front end only renders them when it knows the target; the widget
  comms in ``wiz-widgets`` are what make this the richer channel.  A client may
  also open the comm itself (``comm_open`` with the same target): the kernel then
  reuses that comm and does not close it.
* **iopub stream** — each line is published as an iopub ``stream`` message on
  ``stdout``, in order, as it arrives.  This is the fallback when comm support is
  not present; it needs nothing from the client.

The channel reports which one it uses (``%progress`` and ``describe()``), so a
reader never has to guess.  Lines are parsed for a fraction when one is there
(``3/12``, ``25%``) and forwarded in either case.
"""

from __future__ import annotations

import importlib
import re
import uuid
from dataclasses import dataclass

COMM_TARGET = "wiz.progress"

_PERCENT_RE = re.compile(r"(?<![\d.])(\d{1,3})\s*%")
_FRACTION_RE = re.compile(r"(?<![\d.])(\d+)\s*/\s*(\d+)(?![\d.])")
_CENTRE_RE = re.compile(r"^\s*\[\s*(\d{1,3})\s*%\s*\]")


@dataclass
class ProgressEvent:
    text: str
    fraction: float | None = None


def parse_progress_line(line: str) -> ProgressEvent | None:
    """A progress line, or ``None`` for a blank one.

    The contract is deliberately loose because ``scry --progress`` is new: any
    non-blank stderr line is forwarded; a ``n/m`` or ``n%`` in it also becomes a
    fraction, which the comm path sends as a number for a progress bar.
    """
    text = line.rstrip("\r\n")
    if not text.strip():
        return None
    fraction = None
    match = _FRACTION_RE.search(text)
    if match:
        done, total = int(match.group(1)), int(match.group(2))
        if total > 0:
            fraction = max(0.0, min(1.0, done / total))
    if fraction is None:
        match = _CENTRE_RE.match(text) or _PERCENT_RE.search(text)
        if match:
            fraction = max(0.0, min(1.0, int(match.group(1)) / 100.0))
    return ProgressEvent(text, fraction)


def comm_capability() -> tuple[bool, str]:
    """Whether the kernel should open a progress comm itself, and why.

    ``wiz-widgets`` adds ``wiz_kernel.widgets`` and the comm handlers around it,
    but its front end (``static/widget.js``/``loader.js``) registers only the
    ``wiz.widgets`` target: nothing renders a ``wiz.progress`` comm, and a front
    end that does not know a target drops its messages.  So the default stays on
    iopub streams; a client that does render progress opens the comm itself
    (``ProgressChannel.attach_comm``) and is then used.
    """
    try:
        importlib.import_module(".widgets", __package__)
    except Exception:
        return False, "no widget comm support (wiz-widgets is not merged)"
    return False, "the widget front end does not render wiz.progress comms"


class ProgressChannel:
    """Forward progress lines for one cell over comm or iopub streams."""

    def __init__(self, *, publish, stream, comm_supported: bool | None = None,
                 reason: str | None = None):
        self._publish = publish
        self._stream = stream
        if comm_supported is None:
            self._supported, self._reason = comm_capability()
        else:
            self._supported = comm_supported
            self._reason = reason or ("comm support (test)")
        self.parent: dict | None = None
        self.comm_id: str | None = None
        self._owns_comm = False
        self._open = False
        self.lines: list[str] = []

    # -- configuration ---------------------------------------------------

    def begin(self, parent: dict | None = None) -> None:
        """Start a cell's progress.  Idempotent within one cell."""
        if parent is not None:
            self.parent = parent
        self.lines = []
        if self._open:
            return
        self._open = True
        if self.transport == "comm" and self.comm_id is None:
            self.comm_id = "wiz-progress-" + uuid.uuid4().hex
            self._owns_comm = True
            self._publish("comm_open", {
                "comm_id": self.comm_id,
                "target_name": COMM_TARGET,
                "data": {"state": "running"},
            }, parent=self.parent)

    def finish(self) -> None:
        """Close a comm this kernel opened; leave a client's comm alone."""
        if self._open and self._owns_comm and self.comm_id is not None:
            self._publish("comm_close", {"comm_id": self.comm_id, "data": {}},
                          parent=self.parent)
            self.comm_id = None
            self._owns_comm = False
        self._open = False
        self.parent = None

    def attach_comm(self, comm_id: str) -> None:
        """A client opened the progress comm: reuse it for this kernel."""
        if not comm_id:
            return
        self.comm_id = comm_id
        self._owns_comm = False
        self._open = True

    def detach_comm(self, comm_id: str | None) -> None:
        if comm_id and comm_id == self.comm_id and not self._owns_comm:
            self.comm_id = None
            self._open = False

    # -- state -----------------------------------------------------------

    @property
    def transport(self) -> str:
        if self.comm_id is not None:
            return "comm"
        return "comm" if self._supported else "iopub"

    def describe(self) -> str:
        if self.transport == "comm":
            if self.comm_id is None:
                why = f"available: {self._reason}; a %%scry --progress cell opens it"
            elif self._owns_comm:
                why = f"opened by this kernel; {self._reason}"
            else:
                why = "opened by the client"
            detail = f"progress: comm ({COMM_TARGET}, {why})"
        else:
            detail = (f"progress: iopub stream ({self._reason}); "
                      "each line is a `stdout` stream message, in order")
        return detail + "\n%%scry --progress forwards scry's stderr lines this way " \
                        "while the cell runs"

    # -- forwarding ------------------------------------------------------

    def forward(self, line: str) -> None:
        event = parse_progress_line(line)
        if event is None:
            return
        self.lines.append(event.text)
        if self.transport == "comm":
            self._publish("comm_msg", {
                "comm_id": self.comm_id,
                "data": {
                    "method": "update",
                    "state": "running",
                    "text": event.text,
                    "fraction": event.fraction,
                    "count": len(self.lines),
                },
            }, parent=self.parent)
        else:
            self._stream("stdout", event.text + "\n", parent=self.parent)
