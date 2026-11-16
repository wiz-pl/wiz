"""Wall clock and peak RSS for ``%%time``.

``wall`` is :func:`time.monotonic` around the cell, which is the only number the
kernel can measure honestly.  Peak RSS is *sampled* from ``/proc`` for the
kernel's descendants (the ``wiz repl`` process, or the ``wiz check`` the batch
driver starts) every 50 ms, so it is a lower bound on the true peak; the line
says ``sampled``.  Where ``/proc`` is missing, ``resource.getrusage`` of the
kernel's waited children is the fallback, and the line says ``children peak``
instead.  Sampling costs one small ``/proc`` read per interval and runs on a
daemon thread, so it is cheap enough to be the default for ``%%time``.
"""

from __future__ import annotations

import os
import resource
import threading
import time


def _children(pid: int) -> list[int]:
    try:
        with open(f"/proc/{pid}/task/{pid}/children", encoding="ascii") as handle:
            return [int(part) for part in handle.read().split()]
    except (OSError, ValueError):
        return []


def _rss_kib(pid: int) -> int:
    try:
        with open(f"/proc/{pid}/status", encoding="ascii") as handle:
            for line in handle:
                if line.startswith("VmRSS:"):
                    return int(line.split()[1])
    except (OSError, ValueError):
        pass
    return 0


def _tree_rss_kib(root_pid: int) -> int:
    """The RSS of the root's descendants (not the kernel itself)."""
    total = 0
    pending = _children(root_pid)
    seen: set[int] = set()
    while pending:
        pid = pending.pop()
        if pid in seen:
            continue
        seen.add(pid)
        total += _rss_kib(pid)
        pending.extend(_children(pid))
    return total


class RssSampler:
    """Sample the RSS of a process tree while a cell runs."""

    def __init__(self, root_pid: int | None = None, interval: float = 0.05):
        self.root_pid = root_pid or os.getpid()
        self.interval = interval
        self.peak_kib: int | None = None
        self.note = "sampled descendants (/proc)"
        self._stop = threading.Event()
        self._thread: threading.Thread | None = None
        self._available = os.path.isdir("/proc")

    def start(self) -> "RssSampler":
        if self._available:
            self._thread = threading.Thread(target=self._run, name="wiz-rss-sampler",
                                            daemon=True)
            self._thread.start()
        return self

    def _run(self) -> None:
        while not self._stop.is_set():
            try:
                current = _tree_rss_kib(self.root_pid)
            except Exception:
                current = 0
            if current and (self.peak_kib is None or current > self.peak_kib):
                self.peak_kib = current
            self._stop.wait(self.interval)

    def stop(self) -> tuple[int | None, str]:
        if self._thread is not None:
            self._stop.set()
            self._thread.join(timeout=2)
        if self.peak_kib is None:
            try:
                peak = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
            except (OSError, ValueError):
                peak = 0
            if peak:
                self.peak_kib = peak
                self.note = "children peak (resource.getrusage)"
            else:
                self.note = "unavailable"
        return self.peak_kib, self.note


def timing_line(wall: float, peak_kib: int | None, note: str) -> str:
    """One line, as the cell's last stream: wall always, RSS when measured."""
    line = f"[time] wall {wall:.3f} s"
    if peak_kib:
        line += f", peak RSS {peak_kib / 1024.0:.1f} MiB ({note})"
    elif note == "unavailable":
        line += ", peak RSS unavailable"
    else:
        line += f", peak RSS unavailable ({note})"
    return line


def measure(callable_):
    """Run ``callable_`` and return (value, timing line)."""
    sampler = RssSampler().start()
    started = time.monotonic()
    try:
        value = callable_()
    finally:
        wall = time.monotonic() - started
        peak_kib, note = sampler.stop()
    return value, timing_line(wall, peak_kib, note)
