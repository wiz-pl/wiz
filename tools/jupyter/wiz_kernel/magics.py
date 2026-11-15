"""Cell magics for the Wiz kernel.

* ``%%scry`` — treat the cell as C source and run ``scry taint --json`` on it,
  rendering the findings.  This is a **per-cell** analysis: the C is written to a
  temp file, analysed and forgotten.  There is no project, no include path, no
  notion of the previous cell.  ``%%scry --progress`` forwards scry's stderr
  ``--progress`` lines while the cell runs (see :mod:`wiz_kernel.progress`).
* ``%%sh`` — run the cell as a shell script, streaming stdout/stderr and
  returning the exit status.  It is the user's machine: no sandbox, no claim of
  one; the working directory is the kernel's.
* ``%%time`` — run the cell through the normal backend and append one timing
  line (wall clock, and peak RSS when it can be sampled) after the cell's
  output, so it sits above the cell's result.
* ``%%wiz`` — force the cell through the Wiz backend (the default), useful to
  write a cell that starts with a line that looks like a magic.  Otherwise a
  plain cell and ``%%wiz`` take exactly the same path.
* ``%backend`` — say which driver is in use (``repl`` or ``batch``) and why.
* ``%progress`` — say which progress transport this kernel uses and why.
* ``%wiz`` — a line form: ``%wiz <code>`` is the same as the code without it.
"""

from __future__ import annotations

import html
import json
import os
import queue
import re
import shlex
import shutil
import subprocess
import tempfile
import threading
import time

from .backends import CellResult, Backend, ErrorReport, Stream
from .progress import ProgressChannel, comm_capability, parse_progress_line
from .timing import measure

_MAGIC_RE = re.compile(r"^%%(?P<name>[A-Za-z0-9_]+)(?:[ \t]+(?P<args>.*))?$")
_LINE_MAGIC_RE = re.compile(r"^%(?P<name>[A-Za-z0-9_]+)(?:[ \t]+(?P<rest>.*))?$")


class MagicError(Exception):
    def __init__(self, ename: str, message: str):
        super().__init__(message)
        self.ename = ename


def backend_summary(backend: Backend, fallback_reason: str | None) -> str:
    lines = [f"backend: {backend.name}", backend.description]
    if fallback_reason:
        lines.append(f"(chosen because `wiz repl` was not available: {fallback_reason})")
    else:
        lines.append("(`wiz repl` is available: this is the stateful driver)")
    return "\n".join(lines)


def handle_magic(code: str, backend: Backend, *,
                 fallback_reason: str | None = None, cwd: str = ".",
                 wiz: str | None = None,
                 progress: ProgressChannel | None = None,
                 emit=None) -> CellResult | None:
    """Run a magic cell.  Returns None when the cell is ordinary Wiz code.

    ``progress`` is the kernel's progress channel (a magic may forward lines over
    it); ``emit(name, text)`` publishes a live stream line while the cell runs.
    Both are optional so the magics can be exercised without a kernel.
    """
    lines = code.splitlines()
    if not lines:
        return None
    first = lines[0]
    match = _MAGIC_RE.match(first)
    if match:
        name = match.group("name")
        args = (match.group("args") or "").strip()
        body = "\n".join(lines[1:])
        if name == "scry":
            return run_scry_magic(body, args, cwd=cwd, wiz=wiz,
                                  progress=progress, emit=emit)
        if name == "sh":
            return run_sh_magic(body, args, cwd=cwd, emit=emit)
        if name == "time":
            return run_time_magic(body, backend)
        if name == "wiz":
            # Exactly the plain-cell path: same driver, same temp-file semantics.
            # The only difference is that this line is not offered to magic
            # dispatch, which is what makes a cell starting with `%%` writeable.
            return backend.execute(body)
        return _error("UnknownMagic",
                      f"unknown cell magic %%{name} (use %%scry, %%sh, %%time or %%wiz)")
    match = _LINE_MAGIC_RE.match(first)
    if match and all(not line.strip() for line in lines[1:]):
        name, rest = match.group("name"), (match.group("rest") or "").strip()
        if name in ("backend", "wiz_backend"):
            return CellResult(result=backend_summary(backend, fallback_reason),
                              backend=backend.name)
        if name == "progress":
            if rest:
                return _error("UsageError", "%progress takes no arguments")
            return CellResult(result=_progress_report(progress), backend="progress")
        if name == "wiz":
            return backend.execute(rest)
        if name == "scry":
            return _error("UsageError", "%scry is not a line magic: use a %%scry cell")
        return _error("UnknownMagic",
                      f"unknown line magic %{name} (use %backend or %progress)")
    return None


def _progress_report(progress: ProgressChannel | None) -> str:
    if progress is not None:
        return progress.describe()
    supported, reason = comm_capability()
    transport = "comm" if supported else "iopub stream"
    return (f"progress: {transport} ({reason})\n"
            "%%scry --progress forwards scry's stderr lines this way while the "
            "cell runs")


def _error(ename: str, message: str) -> CellResult:
    return CellResult(streams=[], errors=[ErrorReport(ename, message, [message])])


# -- process streaming --------------------------------------------------

class ProcessUnavailable(Exception):
    """The process could not be started (no such file, not executable, …)."""


def _stream_process(argv: list[str], *, cwd: str, timeout: float,
                    emit=None) -> tuple[int, dict[str, str]]:
    """Run ``argv``, forwarding each line as it arrives.

    Reader threads only put lines on a queue; the caller's thread forwards them,
    so a ZeroMQ socket is never used from two threads.  Returns the exit status
    and the captured text per stream.
    """
    try:
        proc = subprocess.Popen(argv, cwd=cwd, stdin=subprocess.DEVNULL,
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                text=True, bufsize=1)
    except OSError as exc:
        raise ProcessUnavailable(f"cannot run {argv[0]}: {exc}") from exc
    lines: queue.Queue = queue.Queue()
    captured: dict[str, list[str]] = {"stdout": [], "stderr": []}

    def reader(name: str, pipe) -> None:
        try:
            for line in iter(pipe.readline, ""):
                lines.put((name, line))
        except (ValueError, OSError):
            pass
        finally:
            try:
                pipe.close()
            except OSError:
                pass
            lines.put((name, None))

    threads = [threading.Thread(target=reader, args=(name, pipe),
                                name=f"wiz-magic-{name}", daemon=True)
               for name, pipe in (("stdout", proc.stdout), ("stderr", proc.stderr))]
    for thread in threads:
        thread.start()
    deadline = None if timeout <= 0 else time.monotonic() + timeout
    pending = 2
    try:
        while pending:
            if deadline is not None and time.monotonic() > deadline:
                proc.kill()
                proc.wait(timeout=5)
                raise TimeoutError(f"timed out after {timeout:.0f}s")
            try:
                name, line = lines.get(timeout=0.1)
            except queue.Empty:
                continue
            if line is None:
                pending -= 1
                continue
            captured[name].append(line)
            if emit is not None:
                emit(name, line)
        status = proc.wait(timeout=5)
    finally:
        if proc.poll() is None:
            proc.kill()
            proc.wait(timeout=5)
        for thread in threads:
            thread.join(timeout=2)
    return status, {name: "".join(parts) for name, parts in captured.items()}


# -- sh -----------------------------------------------------------------

def run_sh_magic(source: str, args: str, *, cwd: str, emit=None) -> CellResult:
    """Run the cell as a shell script; stdout/stderr stream, status is returned.

    There is no sandbox: the script runs as the user, on the user's machine, in
    the kernel's working directory.  ``%%sh bash -e`` picks another shell (the
    arguments are the interpreter command line).
    """
    try:
        shell = shlex.split(args) or ["/bin/sh"]
    except ValueError as exc:
        return _error("UsageError", f"%%sh: {exc}")
    if not os.path.isabs(shell[0]) and shutil.which(shell[0]) is None:
        return _error("ShellUnavailable", f"no shell executable {shell[0]!r}")
    timeout = float(os.environ.get("WIZ_SHELL_TIMEOUT", "300"))
    try:
        status, captured = _stream_process([*shell, "-c", source], cwd=cwd,
                                           timeout=timeout, emit=emit)
    except TimeoutError as exc:
        return _error("ShellTimeout", str(exc))
    except ProcessUnavailable as exc:
        return _error("ShellUnavailable", str(exc))
    except OSError as exc:
        return _error("ShellError", str(exc))
    streams = ([] if emit is not None else
               [Stream(name, text) for name, text in captured.items() if text])
    text = f"exit status {status}"
    if status != 0:
        return CellResult(streams=streams, errors=[ErrorReport(
            "ShellError", text, [text])], backend="sh")
    return CellResult(streams=streams, result=text, backend="sh")


# -- time ---------------------------------------------------------------

def run_time_magic(source: str, backend: Backend) -> CellResult:
    """Run the cell exactly as a plain cell and append one timing stream line."""
    result, line = measure(lambda: backend.execute(source))
    result.streams.append(Stream("stdout", line + "\n"))
    return result


# -- scry ---------------------------------------------------------------

def _search_dirs(cwd: str, wiz: str | None) -> list[str]:
    roots: list[str] = []
    here = os.path.abspath(cwd)
    while True:
        roots.append(here)
        parent = os.path.dirname(here)
        if parent == here:
            break
        here = parent
    if wiz:
        here = os.path.dirname(os.path.abspath(wiz))
        for _ in range(5):
            roots.append(here)
            parent = os.path.dirname(here)
            if parent == here:
                break
            here = parent
    seen: set[str] = set()
    return [r for r in roots if not (r in seen or seen.add(r))]


def scry_command(cwd: str, wiz: str | None = None) -> list[str] | None:
    """``$WIZ_SCRY``, ``scry`` on PATH, or a checkout's ``scry/.grail/bin/scry``."""
    configured = os.environ.get("WIZ_SCRY")
    if configured:
        return shlex.split(configured)
    found = shutil.which("scry")
    if found:
        return [found]
    for root in _search_dirs(cwd, wiz):
        for rel in (("scry", ".grail", "bin", "scry"), (".grail", "bin", "scry")):
            candidate = os.path.join(root, *rel)
            if os.path.isfile(candidate) and os.access(candidate, os.X_OK):
                return [candidate]
    return None


def default_rules(cwd: str, command: str | None = None) -> str | None:
    for root in _search_dirs(cwd, command):
        candidate = os.path.join(root, "lib", "Scry", "rules", "default.scry")
        if os.path.isfile(candidate):
            return candidate
    return None


def _location(finding: dict) -> tuple[str, int | None, int | None]:
    loc = finding.get("location") or {}
    uri = loc.get("uri") or ""
    return os.path.basename(uri), loc.get("startLine"), loc.get("startColumn")


def _render_text(report: dict) -> str:
    counts = report.get("counts") or {}
    lines = [
        f"scry taint: {counts.get('findings', 0)} finding(s), "
        f"{counts.get('checked', 0)} checked, {counts.get('unchecked', 0)} unchecked, "
        f"{counts.get('boundary', 0)} boundary warning(s)"
    ]
    for finding in report.get("findings") or []:
        name, line, column = _location(finding)
        where = f" at {name}:{line}:{column}" if line else ""
        derivation = finding.get("derivation") or "unchecked"
        lines.append(f"- [{finding.get('severity', 'warning')}] {finding.get('rule', '?')}"
                     f"{where} ({derivation}): {finding.get('message', '')}")
    for boundary in report.get("boundary") or []:
        name, line, column = _location(boundary)
        where = f" at {name}:{line}:{column}" if line else ""
        lines.append(f"- [boundary]{where} in {boundary.get('function', '?')}: "
                     f"{boundary.get('message', '')}")
    return "\n".join(lines)


def _render_html(report: dict) -> str:
    counts = report.get("counts") or {}

    def rows(key: str, boundary: bool) -> str:
        out = []
        for finding in report.get(key) or []:
            name, line, column = _location(finding)
            where = f"{html.escape(name)}:{line}:{column}" if line else ""
            derivation = html.escape(finding.get("derivation") or "unchecked")
            severity = html.escape(finding.get("severity") or "warning")
            rule = html.escape(finding.get("rule") or "?")
            message = html.escape(finding.get("message") or "")
            if boundary:
                out.append(f"<tr><td>warning</td><td>{rule}</td><td>{where}</td>"
                           f"<td>{message}</td><td>unchecked</td></tr>")
            else:
                out.append(f"<tr><td>{severity}</td><td>{rule}</td><td>{where}</td>"
                           f"<td>{message}</td><td>{derivation}</td></tr>")
        return "".join(out)

    body = rows("findings", False) + rows("boundary", True)
    if not body:
        body = '<tr><td colspan="5">no findings</td></tr>'
    return (
        '<div class="wiz-scry">'
        f"<p><b>scry taint</b>: {counts.get('findings', 0)} finding(s), "
        f"{counts.get('checked', 0)} checked, {counts.get('unchecked', 0)} unchecked, "
        f"{counts.get('boundary', 0)} boundary warning(s)</p>"
        '<table><thead><tr><th>severity</th><th>rule</th><th>location</th>'
        "<th>message</th><th>derivation</th></tr></thead>"
        f"<tbody>{body}</tbody></table></div>"
    )


def run_scry_magic(source: str, args: str, *, cwd: str, wiz: str | None = None,
                   timeout: float | None = None,
                   progress: ProgressChannel | None = None,
                   emit=None) -> CellResult:
    command = scry_command(cwd, wiz)
    if command is None:
        message = (
            "no scry executable: install one (build the scry package, then put its "
            "binary on PATH) or set WIZ_SCRY, for example "
            "WIZ_SCRY='grail run scry --' from a checkout's scry/ directory")
        return _error("ScryUnavailable", message)
    try:
        extra = shlex.split(args)
    except ValueError as exc:
        return _error("UsageError", f"%%scry: {exc}")
    extra = [a for a in extra if a != "--json"]
    want_progress = "--progress" in extra
    if "--rules" not in extra:
        rules = default_rules(cwd, command[0])
        if rules:
            extra += ["--rules", rules]
    timeout = float(os.environ.get("WIZ_SCRY_TIMEOUT", timeout or 120.0))
    handle = tempfile.NamedTemporaryFile("w", suffix=".c", prefix="wiz-scry-",
                                         delete=False, dir=None)
    try:
        handle.write(source)
        if not source.endswith("\n"):
            handle.write("\n")
        handle.close()
        invocation = [*command, "taint", handle.name, "--json", *extra]
        if want_progress:
            if progress is not None:
                progress.begin()
            collected: list[str] = []

            def on_line(name: str, line: str) -> None:
                if name != "stderr":
                    return
                if progress is not None:
                    progress.forward(line)
                elif parse_progress_line(line) is not None:
                    collected.append(line)

            try:
                status, captured = _stream_process(invocation, cwd=cwd,
                                                   timeout=timeout, emit=on_line)
            except TimeoutError:
                return _error("ScryTimeout",
                              f"scry taint timed out after {timeout:.0f}s")
            except ProcessUnavailable as exc:
                return _error("ScryUnavailable", str(exc))
            finally:
                if progress is not None:
                    progress.finish()
            stdout = captured.get("stdout", "")
            stderr = captured.get("stderr", "")
            extra_streams = ([Stream("stdout", line) for line in collected]
                             if progress is None else [])
        else:
            status = None
            try:
                done = subprocess.run(invocation, cwd=cwd, capture_output=True,
                                      text=True, timeout=timeout)
            except subprocess.TimeoutExpired:
                return _error("ScryTimeout", f"scry taint timed out after {timeout:.0f}s")
            except OSError as exc:
                return _error("ScryUnavailable", f"cannot run {command[0]}: {exc}")
            status, stdout, stderr = done.returncode, done.stdout, done.stderr
            extra_streams = []
        report = None
        for line in reversed((stdout or "").splitlines()):
            line = line.strip()
            if line.startswith("{"):
                try:
                    report = json.loads(line)
                    break
                except json.JSONDecodeError:
                    continue
        if report is None:
            detail = (stderr or stdout or "").strip() or "(no output)"
            return CellResult(streams=extra_streams, errors=[ErrorReport(
                "ScryError", f"scry taint failed (status {status}): {detail}",
                [f"scry taint failed (status {status}): {detail}"])])
        text = _render_text(report)
        data = {"text/plain": text, "text/html": _render_html(report),
                "application/json": report}
        return CellResult(streams=extra_streams, result=text, data=data,
                          metadata={"scry": {"file": report.get("file", handle.name)}})
    finally:
        try:
            os.unlink(handle.name)
        except OSError:
            pass
