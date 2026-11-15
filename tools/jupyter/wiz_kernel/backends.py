"""Backends: how a cell actually reaches the Wiz toolchain.

Two drivers, chosen at run time:

* :class:`ReplBackend` keeps one ``wiz repl`` process alive.  Each cell is written
  to a temp file and elaborated with the REPL's ``:load``, which is a file, so a
  definition may span lines and the messages carry the cell's own line numbers.
  Definitions, ``syntax``, ``macro``s and ``instance``s stay in the session: this
  is the stateful driver.

* :class:`BatchBackend` has no process to keep state in.  It writes *the whole
  notebook so far* plus the cell to a temp file and runs ``wiz check`` on it,
  reporting only the messages of the cell's line range.  Nothing is faked: the
  state is the accumulated source, so every cell costs a check of the notebook so
  far.

Both parse the toolchain's ``FILE:LINE:COL: severity: text`` messages (see
``Wiz/Core/Msg.lean`` / ``Msg.render``) into the same :class:`CellResult`.
"""

from __future__ import annotations

import os
import queue
import re
import shutil
import subprocess
import tempfile
import threading
import time
import uuid
from dataclasses import dataclass, field

# Wiz reports messages as `1:12: error: …` (REPL lines) or `/tmp/f.wiz:1:12: error: …`
# (`:load`, `wiz check`).  The text after the prefix may continue on later lines.
_MESSAGE_RE = re.compile(r"^(?:(?P<path>.*?):)?(?P<line>\d+):(?P<col>\d+): "
                         r"(?P<sev>info|warning|error): (?P<text>.*)$")

# A line that looks like an expression at the end of a cell: the elaborator's answer to
# `1 + 1` written as a command is `unexpected '1'; expected command`.
_EXPECTED_COMMAND = re.compile(r"expected command\b")


class BackendError(Exception):
    """The backend could not run the cell."""


class BackendUnavailable(BackendError):
    """This driver cannot be used (for example, `wiz` has no `repl` subcommand)."""


@dataclass
class Stream:
    name: str  # "stdout" or "stderr"
    text: str


@dataclass
class ErrorReport:
    ename: str
    evalue: str
    traceback: list[str] = field(default_factory=list)
    line: int | None = None
    column: int | None = None


@dataclass
class CellResult:
    streams: list[Stream] = field(default_factory=list)
    errors: list[ErrorReport] = field(default_factory=list)
    result: str | None = None  # text/plain of the cell's last expression
    backend: str = ""
    # A magic may answer with a full mime bundle (for example `%%scry`'s HTML table);
    # when it does, it is used instead of `{"text/plain": result}`.
    data: dict | None = None
    metadata: dict = field(default_factory=dict)


@dataclass
class WizMessage:
    severity: str  # info | warning | error | stdout | stderr
    text: str
    line: int | None = None
    col: int | None = None


def parse_messages(text: str, *, path: str | None = None,
                   default_severity: str = "stdout") -> list[WizMessage]:
    """Parse the toolchain's message lines, attaching continuation lines to the
    message above them.  Lines that are not messages become ``default_severity``."""
    out: list[WizMessage] = []
    for raw in text.splitlines():
        line = raw
        if path and line.startswith(path + ":"):
            line = line[len(path) + 1:]
        match = _MESSAGE_RE.match(line)
        if match is None:
            if out:
                out[-1].text += "\n" + raw
            else:
                out.append(WizMessage(default_severity, raw))
            continue
        out.append(WizMessage(match.group("sev"), match.group("text"),
                              int(match.group("line")), int(match.group("col"))))
    return out


def _is_expression_error(msg: WizMessage) -> bool:
    return msg.severity == "error" and _EXPECTED_COMMAND.search(msg.text) is not None


def _last_code_line(code: str) -> tuple[int, str] | None:
    """The 1-based line number and text of the cell's last non-blank line."""
    lines = code.splitlines()
    for index in range(len(lines) - 1, -1, -1):
        if lines[index].strip():
            return index + 1, lines[index]
    return None


def _messages_to_result(messages: list[WizMessage], *, backend: str,
                        result: str | None = None) -> CellResult:
    result_value = result
    streams: list[Stream] = []
    errors: list[ErrorReport] = []
    for msg in messages:
        if msg.severity == "error":
            trace = f"{msg.line}:{msg.col}: error: {msg.text}" if msg.line else msg.text
            errors.append(ErrorReport("WizError", msg.text.splitlines()[0] if msg.text else "",
                                      [trace], msg.line, msg.col))
        elif msg.severity == "info":
            streams.append(Stream("stdout", msg.text + "\n"))
        elif msg.severity == "warning":
            streams.append(Stream("stderr", "warning: " + msg.text + "\n"))
        else:
            streams.append(Stream(msg.severity if msg.severity in ("stdout", "stderr") else "stdout",
                                  msg.text + "\n"))
    return CellResult(streams=streams, errors=errors, result=result_value, backend=backend)


class Backend:
    name = "base"
    description = ""

    def start(self) -> None:  # pragma: no cover - interface
        raise NotImplementedError

    def execute(self, code: str) -> CellResult:  # pragma: no cover - interface
        raise NotImplementedError

    def close(self) -> None:  # pragma: no cover - interface
        pass

    def info(self) -> dict:
        return {"name": self.name, "description": self.description}


class ReplBackend(Backend):
    """One long-lived ``wiz repl`` process; cells are ``:load``ed files."""

    name = "repl"
    description = "a persistent `wiz repl` process: definitions persist, cells may span lines"
    timeout = 120.0

    def __init__(self, wiz: str, cwd: str, toolchain_args: list[str] | None = None):
        self.wiz = wiz
        self.cwd = os.path.abspath(cwd)
        self.toolchain_args = list(toolchain_args or [])
        self._tmpdir: str | None = None
        self._proc: subprocess.Popen | None = None
        self._queues: dict[str, queue.Queue] = {}
        self._threads: list[threading.Thread] = []
        self._counter = 0
        self._closed = False
        self._stderr_tail: list[str] = []

    # -- process ---------------------------------------------------------

    def start(self) -> None:
        self._tmpdir = tempfile.mkdtemp(prefix="wiz-kernel-repl-")
        args = [self.wiz, *self.toolchain_args, "-I", self.cwd, "repl"]
        try:
            self._proc = subprocess.Popen(
                args, cwd=self.cwd, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                stderr=subprocess.PIPE, bufsize=0)
        except OSError as exc:
            raise BackendUnavailable(f"cannot run {self.wiz}: {exc}") from exc
        self._queues = {"stdout": queue.Queue(), "stderr": queue.Queue()}
        for name, pipe in (("stdout", self._proc.stdout), ("stderr", self._proc.stderr)):
            thread = threading.Thread(target=self._reader, args=(name, pipe),
                                      name=f"wiz-kernel-{name}", daemon=True)
            thread.start()
            self._threads.append(thread)
        token = self._token("HELLO")
        try:
            self._send(f'#eval "{token}"\n#check {token}_END\n')
            stdout, stderr = self._collect(token, token + "_END", timeout=120.0)
        except BackendError as exc:
            code = self._proc.poll()
            detail = next((line.strip() for line in self._stderr_tail if line.strip()), "")
            if len(detail) > 160:
                detail = detail[:157] + "..."
            self.close()
            if code is not None:
                raise BackendUnavailable(
                    f"`wiz repl` exited with status {code}"
                    + (f": {detail}" if detail else "")) from exc
            raise BackendUnavailable(f"`wiz repl` did not answer: {exc}") from exc
        # the handshake itself must not leak into the user's first cell
        del stdout, stderr

    def _reader(self, name: str, pipe) -> None:
        try:
            for raw in iter(pipe.readline, b""):
                text = raw.decode("utf-8", "replace").rstrip("\n")
                if name == "stderr" and len(self._stderr_tail) < 6:
                    # the first lines say why a start failed (`unknown command: repl`)
                    self._stderr_tail.append(text)
                self._queues[name].put(text)
        except (ValueError, OSError):
            pass
        finally:
            try:
                pipe.close()
            except OSError:
                pass

    def _send(self, text: str) -> None:
        if self._proc is None or self._proc.stdin is None:
            raise BackendError("wiz repl is not running")
        try:
            self._proc.stdin.write(text.encode("utf-8"))
            self._proc.stdin.flush()
        except OSError as exc:
            raise BackendError(f"cannot write to wiz repl: {exc}") from exc

    @staticmethod
    def _token(kind: str) -> str:
        return f"__WIZ_KERNEL_{kind}_{uuid.uuid4().hex}__"

    def _collect(self, stdout_token: str, stderr_token: str,
                 timeout: float | None = None) -> tuple[list[str], list[str]]:
        """Read both pipes until the two sentinels are seen.

        The REPL flushes stdout *then* stderr after each line, so a `:load`'s output
        (which is never flushed by the REPL itself) is on the pipes once a later
        line's sentinel has gone through.  The caller sends two sentinel lines: an
        `#eval` (stdout) and an unknown `#check` (stderr); waiting for the stderr
        one means both flushes have happened.
        """
        timeout = self.timeout if timeout is None else timeout
        deadline = time.monotonic() + timeout
        stdout: list[str] = []
        stderr: list[str] = []
        seen_out = seen_err = False
        while not (seen_out and seen_err):
            if self._proc is not None and self._proc.poll() is not None and \
                    self._queues["stdout"].empty() and self._queues["stderr"].empty():
                raise BackendError(f"wiz repl exited (status {self._proc.returncode})")
            if time.monotonic() > deadline:
                raise BackendError(f"wiz repl timed out after {timeout:.0f}s")
            progressed = False
            for name, lines in (("stdout", stdout), ("stderr", stderr)):
                try:
                    line = self._queues[name].get(timeout=0.05)
                except queue.Empty:
                    continue
                progressed = True
                lines.append(line)
                if name == "stdout" and stdout_token in line:
                    seen_out = True
                if name == "stderr" and stderr_token in line:
                    seen_err = True
            if not progressed and not (seen_out and seen_err):
                time.sleep(0.01)
        # `#eval`'s line (stdout) is flushed before the error sentinel (stderr); once the
        # latter is in hand, everything the cell wrote is already in the queues.
        def drain(name: str, lines: list[str]) -> None:
            while True:
                try:
                    lines.append(self._queues[name].get_nowait())
                except queue.Empty:
                    return
        drain("stdout", stdout)
        drain("stderr", stderr)
        return stdout, stderr

    # -- cells -----------------------------------------------------------

    def _next_path(self, stem: str) -> str:
        self._counter += 1
        assert self._tmpdir is not None
        return os.path.join(self._tmpdir, f"{stem}-{self._counter}.wiz")

    def _run_file(self, text: str, stem: str) -> tuple[list[WizMessage], str]:
        path = self._next_path(stem)
        with open(path, "w", encoding="utf-8") as handle:
            handle.write(text)
            if not text.endswith("\n"):
                handle.write("\n")
        token_out = self._token("DONE")
        token_err = self._token("END")
        # `:load` takes the rest of the line as the path: no quoting, no spaces.  The
        # kernel's temp directories are under $TMPDIR, which has none on Linux.
        self._send(f':load {path}\n#eval "{token_out}"\n#check {token_err}\n')
        stdout, stderr = self._collect(token_out, token_err)
        stdout = [line for line in stdout if token_out not in line]
        stderr = [line for line in stderr if token_err not in line]
        messages = (parse_messages("\n".join(stdout), path=path, default_severity="stdout")
                    + parse_messages("\n".join(stderr), path=path, default_severity="stderr"))
        return messages, path

    def execute(self, code: str) -> CellResult:
        if not code.strip():
            return CellResult(backend=self.name)
        messages, _ = self._run_file(code, "cell")
        last = _last_code_line(code)
        result = None
        if last is not None:
            line_no, text = last
            at_last = [m for m in messages if m.line == line_no and _is_expression_error(m)]
            if at_last:
                value = self._eval_expression(text.strip())
                if value is not None:
                    messages = [m for m in messages
                                if not (m.line == line_no and _is_expression_error(m))]
                    result = value
        return _messages_to_result(messages, backend=self.name, result=result)

    def _eval_expression(self, expression: str) -> str | None:
        """Evaluate `expression` as `#eval expression` in the session; None on error."""
        messages, _ = self._run_file(f"#eval {expression}\n", "eval")
        if any(m.severity == "error" for m in messages):
            return None
        infos = [m.text for m in messages if m.severity == "info"]
        return infos[-1] if infos else None

    def close(self) -> None:
        if self._closed:
            return
        self._closed = True
        proc = self._proc
        if proc is not None:
            try:
                if proc.stdin is not None:
                    proc.stdin.write(b":quit\n")
                    proc.stdin.flush()
                    proc.stdin.close()
            except (OSError, ValueError):
                pass
            try:
                proc.wait(timeout=5)
            except subprocess.TimeoutExpired:
                proc.kill()
                proc.wait(timeout=5)
        if self._tmpdir is not None:
            shutil.rmtree(self._tmpdir, ignore_errors=True)


class BatchBackend(Backend):
    """No process state: every cell reruns the notebook's source with `wiz check`."""

    name = "batch"
    description = ("`wiz check` on a temp file: the whole notebook is rechecked per cell, "
                   "so definitions persist only as source (a `wiz run` prints no messages)")
    timeout = 300.0

    def __init__(self, wiz: str, cwd: str, toolchain_args: list[str] | None = None):
        self.wiz = wiz
        self.cwd = os.path.abspath(cwd)
        self.toolchain_args = list(toolchain_args or [])
        self._cells: list[str] = []
        self._counter = 0
        self._tmpdir: str | None = None

    def start(self) -> None:
        if not os.path.isabs(self.wiz) and shutil.which(self.wiz) is None:
            raise BackendUnavailable(f"no wiz executable {self.wiz!r}")
        self._tmpdir = tempfile.mkdtemp(prefix="wiz-kernel-batch-")

    def _source(self, cells: list[str]) -> tuple[str, int, int]:
        """The notebook as one file; the (start, end) lines of the last cell."""
        prelude = "" if any(re.search(r"^\s*import\s+Prelude\b", c, re.M)
                            for c in cells) else "import Prelude\n"
        parts: list[str] = []
        line = 1
        if prelude:
            parts.append(prelude)
            line += 1
        for cell in cells[:-1]:
            text = cell if cell.endswith("\n") else cell + "\n"
            parts.append(text)
            line += text.count("\n")
        current = cells[-1] if cells[-1].endswith("\n") else cells[-1] + "\n"
        start = line
        end = start + current.count("\n") - 1
        parts.append(current)
        return "".join(parts), start, end

    def _check(self, cells: list[str]) -> tuple[list[WizMessage], int, int]:
        source, start, end = self._source(cells)
        self._counter += 1
        assert self._tmpdir is not None
        path = os.path.join(self._tmpdir, f"notebook-{self._counter}.wiz")
        with open(path, "w", encoding="utf-8") as handle:
            handle.write(source)
        try:
            done = subprocess.run(
                [self.wiz, *self.toolchain_args, "-I", self.cwd, "check", path],
                cwd=self.cwd, capture_output=True, text=True, timeout=self.timeout)
        except subprocess.TimeoutExpired as exc:
            raise BackendError(f"`wiz check` timed out after {self.timeout:.0f}s") from exc
        except OSError as exc:
            raise BackendError(f"cannot run {self.wiz}: {exc}") from exc
        messages = (parse_messages(done.stdout, path=path, default_severity="stdout")
                    + parse_messages(done.stderr, path=path, default_severity="stderr"))
        return messages, start, end

    def execute(self, code: str) -> CellResult:
        if not code.strip():
            return CellResult(backend=self.name)
        cells = self._cells + [code]
        messages, start, end = self._check(cells)
        current = [m for m in messages if m.line is None or start <= m.line <= end]
        result = None
        last = _last_code_line(code)
        if last is not None:
            line_no, text = last
            at_last = [m for m in current if m.line == start + line_no - 1
                       and _is_expression_error(m)]
            if at_last:
                rewritten = code.splitlines()
                rewritten[line_no - 1] = "#eval " + text.strip()
                retry_messages, retry_start, retry_end = self._check(
                    self._cells + ["\n".join(rewritten) + "\n"])
                retry = [m for m in retry_messages
                         if m.line is None or retry_start <= m.line <= retry_end]
                if not any(m.severity == "error" for m in retry):
                    infos = [m.text for m in retry if m.severity == "info"]
                    if infos:
                        current = [m for m in current
                                   if not (m.line == start + line_no - 1
                                           and _is_expression_error(m))]
                        result = infos[-1]
        self._cells.append(code)
        return _messages_to_result(current, backend=self.name, result=result)

    def close(self) -> None:
        if self._tmpdir is not None:
            shutil.rmtree(self._tmpdir, ignore_errors=True)
            self._tmpdir = None


def find_wiz(explicit: str | None = None) -> str | None:
    """The toolchain: `--wiz`, `$WIZ`, `wiz` on PATH, or a checkout's build."""
    candidates: list[str] = []
    if explicit:
        candidates.append(explicit)
    env = os.environ.get("WIZ")
    if env:
        candidates.append(env)
    on_path = shutil.which("wiz")
    if on_path:
        candidates.append(on_path)
    # tools/jupyter/wiz_kernel/backends.py -> the checkout root
    here = os.path.dirname(os.path.dirname(os.path.dirname(
        os.path.dirname(os.path.abspath(__file__)))))
    candidates.append(os.path.join(here, ".lake", "build", "bin", "wiz"))
    for candidate in candidates:
        candidate = os.path.expanduser(candidate)
        if os.path.isfile(candidate) and os.access(candidate, os.X_OK):
            return candidate
    return None


def make_backend(kind: str, wiz: str | None, cwd: str,
                 toolchain_args: list[str] | None = None) -> tuple[Backend, str | None]:
    """Pick a driver.  Returns the backend and, for `auto`, why repl was not used."""
    kind = (kind or "auto").lower()
    if kind not in ("auto", "repl", "batch"):
        raise BackendError(f"unknown backend {kind!r} (auto, repl or batch)")
    executable = find_wiz(wiz)
    if executable is None:
        raise BackendUnavailable(
            "no wiz executable: pass --wiz PATH, set $WIZ, or put wiz on PATH")
    reason = None
    if kind in ("auto", "repl"):
        backend = ReplBackend(executable, cwd, toolchain_args)
        try:
            backend.start()
            return backend, None
        except BackendUnavailable as exc:
            if kind == "repl":
                raise
            reason = str(exc)
    backend = BatchBackend(executable, cwd, toolchain_args)
    backend.start()
    return backend, reason
