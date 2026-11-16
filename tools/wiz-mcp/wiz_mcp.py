#!/usr/bin/env python3
"""wiz-mcp: a small, stdlib-only MCP server for the Wiz toolchain.

Transport: MCP stdio, one JSON-RPC message per line. The client (OpenCode V2,
Claude Code, Zed, ...) spawns one process per workspace/location; this process
runs the tools a Wiz agent needs:

  version                  `wiz --version`
  check      {path}        `wiz check` (the workhorse)
  parse      {path}        `wiz parse`
  fmt        {path,...}    `wiz fmt [--check] [--width N]`
  build      {path,out}    `wiz build PATH -o OUT [--lib]`
  diagnostics {path,text?} diagnostics from `wiz lsp`
  hover      {path,text?,line,character}  the type at a position
  goals      {path,text?,line,character}  the tactic state (`wiz/interactiveGoals`)

The text tools are one `wiz` process per call. The three language-server tools
share **one** lazily started `wiz lsp` daemon on its own stdin/stdout (no socket),
belonging to this process and therefore to this workspace. It is killed after
`--idle` seconds (default 600) and on exit. A daemon is never shared between
worktrees: its module roots and `lib/` are fixed at startup, and documents are
keyed by URI only, so sharing would silently check the wrong library and let
documents collide.

Paths are relative to the workspace (the directory the client spawns us in),
not to this script. `--wiz` defaults to `./.lake/build/bin/wiz`, so a worktree
gets its own build unless another binary is named explicitly.

Safety: a path must resolve (symlinks followed) inside the workspace, the
toolchain's library or an `--allow-root` directory; `build` is listed only with
`--allow-build` and writes only inside the workspace; children get an
allowlisted environment with secret-looking names removed.

Run with --help for the options. No third-party packages are used; the
language server is spoken to with `Content-Length` framing over pipes.
"""

from __future__ import annotations

import argparse
import collections
import json
import os
import re
import select
import shutil
import signal
import subprocess
import sys
import threading
import time
import traceback
import urllib.parse
from dataclasses import dataclass
from typing import Any, Iterable, Optional

# ---------------------------------------------------------------------------
# Protocol and limits

PROTOCOL_VERSION = "2025-06-18"
SUPPORTED_PROTOCOLS = ("2024-11-05", "2025-03-26", "2025-06-18")
SERVER_NAME = "wiz"
SERVER_VERSION = "1.0.0"

DEFAULT_IDLE = 600.0
DEFAULT_TIMEOUT = 300.0

#: One text field (stdout/stderr) is clipped to this many characters.
MAX_TEXT = 64 * 1024
#: A JSON `result` is clipped to this many characters of serialized JSON.
MAX_RESULT = 64 * 1024
#: Language-server messages above this are rejected.
MAX_LSP_MESSAGE = 64 * 1024 * 1024

TRUNCATION_MARK = "\n… [truncated: {n} characters omitted]"

INSTRUCTIONS = (
    "Wiz toolchain tools for this workspace. Paths are relative to the workspace and must "
    "stay inside it (or the toolchain library); others are refused with path_denied. "
    "Call check after editing a .wiz file: result.diagnostics lists its messages with positions "
    "(source=lsp adds range ends and error codes, and checks unsaved text); "
    "use fmt --check before committing, and diagnostics/hover/goals when you need the "
    "language server's view. diagnostics, hover and goals share one lazy `wiz lsp` "
    "daemon for this worktree and can be slow on a cold cache."
)


def log(*args: Any) -> None:
    """Diagnostics go to stderr; stdout is the MCP transport."""
    print(*args, file=sys.stderr, flush=True)


class ProtocolError(Exception):
    """A JSON-RPC level error (bad tool name, unreadable message)."""

    def __init__(self, code: int, message: str) -> None:
        super().__init__(message)
        self.code = code
        self.message = message


class ToolError(Exception):
    """A tool failed in a way the caller should see as an error envelope."""

    def __init__(self, kind: str, message: str, stdout: str = "", stderr: str = "") -> None:
        super().__init__(message)
        self.kind = kind
        self.message = message
        self.stdout = stdout
        self.stderr = stderr


# ---------------------------------------------------------------------------
# Configuration and paths


@dataclass(frozen=True)
class Config:
    workspace: str
    wiz: str
    cache: Optional[str] = None
    idle: float = DEFAULT_IDLE
    timeout: float = DEFAULT_TIMEOUT
    #: `build` writes a file and runs the host C toolchain: off unless asked for.
    allow_build: bool = False
    #: More directories tools may read (besides the workspace and the toolchain).
    extra_roots: tuple[str, ...] = ()
    #: More environment variables to pass to children (secret-looking names never pass).
    pass_env: tuple[str, ...] = ()


def resolve_path(workspace: str, path: str) -> str:
    """Resolve a tool path against the workspace (not this process's cwd).

    This only normalizes; `confine` decides whether the result may be used.
    """
    if not isinstance(path, str) or not path.strip():
        raise ToolError("invalid_args", "`path` must be a non-empty string")
    path = os.path.expanduser(path)
    if not os.path.isabs(path):
        path = os.path.join(workspace, path)
    return os.path.normpath(os.path.abspath(path))


def _is_under(path: str, root: str) -> bool:
    try:
        return os.path.commonpath([path, root]) == root
    except ValueError:
        return False


def toolchain_roots(wiz_path: Optional[str]) -> list[str]:
    """The library directories of the toolchain `wiz_path` belongs to.

    A release or Nix toolchain keeps its library in `PREFIX/share/wiz`; a
    checkout build (`CHECKOUT/.lake/build/bin/wiz`) uses `CHECKOUT/lib`. Only
    those directories are allowed, never the whole prefix (which could be /usr).
    """
    if not wiz_path:
        return []
    prefix = os.path.dirname(os.path.dirname(os.path.realpath(wiz_path)))
    roots = [os.path.join(prefix, "share", "wiz")]
    if os.path.basename(prefix) == "build" and os.path.basename(os.path.dirname(prefix)) == ".lake":
        roots.append(os.path.join(os.path.dirname(os.path.dirname(prefix)), "lib"))
    return [os.path.realpath(root) for root in roots if os.path.isdir(root)]


def confine(path: str, roots: Iterable[str], what: str = "path") -> str:
    """`path` itself if its real path (all symlinks followed) is under one of `roots`.

    The check uses the real path, so an absolute path, `..` and a symlink that
    leads out of the workspace are all refused. The normalized path (symlinks
    kept) is what the tools see, so messages keep the caller's spelling.
    """
    real = os.path.realpath(path)
    roots = list(roots)
    if any(_is_under(real, root) for root in roots):
        return path
    shown = path if real == path else f"{path} (really {real})"
    raise ToolError(
        "path_denied",
        f"{what} {shown} is outside the workspace and the toolchain library; "
        "only those may be used (start the server with --allow-root DIR to add one)",
    )


#: Variables passed to `wiz` and its children: the toolchain, the C compiler
#: (a Nix dev shell's `cc` wrapper reads `NIX_*`), locale and temp dirs.
ENV_ALLOW = frozenset(
    {
        "PATH", "HOME", "USER", "LOGNAME", "SHELL", "LANG", "LANGUAGE", "TZ",
        "TMPDIR", "TMP", "TEMP", "XDG_CACHE_HOME", "XDG_RUNTIME_DIR",
        "CC", "CXX", "CFLAGS", "CPPFLAGS", "LDFLAGS", "CPATH", "C_INCLUDE_PATH",
        "LIBRARY_PATH", "LD_LIBRARY_PATH", "PKG_CONFIG_PATH",
    }
)
ENV_ALLOW_PREFIXES = ("LC_", "WIZ_", "NIX_")
#: A name that looks like a credential never reaches a child, even when allowed.
ENV_SECRET = re.compile(r"TOKEN|SECRET|PASSW|CREDENTIAL|AUTH|API_?KEY|PRIVATE|COOKIE|SESSION", re.IGNORECASE)


def child_env(environ: Optional[dict[str, str]] = None, extra: Iterable[str] = ()) -> dict[str, str]:
    """The environment for a child process: an allowlist, minus anything secret-looking."""
    source = os.environ if environ is None else environ
    allowed = set(ENV_ALLOW) | set(extra)
    return {
        name: value
        for name, value in source.items()
        if (name in allowed or name.startswith(ENV_ALLOW_PREFIXES)) and not ENV_SECRET.search(name)
    }


def path_to_uri(path: str) -> str:
    """A `file:` URI for a local path, percent-escaped the way Wiz decodes it."""
    return "file://" + urllib.parse.quote(os.path.abspath(path), safe="/")


def _is_executable(path: str) -> bool:
    return os.path.isfile(path) and os.access(path, os.X_OK)


def resolve_wiz(workspace: str, wiz: str) -> Optional[str]:
    """The executable for `wiz`, or None. Relative paths use the workspace."""
    if os.sep in wiz or (os.altsep and os.altsep in wiz) or wiz.startswith("."):
        candidate = wiz if os.path.isabs(wiz) else os.path.join(workspace, wiz)
        candidate = os.path.normpath(os.path.abspath(candidate))
        return candidate if _is_executable(candidate) else None
    found = shutil.which(wiz)
    return found if found and _is_executable(found) else None


def _wiz_missing_message(workspace: str, wiz: str) -> str:
    if os.sep in wiz or (os.altsep and os.altsep in wiz) or wiz.startswith("."):
        candidate = wiz if os.path.isabs(wiz) else os.path.join(workspace, wiz)
        return (
            f"no wiz executable at {os.path.normpath(os.path.abspath(candidate))}; "
            "this workspace has no built toolchain: run `lake build wiz` there, or "
            "pass --wiz PATH (see tools/wiz-mcp/README.md)"
        )
    return (
        f"`{wiz}` was not found on PATH; pass --wiz PATH "
        "(for a checkout, ./.lake/build/bin/wiz)"
    )


def _wiz_command(wiz_path: str, cache: Optional[str], args: list[str], use_cache: bool = True) -> list[str]:
    cmd = [wiz_path]
    if use_cache and cache:
        cmd += ["--cache", cache]
    return cmd + args


# ---------------------------------------------------------------------------
# Bounded output and the stable envelope


def clip_text(text: str, limit: int = MAX_TEXT) -> tuple[str, bool]:
    if len(text) <= limit:
        return text, False
    return text[:limit] + TRUNCATION_MARK.format(n=len(text) - limit), True


def clip_result(result: Any) -> tuple[Any, bool]:
    """Serialize a JSON result; if it is too big, return an explicit preview object."""
    raw = json.dumps(result, ensure_ascii=False, separators=(",", ":"))
    if len(raw) <= MAX_RESULT:
        return result, False
    omitted = len(raw) - MAX_RESULT
    return (
        {
            "_truncated": True,
            "bytes": len(raw.encode("utf-8")),
            "preview": raw[:MAX_RESULT]
            + TRUNCATION_MARK.format(n=omitted),
        },
        True,
    )


ENVELOPE_KEYS = (
    "ok",
    "tool",
    "path",
    "exit",
    "stdout",
    "stderr",
    "result",
    "truncated",
    "error",
)


def make_envelope(
    tool: str,
    *,
    ok: bool = True,
    path: Optional[str] = None,
    exit_code: Optional[int] = None,
    stdout: str = "",
    stderr: str = "",
    result: Any = None,
    error: Optional[dict[str, str]] = None,
) -> dict[str, Any]:
    """The shape every tool returns, success or failure.

    `ok` is true when the tool ran and (for the text tools) `wiz` exited 0.
    `exit` carries the command's status; a `check` with type errors is
    `ok: false, exit: 1, error: null` with the messages in stderr. `error` is
    non-null only for a bridge-level failure (missing toolchain, timeout, bad
    arguments, daemon failure).
    """
    stdout, trunc_out = clip_text(stdout)
    stderr, trunc_err = clip_text(stderr)
    truncated = trunc_out or trunc_err
    if result is not None:
        result, trunc_result = clip_result(result)
        truncated = truncated or trunc_result
    return {
        "ok": ok,
        "tool": tool,
        "path": path,
        "exit": exit_code,
        "stdout": stdout,
        "stderr": stderr,
        "result": result,
        "truncated": truncated,
        "error": error,
    }


def error_envelope(
    tool: str,
    kind: str,
    message: str,
    *,
    path: Optional[str] = None,
    stdout: str = "",
    stderr: str = "",
) -> dict[str, Any]:
    return make_envelope(
        tool,
        ok=False,
        path=path,
        stdout=stdout,
        stderr=stderr,
        error={"kind": kind, "message": message},
    )


def envelope_text(envelope: dict[str, Any]) -> str:
    return json.dumps(envelope, ensure_ascii=False, separators=(",", ":"))


# ---------------------------------------------------------------------------
# MCP stdio framing


def iter_messages(lines: Iterable[str]) -> Iterable[dict[str, Any]]:
    """Yield JSON objects from newline-delimited MCP input; skip noise."""
    for line in lines:
        line = line.strip()
        if not line:
            continue
        try:
            message = json.loads(line)
        except json.JSONDecodeError as exc:
            log(f"wiz-mcp: ignoring a non-JSON input line ({exc.msg})")
            continue
        if not isinstance(message, dict):
            log("wiz-mcp: ignoring a JSON value that is not an object")
            continue
        yield message


def write_message(stream: Any, message: dict[str, Any]) -> None:
    stream.write(json.dumps(message, ensure_ascii=False, separators=(",", ":")) + "\n")
    stream.flush()


def reply(msg_id: Any, result: Any) -> dict[str, Any]:
    return {"jsonrpc": "2.0", "id": msg_id, "result": result}


def reply_error(msg_id: Any, code: int, message: str) -> dict[str, Any]:
    return {"jsonrpc": "2.0", "id": msg_id, "error": {"code": code, "message": message}}


# ---------------------------------------------------------------------------
# The language server's transport: LSP over the daemon's own stdin/stdout


class LSPError(Exception):
    """The language server failed, closed, or answered with an error."""


class LSPTimeout(LSPError):
    """A language-server call exceeded its deadline."""


class LSPClosed(LSPError):
    """The daemon's connection is gone."""


class StdioLSP:
    """A `Content-Length` framed LSP connection over a child's stdin/stdout pipes.

    The daemon is a plain `wiz lsp` on stdio: it opens no socket, so no other
    process on the machine can connect to it (the `--ws` port it used before had
    no authentication). Writes and reads use the raw file descriptors with
    `select`, so both honour a deadline; a daemon that stops reading its input
    cannot block a call forever.
    """

    def __init__(self, writer: Any, read_fd: int) -> None:
        # `writer` is the daemon's stdin as an unbuffered file object: it owns the
        # descriptor, so closing it twice is harmless (a bare fd could be reused).
        self.writer = writer
        self.write_fd = writer.fileno()
        self.read_fd = read_fd
        os.set_blocking(self.write_fd, False)
        self._buf = bytearray()
        self._closed = False
        self._send_lock = threading.Lock()

    @staticmethod
    def _remaining(deadline: Optional[float], what: str) -> Optional[float]:
        if deadline is None:
            return None
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            raise LSPTimeout(what)
        return remaining

    def _send_all(self, data: bytes, deadline: Optional[float]) -> None:
        if self._closed:
            raise LSPClosed("the language server's input is closed")
        with self._send_lock:
            view = memoryview(data)
            while view:
                remaining = self._remaining(deadline, "the language server is not reading its input")
                _, writable, _ = select.select([], [self.write_fd], [], remaining)
                if not writable:
                    continue
                try:
                    view = view[os.write(self.write_fd, view):]
                except BlockingIOError:
                    continue
                except OSError as exc:  # EPIPE: the daemon exited
                    raise LSPClosed(f"cannot send to the language server: {exc}") from exc

    def _fill(self, deadline: Optional[float]) -> None:
        remaining = self._remaining(deadline, "the language server did not answer in time")
        readable, _, _ = select.select([self.read_fd], [], [], remaining)
        if not readable:
            return
        try:
            chunk = os.read(self.read_fd, 65536)
        except OSError as exc:
            raise LSPClosed(f"cannot read from the language server: {exc}") from exc
        if not chunk:
            raise LSPClosed("the language server closed its output")
        self._buf += chunk

    def send_text(self, text: str, deadline: Optional[float] = None) -> None:
        body = text.encode("utf-8")
        self._send_all(b"Content-Length: %d\r\n\r\n" % len(body) + body, deadline)

    def recv_text(self, deadline: Optional[float] = None) -> str:
        while True:
            end = self._buf.find(b"\r\n\r\n")
            if end >= 0:
                break
            if len(self._buf) > 65536:
                raise LSPError("the language server sent an oversized header")
            self._fill(deadline)
        header = bytes(self._buf[:end]).decode("ascii", "replace")
        del self._buf[: end + 4]
        length: Optional[int] = None
        for line in header.split("\r\n"):
            name, _, value = line.partition(":")
            if name.strip().lower() == "content-length":
                try:
                    length = int(value.strip())
                except ValueError as exc:
                    raise LSPError(f"bad Content-Length: {value.strip()!r}") from exc
        if length is None or length < 0:
            raise LSPError("the language server sent a message without Content-Length")
        if length > MAX_LSP_MESSAGE:
            raise LSPError(f"language server message too large ({length} bytes)")
        while len(self._buf) < length:
            self._fill(deadline)
        body = bytes(self._buf[:length])
        del self._buf[:length]
        try:
            return body.decode("utf-8")
        except UnicodeDecodeError as exc:
            raise LSPError(f"the language server sent invalid UTF-8: {exc}") from exc

    def close(self) -> None:
        """Close the daemon's stdin (it exits on EOF). The read side belongs to the process."""
        if self._closed:
            return
        self._closed = True
        with self._send_lock:
            try:
                self.writer.close()
            except OSError:
                pass


# ---------------------------------------------------------------------------
# The lazy `wiz lsp` daemon (one per bridge, hence one per workspace)


PDEATHSIG_WRAPPER = r"""
import ctypes, os, signal, sys
try:
    ctypes.CDLL("libc.so.6", use_errno=True).prctl(1, signal.SIGTERM, 0, 0, 0)
except Exception:
    pass
os.execv(sys.argv[1], sys.argv[1:])
"""


def daemon_command(cmd: list[str]) -> list[str]:
    """Run `cmd` with PR_SET_PDEATHSIG on Linux, so a killed bridge cannot orphan it.

    The wrapper is a `python -c` process that sets the parent-death signal and then
    `execv`s the real command, so the PID (and the pdeathsig) stay the daemon's.
    `preexec_fn` is avoided on purpose: it is unsafe in a threaded parent.
    """
    if sys.platform.startswith("linux"):
        return [sys.executable, "-c", PDEATHSIG_WRAPPER] + cmd
    return cmd


class LSPDaemon:
    """One `wiz lsp` process on stdio, owned by one bridge/workspace.

    Lifecycle: started on the first LSP-backed call, used under `op` (one call
    at a time, matching the server's single event loop), killed after `idle`
    seconds without a call, and killed on bridge exit. There is deliberately no
    way to attach to someone else's daemon: worktrees have different `lib/`
    roots, and documents collide by URI. The daemon talks only over its own
    pipes and listens on no socket.
    """

    def __init__(self, config: Config) -> None:
        self.config = config
        self.life = threading.RLock()
        self.op = threading.Lock()
        self.cv = threading.Condition()
        self.conn: Optional[StdioLSP] = None
        self.proc: Optional[subprocess.Popen[bytes]] = None
        self.dead = True
        self.pending: dict[int, dict[str, Any]] = {}
        self.inbox: list[dict[str, Any]] = []
        self.next_id = 0
        self.version = 0
        self.last_use = 0.0
        self._stderr_tail: collections.deque[str] = collections.deque(maxlen=40)
        self._stderr_done = threading.Event()
        self._reader_thread: Optional[threading.Thread] = None

    # -- lifecycle ---------------------------------------------------------

    def _pump_stderr(self, proc: subprocess.Popen[bytes], tail: collections.deque[str], done: threading.Event) -> None:
        try:
            assert proc.stderr is not None
            for raw in proc.stderr:
                tail.append(raw.decode("utf-8", "replace").rstrip())
        except Exception:
            pass
        finally:
            done.set()

    def _kill_locked(self) -> None:
        conn, proc = self.conn, self.proc
        self.conn = None
        self.proc = None
        if conn is not None:
            conn.close()
        if proc is not None:
            try:
                if proc.poll() is None:
                    proc.terminate()
                try:
                    proc.wait(timeout=5)
                except subprocess.TimeoutExpired:
                    proc.kill()
                    proc.wait(timeout=2)
            except Exception:
                pass
            # The reader sees EOF once the daemon is gone; let it finish before its
            # descriptor is closed (a closed fd number can be reused under a select).
            reader, self._reader_thread = self._reader_thread, None
            if reader is not None and reader is not threading.current_thread():
                reader.join(timeout=2)
            streams = [proc.stdin, proc.stderr]
            if reader is None or not reader.is_alive():
                streams.append(proc.stdout)
            for stream in streams:
                if stream is not None:
                    try:
                        stream.close()
                    except Exception:
                        pass
        with self.cv:
            self.dead = True
            self.pending.clear()
            self.cv.notify_all()

    def close(self) -> None:
        """Kill the daemon if it exists. Safe to call from any thread."""
        with self.life:
            self._kill_locked()

    def _startup_error(self, proc: subprocess.Popen[bytes], reason: str) -> ToolError:
        """`lsp_startup` with the daemon's exit status and the tail of its stderr."""
        try:
            proc.wait(timeout=2)
        except subprocess.TimeoutExpired:
            pass
        self._stderr_done.wait(timeout=2)
        code = proc.poll()
        tail = "\n".join(self._stderr_tail)[-2000:]
        detail = f" (exit {code})" if code is not None else ""
        return ToolError("lsp_startup", f"`wiz lsp` {reason}{detail}" + (f":\n{tail}" if tail else ""))

    def ensure(self, deadline: float) -> None:
        with self.life:
            if self.conn is not None:
                return
            self._kill_locked()  # a stale process from a dead connection
            wiz = resolve_wiz(self.config.workspace, self.config.wiz)
            if wiz is None:
                raise ToolError("wiz_not_found", _wiz_missing_message(self.config.workspace, self.config.wiz))
            if deadline - time.monotonic() <= 0:
                raise LSPTimeout("no time left to start the language server")
            cmd = daemon_command(_wiz_command(wiz, self.config.cache, ["lsp"]))
            try:
                proc = subprocess.Popen(
                    cmd,
                    cwd=self.config.workspace,
                    env=child_env(extra=self.config.pass_env),
                    stdin=subprocess.PIPE,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE,
                    bufsize=0,
                )
            except OSError as exc:
                raise ToolError("lsp_startup", f"cannot start the language server: {exc}") from exc
            assert proc.stdin is not None and proc.stdout is not None
            self.proc = proc
            self._stderr_tail = collections.deque(maxlen=40)
            self._stderr_done = threading.Event()
            threading.Thread(
                target=self._pump_stderr, args=(proc, self._stderr_tail, self._stderr_done), daemon=True
            ).start()
            conn = StdioLSP(proc.stdin, proc.stdout.fileno())
            self.conn = conn
            with self.cv:
                self.dead = False
                self.pending.clear()
                self.inbox.clear()
            self._reader_thread = threading.Thread(target=self._reader, args=(conn,), daemon=True)
            self._reader_thread.start()
            # Startup (the initialize round trip) is bounded by the call deadline, with a cap.
            startup_deadline = min(deadline, time.monotonic() + 120.0)
            try:
                self._request_locked(
                    "initialize",
                    {
                        "processId": os.getpid(),
                        "clientInfo": {"name": SERVER_NAME, "version": SERVER_VERSION},
                        "rootUri": path_to_uri(self.config.workspace),
                        "workspaceFolders": [
                            {"uri": path_to_uri(self.config.workspace), "name": os.path.basename(self.config.workspace.rstrip(os.sep)) or "workspace"}
                        ],
                        "capabilities": {},
                    },
                    startup_deadline,
                )
                self._send({"jsonrpc": "2.0", "method": "initialized", "params": {}}, startup_deadline)
            except LSPTimeout:
                self._kill_locked()
                raise
            except LSPError as exc:
                error = self._startup_error(proc, f"exited before answering initialize ({exc})")
                self._kill_locked()
                raise error from exc
            except Exception:
                self._kill_locked()
                raise
            self.last_use = time.monotonic()

    def reap(self) -> None:
        if self.config.idle <= 0:
            return
        if time.monotonic() - self.last_use <= self.config.idle:
            return
        if not self.op.acquire(blocking=False):
            return  # a call is in flight; it just touched last_use
        try:
            with self.life:
                if self.conn is not None or self.proc is not None:
                    log("wiz-mcp: unloading the idle language server")
                    self._kill_locked()
        finally:
            self.op.release()

    # -- JSON-RPC over the daemon -----------------------------------------

    def _reader(self, conn: StdioLSP) -> None:
        try:
            while True:
                raw = conn.recv_text(deadline=None)
                try:
                    message = json.loads(raw)
                except json.JSONDecodeError:
                    continue
                if not isinstance(message, dict):
                    continue
                with self.cv:
                    if "id" in message and "method" not in message:
                        self.pending[message["id"]] = message
                    else:
                        self.inbox.append(message)
                    self.cv.notify_all()
        except Exception:
            pass
        finally:
            try:
                conn.close()
            except Exception:
                pass
            with self.cv:
                if self.conn is conn:
                    self.conn = None
                    self.dead = True
                self.cv.notify_all()

    def _next_id(self) -> int:
        with self.cv:
            self.next_id += 1
            return self.next_id

    def _send(self, message: dict[str, Any], deadline: Optional[float]) -> None:
        conn = self.conn
        if conn is None:
            raise LSPClosed("the language server is not running")
        try:
            conn.send_text(json.dumps(message), deadline)
        except LSPError:
            raise
        except OSError as exc:
            raise LSPClosed(f"cannot send to the language server: {exc}") from exc

    def _request_locked(self, method: str, params: dict[str, Any], deadline: float) -> dict[str, Any]:
        rid = self._next_id()
        self._send({"jsonrpc": "2.0", "id": rid, "method": method, "params": params}, deadline)
        with self.cv:
            while rid not in self.pending:
                if self.dead or self.conn is None:
                    raise LSPClosed("the language server closed the connection")
                remaining = deadline - time.monotonic()
                if remaining <= 0:
                    break
                self.cv.wait(min(remaining, 0.5))
            if rid in self.pending:
                return self.pending.pop(rid)
        self.close()
        raise LSPTimeout(f"no reply to {method} in time")

    def request(self, method: str, params: dict[str, Any], deadline: float) -> dict[str, Any]:
        return self._request_locked(method, params, deadline)

    # -- documents ---------------------------------------------------------

    def _did_open(self, uri: str, text: str, deadline: float) -> None:
        self.version += 1
        self._send(
            {
                "jsonrpc": "2.0",
                "method": "textDocument/didOpen",
                "params": {
                    "textDocument": {
                        "uri": uri,
                        "languageId": "wiz",
                        "version": self.version,
                        "text": text,
                    }
                },
            },
            deadline,
        )

    def _did_close(self, uri: str, deadline: Optional[float] = None) -> None:
        try:
            self._send(
                {"jsonrpc": "2.0", "method": "textDocument/didClose", "params": {"textDocument": {"uri": uri}}},
                deadline,
            )
        except Exception:
            pass

    def wait_diagnostics(self, uri: str, deadline: float) -> list[Any]:
        """Wait for the push that follows didOpen/didChange for `uri`."""
        with self.cv:
            while True:
                found = None
                remaining_messages: list[dict[str, Any]] = []
                for message in self.inbox:
                    if (
                        message.get("method") == "textDocument/publishDiagnostics"
                        and (message.get("params") or {}).get("uri") == uri
                    ):
                        found = message  # keep the last of a burst
                    else:
                        remaining_messages.append(message)
                if found is not None:
                    self.inbox = remaining_messages
                    return list((found.get("params") or {}).get("diagnostics") or [])
                if self.dead or self.conn is None:
                    raise LSPClosed("the language server closed the connection")
                remaining = deadline - time.monotonic()
                if remaining <= 0:
                    raise LSPTimeout("no publishDiagnostics in time")
                self.cv.wait(min(remaining, 0.5))

    def diagnostics(self, uri: str, text: str, deadline: float) -> list[Any]:
        with self.op:
            self.ensure(deadline)
            self.last_use = time.monotonic()
            self._did_open(uri, text, deadline)
            try:
                return self.wait_diagnostics(uri, deadline)
            finally:
                self._did_close(uri, deadline)
                self.last_use = time.monotonic()

    def at(self, method: str, uri: str, text: str, line: int, character: int, deadline: float) -> Any:
        with self.op:
            self.ensure(deadline)
            self.last_use = time.monotonic()
            self._did_open(uri, text, deadline)
            try:
                self.wait_diagnostics(uri, deadline)  # elaboration finished
                response = self._request_locked(
                    method,
                    {"textDocument": {"uri": uri}, "position": {"line": line, "character": character}},
                    deadline,
                )
                if "error" in response:
                    error = response.get("error") or {}
                    raise LSPError(f"{error.get('code')}: {error.get('message')}")
                return response.get("result")
            finally:
                self._did_close(uri, deadline)
                self.last_use = time.monotonic()


# ---------------------------------------------------------------------------
# Tool surface


def _require_str(args: dict[str, Any], key: str) -> str:
    value = args.get(key)
    if not isinstance(value, str) or not value.strip():
        raise ToolError("invalid_args", f"`{key}` must be a non-empty string")
    return value


def _optional_bool(args: dict[str, Any], key: str) -> bool:
    value = args.get(key, False)
    if not isinstance(value, bool):
        raise ToolError("invalid_args", f"`{key}` must be a boolean")
    return value


# ---------------------------------------------------------------------------
# Structured diagnostics for `check`

SEVERITIES = ("error", "warning", "info")
#: LSP DiagnosticSeverity numbers (Wiz uses 1–3; 4, hint, is reported as info).
LSP_SEVERITY = {1: "error", 2: "warning", 3: "info", 4: "info"}
#: stderr lines `wiz check` may print that are not part of a message.
NOT_A_MESSAGE = ("region cache:", "cache verify:", "uncaught exception:", "INTERNAL PANIC", "wiz check:")


def _diagnostic(path: str, line: int, column: int, severity: str, message: str,
                code: Optional[str] = None, end: Optional[tuple[int, int]] = None) -> dict[str, Any]:
    """One diagnostic: `line`/`column` 1-based as Wiz prints them, `range` 0-based as LSP.

    Columns count Unicode code points, as in Wiz's messages and its language server.
    """
    start = {"line": line - 1, "character": column - 1}
    stop = {"line": end[0], "character": end[1]} if end is not None else dict(start)
    return {
        "file": path,
        "line": line,
        "column": column,
        "range": {"start": start, "end": stop},
        "severity": severity,
        "code": code or None,
        "message": message,
    }


def parse_check_output(path: str, stdout: str, stderr: str) -> tuple[list[dict[str, Any]], list[str]]:
    """The messages of `wiz check PATH`, and the lines that are not part of one.

    `wiz check` prints each message as `PATH:LINE:COLUMN: SEVERITY: TEXT` (errors on
    stderr, warnings and info on stdout); a parse error has no severity
    (`PATH:LINE:COLUMN: TEXT`) and is an error. TEXT may continue on later lines
    (an import's errors are listed indented under it), so a line that does not
    start a message belongs to the one before it. Matching on the checked path
    itself keeps a `:` in the path from confusing the parser.
    """
    prefix = path + ":"
    head = re.compile(r"(\d+):(\d+): (?:(error|warning|info): )?(.*)\Z", re.DOTALL)
    diagnostics: list[dict[str, Any]] = []
    unparsed: list[str] = []
    for stream in (stdout, stderr):
        current: Optional[dict[str, Any]] = None
        for raw in stream.splitlines():
            match = head.match(raw[len(prefix):]) if raw.startswith(prefix) else None
            if match:
                line, column, severity, text = match.groups()
                current = _diagnostic(path, int(line), int(column), severity or "error", text)
                diagnostics.append(current)
            elif current is not None and not raw.startswith(NOT_A_MESSAGE):
                current["message"] += "\n" + raw
            elif raw.strip():
                unparsed.append(raw)
                current = None
    diagnostics.sort(key=lambda d: (d["line"], d["column"]))  # stable: stdout before stderr at a tie
    return diagnostics, unparsed


def lsp_diagnostic(path: str, diagnostic: dict[str, Any]) -> dict[str, Any]:
    """A language-server Diagnostic in the same shape as a parsed `wiz check` message."""
    rng = diagnostic.get("range") or {}
    start = rng.get("start") or {}
    end = rng.get("end") or start
    line = int(start.get("line", 0))
    character = int(start.get("character", 0))
    code = diagnostic.get("code")
    return _diagnostic(
        path,
        line + 1,
        character + 1,
        LSP_SEVERITY.get(diagnostic.get("severity"), "error"),
        str(diagnostic.get("message", "")),
        code=str(code) if code not in (None, "") else None,
        end=(int(end.get("line", line)), int(end.get("character", character))),
    )


def check_result(source: str, diagnostics: list[dict[str, Any]], unparsed: Optional[list[str]] = None) -> dict[str, Any]:
    counts = {severity: 0 for severity in SEVERITIES}
    for diagnostic in diagnostics:
        counts[diagnostic["severity"]] += 1
    return {"source": source, "diagnostics": diagnostics, "counts": counts, "unparsed": unparsed or []}


def _position_arg(args: dict[str, Any], key: str) -> int:
    value = args.get(key)
    if isinstance(value, bool) or not isinstance(value, int) or value < 0:
        raise ToolError("invalid_args", f"`{key}` must be a non-negative integer")
    return value


TOOLS: list[dict[str, Any]] = [
    {
        "name": "version",
        "annotations": {"title": "Wiz version", "readOnlyHint": True, "destructiveHint": False, "idempotentHint": True, "openWorldHint": False},
        "description": "Print the Wiz toolchain version (`wiz --version`).",
        "inputSchema": {"type": "object", "properties": {}, "additionalProperties": False},
    },
    {
        "name": "check",
        "annotations": {"title": "Type check a Wiz file", "readOnlyHint": True, "destructiveHint": False, "idempotentHint": True, "openWorldHint": False},
        "description": (
            "Type check a Wiz file and return structured diagnostics in `result.diagnostics` "
            "(file, 1-based line/column, 0-based LSP range, severity, code, message) with counts, "
            "plus the raw output. source=cli (default) runs `wiz check`; source=lsp asks the "
            "language server, which adds range ends and error codes and accepts unsaved `text`."
        ),
        "inputSchema": {
            "type": "object",
            "properties": {
                "path": {"type": "string", "description": "file path, relative to the workspace"},
                "source": {"type": "string", "enum": ["cli", "lsp"], "description": "default cli"},
                "text": {"type": "string", "description": "buffer text (source=lsp only); defaults to the file"},
            },
            "required": ["path"],
            "additionalProperties": False,
        },
    },
    {
        "name": "parse",
        "annotations": {"title": "Parse a Wiz file", "readOnlyHint": True, "destructiveHint": False, "idempotentHint": True, "openWorldHint": False},
        "description": "Print the syntax tree of a Wiz file (`wiz parse`).",
        "inputSchema": {
            "type": "object",
            "properties": {"path": {"type": "string"}},
            "required": ["path"],
            "additionalProperties": False,
        },
    },
    {
        "name": "fmt",
        "annotations": {"title": "Format a Wiz file (prints, does not rewrite)", "readOnlyHint": True, "destructiveHint": False, "idempotentHint": True, "openWorldHint": False},
        "description": "Reprint a Wiz file from its syntax tree (`wiz fmt`); check=true only reports whether it differs.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "path": {"type": "string"},
                "check": {"type": "boolean", "description": "do not print; exit 1 if the file is not formatted"},
                "width": {"type": "integer", "minimum": 1, "maximum": 10000},
            },
            "required": ["path"],
            "additionalProperties": False,
        },
    },
    {
        "name": "build",
        "annotations": {"title": "Build a Wiz program (writes OUT, runs cc; needs --allow-build)", "readOnlyHint": False, "destructiveHint": True, "idempotentHint": True, "openWorldHint": False},
        "description": "Compile `main` of a Wiz file (`wiz build FILE -o OUT [--lib]`).",
        "inputSchema": {
            "type": "object",
            "properties": {
                "path": {"type": "string"},
                "out": {"type": "string", "description": "output path, relative to the workspace"},
                "lib": {"type": "boolean", "description": "build a library instead of an executable"},
            },
            "required": ["path", "out"],
            "additionalProperties": False,
        },
    },
    {
        "name": "diagnostics",
        "annotations": {"title": "Language-server diagnostics", "readOnlyHint": True, "destructiveHint": False, "idempotentHint": True, "openWorldHint": False},
        "description": "Diagnostics from the language server for a file (or for `text`), from this worktree's daemon.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "path": {"type": "string"},
                "text": {"type": "string", "description": "buffer text; defaults to the file on disk"},
            },
            "required": ["path"],
            "additionalProperties": False,
        },
    },
    {
        "name": "hover",
        "annotations": {"title": "Type at a position", "readOnlyHint": True, "destructiveHint": False, "idempotentHint": True, "openWorldHint": False},
        "description": "The type of the identifier at a position (0-based line and character).",
        "inputSchema": {
            "type": "object",
            "properties": {
                "path": {"type": "string"},
                "text": {"type": "string"},
                "line": {"type": "integer", "minimum": 0},
                "character": {"type": "integer", "minimum": 0},
            },
            "required": ["path", "line", "character"],
            "additionalProperties": False,
        },
    },
    {
        "name": "goals",
        "annotations": {"title": "Tactic goals at a position", "readOnlyHint": True, "destructiveHint": False, "idempotentHint": True, "openWorldHint": False},
        "description": "The tactic state at a position (`wiz/interactiveGoals`).",
        "inputSchema": {
            "type": "object",
            "properties": {
                "path": {"type": "string"},
                "text": {"type": "string"},
                "line": {"type": "integer", "minimum": 0},
                "character": {"type": "integer", "minimum": 0},
            },
            "required": ["path", "line", "character"],
            "additionalProperties": False,
        },
    },
]
TOOL_NAMES = {tool["name"] for tool in TOOLS}
#: Tools that write files or run the host toolchain, and the flag that enables each.
GATED_TOOLS = {"build": "--allow-build"}


def visible_tools(config: Config) -> list[dict[str, Any]]:
    """The tools this server lists: gated tools only when their flag was given."""
    enabled = {"build": config.allow_build}
    return [tool for tool in TOOLS if enabled.get(tool["name"], True)]


class Server:
    """The MCP server: dispatch is separated from I/O so tests can drive it."""

    def __init__(self, config: Config) -> None:
        self.config = config
        self.daemon = LSPDaemon(config)
        self.shutting_down = False
        self._reaper_stop = threading.Event()
        if config.idle > 0:
            interval = max(1.0, min(10.0, config.idle / 4.0))
            threading.Thread(target=self._reap_loop, args=(interval,), daemon=True).start()

    def _reap_loop(self, interval: float) -> None:
        while not self._reaper_stop.wait(interval):
            try:
                self.daemon.reap()
            except Exception:
                log("wiz-mcp: idle reaper failed:\n" + traceback.format_exc())

    def close(self) -> None:
        self._reaper_stop.set()
        self.daemon.close()

    # -- path policy ---------------------------------------------------------

    def read_roots(self) -> list[str]:
        """Where tools may read: the workspace, --allow-root dirs, the toolchain library."""
        roots = [os.path.realpath(self.config.workspace)]
        roots += [os.path.realpath(root) for root in self.config.extra_roots]
        roots += toolchain_roots(resolve_wiz(self.config.workspace, self.config.wiz))
        return roots

    def write_roots(self) -> list[str]:
        """Where tools may write: the workspace only."""
        return [os.path.realpath(self.config.workspace)]

    # -- tool implementations ---------------------------------------------

    def _run(self, args: list[str], timeout: float, use_cache: bool = True) -> dict[str, Any]:
        wiz = resolve_wiz(self.config.workspace, self.config.wiz)
        if wiz is None:
            raise ToolError("wiz_not_found", _wiz_missing_message(self.config.workspace, self.config.wiz))
        cmd = _wiz_command(wiz, self.config.cache, args, use_cache=use_cache)
        # A new session means a timeout can kill the whole call, including any
        # `cc`/solver child, not just the `wiz` process.
        popen_options: dict[str, Any] = {}
        if os.name == "posix":
            popen_options["start_new_session"] = True
        try:
            proc = subprocess.Popen(
                cmd,
                cwd=self.config.workspace,
                env=child_env(extra=self.config.pass_env),
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                **popen_options,
            )
        except FileNotFoundError as exc:
            raise ToolError("wiz_not_found", _wiz_missing_message(self.config.workspace, self.config.wiz)) from exc
        except OSError as exc:
            raise ToolError("io_error", f"cannot run wiz: {exc}", stderr=str(exc)) from exc
        try:
            stdout, stderr = proc.communicate(timeout=timeout)
        except subprocess.TimeoutExpired as exc:
            _kill_process_group(proc)
            try:
                stdout, stderr = proc.communicate(timeout=5)
            except subprocess.TimeoutExpired:
                stdout, stderr = "", ""
            raise ToolError(
                "timeout",
                f"`wiz {' '.join(args)}` did not finish within {timeout:.0f}s (the process group was killed)",
                stdout=_as_text(stdout) or _as_text(exc.stdout),
                stderr=_as_text(stderr) or _as_text(exc.stderr),
            ) from exc
        except BaseException:
            _kill_process_group(proc)
            proc.wait()
            raise
        return {"exit": proc.returncode, "stdout": stdout or "", "stderr": stderr or ""}

    def _text_of(self, args: dict[str, Any], path: str) -> str:
        text = args.get("text")
        if text is not None:
            if not isinstance(text, str):
                raise ToolError("invalid_args", "`text` must be a string")
            return text
        try:
            with open(path, encoding="utf-8") as handle:
                return handle.read()
        except OSError as exc:
            raise ToolError("io_error", f"cannot read {path}: {exc.strerror or exc}") from exc

    def _call_tool(self, name: str, args: dict[str, Any]) -> dict[str, Any]:
        timeout = self.config.timeout
        if name == "version":
            run = self._run(["--version"], timeout, use_cache=False)
            return make_envelope(name, ok=run["exit"] == 0, exit_code=run["exit"], stdout=run["stdout"], stderr=run["stderr"])

        if name in GATED_TOOLS and not any(tool["name"] == name for tool in visible_tools(self.config)):
            raise ToolError(
                "not_enabled",
                f"`{name}` writes files and runs the host toolchain; it is off unless the server "
                f"is started with {GATED_TOOLS[name]}",
            )
        path = confine(resolve_path(self.config.workspace, _require_str(args, "path")), self.read_roots())
        if name == "check":
            source = args.get("source", "cli")
            if source not in ("cli", "lsp"):
                raise ToolError("invalid_args", "`source` must be \"cli\" or \"lsp\"")
            if source == "lsp":
                deadline = time.monotonic() + timeout
                raw = self.daemon.diagnostics(path_to_uri(path), self._text_of(args, path), deadline)
                diagnostics = [lsp_diagnostic(path, d) for d in raw if isinstance(d, dict)]
                result = check_result("lsp", diagnostics)
                return make_envelope(name, ok=result["counts"]["error"] == 0, path=path, result=result)
            if "text" in args:
                raise ToolError("invalid_args", "`text` needs source=lsp (`wiz check` reads the file)")
            run = self._run(["check", path], timeout)
            diagnostics, unparsed = parse_check_output(path, run["stdout"], run["stderr"])
            result = check_result("cli", diagnostics, unparsed)
            return make_envelope(
                name, ok=run["exit"] == 0, path=path, exit_code=run["exit"],
                stdout=run["stdout"], stderr=run["stderr"], result=result,
            )
        if name == "parse":
            run = self._run(["parse", path], timeout)
            return make_envelope(name, ok=run["exit"] == 0, path=path, exit_code=run["exit"], stdout=run["stdout"], stderr=run["stderr"])
        if name == "fmt":
            extra = ["fmt", path]
            if _optional_bool(args, "check"):
                extra.append("--check")
            width = args.get("width")
            if width is not None:
                if isinstance(width, bool) or not isinstance(width, int) or not 1 <= width <= 10000:
                    raise ToolError("invalid_args", "`width` must be an integer between 1 and 10000")
                extra += ["--width", str(width)]
            run = self._run(extra, timeout)
            return make_envelope(name, ok=run["exit"] == 0, path=path, exit_code=run["exit"], stdout=run["stdout"], stderr=run["stderr"])
        if name == "build":
            out = _require_str(args, "out")
            out = confine(resolve_path(self.config.workspace, out), self.write_roots(), what="output")
            if os.path.islink(out):
                raise ToolError("path_denied", f"output {out} is a symlink; build will not write through it")
            extra = ["build", path, "-o", out]
            if _optional_bool(args, "lib"):
                extra.append("--lib")
            run = self._run(extra, timeout)
            return make_envelope(name, ok=run["exit"] == 0, path=path, exit_code=run["exit"], stdout=run["stdout"], stderr=run["stderr"])

        # LSP-backed tools: one daemon, one call at a time, one deadline.
        deadline = time.monotonic() + timeout
        uri = path_to_uri(path)
        if name == "diagnostics":
            text = self._text_of(args, path)
            result = self.daemon.diagnostics(uri, text, deadline)
            return make_envelope(name, path=path, result=result)
        if name in ("hover", "goals"):
            line = _position_arg(args, "line")
            character = _position_arg(args, "character")
            text = self._text_of(args, path)
            method = "textDocument/hover" if name == "hover" else "wiz/interactiveGoals"
            result = self.daemon.at(method, uri, text, line, character, deadline)
            return make_envelope(name, path=path, result=result)
        raise ProtocolError(-32602, f"unknown tool {name!r}")

    def call_tool(self, name: str, args: dict[str, Any]) -> dict[str, Any]:
        path: Optional[str] = None
        try:
            return self._call_tool(name, args)
        except ProtocolError:
            raise
        except ToolError as exc:
            try:
                if "path" in args and isinstance(args["path"], str):
                    path = resolve_path(self.config.workspace, args["path"])
            except ToolError:
                path = None
            if exc.kind == "lsp_startup":
                self.daemon.close()
            return error_envelope(
                name,
                exc.kind,
                exc.message,
                path=path,
                stdout=exc.stdout,
                stderr=exc.stderr,
            )
        except LSPTimeout as exc:
            self.daemon.close()
            return error_envelope(name, "timeout", str(exc), path=path)
        except LSPClosed as exc:
            self.daemon.close()
            return error_envelope(name, "lsp_closed", str(exc), path=path)
        except LSPError as exc:
            self.daemon.close()
            return error_envelope(name, "lsp_error", str(exc), path=path)
        except Exception as exc:  # a bug must not kill the server
            log("wiz-mcp: tool call failed:\n" + traceback.format_exc())
            return error_envelope(name, "internal", f"{type(exc).__name__}: {exc}", path=path)

    # -- MCP dispatch ------------------------------------------------------

    def dispatch(self, message: dict[str, Any]) -> tuple[list[dict[str, Any]], bool]:
        """Handle one MCP message; returns (responses, stop)."""
        method = message.get("method")
        msg_id = message.get("id")
        params = message.get("params") if isinstance(message.get("params"), dict) else {}

        if method == "initialize":
            requested = params.get("protocolVersion")
            version = requested if requested in SUPPORTED_PROTOCOLS else PROTOCOL_VERSION
            return [
                reply(
                    msg_id,
                    {
                        "protocolVersion": version,
                        "capabilities": {"tools": {"listChanged": False}},
                        "serverInfo": {"name": SERVER_NAME, "version": SERVER_VERSION},
                        "instructions": INSTRUCTIONS,
                    },
                )
            ], False
        if method == "notifications/initialized":
            return [], False
        if method == "notifications/cancelled":
            # Calls are sequential and bounded by --timeout, so there is nothing
            # to interrupt here without a second thread; the deadline wins.
            return [], False
        if method == "ping":
            return [reply(msg_id, {})], False
        if method == "tools/list":
            return [reply(msg_id, {"tools": visible_tools(self.config)})], False
        if method == "tools/call":
            name = params.get("name")
            arguments = params.get("arguments") or {}
            if not isinstance(name, str):
                return [reply_error(msg_id, -32602, "tools/call needs a tool name")], False
            if not isinstance(arguments, dict):
                return [reply_error(msg_id, -32602, "tools/call arguments must be an object")], False
            if name not in TOOL_NAMES:
                return [reply_error(msg_id, -32602, f"unknown tool {name!r}")], False
            envelope = self.call_tool(name, arguments)
            result: dict[str, Any] = {
                "content": [{"type": "text", "text": envelope_text(envelope)}],
                "isError": not envelope["ok"],
            }
            result["structuredContent"] = envelope
            return [reply(msg_id, result)], False
        if method == "shutdown":
            self.shutting_down = True
            return [reply(msg_id, {})], False
        if method == "exit":
            return [], True
        if msg_id is not None:
            return [reply_error(msg_id, -32601, f"{method} is not supported")], False
        return [], False

    def serve(self, stdin: Any, stdout: Any) -> None:
        for message in iter_messages(stdin):
            try:
                responses, stop = self.dispatch(message)
            except Exception:
                log("wiz-mcp: dispatch failed:\n" + traceback.format_exc())
                responses, stop = [], False
                if "id" in message:
                    responses = [reply_error(message.get("id"), -32603, "internal error")]
            for response in responses:
                write_message(stdout, response)
            if stop:
                break


def _as_text(value: Any) -> str:
    if value is None:
        return ""
    if isinstance(value, bytes):
        return value.decode("utf-8", "replace")
    return str(value)


def _kill_process_group(proc: subprocess.Popen[Any]) -> None:
    """Kill a `_run` child and anything it spawned (it is a session leader)."""
    try:
        if os.name == "posix":
            os.killpg(proc.pid, signal.SIGKILL)
        else:
            proc.kill()
    except ProcessLookupError:
        pass
    except Exception:
        try:
            proc.kill()
        except Exception:
            pass


# ---------------------------------------------------------------------------
# Entry point


def parse_args(argv: Optional[list[str]] = None) -> Config:
    parser = argparse.ArgumentParser(
        prog="wiz_mcp.py",
        description="A stdlib-only MCP stdio server for the Wiz toolchain.",
    )
    parser.add_argument(
        "--workspace",
        default=os.getcwd(),
        help="the directory tool paths are relative to (default: cwd, which the MCP client sets)",
    )
    parser.add_argument(
        "--wiz",
        default=os.environ.get("WIZ_BIN", os.path.join(".", ".lake", "build", "bin", "wiz")),
        help="the wiz executable; a relative path resolves against --workspace (default: ./.lake/build/bin/wiz)",
    )
    parser.add_argument(
        "--cache",
        default=os.environ.get("WIZ_MCP_CACHE"),
        help="--cache DIR for wiz calls and the language server (default: wiz's own ~/.cache/wiz)",
    )
    parser.add_argument(
        "--idle",
        type=float,
        default=DEFAULT_IDLE,
        help="unload an idle language server after N seconds; 0 keeps it (default: 600)",
    )
    parser.add_argument(
        "--timeout",
        type=float,
        default=DEFAULT_TIMEOUT,
        help="per-call timeout in seconds (default: 300)",
    )
    parser.add_argument(
        "--allow-build",
        action="store_true",
        help="list and allow `build` (writes an output file in the workspace and runs the host C toolchain)",
    )
    parser.add_argument(
        "--allow-root",
        action="append",
        default=[],
        metavar="DIR",
        help="another directory tools may read (repeatable); writes stay in the workspace",
    )
    parser.add_argument(
        "--pass-env",
        action="append",
        default=[],
        metavar="NAME",
        help="pass another environment variable to wiz (repeatable); secret-looking names are still dropped",
    )
    args = parser.parse_args(argv)
    workspace = os.path.abspath(os.path.expanduser(args.workspace))
    if not os.path.isdir(workspace):
        parser.error(f"--workspace is not a directory: {workspace}")
    if args.timeout <= 0:
        parser.error("--timeout must be positive")
    if args.idle < 0:
        parser.error("--idle must be non-negative (0 disables unloading)")
    cache = args.cache
    if cache:
        cache = os.path.expanduser(cache)
        if not os.path.isabs(cache):
            cache = os.path.join(workspace, cache)
        cache = os.path.normpath(os.path.abspath(cache))
    extra_roots = []
    for root in args.allow_root:
        root = os.path.expanduser(root)
        if not os.path.isabs(root):
            root = os.path.join(workspace, root)
        if not os.path.isdir(root):
            parser.error(f"--allow-root is not a directory: {root}")
        extra_roots.append(os.path.realpath(root))
    return Config(
        workspace=workspace,
        wiz=args.wiz,
        cache=cache,
        idle=args.idle,
        timeout=args.timeout,
        allow_build=args.allow_build,
        extra_roots=tuple(extra_roots),
        pass_env=tuple(args.pass_env),
    )


def main(argv: Optional[list[str]] = None) -> int:
    config = parse_args(argv)
    wiz = resolve_wiz(config.workspace, config.wiz)
    log(
        f"wiz-mcp: workspace={config.workspace} wiz={wiz or config.wiz} idle={config.idle:g}s "
        f"timeout={config.timeout:g}s build={'on' if config.allow_build else 'off'}"
    )
    if wiz is None:
        log(f"wiz-mcp: warning: {_wiz_missing_message(config.workspace, config.wiz)}")

    server = Server(config)

    def stop(_signum: int, _frame: Any) -> None:
        raise SystemExit(0)

    for sig in (signal.SIGTERM, signal.SIGINT, getattr(signal, "SIGHUP", None)):
        if sig is None:
            continue
        try:
            signal.signal(sig, stop)
        except (ValueError, OSError):
            pass

    try:
        server.serve(sys.stdin, sys.stdout)
    finally:
        server.close()
    return 0


if __name__ == "__main__":
    sys.exit(main())
