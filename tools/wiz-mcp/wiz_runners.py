"""wiz_runners: the explicit, sandboxed runners of the Wiz and Scry MCP servers (phase 3).

Stdlib only; shared by `wiz_mcp.py` (test groups, the live trust ledger, `run`) and
`tools/scry-mcp` (dynamic analysis, repro/verify, triage). Nothing here decides *whether*
a runner is enabled: each server lists a runner only when its flag was given. This module
decides *how* an enabled runner executes:

* **Through the scheduler, never directly.** A long job runs as
  `heavy --mem M timeout -k 30 T SANDBOX… CMD…` (the time limit is inside `heavy`, so
  queueing never counts against it); a short one as `light SANDBOX… CMD…`. When the
  scheduler script is missing the runner refuses; it never falls back to running the
  command itself.
* **Admission before queueing.** `heavy --status` is read first. A measurement window, a
  non-empty queue, or a job that fits neither the budget nor the measured headroom is
  refused with `heavy_busy` (and the status) unless the caller asked to `queue`; then the
  job starts at once and `job_status` reports its place in heavy's FIFO queue instead of
  blocking the call.
* **One job per server**, kept in a private 0700 directory with its output, killed (its
  whole process group) on cancel and when the server exits.
* **A sandbox** (`bwrap`): no network, IPC, UTS or PID sharing; the root file system
  read-only; a private `/tmp`; either the home directory hidden (code under test) or its
  credential directories masked (the test driver); only named directories writable.
  Without `bwrap` the runner refuses.
* **A fixed argument vector.** Callers choose values (selectors, a path, a size), never a
  command line: there is no shell anywhere on the path.
"""

from __future__ import annotations

import os
import re
import shutil
import signal
import subprocess
import threading
import time
from dataclasses import dataclass, field
from typing import Any, Callable, Iterable, Optional

#: The machine's scheduler scripts (overridable per server with --heavy/--light).
DEFAULT_HEAVY = "/workspace/wiz-tools/heavy"
DEFAULT_LIGHT = "/workspace/wiz-tools/light"
#: The largest --mem a caller may declare unless the server raises it (--max-mem).
DEFAULT_MAX_MEM = "8G"
#: The longest time limit a caller may ask for unless the server raises it (--max-runtime).
DEFAULT_MAX_RUNTIME = 3600
#: Jobs kept for job_status after they end (the oldest finished ones go first).
KEEP_JOBS = 20
#: How much of a job's output a status shows (the tail).
TAIL_BYTES = 48 * 1024

SIZE = re.compile(r"^([1-9][0-9]{0,6})([MG])$")

#: Scheduler overrides a child must never inherit: `WIZ_HEAVY_TOTAL_MEM=999G` or
#: `WIZ_LOCK_HELD=heavy` would let a job bypass the budget or the locks.
SCHEDULER_ENV = re.compile(r"^(WIZ_HEAVY_|WIZ_LIGHT_|WIZ_LOCK)")
#: Needed by `systemd-run --user` inside heavy/light; not a credential.
RUNNER_ENV_EXTRA = ("DBUS_SESSION_BUS_ADDRESS", "XDG_RUNTIME_DIR")

#: Credential locations under $HOME that the test-driver sandbox masks.
HOME_SECRETS = (
    ".ssh", ".gnupg", ".config", ".local/state", ".netrc", ".aws", ".docker",
    ".git-credentials", ".cachix", ".npmrc", ".pypirc", ".kube", ".password-store",
    ".local/share/keyrings",
)


class RunnerError(Exception):
    """A refusal or failure the caller sees as an error envelope (`kind`, `message`)."""

    def __init__(self, kind: str, message: str, detail: Any = None) -> None:
        super().__init__(message)
        self.kind = kind
        self.message = message
        self.detail = detail


# ---------------------------------------------------------------------------
# Values from callers


def parse_size_mib(value: Any, what: str = "`mem`") -> int:
    """`6G`/`4096M` (whole numbers, as heavy takes them) in MiB."""
    if not isinstance(value, str) or not SIZE.match(value):
        raise RunnerError("invalid_args", f"{what} must be a whole number of M or G, such as 6G or 4096M")
    number, unit = SIZE.match(value).groups()  # type: ignore[union-attr]
    return int(number) * (1024 if unit == "G" else 1)


def check_mem(value: Any, default: str, maximum: str) -> str:
    """A declared --mem, at most the server's maximum."""
    mem = default if value is None else value
    if parse_size_mib(mem) > parse_size_mib(maximum, "--max-mem"):
        raise RunnerError("invalid_args", f"`mem` {mem} is above this server's maximum {maximum} (--max-mem)")
    return mem


def check_seconds(value: Any, default: int, maximum: int, what: str) -> int:
    seconds = default if value is None else value
    if isinstance(seconds, bool) or not isinstance(seconds, int) or not 1 <= seconds <= maximum:
        raise RunnerError("invalid_args", f"`{what}` must be an integer between 1 and {maximum}")
    return seconds


def check_bool(args: dict[str, Any], key: str, default: bool = False) -> bool:
    value = args.get(key, default)
    if not isinstance(value, bool):
        raise RunnerError("invalid_args", f"`{key}` must be a boolean")
    return value


def job_args(args: dict[str, Any], config: "RunnerConfig", max_wait: float, default_mem: str,
             default_timeout: int) -> tuple[str, int, bool, float]:
    """A heavy runner's `mem`, `timeout`, `queue` and `wait`, checked against the server's limits."""
    mem = check_mem(args.get("mem"), default_mem, config.max_mem)
    timeout = check_seconds(args.get("timeout"), min(default_timeout, config.max_runtime),
                            config.max_runtime, "timeout")
    queue = check_bool(args, "queue")
    wait = args.get("wait", 20)
    if isinstance(wait, bool) or not isinstance(wait, int) or wait < 0:
        raise RunnerError("invalid_args", "`wait` must be a non-negative integer")
    return mem, timeout, queue, float(min(wait, max_wait))


def runner_env(base: dict[str, str], environ: Optional[dict[str, str]] = None) -> dict[str, str]:
    """`base` (an already allowlisted environment) without scheduler overrides, plus what
    `systemd-run --user` needs to reach the user manager."""
    source = os.environ if environ is None else environ
    env = {k: v for k, v in base.items() if not SCHEDULER_ENV.match(k)}
    for name in RUNNER_ENV_EXTRA:
        if name in source and not SCHEDULER_ENV.match(name):
            env[name] = source[name]
    return env


def _executable(path: Optional[str]) -> Optional[str]:
    if not path:
        return None
    if os.sep not in path:
        found = shutil.which(path)
        return found if found and os.access(found, os.X_OK) else None
    return path if os.path.isfile(path) and os.access(path, os.X_OK) else None


# ---------------------------------------------------------------------------
# The scheduler's state (`heavy --status`, `heavy --queue`)


@dataclass
class HeavyStatus:
    perf_window: str = "none"
    reserved_mib: int = 0
    budget_mib: Optional[int] = None
    ceiling_mib: Optional[int] = None
    jobs: int = 0
    headroom_mib: Optional[int] = None
    waiting: list[str] = field(default_factory=list)
    raw: str = ""

    def summary(self) -> dict[str, Any]:
        return {
            "perf_window": self.perf_window, "reserved_mib": self.reserved_mib,
            "budget_mib": self.budget_mib, "ceiling_mib": self.ceiling_mib, "jobs": self.jobs,
            "headroom_mib": self.headroom_mib, "waiting": len(self.waiting),
        }


_ADMISSION = re.compile(
    r"^admission: reserved (\d+) MiB of (\S+) in (\d+) jobs;.*headroom for a new job (-?\d+) MiB", re.M)
_LIMITS = re.compile(r"^limits: budget (\S+) ceiling (\S+) \(effective (\d+) MiB", re.M)
_PERF = re.compile(r"^perf-window: (.*)$", re.M)


def _size_to_mib(text: str) -> Optional[int]:
    match = re.fullmatch(r"(\d+)([KMGT])?", text)
    if not match:
        return None
    n, unit = int(match.group(1)), match.group(2) or "M"
    return {"K": n // 1024, "M": n, "G": n * 1024, "T": n * 1024 * 1024}[unit]


def parse_heavy_status(text: str) -> HeavyStatus:
    """Parse `heavy --status`; raises RunnerError when the admission line is missing."""
    admission = _ADMISSION.search(text)
    if not admission:
        raise RunnerError("scheduler_error", "`heavy --status` has no admission line; refusing to queue blind")
    status = HeavyStatus(raw=text)
    status.reserved_mib = int(admission.group(1))
    status.budget_mib = _size_to_mib(admission.group(2))
    status.jobs = int(admission.group(3))
    status.headroom_mib = int(admission.group(4))
    limits = _LIMITS.search(text)
    if limits:
        status.ceiling_mib = int(limits.group(3))
    perf = _PERF.search(text)
    if perf:
        status.perf_window = perf.group(1).strip() or "none"
    lines = text.split("\n")
    if "waiting (FIFO order):" in lines:
        for line in lines[lines.index("waiting (FIFO order):") + 1:]:
            if not line.startswith("  "):
                break
            status.waiting.append(line.strip())
    return status


def admission(status: HeavyStatus, mem_mib: int) -> tuple[bool, str]:
    """Whether heavy would start a job of `mem_mib` now (its rules, read-only)."""
    if status.perf_window != "none":
        return False, f"a measurement window is open ({status.perf_window}); heavy refuses new jobs"
    if status.ceiling_mib is not None and status.reserved_mib + mem_mib > status.ceiling_mib and status.jobs:
        return False, f"{mem_mib} MiB more would pass the {status.ceiling_mib} MiB ceiling"
    if status.waiting:
        return False, f"{len(status.waiting)} job(s) already wait in heavy's FIFO queue"
    if status.jobs == 0:
        return True, "no heavy job is running"
    if status.budget_mib is not None and status.reserved_mib + mem_mib <= status.budget_mib:
        return True, "fits the reservation budget"
    if status.headroom_mib is not None and status.headroom_mib >= mem_mib:
        return True, "fits the measured headroom"
    return False, (f"{status.reserved_mib} MiB of {status.budget_mib} MiB are reserved by {status.jobs} job(s) "
                   f"and the headroom is {status.headroom_mib} MiB")


def queue_position(queue_text: str, pid: int) -> Optional[int]:
    """`pid`'s 1-based place in `heavy --queue`, or None when it is not waiting."""
    for line in queue_text.split("\n"):
        match = re.match(r"^\s*(\d+)\.\s.*\bpid=(\d+)\b", line)
        if match and int(match.group(2)) == pid:
            return int(match.group(1))
    return None


# ---------------------------------------------------------------------------
# The sandbox


@dataclass(frozen=True)
class Sandbox:
    """A bwrap profile. `hide_home` hides $HOME entirely (code under test); otherwise its
    credential locations are masked. `readable` paths are re-exposed read-only (a toolchain
    under a hidden home or /tmp); `writable` ones read-write. The workspace is read-only
    unless `workspace_rw`."""

    workspace: str
    workspace_rw: bool = False
    hide_home: bool = True
    readable: tuple[str, ...] = ()
    writable: tuple[str, ...] = ()
    home: Optional[str] = None


def _existing(paths: Iterable[str]) -> list[str]:
    seen: list[str] = []
    for path in paths:
        if path and os.path.exists(path):
            real = os.path.realpath(path)
            if real not in seen:
                seen.append(real)
    return seen


def sandbox_argv(bwrap: str, box: Sandbox) -> list[str]:
    """The `bwrap … --` prefix for `box` (the command follows)."""
    home = box.home if box.home is not None else os.path.expanduser("~")
    home = os.path.realpath(home) if home else None
    argv = [
        bwrap, "--unshare-net", "--unshare-ipc", "--unshare-pid", "--unshare-uts",
        "--die-with-parent", "--new-session",
        "--ro-bind", "/", "/", "--dev", "/dev", "--proc", "/proc", "--tmpfs", "/tmp",
    ]
    if home and home != "/":
        if box.hide_home:
            argv += ["--tmpfs", home]
        else:
            for rel in HOME_SECRETS:
                path = os.path.join(home, rel)
                if os.path.isdir(path) and not os.path.islink(path):
                    argv += ["--tmpfs", path]
                elif os.path.lexists(path):
                    argv += ["--ro-bind", "/dev/null", path]
    workspace = os.path.realpath(box.workspace)
    for path in _existing(box.readable):
        argv += ["--ro-bind", path, path]
    argv += ["--bind" if box.workspace_rw else "--ro-bind", workspace, workspace]
    for path in _existing(box.writable):
        argv += ["--bind", path, path]
    argv += ["--setenv", "TMPDIR", "/tmp", "--chdir", workspace, "--"]
    return argv


# ---------------------------------------------------------------------------
# Jobs


@dataclass
class Job:
    id: str
    kind: str
    title: str
    directory: str
    proc: subprocess.Popen[bytes]
    mem: Optional[str]
    timeout: int
    post: Optional[Callable[["Job", str, str, int], Any]]
    started: float = field(default_factory=time.time)
    ended: Optional[float] = None
    exit: Optional[int] = None
    cancelled: bool = False
    result: Any = None
    post_error: Optional[str] = None

    @property
    def stdout_path(self) -> str:
        return os.path.join(self.directory, "stdout")

    @property
    def stderr_path(self) -> str:
        return os.path.join(self.directory, "stderr")


#: Exit statuses with a meaning of their own (timeout's, heavy's and the kernel's).
EXIT_STATES = {124: "timeout", 137: "killed", 143: "terminated", 75: "refused", 2: "failed"}


def _tail(path: str, limit: int = TAIL_BYTES) -> tuple[str, bool]:
    try:
        size = os.path.getsize(path)
        with open(path, "rb") as handle:
            if size > limit:
                handle.seek(size - limit)
            data = handle.read()
    except OSError:
        return "", False
    return data.decode("utf-8", "replace"), size > limit


def read_all(path: str, limit: int = 16 << 20) -> str:
    try:
        with open(path, "rb") as handle:
            return handle.read(limit).decode("utf-8", "replace")
    except OSError:
        return ""


class JobManager:
    """At most `max_active` running jobs, each in its own process group and directory."""

    def __init__(self, root: str, max_active: int = 1, keep: int = KEEP_JOBS) -> None:
        self.root = root
        os.makedirs(root, mode=0o700, exist_ok=True)
        os.chmod(root, 0o700)
        self.max_active = max_active
        self.keep = keep
        self.jobs: dict[str, Job] = {}
        self._counter = 0
        self._lock = threading.Lock()

    def new_directory(self) -> tuple[str, str]:
        with self._lock:
            self._counter += 1
            job_id = f"j{self._counter}"
        directory = os.path.join(self.root, job_id)
        os.makedirs(directory, mode=0o700)
        return job_id, directory

    def active(self) -> list[Job]:
        return [job for job in self.jobs.values() if self.poll(job) is None]

    def start(self, kind: str, title: str, argv: list[str], cwd: str, env: dict[str, str], *,
              mem: Optional[str], timeout: int,
              post: Optional[Callable[[Job, str, str, int], Any]] = None,
              job_dir: Optional[tuple[str, str]] = None) -> Job:
        running = self.active()
        if len(running) >= self.max_active:
            raise RunnerError(
                "busy", f"job {running[0].id} ({running[0].title}) is still running; one job at a time "
                "(job_status to follow it, job_cancel to stop it)")
        job_id, directory = job_dir or self.new_directory()
        with open(os.path.join(directory, "stdout"), "wb") as out, open(os.path.join(directory, "stderr"), "wb") as err:
            try:
                proc = subprocess.Popen(argv, cwd=cwd, env=env, stdin=subprocess.DEVNULL, stdout=out,
                                        stderr=err, start_new_session=True)
            except OSError as exc:
                raise RunnerError("io_error", f"cannot start {os.path.basename(argv[0])}: {exc}") from exc
        job = Job(job_id, kind, title, directory, proc, mem, timeout, post)
        with self._lock:
            self.jobs[job_id] = job
            finished = [j for j in self.jobs.values() if j.ended is not None]
            while len(self.jobs) > self.keep and finished:
                old = finished.pop(0)
                self.jobs.pop(old.id, None)
                shutil.rmtree(old.directory, ignore_errors=True)
        return job

    def poll(self, job: Job) -> Optional[int]:
        if job.exit is not None:
            return job.exit
        code = job.proc.poll()
        if code is None:
            return None
        job.exit = code
        job.ended = time.time()
        if job.post is not None and not job.cancelled:
            try:
                job.result = job.post(job, read_all(job.stdout_path), read_all(job.stderr_path), code)
            except RunnerError as exc:
                job.post_error = f"{exc.kind}: {exc.message}"
            except Exception as exc:  # a parser bug must not lose the job
                job.post_error = f"{type(exc).__name__}: {exc}"
        return code

    def wait(self, job: Job, seconds: float) -> Optional[int]:
        deadline = time.monotonic() + max(0.0, seconds)
        while True:
            code = self.poll(job)
            if code is not None or time.monotonic() >= deadline:
                return code
            time.sleep(min(0.2, max(0.0, deadline - time.monotonic())))

    def get(self, job_id: Any) -> Job:
        if not isinstance(job_id, str) or job_id not in self.jobs:
            raise RunnerError("not_found", f"no job {job_id!r} (job_status without `job` lists them)")
        return self.jobs[job_id]

    def state(self, job: Job, queue_text: Optional[str] = None) -> tuple[str, Optional[int]]:
        code = self.poll(job)
        if code is None:
            position = queue_position(queue_text, job.proc.pid) if queue_text else None
            return ("queued" if position else "running"), position
        if job.cancelled:
            return "cancelled", None
        if code == 0:
            return "done", None
        return EXIT_STATES.get(code, "failed"), None

    def describe(self, job: Job, queue_text: Optional[str] = None, with_output: bool = True) -> dict[str, Any]:
        state, position = self.state(job, queue_text)
        out: dict[str, Any] = {
            "job": job.id, "kind": job.kind, "title": job.title, "state": state, "exit": job.exit,
            "mem": job.mem, "timeout": job.timeout,
            "elapsed": round((job.ended or time.time()) - job.started, 1),
        }
        if position is not None:
            out["queue_position"] = position
        if state == "killed":
            out["hint"] = "exit 137: killed, most likely over its declared --mem; retry with a larger `mem`"
        elif state == "timeout":
            out["hint"] = f"exit 124: the {job.timeout} s limit was reached"
        elif state == "terminated":
            out["hint"] = ("exit 143: terminated; heavy stops the whole job with SIGTERM when a process in it is "
                           "OOM-killed (stderr says so), so a larger `mem` may help")
        elif state == "refused":
            out["hint"] = "exit 75: heavy refused (a measurement window opened); retry later"
        if with_output:
            stdout, cut_out = _tail(job.stdout_path)
            stderr, cut_err = _tail(job.stderr_path)
            out["stdout_tail"], out["stderr_tail"] = stdout, stderr
            out["output_cut"] = cut_out or cut_err
        if job.exit is not None:
            out["result"] = job.result
            if job.post_error:
                out["result_error"] = job.post_error
        return out

    def cancel(self, job: Job) -> None:
        if self.poll(job) is not None:
            return
        job.cancelled = True
        _signal_group(job.proc, signal.SIGTERM)
        try:
            job.proc.wait(timeout=10)
        except subprocess.TimeoutExpired:
            _signal_group(job.proc, signal.SIGKILL)
            job.proc.wait()
        self.poll(job)

    def close(self) -> None:
        for job in list(self.jobs.values()):
            try:
                self.cancel(job)
            except Exception:
                pass
        shutil.rmtree(self.root, ignore_errors=True)


def session_pids(sid: int, proc_root: str = "/proc") -> list[int]:
    """Every process in session `sid` (Linux /proc; empty elsewhere)."""
    pids = []
    try:
        names = os.listdir(proc_root)
    except OSError:
        return []
    for name in names:
        if not name.isdigit():
            continue
        try:
            with open(os.path.join(proc_root, name, "stat"), encoding="utf-8", errors="replace") as handle:
                stat = handle.read()
            fields = stat[stat.rfind(")") + 2:].split()
            if len(fields) > 3 and int(fields[3]) == sid:
                pids.append(int(name))
        except (OSError, ValueError):
            continue
    return pids


def _signal_group(proc: subprocess.Popen[Any], sig: int) -> None:
    """Signal a job's whole session, not only its process group: coreutils `timeout`
    moves itself (and the command under it) into a process group of its own, but it
    stays in the session the job started (`start_new_session`). bwrap's sandboxed child
    dies with bwrap (`--die-with-parent`)."""
    targets = [proc.pid] + [pid for pid in session_pids(proc.pid) if pid != proc.pid]
    try:
        os.killpg(proc.pid, sig)
    except OSError:
        pass
    for pid in targets:
        try:
            os.kill(pid, sig)
        except OSError:
            pass


# ---------------------------------------------------------------------------
# The runner: scheduler + sandbox + jobs, for one server


@dataclass(frozen=True)
class RunnerConfig:
    heavy: str = DEFAULT_HEAVY
    light: str = DEFAULT_LIGHT
    bwrap: str = "bwrap"
    max_mem: str = DEFAULT_MAX_MEM
    max_runtime: int = DEFAULT_MAX_RUNTIME


class Runner:
    """Starts heavy jobs and runs light commands for one server; owns its JobManager."""

    def __init__(self, config: RunnerConfig, root: str) -> None:
        self.config = config
        self.jobs = JobManager(root)

    # -- tools on the path --------------------------------------------------

    def _tool(self, path: str, what: str, flag: str) -> str:
        found = _executable(path)
        if not found:
            raise RunnerError("scheduler_not_found" if what != "bwrap" else "sandbox_unavailable",
                              f"no {what} at {path!r} ({flag}); runners never run unscheduled or unsandboxed")
        return found

    def heavy(self) -> str:
        return self._tool(self.config.heavy, "heavy", "--heavy")

    def light(self) -> str:
        return self._tool(self.config.light, "light", "--light")

    def bwrap(self) -> str:
        return self._tool(self.config.bwrap, "bwrap", "--bwrap")

    def _query(self, args: list[str], env: dict[str, str]) -> str:
        try:
            result = subprocess.run([self.heavy()] + args, env=env, stdin=subprocess.DEVNULL,
                                    capture_output=True, text=True, timeout=30)
        except (OSError, subprocess.TimeoutExpired) as exc:
            raise RunnerError("scheduler_error", f"heavy {' '.join(args)} failed: {exc}") from exc
        return result.stdout

    def status(self, env: dict[str, str]) -> HeavyStatus:
        return parse_heavy_status(self._query(["--status"], env))

    def queue_text(self, env: dict[str, str]) -> Optional[str]:
        try:
            return self._query(["--queue"], env)
        except RunnerError:
            return None

    # -- starting -------------------------------------------------------------

    def start_heavy(self, kind: str, title: str, command: list[str], box: Sandbox, env: dict[str, str], *,
                    mem: str, timeout: int, queue: bool,
                    post: Optional[Callable[[Job, str, str, int], Any]] = None,
                    job_dir: Optional[tuple[str, str]] = None) -> Job:
        """`heavy --mem MEM timeout -k 30 TIMEOUT bwrap … -- COMMAND`, after the admission check."""
        heavy, bwrap = self.heavy(), self.bwrap()
        env = runner_env(env)
        running = self.jobs.active()
        if running:
            raise RunnerError(
                "busy", f"job {running[0].id} ({running[0].title}) is still running; one job at a time "
                "(job_status to follow it, job_cancel to stop it)")
        status = self.status(env)
        mem_mib = parse_size_mib(mem)
        if status.ceiling_mib is not None and mem_mib > status.ceiling_mib:
            raise RunnerError("invalid_args", f"`mem` {mem} is above heavy's {status.ceiling_mib} MiB ceiling")
        fits, why = admission(status, mem_mib)
        if status.perf_window != "none":
            raise RunnerError("measurement_window", why, status.summary())
        if not fits and not queue:
            raise RunnerError(
                "heavy_busy", f"heavy would not start a {mem} job now: {why}. Retry later, or pass "
                "queue=true to wait in heavy's FIFO queue (job_status reports the position)", status.summary())
        argv = [heavy, "--mem", mem, "timeout", "-k", "30", str(timeout)] + sandbox_argv(bwrap, box) + command
        return self.jobs.start(kind, title, argv, box.workspace, env, mem=mem, timeout=timeout,
                               post=post, job_dir=job_dir)

    def run_light(self, command: list[str], box: Sandbox, env: dict[str, str], timeout: float) -> dict[str, Any]:
        """`light bwrap … -- COMMAND`, synchronously (light has its own 180 s and 2 GB caps)."""
        argv = [self.light()] + sandbox_argv(self.bwrap(), box) + command
        try:
            proc = subprocess.Popen(argv, cwd=box.workspace, env=runner_env(env), stdin=subprocess.DEVNULL,
                                    stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
                                    start_new_session=True)
        except OSError as exc:
            raise RunnerError("io_error", f"cannot run light: {exc}") from exc
        try:
            stdout, stderr = proc.communicate(timeout=timeout)
        except subprocess.TimeoutExpired as exc:
            _signal_group(proc, signal.SIGKILL)
            proc.communicate()
            raise RunnerError("timeout", f"the light command did not finish within {timeout:.0f}s") from exc
        except BaseException:
            _signal_group(proc, signal.SIGKILL)
            proc.wait()
            raise
        return {"exit": proc.returncode, "stdout": stdout or "", "stderr": stderr or ""}

    # -- following ------------------------------------------------------------

    def status_of(self, job_id: Any, env: dict[str, str], wait: float = 0.0) -> dict[str, Any]:
        job = self.jobs.get(job_id)
        if wait > 0:
            self.jobs.wait(job, wait)
        queue = self.queue_text(runner_env(env)) if self.jobs.poll(job) is None else None
        return self.jobs.describe(job, queue)

    def list_jobs(self) -> list[dict[str, Any]]:
        return [self.jobs.describe(job, None, with_output=False) for job in self.jobs.jobs.values()]

    def cancel(self, job_id: Any) -> dict[str, Any]:
        job = self.jobs.get(job_id)
        self.jobs.cancel(job)
        return self.jobs.describe(job, None)

    def close(self) -> None:
        self.jobs.close()


# ---------------------------------------------------------------------------
# Output parsers (pure)

#: An exact test selector: `=GROUP` or `=GROUP#1,2`. Prefixes are refused (one letter
#: would select half the suite), and so is anything that looks like an option.
TEST_SELECTOR = re.compile(r"^=[A-Za-z0-9][A-Za-z0-9_.-]{0,63}(#[0-9]{1,4}(,[0-9]{1,4}){0,63})?$")
_CASE = re.compile(r"^  ([✓✗⊘]) (.*) \(([0-9.]+) s\)$")
_GROUP = re.compile(r"^── (\S+)")
_SUMMARY = re.compile(r"^(\d+) passed, (\d+) failed(?:, (\d+) skipped)?\s*$")
_STATUS = {"✓": "passed", "✗": "failed", "⊘": "skipped"}


def check_selectors(value: Any) -> list[str]:
    if not isinstance(value, list) or not 1 <= len(value) <= 16:
        raise RunnerError("invalid_args", "`selectors` must be a list of 1 to 16 exact selectors such as \"=native\"")
    for selector in value:
        if not isinstance(selector, str) or not TEST_SELECTOR.match(selector):
            raise RunnerError(
                "invalid_args", f"bad selector {selector!r}: use an exact group, `=NAME` or `=NAME#0,3` "
                "(prefix selectors are refused: they can select many groups)")
    return list(value)


def parse_test_output(stdout: str) -> dict[str, Any]:
    """The test driver's per-case lines and summary: counts per group, failed and skipped cases."""
    groups: dict[str, dict[str, int]] = {}
    failed: list[dict[str, Any]] = []
    skipped: list[dict[str, Any]] = []
    summary: Optional[dict[str, int]] = None
    group = None
    current: Optional[dict[str, Any]] = None
    for line in stdout.split("\n"):
        heading = _GROUP.match(line)
        if heading:
            group = heading.group(1)
            groups.setdefault(group, {"passed": 0, "failed": 0, "skipped": 0})
            current = None
            continue
        case = _CASE.match(line)
        if case and group is not None:
            status = _STATUS[case.group(1)]
            groups[group][status] += 1
            current = None
            if status != "passed":
                current = {"group": group, "name": case.group(2), "seconds": float(case.group(3)), "output": []}
                (failed if status == "failed" else skipped).append(current)
            continue
        total = _SUMMARY.match(line)
        if total:
            summary = {"passed": int(total.group(1)), "failed": int(total.group(2)),
                       "skipped": int(total.group(3) or 0)}
            current = None
            continue
        if current is not None and line.startswith("      ") and len(current["output"]) < 40:
            current["output"].append(line[6:])
    for item in failed + skipped:
        item["output"] = "\n".join(item["output"])
    return {
        "summary": summary,
        "complete": summary is not None,
        # A skip is not a pass: all_passed needs no failure and no skip.
        "all_passed": summary is not None and summary["failed"] == 0 and summary["skipped"] == 0,
        "groups": groups,
        "failed": failed,
        "skipped": skipped,
    }


def parse_ledger_sources(stdout: str) -> list[tuple[str, str, str]]:
    """`tests --trust-ledger --print`: one `module<TAB>declaration<TAB>item` per line."""
    out = []
    for line in stdout.split("\n"):
        cells = line.split("\t")
        if len(cells) == 3 and all(cells):
            out.append((cells[0], cells[1], cells[2]))
    return out


def compare_ledger(live: list[tuple[str, str, str]], ledger_rows: list[dict[str, str]],
                   complete: bool) -> dict[str, Any]:
    """Live sources against the checked-in ledger: `unreviewed` (live, no row) and, when the
    live scope is the ledger's whole scope, `stale` (a row with no live source)."""
    rows = {(r.get("module", ""), r.get("declaration", ""), r.get("item", "")): r for r in ledger_rows}
    live_set = set(live)
    unreviewed = [{"module": m, "declaration": d, "item": i} for (m, d, i) in sorted(live_set - set(rows))]
    result: dict[str, Any] = {
        "sources": len(live_set),
        "ledger_rows": len(rows),
        "unreviewed": unreviewed,
        "stale": None,
    }
    if complete:
        result["stale"] = [{"module": m, "declaration": d, "item": i} for (m, d, i) in sorted(set(rows) - live_set)]
    else:
        result["stale_note"] = "lib_only: rows for the examples are not compared, so stale rows are not reported"
    modules: dict[str, int] = {}
    for module, _, _ in live_set:
        modules[module] = modules.get(module, 0) + 1
    result["by_module"] = dict(sorted(modules.items()))
    return result
