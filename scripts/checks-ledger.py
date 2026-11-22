#!/usr/bin/env python3
"""A local, gitignored ledger of the light checks that ran on each commit.

The light checks (docs style, the companion lists, the repo subsets, the two
generators) are cheap enough to run before every push, but easy to forget after
an amend or a rebase.  This tool records each run against the exact commit it
ran on, and `.githooks/pre-push` prints a reminder for the registered checks
that have no **clean** record for the commit being pushed.

  * a record is keyed by `(commit, name)`, so `git commit --amend` or a rebase
    makes the old records invisible: a new SHA needs new runs, by design;
  * `dirty` is whether `git status --porcelain` was non-empty **before** the
    command started; `dirty_after` records the same after it finished.  A run is
    clean when it started clean and exited 0.  The two update scripts are
    registered too: on a stale tree they write a file after a clean start, which
    the record shows as `dirty_after` (commit or discard that output); they do
    not turn the run itself into a dirty one;
  * `exit` is the command's exit status; only 0 counts as clean.

This file is **untrusted by design**.  `.checks/` sits in the worktree, nothing
signs it, and any process can edit or delete it.  It is a fast-fail reminder for
a local developer ("did I run this since the last amend?"), never a security
gate, never a merge gate, and CI does not read it.  The pre-push hook that uses
it only warns; it never blocks a push.

Usage
  scripts/checks-ledger.py run NAME [-- COMMAND ...]
        Run a registered check (or COMMAND after `--`) and record it.  Without
        `--`, NAME must be in the CHECKS table below.  The command's exit status
        is returned.
  scripts/checks-ledger.py status
        Show, for HEAD, each registered check's state and the record it comes
        from (clean, dirty, failed, stale@COMMIT, or missing).
  scripts/checks-ledger.py warn [--pre-push] [--commit SHA ...]
        Print the reminder lines for commits with no clean record.  `--pre-push`
        reads git's pre-push stdin (local-ref lines); otherwise the default is
        HEAD, or the given `--commit` shas.  Prints nothing when every
        registered check is clean.  Always exit 0.
  scripts/checks-ledger.py --self-test
        Prove the three behaviours on a throwaway repository: no record warns,
        a clean run stops the warning, a dirty run does not count, and a new
        SHA (amend) warns again.

The registry is the CHECKS table: adding a check is one line.  Commands are
argv lists, run in the repository root.

Exit status: 0 success (a `run` returns its command's status), 1 self-test
failure, 2 usage error or a tree that cannot be read.  `warn` always exits 0,
because the hook must not block a push.
"""

from __future__ import annotations

import json
import os
import shutil
import subprocess
import sys
import tempfile
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LEDGER_DIR = ".checks"
LEDGER_FILE = "records.jsonl"

# The light checks that exist today.  One line per check.  The two update
# scripts are registered too: run on a current tree they write nothing, so they
# can be clean; run on a stale tree they edit a file, which makes that record
# dirty (and the next commit needs its own run).
CHECKS: tuple[tuple[str, tuple[str, ...]], ...] = (
    ("docs-style", ("python3", "scripts/check-docs-style.py")),
    ("companion-lists", ("python3", "scripts/check-companion-lists.py")),
    ("repo-subsets", ("python3", "scripts/repo-subsets.py", "--check")),
    ("legacy-names-digest", ("python3", "scripts/gen-legacy-names.py", "--update-digest")),
    ("repo-subsets-write", ("python3", "scripts/repo-subsets.py", "--write")),
)

CHECK_NAMES = tuple(name for name, _ in CHECKS)
CHECK_COMMANDS = dict(CHECKS)


class Error(Exception):
    """A usage error, or a tree this tool cannot read (exit 2)."""


def git(root: Path, *args: str, stdin: str | None = None) -> subprocess.CompletedProcess[str]:
    try:
        return subprocess.run(
            ["git", *args], cwd=root, input=stdin, capture_output=True, text=True, timeout=120
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise Error(f"cannot run git {' '.join(args)}: {exc}") from exc


def repository_root(start: Path) -> Path:
    proc = git(start, "rev-parse", "--show-toplevel")
    if proc.returncode != 0:
        raise Error(f"{start} is not inside a git checkout")
    return Path(proc.stdout.strip())


def head_commit(root: Path) -> str:
    proc = git(root, "rev-parse", "--verify", "HEAD")
    if proc.returncode != 0:
        raise Error("HEAD is not a commit (an empty repository?)")
    return proc.stdout.strip()


def head_label(root: Path) -> str:
    branch = git(root, "rev-parse", "--abbrev-ref", "HEAD").stdout.strip()
    return branch or "(unknown)"


def porcelain(root: Path) -> list[str]:
    proc = git(root, "status", "--porcelain")
    if proc.returncode != 0:
        raise Error("cannot read `git status --porcelain`")
    return [line for line in proc.stdout.splitlines() if line]


def ledger_path(root: Path) -> Path:
    return root / LEDGER_DIR / LEDGER_FILE


def read_records(root: Path) -> list[dict]:
    """The ledger, in file order.  Malformed lines are skipped: untrusted."""
    path = ledger_path(root)
    try:
        text = path.read_text(encoding="utf-8")
    except FileNotFoundError:
        return []
    except OSError as exc:
        raise Error(f"cannot read {path}: {exc}") from exc
    records = []
    for number, line in enumerate(text.splitlines(), 1):
        if not line.strip():
            continue
        try:
            record = json.loads(line)
        except json.JSONDecodeError:
            continue
        if (
            isinstance(record, dict)
            and isinstance(record.get("commit"), str)
            and isinstance(record.get("name"), str)
        ):
            records.append(record)
    return records


def append_record(root: Path, record: dict) -> None:
    path = ledger_path(root)
    try:
        path.parent.mkdir(parents=True, exist_ok=True)
        with path.open("a", encoding="utf-8") as handle:
            handle.write(json.dumps(record, sort_keys=True) + "\n")
    except OSError as exc:
        raise Error(f"cannot write {path}: {exc}") from exc


def latest(records: list[dict]) -> dict[tuple[str, str], dict]:
    """The last record for each `(commit, name)` key wins."""
    out: dict[tuple[str, str], dict] = {}
    for record in records:
        out[(record["commit"], record["name"])] = record
    return out


def last_for_name(records: list[dict], name: str) -> dict | None:
    for record in reversed(records):
        if record["name"] == name:
            return record
    return None


def is_clean(record: dict | None) -> bool:
    return bool(record) and record.get("exit") == 0 and record.get("dirty") is False


def state_for(record: dict | None, records: list[dict], name: str, commit: str) -> str:
    if record is not None:
        if record.get("exit") != 0:
            return "failed"
        if record.get("dirty") is not False:
            return "dirty"
        return "clean"
    older = last_for_name(records, name)
    if older is not None:
        return f"stale@{older['commit'][:7]}"
    return "missing"


def resolve_command(name: str, command: list[str] | None) -> list[str]:
    if command is not None:
        if not command:
            raise Error("`--` must be followed by a command")
        return command
    registered = CHECK_COMMANDS.get(name)
    if registered is None:
        raise Error(
            f"unknown check {name!r}; registered: {', '.join(CHECK_NAMES)}"
            " (or pass `-- COMMAND ...`)"
        )
    return list(registered)


def run_command(root: Path, name: str, command: list[str]) -> int:
    commit = head_commit(root)
    # Create the ledger directory before the cleanliness probe: if it is not
    # gitignored, that shows up as dirty instead of being silently invisible.
    ledger_path(root).parent.mkdir(parents=True, exist_ok=True)
    before = porcelain(root)
    if before:
        print(
            f"checks-ledger: worktree has {len(before)} uncommitted change(s);"
            " the record will not count as clean",
            file=sys.stderr,
        )
    shown = " ".join(command)
    print(f"checks-ledger: running {name}: {shown}", file=sys.stderr)
    try:
        proc = subprocess.run(command, cwd=root)
        code = proc.returncode
    except FileNotFoundError:
        print(f"checks-ledger: {command[0]}: not found", file=sys.stderr)
        code = 127
    except PermissionError:
        print(f"checks-ledger: {command[0]}: permission denied", file=sys.stderr)
        code = 126
    after = porcelain(root)
    dirty = bool(before)
    record = {
        "commit": commit,
        "name": name,
        "dirty": dirty,
        "dirty_before": bool(before),
        "dirty_after": bool(after),
        "timestamp": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "command": command,
        "exit": code,
    }
    append_record(root, record)
    verdict = "clean" if is_clean(record) else "NOT clean"
    print(
        f"checks-ledger: recorded {name} on {commit[:7]}"
        f" (exit {code}, {verdict})",
        file=sys.stderr,
    )
    if after and not before:
        print(
            "checks-ledger: the command changed the worktree after a clean start;"
            " commit or discard its output (dirty_after)",
            file=sys.stderr,
        )
    return code


def status(root: Path) -> int:
    commit = head_commit(root)
    records = read_records(root)
    index = latest(records)
    print(f"checks-ledger: HEAD {commit[:7]} ({head_label(root)})")
    print(f"  {'check':<20} {'state':<18} {'record':<8} {'when':<21} exit  command")
    clean = 0
    for name, _ in CHECKS:
        record = index.get((commit, name))
        state = state_for(record, records, name, commit)
        if state == "clean":
            clean += 1
            shown = record
        elif record is not None:
            shown = record
        else:
            shown = last_for_name(records, name)
        if shown is None:
            row = ("-", "-", "-", "-")
        else:
            row = (
                shown["commit"][:7],
                str(shown.get("timestamp", "-")),
                str(shown.get("exit", "-")),
                " ".join(shown.get("command", [])),
            )
        print(f"  {name:<20} {state:<18} {row[0]:<8} {row[1]:<21} {row[2]:<5} {row[3]}")
    total = len(CHECKS)
    if clean == total:
        print(f"checks-ledger: {clean} of {total} registered check(s) clean for {commit[:7]}")
    else:
        print(
            f"checks-ledger: warning: {clean} of {total} registered check(s) clean"
            f" for {commit[:7]}; run `python3 scripts/checks-ledger.py run NAME`"
        )
    changed = sum(
        1
        for name, _ in CHECKS
        if (record := index.get((commit, name))) is not None
        and is_clean(record)
        and record.get("dirty_after")
    )
    if changed:
        print(
            f"checks-ledger: note: {changed} clean record(s) modified the worktree"
            " after a clean start (an update script); commit or discard that output"
        )
    print("checks-ledger: local, untrusted reminder; not a security or merge gate")
    return 0


def warn_commits(root: Path, pre_push: bool, commits: list[str]) -> int:
    records = read_records(root)
    index = latest(records)

    targets: list[tuple[str, str]] = []  # (commit, label)
    if pre_push:
        for line in sys.stdin.read().splitlines():
            fields = line.split()
            if len(fields) < 2:
                continue
            local_sha, local_ref = fields[0], fields[1]
            if set(local_sha) == {"0"}:
                continue  # a deletion
            proc = git(root, "rev-parse", "--verify", "--quiet", f"{local_sha}^{{commit}}")
            if proc.returncode != 0 or not proc.stdout.strip():
                continue  # not a commit (for example a tree/notes push)
            targets.append((proc.stdout.strip(), local_ref))
    else:
        for sha in commits or [head_commit(root)]:
            proc = git(root, "rev-parse", "--verify", "--quiet", f"{sha}^{{commit}}")
            if proc.returncode != 0 or not proc.stdout.strip():
                raise Error(f"{sha} is not a commit")
            targets.append((proc.stdout.strip(), sha))

    seen: set[str] = set()
    for commit, label in targets:
        if commit in seen:
            continue
        seen.add(commit)
        missing = []
        for name, _ in CHECKS:
            record = index.get((commit, name))
            if is_clean(record):
                continue
            state = state_for(record, records, name, commit)
            detail = state
            if record is not None and state in ("dirty", "failed"):
                detail = f"{state} run (exit {record.get('exit', '?')})"
            elif state.startswith("stale@"):
                detail = f"last run on {state.split('@', 1)[1]}, not this commit"
            missing.append((name, detail))
        if not missing:
            continue
        print(
            f"checks-ledger: no clean record for {commit[:7]} ({label})"
            " for these registered check(s):",
            file=sys.stderr,
        )
        for name, detail in missing:
            print(f"  {name}: {detail}", file=sys.stderr)
        print(
            "  local reminder only; the push is not blocked."
            " Run: python3 scripts/checks-ledger.py run NAME",
            file=sys.stderr,
        )
    return 0


# --- self-test ---------------------------------------------------------------------


def _tool_run(root: Path, *args: str, expect: int | None = None) -> subprocess.CompletedProcess[str]:
    proc = subprocess.run(
        [sys.executable, str(root / "scripts" / "checks-ledger.py"), *args],
        cwd=root,
        capture_output=True,
        text=True,
    )
    if expect is not None and proc.returncode != expect:
        raise AssertionError(
            f"expected exit {expect}, got {proc.returncode}: {args}\n"
            f"stdout:\n{proc.stdout}\nstderr:\n{proc.stderr}"
        )
    return proc


def _hook_run(root: Path, sha: str) -> subprocess.CompletedProcess[str]:
    hook = root / ".githooks" / "pre-push"
    stdin = f"{sha} refs/heads/main refs/heads/main {'0' * 40}\n"
    proc = subprocess.run(
        ["sh", str(hook)], cwd=root, input=stdin, capture_output=True, text=True
    )
    if proc.returncode != 0:
        raise AssertionError(f"pre-push hook blocked the push (exit {proc.returncode})")
    return proc


def _git(root: Path, *args: str, expect: int = 0) -> subprocess.CompletedProcess[str]:
    proc = subprocess.run(["git", *args], cwd=root, capture_output=True, text=True)
    if proc.returncode != expect:
        raise AssertionError(
            f"git {' '.join(args)} exited {proc.returncode} (wanted {expect})\n"
            f"{proc.stdout}\n{proc.stderr}"
        )
    return proc


def _check(condition: bool, label: str) -> None:
    if not condition:
        raise AssertionError(label)
    print(f"self-test: ok: {label}")


def self_test() -> int:
    """The three behaviours, plus the dirty case, in a temporary repository."""
    source = Path(__file__).resolve()
    hook_source = source.parent.parent / ".githooks" / "pre-push"
    if not hook_source.is_file():
        print(f"checks-ledger: self-test needs {hook_source}", file=sys.stderr)
        return 1
    try:
        with tempfile.TemporaryDirectory(prefix="checks-ledger-selftest-") as tmp:
            root = Path(tmp)
            (root / "scripts").mkdir()
            shutil.copy2(source, root / "scripts" / "checks-ledger.py")
            (root / ".githooks").mkdir()
            shutil.copy2(hook_source, root / ".githooks" / "pre-push")
            (root / ".gitignore").write_text("/.checks/\n", encoding="utf-8")
            (root / "tracked.txt").write_text("one\n", encoding="utf-8")
            _git(root, "init", "-q", "-b", "main")
            _git(root, "config", "user.name", "checks-ledger self-test")
            _git(root, "config", "user.email", "selftest@example.invalid")
            _git(root, "config", "core.hooksPath", ".githooks")
            _git(root, "add", "-A")
            _git(root, "commit", "-q", "-m", "initial")
            first = _git(root, "rev-parse", "HEAD").stdout.strip()

            # 1. No record for the commit: the hook warns, and a push would pass.
            out = _hook_run(root, first)
            _check(
                "no clean record" in (out.stdout + out.stderr),
                "no record -> hook warns (and exits 0)",
            )

            # 2. A clean run of every registered check (the demo command stands
            # in for the real scripts in this throwaway tree): the warning goes
            # away and the tree stays clean.
            for name in CHECK_NAMES:
                _tool_run(root, "run", name, "--", sys.executable, "-c", "pass", expect=0)
            out = _hook_run(root, first)
            _check(
                "no clean record" not in (out.stdout + out.stderr),
                "clean run -> no warning",
            )
            _check(
                _git(root, "status", "--porcelain").stdout == "",
                "the ledger is gitignored (the run left the tree clean)",
            )
            shown = _tool_run(root, "status", expect=0).stdout
            _check(f"{first[:7]}" in shown and "clean" in shown, "status shows the clean record")

            # 2b. A command that writes after a clean start is still a clean
            # *run* (dirty_after records the change); the update scripts are
            # registered for exactly this case.
            _tool_run(
                root,
                "run",
                "docs-style",
                "--",
                sys.executable,
                "-c",
                "open('generated.txt', 'w').write('x')",
                expect=0,
            )
            out = _hook_run(root, first)
            _check(
                "no clean record" not in (out.stdout + out.stderr),
                "clean start + update write -> clean record",
            )
            (root / "generated.txt").unlink()

            # 3. A dirty run is recorded but never counts as clean.
            (root / "tracked.txt").write_text("two\n", encoding="utf-8")
            _tool_run(root, "run", "docs-style", "--", sys.executable, "-c", "pass", expect=0)
            out = _hook_run(root, first)
            text = out.stdout + out.stderr
            _check(
                "docs-style" in text and "dirty" in text,
                "dirty run -> still warns (not clean)",
            )
            shown = _tool_run(root, "status", expect=0).stdout
            _check("dirty" in shown, "status calls the dirty record dirty")

            # ... and a clean rerun after discarding the change restores it.
            _git(root, "checkout", "--", "tracked.txt")
            _tool_run(root, "run", "docs-style", "--", sys.executable, "-c", "pass", expect=0)
            out = _hook_run(root, first)
            _check(
                "no clean record" not in (out.stdout + out.stderr),
                "clean rerun -> no warning again",
            )

            # 4. A new SHA (amend) invalidates the record: the hook warns again.
            _git(root, "commit", "-q", "--amend", "-m", "amended")
            second = _git(root, "rev-parse", "HEAD").stdout.strip()
            _check(first != second, "amend produced a new commit")
            out = _hook_run(root, second)
            text = out.stdout + out.stderr
            _check(
                "no clean record" in text and "docs-style" in text,
                "new SHA -> warns again",
            )
            shown = _tool_run(root, "status", expect=0).stdout
            _check(f"stale@{first[:7]}" in shown, "status reports the old record as stale")
    except (AssertionError, Error, OSError, subprocess.SubprocessError) as exc:
        print(f"checks-ledger: self-test FAILED: {exc}", file=sys.stderr)
        return 1
    print("checks-ledger: self-test passed")
    return 0


# --- command line ------------------------------------------------------------------


def usage() -> None:
    print("usage: checks-ledger.py [--root DIR] run NAME [-- COMMAND ...]", file=sys.stderr)
    print("       checks-ledger.py [--root DIR] status", file=sys.stderr)
    print("       checks-ledger.py [--root DIR] warn [--pre-push] [--commit SHA ...]", file=sys.stderr)
    print("       checks-ledger.py --self-test", file=sys.stderr)


def main(argv: list[str]) -> int:
    root: Path | None = None
    index = 0
    while index < len(argv):
        arg = argv[index]
        if arg == "--root":
            if index + 1 >= len(argv):
                raise Error("--root needs a directory")
            root = Path(argv[index + 1]).resolve()
            index += 2
        elif arg.startswith("--root="):
            root = Path(arg.split("=", 1)[1]).resolve()
            index += 1
        elif arg in ("-h", "--help"):
            usage()
            return 0
        elif arg == "--self-test":
            return self_test()
        elif arg.startswith("-"):
            raise Error(f"unknown option {arg!r}")
        else:
            break

    if index >= len(argv):
        usage()
        raise Error("a command is required")
    command = argv[index]
    args = argv[index + 1 :]
    root = repository_root(root or Path.cwd())

    if command == "run":
        if not args:
            raise Error("run needs a check name")
        name = args[0]
        rest = args[1:]
        explicit: list[str] | None = None
        if rest:
            if rest[0] != "--":
                raise Error(f"unexpected arguments after {name!r}: {' '.join(rest)}")
            explicit = rest[1:]
        return run_command(root, name, resolve_command(name, explicit))
    if command == "status":
        if args:
            raise Error(f"status takes no arguments: {' '.join(args)}")
        return status(root)
    if command == "warn":
        pre_push = False
        commits: list[str] = []
        cursor = 0
        while cursor < len(args):
            if args[cursor] == "--pre-push":
                pre_push = True
                cursor += 1
            elif args[cursor] == "--commit":
                if cursor + 1 >= len(args):
                    raise Error("--commit needs a SHA")
                commits.append(args[cursor + 1])
                cursor += 2
            else:
                raise Error(f"unknown argument to warn: {args[cursor]!r}")
        return warn_commits(root, pre_push, commits)
    usage()
    raise Error(f"unknown command {command!r}")


if __name__ == "__main__":
    try:
        sys.exit(main(sys.argv[1:]))
    except Error as exc:
        print(f"checks-ledger: {exc}", file=sys.stderr)
        sys.exit(2)
