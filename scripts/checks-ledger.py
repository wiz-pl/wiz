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
gate, never a merge gate, and CI does not read it.

The light checks are advisory.  `heavy` (`/workspace/wiz-tools/heavy`, outside
this repository) writes a second kind of record -- `heavy:lake` (or
`heavy:nix-build:ATTR`) for the commit whose tree its Slurm job built -- and
`require` makes *that* one blocking, for pushes to `refs/heads/integration/*`
only.  The reason is the class of red where a branch was pushed for CI before
this exact sha had ever been built: `nix eval` does not run a builder, so only
a build of the *pushed* sha proves that sha compiles.  A merge commit is a new
sha, so the merge result must be built too.  A dirty tree never counts: `heavy`
copies the working tree, so a dirty run built something that is not the commit.

`--no-verify` still bypasses the hook, by design (git's own escape hatch, and
this is a guard against mistakes, not a security gate).  A bypass leaves no
local trace at the moment it happens; `audit` recovers it later, from the
remote-tracking refs: a `refs/remotes/REMOTE/integration/*` tip with no clean
record for its sha is a push that skipped the check, and it is logged to
`.checks/bypass.log`.

Usage
  scripts/checks-ledger.py run NAME [-- COMMAND ...]
        Run a registered check (or COMMAND after `--`) and record it.  Without
        `--`, NAME must be in the CHECKS table below.  The command's exit status
        is returned.
  scripts/checks-ledger.py record --name NAME --commit SHA --exit CODE
                                  [--clean|--dirty] [-- COMMAND ...]
        Write a record for a command that ran elsewhere (`heavy` calls this
        after its Slurm job ends; it never runs anything).  The default for an
        unstated tree is `--dirty`: a record that does not state it was clean
        must never satisfy `require`.  `COMMAND` (after `--`) is the argv, which
        `require` searches for `build`.
  scripts/checks-ledger.py status
        Show, for HEAD, each registered check's state and the record it comes
        from (clean, dirty, failed, stale@COMMIT, or missing), and any other
        record for HEAD by name (the `heavy:*` ones `record` writes).
  scripts/checks-ledger.py warn [--pre-push] [--commit SHA ...]
        Print the reminder lines for commits with no clean record.  `--pre-push`
        reads git's pre-push stdin (local-ref lines); otherwise the default is
        HEAD, or the given `--commit` shas.  Prints nothing when every
        registered check is clean.  Always exit 0.
  scripts/checks-ledger.py require --pre-push --name PATTERN [--name ...]
                                  --for GLOB [--for ...]
        For each pushed ref whose *remote* name matches a `--for` glob, require a
        clean record for the sha being pushed (the new value of the ref) whose
        name matches a `--name` pattern and whose argv contains `build`.  Prints
        the sha and the best reason it has (`missing`, `dirty`, `failed`,
        `stale@COMMIT`, `not-a-build`) and exits 1 when one is missing; refs
        outside the globs are not checked.  The pre-push hook runs it for
        `refs/heads/integration/*`.
  scripts/checks-ledger.py audit [--for GLOB ...] [--name PATTERN ...] [--fetch]
        Report (and append to `.checks/bypass.log`) every
        `refs/remotes/REMOTE/...` tip that matches a `--for` glob and has no
        clean record: a push that took the `--no-verify` escape hatch, seen on
        the next fetch.  `--fetch` fetches first.  Always exits 0.
  scripts/checks-ledger.py --self-test
        Prove the behaviours on a throwaway repository: no record warns, a clean
        run stops the warning, a dirty run does not count, a new SHA (amend)
        warns again, and `require` refuses a push to `integration/*` without a
        clean build record for that sha (but not to other refs).

The registry is the CHECKS table: adding a check is one line.  Commands are
argv lists, run in the repository root.

Exit status: 0 success; a `run` returns its command's status even when that is
nonzero.  1 means a failed self-test or a refused push (`require`), 2 a usage
error or a tree that cannot be read.  `warn` and `audit` always exit 0, because
neither may block a push.
"""

from __future__ import annotations

import fnmatch
import json
import shlex
import shutil
import subprocess
import sys
import tempfile
from datetime import datetime, timezone
from pathlib import Path

LEDGER_DIR = ".checks"
LEDGER_FILE = "records.jsonl"
BYPASS_FILE = "bypass.log"
# The push guard (`require`) is for integration pushes only: every other branch
# is a work in progress, and a build per amend would tax the scarce heavy slots.
INTEGRATION_REFS = "refs/heads/integration/*"

# The light checks that exist today.  One line per check.  The two update
# scripts are registered too: on a current tree they normally write nothing,
# and when one does write (repo-subsets --write refreshes its informational
# `git` field) the run started clean, so `dirty_after` records the output that
# still needs committing or discarding.
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
        text = path.read_text(encoding="utf-8", errors="replace")
    except FileNotFoundError:
        return []
    except OSError as exc:
        raise Error(f"cannot read {path}: {exc}") from exc
    records = []
    for line in text.splitlines():
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


def state_for(record: dict | None, records: list[dict], name: str) -> str:
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
    try:
        ledger_path(root).parent.mkdir(parents=True, exist_ok=True)
    except OSError as exc:
        raise Error(f"cannot create {ledger_path(root).parent}: {exc}") from exc
    before = porcelain(root)
    if before:
        print(
            f"checks-ledger: worktree has {len(before)} uncommitted change(s);"
            " the record will not count as clean",
            file=sys.stderr,
        )
    shown = shlex.join(command)
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
    def row_for(name: str, record: dict | None) -> str:
        state = state_for(record, records, name)
        shown = record if record is not None else last_for_name(records, name)
        if shown is None:
            row = ("-", "-", "-", "-")
        else:
            row = (
                shown["commit"][:7],
                str(shown.get("timestamp", "-")),
                str(shown.get("exit", "-")),
                " ".join(record_argv(shown)) or " ".join(shown.get("command", [])),
            )
        return f"  {name:<20} {state:<18} {row[0]:<8} {row[1]:<21} {row[2]:<5} {row[3]}"
    for name, _ in CHECKS:
        record = index.get((commit, name))
        if record is not None and is_clean(record):
            clean += 1
        print(row_for(name, record))
    # The records `heavy`/`record` write are not in the registry: show every one for
    # HEAD by name (a build record is what `require` reads, so it must be visible).
    extra = sorted(name for c, name in index if c == commit and name not in CHECK_NAMES)
    for name in extra:
        print(row_for(name, index[(commit, name)]))
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
            state = state_for(record, records, name)
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


# --- the build record (`heavy` writes it) and the push guard (`require`) -------------


def record_command(root: Path, args: list[str]) -> int:
    """`record`: append a record for a command that ran elsewhere, without running it.

    `heavy` calls this when its Slurm job ends, with the commit and the cleanliness
    it captured at submit time and the command it ran.  It runs nothing, so it can
    record a job whose tree is on another node.

    `--clean`/`--dirty` state whether the tree had uncommitted changes at submit.
    The **default is dirty**: a record that does not state its tree was clean must
    never satisfy `require` (the safe direction for a guard that cannot verify it).
    """
    name: str | None = None
    commit: str | None = None
    code: int | None = None
    dirty = True
    command: list[str] = []
    cursor = 0
    while cursor < len(args):
        arg = args[cursor]
        if arg == "--":
            command = args[cursor + 1:]
            cursor = len(args)
        elif arg == "--name":
            if cursor + 1 >= len(args):
                raise Error("--name needs a value")
            name = args[cursor + 1]
            cursor += 2
        elif arg == "--commit":
            if cursor + 1 >= len(args):
                raise Error("--commit needs a SHA")
            commit = args[cursor + 1]
            cursor += 2
        elif arg == "--exit":
            if cursor + 1 >= len(args):
                raise Error("--exit needs a status")
            try:
                code = int(args[cursor + 1])
            except ValueError as exc:
                raise Error(f"--exit needs an integer, not {args[cursor + 1]!r}") from exc
            cursor += 2
        elif arg == "--clean":
            dirty = False
            cursor += 1
        elif arg == "--dirty":
            dirty = True
            cursor += 1
        else:
            raise Error(f"unknown argument to record: {arg!r} (the command follows `--`)")
    if name is None:
        raise Error("record needs --name")
    proc = git(root, "rev-parse", "--verify", "--quiet", f"{commit or 'HEAD'}^{{commit}}")
    if proc.returncode != 0 or not proc.stdout.strip():
        raise Error(f"{commit or 'HEAD'} is not a commit")
    commit = proc.stdout.strip()
    record = {
        "commit": commit,
        "name": name,
        "dirty": dirty,
        "dirty_before": dirty,
        "dirty_after": None,  # the command ran on another node; this tree did not
        "timestamp": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "command": command,
        "exit": code,
    }
    append_record(root, record)
    verdict = "clean" if is_clean(record) else "NOT clean"
    shown = " ".join(command) or "(no command)"
    print(
        f"checks-ledger: recorded {name} on {commit[:7]} (exit {code}, {verdict}): {shown}",
        file=sys.stderr,
    )
    return 0


def record_argv(record: dict) -> list[str]:
    """A record's argv.  `command` is this ledger's key; `argv` the name the guard's
    brief uses (accepted too, so an externally written record need not guess)."""
    for key in ("command", "argv"):
        argv = record.get(key)
        if isinstance(argv, list):
            return [str(a) for a in argv]
    return []


def is_build_record(record: dict) -> bool:
    """Whether the record's command builds: `lake build wiz tests`, `nix build .#wiz`,
    ...  `nix eval`, `lake test` and `lake exe` do not: evaluation does not run a
    builder, so it cannot prove that the tree compiles (a buildPhase bug or a missing
    runtime flag passes evaluation)."""
    return "build" in record_argv(record)


def required_state(records: list[dict], commit: str, patterns: list[str]) -> tuple[str, dict | None]:
    """Why `commit` does or does not satisfy the requirement, and the record it came
    from: `("clean", record)` or a reason (`missing`, `dirty`, `failed`,
    `stale@COMMIT`, `not-a-build`) with the latest record of a matching name."""
    def named(record: dict) -> bool:
        return any(fnmatch.fnmatchcase(record["name"], p) for p in patterns)

    here = [r for r in records if r["commit"] == commit and named(r)]
    if here:
        for record in reversed(here):
            if is_clean(record) and is_build_record(record):
                return "clean", record
        latest = here[-1]
        if latest.get("exit") != 0:
            return f"failed (exit {latest.get('exit', '?')})", latest
        if latest.get("dirty") is not False:
            return "dirty", latest
        return "not-a-build", latest
    older = [r for r in records if named(r)]
    if older:
        return f"stale@{older[-1]['commit'][:7]}", older[-1]
    return "missing", None


def pushed_refs(root: Path, patterns: list[str]) -> list[tuple[str, str]]:
    """The (commit, remote ref) pairs a pre-push stdin says are being pushed to a ref
    matching `patterns`.  A deletion pushes no commit and is skipped; the sha checked
    is the ref's *new* value (`local sha`), because that is the tree CI would build --
    the remote sha on the same line is the tip being replaced."""
    targets: list[tuple[str, str]] = []
    for line in sys.stdin.read().splitlines():
        fields = line.split()
        if len(fields) < 3:
            continue
        local_sha, remote_ref = fields[0], fields[2]
        if set(local_sha) == {"0"}:
            continue
        if not any(fnmatch.fnmatchcase(remote_ref, p) for p in patterns):
            continue
        proc = git(root, "rev-parse", "--verify", "--quiet", f"{local_sha}^{{commit}}")
        if proc.returncode != 0 or not proc.stdout.strip():
            continue
        targets.append((proc.stdout.strip(), remote_ref))
    return targets


def require_refs(root: Path, names: list[str], ref_globs: list[str]) -> int:
    """`require --pre-push`: 0 when every pushed integration ref has a clean build
    record for its new sha, 1 when one does not (and says which and why)."""
    if not names:
        raise Error("require needs at least one --name")
    records = read_records(root)
    refused: list[tuple[str, str, str]] = []
    for commit, remote_ref in pushed_refs(root, ref_globs):
        detail, record = required_state(records, commit, names)
        if detail == "clean":
            print(
                f"checks-ledger: {commit[:7]} -> {remote_ref}: clean build record"
                f" ({record['name']}, {' '.join(record_argv(record))})",
                file=sys.stderr,
            )
            continue
        refused.append((commit, remote_ref, detail))
    if not refused:
        return 0
    for commit, remote_ref, detail in refused:
        print(
            f"checks-ledger: refusing to push {commit} to {remote_ref}: {detail}",
            file=sys.stderr,
        )
    print(
        "checks-ledger: this exact sha has no clean build record, and evaluation is not"
        " a build (`nix eval` never runs the builder). Build it first, from a clean tree:"
        "\n  heavy --rsync -- lake build wiz tests   # or, for one derivation:"
        "\n  heavy --sshfs -- nix build .#ATTR --no-link",
        file=sys.stderr,
    )
    print(
        "checks-ledger: a merge commit is a new sha, so build the merge result."
        " (`git push --no-verify` bypasses this; `audit` lists the remote tips"
        " afterwards that this ledger cannot explain.)",
        file=sys.stderr,
    )
    return 1


def audit_refs(root: Path, names: list[str], ref_globs: list[str], remote: str, fetch: bool) -> int:
    """`audit`: list remote-tracking tips that this worktree's ledger cannot explain.

    It cannot see a bypassed push itself (`--no-verify` never runs a hook), but the
    remote-tracking ref is the evidence afterwards: this ref, at this sha, has no clean
    record *here*.  Another clone's worktree may hold the record (`.checks/` is
    per-worktree, by design), so this is a lead to check, not a verdict; it is logged
    once per (ref, sha) to `.checks/bypass.log`, and never fails anything."""
    if fetch:
        proc = git(root, "fetch", "--quiet", remote)
        if proc.returncode != 0:
            print(f"checks-ledger: fetch {remote} failed: {proc.stderr.strip()}", file=sys.stderr)
    prefix = f"refs/remotes/{remote}/"
    listing = git(root, "for-each-ref", "--format=%(refname) %(objectname)", prefix)
    if listing.returncode != 0:
        raise Error(f"cannot list {prefix}")
    records = read_records(root)
    log = root / LEDGER_DIR / BYPASS_FILE
    try:
        logged_before = log.read_text(encoding="utf-8", errors="replace").splitlines()
    except OSError:
        logged_before = []
    known = {tuple(line.split("\t")[1:3]) for line in logged_before if line.count("\t") >= 3}
    logged = 0
    for line in listing.stdout.splitlines():
        ref, _, sha = line.partition(" ")
        branch = "refs/heads/" + ref[len(prefix):]
        if not any(fnmatch.fnmatchcase(branch, g) for g in ref_globs):
            continue
        detail, _ = required_state(records, sha.strip(), names)
        if detail == "clean":
            continue
        if (sha.strip(), branch) in known:
            continue
        logged += 1
        entry = f"{datetime.now(timezone.utc).strftime('%Y-%m-%dT%H:%M:%SZ')}\t{sha.strip()}\t{branch}\t{detail}"
        try:
            log.parent.mkdir(parents=True, exist_ok=True)
            with log.open("a", encoding="utf-8") as handle:
                handle.write(entry + "\n")
        except OSError as exc:
            print(f"checks-ledger: cannot write {log}: {exc}", file=sys.stderr)
        print(
            f"checks-ledger: {branch} is at {sha.strip()[:7]}, which has no clean build"
            f" record in this worktree's ledger ({detail});"
            f" logged to {LEDGER_DIR}/{BYPASS_FILE}",
            file=sys.stderr,
        )
    if not logged:
        print(f"checks-ledger: every {remote} ref matching {', '.join(ref_globs)} has a clean build record")
    return 0


# --- self-test ---------------------------------------------------------------------


def _tool_run(root: Path, *args: str, expect: int | None = None,
              stdin: str | None = None) -> subprocess.CompletedProcess[str]:
    proc = subprocess.run(
        [sys.executable, str(root / "scripts" / "checks-ledger.py"), *args],
        cwd=root,
        input=stdin,
        capture_output=True,
        text=True,
    )
    if expect is not None and proc.returncode != expect:
        raise AssertionError(
            f"expected exit {expect}, got {proc.returncode}: {args}\n"
            f"stdout:\n{proc.stdout}\nstderr:\n{proc.stderr}"
        )
    return proc


def _require(root: Path, sha: str, remote_ref: str) -> subprocess.CompletedProcess[str]:
    """A pre-push line as git writes it, through `require` (stdin, exactly as the hook
    does it): `<local ref> <local sha> <remote ref> <remote sha>`."""
    stdin = f"{sha} refs/heads/local {remote_ref} {'0' * 40}\n"
    return _tool_run(root, "require", "--pre-push", "--name", "heavy:lake",
                     "--for", INTEGRATION_REFS, stdin=stdin)


def _commit(root: Path, message: str) -> str:
    """A new commit, so a test has a sha that no record mentions yet."""
    (root / "tracked.txt").write_text(message + "\n", encoding="utf-8")
    _git(root, "add", "-A")
    _git(root, "commit", "-q", "-m", message)
    return _git(root, "rev-parse", "HEAD").stdout.strip()


def _hook_ref(root: Path, sha: str, remote_ref: str) -> subprocess.CompletedProcess[str]:
    """The pre-push hook, fed one pushed ref (its exit status is the verdict)."""
    hook = root / ".githooks" / "pre-push"
    stdin = f"{sha} refs/heads/local {remote_ref} {'0' * 40}\n"
    return subprocess.run(
        ["sh", str(hook)], cwd=root, input=stdin, capture_output=True, text=True
    )



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

            # 5. `require`: a push to integration/* needs a clean BUILD record for the
            # sha being pushed.  With no record at all the reason is `missing`.
            _check(_require(root, second, "refs/heads/integration/train9").returncode == 1,
                   "no record for the sha -> push refused (exit 1)")
            out = _require(root, second, "refs/heads/integration/train9")
            _check("missing" in (out.stdout + out.stderr), "... and the reason is missing")
            _check(_require(root, second, "refs/heads/agent/someone").returncode == 0,
                   "a push to agent/* is not checked (no record needed)")

            # 6. `record` + `status` show a build record written elsewhere (what `heavy`
            # does after its Slurm job; the command is not run here), and it satisfies
            # the guard for that exact sha.
            third = _commit(root, "third")
            _tool_run(root, "record", "--name", "heavy:lake", "--commit", third,
                      "--exit", "0", "--clean", "--", "lake", "build", "wiz", "tests",
                      expect=0)
            shown = _tool_run(root, "status", expect=0).stdout
            _check("heavy:lake" in shown and "clean" in shown,
                   "record followed by status shows heavy:lake clean")
            out = _require(root, third, "refs/heads/integration/train9")
            _check(out.returncode == 0, "a clean heavy:lake record for the sha -> push accepted")
            _check("clean build record" in (out.stdout + out.stderr),
                   "the accepted push names the record it found")

            # 7. A record for the PARENT sha only is stale, not clean: an amend, a rebase
            # or a merge is a new sha, and only a build of *that* sha is evidence.
            fourth = _commit(root, "fourth")
            parent = _git(root, "rev-parse", f"{fourth}^").stdout.strip()
            _check(parent == third, "the test commit's parent is the recorded sha")
            out = _require(root, fourth, "refs/heads/integration/train9")
            _check(out.returncode == 1 and f"stale@{third[:7]}" in (out.stdout + out.stderr),
                   "a record for the parent sha only -> refused as stale@parent")

            # ... a dirty record never counts: the tree that ran was not the commit.
            _tool_run(root, "record", "--name", "heavy:lake", "--commit", fourth,
                      "--exit", "0", "--dirty", "--", "lake", "build", "wiz", "tests",
                      expect=0)
            out = _require(root, fourth, "refs/heads/integration/train9")
            _check(out.returncode == 1 and "dirty" in (out.stdout + out.stderr),
                   "a dirty build record -> push refused (dirty)")

            # ... a failed build is not a build that passed.
            _tool_run(root, "record", "--name", "heavy:lake", "--commit", fourth,
                      "--exit", "2", "--clean", "--", "lake", "build", "wiz", "tests",
                      expect=0)
            out = _require(root, fourth, "refs/heads/integration/train9")
            _check(out.returncode == 1 and "failed" in (out.stdout + out.stderr),
                   "a failed build record -> push refused (failed)")

            # ... and evaluation is not a build: the argv must contain `build`.
            _tool_run(root, "record", "--name", "heavy:lake", "--commit", fourth,
                      "--exit", "0", "--clean", "--", "lake", "test", "--", "=library",
                      expect=0)
            out = _require(root, fourth, "refs/heads/integration/train9")
            _check(out.returncode == 1 and "not-a-build" in (out.stdout + out.stderr),
                   "a clean record of a non-build command -> push refused (not-a-build)")

            # ... and the clean build record the guard wants makes it pass.
            _tool_run(root, "record", "--name", "heavy:lake", "--commit", fourth,
                      "--exit", "0", "--clean", "--", "lake", "build", "wiz", "tests",
                      expect=0)
            out = _require(root, fourth, "refs/heads/integration/train9")
            _check(out.returncode == 0, "a clean build record for the push's sha -> accepted")

            # 7. The hook propagates the refusal, so a push cannot proceed by accident.
            _git(root, "update-ref", "refs/remotes/origin/integration/train9", first)
            hook = _hook_ref(root, fourth, "refs/heads/integration/train9")
            _check(hook.returncode == 0, "the hook accepts an integration push with a record")
            hook = _hook_ref(root, first, "refs/heads/integration/train9")
            _check(hook.returncode == 1 and "refusing to push" in hook.stdout + hook.stderr,
                   "the hook refuses an integration push without a record (exit 1)")

            # 8. `audit` logs a remote tip that no clean record explains: the trace a
            # `--no-verify` push leaves behind.
            _tool_run(root, "audit", "--for", "refs/heads/integration/*", expect=0)
            bypass = root / ".checks" / "bypass.log"
            _check(bypass.is_file() and first[:7] in bypass.read_text(encoding="utf-8"),
                   "audit logs a bypassed push (the remote tip has no record)")

    except (AssertionError, Error, OSError, subprocess.SubprocessError) as exc:
        print(f"checks-ledger: self-test FAILED: {exc}", file=sys.stderr)
        return 1
    print("checks-ledger: self-test passed")
    return 0


# --- command line ------------------------------------------------------------------


def usage() -> None:
    print("usage: checks-ledger.py [--root DIR] run NAME [-- COMMAND ...]", file=sys.stderr)
    print("       checks-ledger.py [--root DIR] record --name NAME --commit SHA --exit CODE"
          " [--clean|--dirty] [-- COMMAND ...]", file=sys.stderr)
    print("       checks-ledger.py [--root DIR] status", file=sys.stderr)
    print("       checks-ledger.py [--root DIR] warn [--pre-push] [--commit SHA ...]", file=sys.stderr)
    print("       checks-ledger.py [--root DIR] require --pre-push --name PATTERN --for GLOB",
          file=sys.stderr)
    print("       checks-ledger.py [--root DIR] audit [--for GLOB ...] [--name PATTERN ...]"
          " [--remote NAME] [--fetch]", file=sys.stderr)
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
    if command == "record":
        return record_command(root, args)
    if command == "require":
        pre_push = False
        names: list[str] = []
        refs: list[str] = []
        cursor = 0
        while cursor < len(args):
            arg = args[cursor]
            if arg == "--pre-push":
                pre_push = True
                cursor += 1
            elif arg in ("--name", "--for"):
                if cursor + 1 >= len(args):
                    raise Error(f"{arg} needs a value")
                (names if arg == "--name" else refs).append(args[cursor + 1])
                cursor += 2
            else:
                raise Error(f"unknown argument to require: {arg!r}")
        if not pre_push:
            raise Error("require reads git's pre-push stdin: --pre-push is required")
        if not refs:
            raise Error("require needs at least one --for GLOB (there is no default ref)")
        return require_refs(root, names, refs)
    if command == "audit":
        names: list[str] = []
        refs: list[str] = []
        remote = "origin"
        fetch = False
        cursor = 0
        while cursor < len(args):
            arg = args[cursor]
            if arg in ("--name", "--for", "--remote"):
                if cursor + 1 >= len(args):
                    raise Error(f"{arg} needs a value")
                if arg == "--name":
                    names.append(args[cursor + 1])
                elif arg == "--for":
                    refs.append(args[cursor + 1])
                else:
                    remote = args[cursor + 1]
                cursor += 2
            elif arg == "--fetch":
                fetch = True
                cursor += 1
            else:
                raise Error(f"unknown argument to audit: {arg!r}")
        return audit_refs(root, names or ["heavy:*"], refs or [INTEGRATION_REFS], remote, fetch)

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
