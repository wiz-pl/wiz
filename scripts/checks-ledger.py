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
`heavy:nix-build:ATTR`, or `heavy:nix`) for the commit whose tree its Slurm job
built -- and `require` makes *that* one blocking, for pushes to
`refs/heads/integration/*` only.  The reason is the class of red where a branch
was pushed for CI before this exact sha had ever been built: `nix eval` does not
run a builder, so only a build of the *pushed* sha proves that sha compiles.  A
merge commit is a new sha, so the merge result must be built too.  A dirty tree
never counts: `heavy` copies the working tree, so a dirty run built something
that is not the commit.

What counts as a build is decided from the record's own argv (`build_evidence`),
because the name is only `heavy:<program>`: `lake build` with no target (the
default build) or with both `wiz` and `tests`, `lake test` (it compiles and links
the test driver before it runs anything) or `nix build` (every package in this
flake either is, or depends on, the `unwrapped` derivation whose buildPhase is
`lake build wiz grail tests`).  A single `lake build Wiz.Lexer` is a partial
build and does not count.  A `bash -c '...'` wrapper is not read as a build: its
argv has no `build` element, and a shell script can run anything.

The ledger is per-worktree, but a sha is a sha: `require` reads every worktree of
this checkout (`git worktree list`) and every `/workspace/wt/*` checkout, keyed by
commit, so a build in one tree satisfies a push from another.  A push from a tree
that never built, in a machine that did, must not be refused.

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
        `require` reads to tell a build from an evaluation.
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
        name matches a `--name` pattern and whose argv is a build of the whole
        tree (`build_evidence`: the default `lake build`, `lake build wiz tests`,
        `lake test`, or `nix build`).  Prints the sha and the best reason it has
        (`missing`, `dirty`, `failed`, `stale@COMMIT`, `not-a-build`,
        `partial-build`) and exits 1 when one is missing; refs outside the globs
        are not checked.  The records come from every worktree of this checkout,
        keyed by commit, so the tree that built need not be the tree that pushes.
        The pre-push hook runs it for `refs/heads/integration/*` with the three
        names `heavy` writes: `heavy:lake`, `heavy:nix-build:*`, `heavy:nix`.
  scripts/checks-ledger.py audit [--for GLOB ...] [--name PATTERN ...] [--fetch]
        Report (and append to `.checks/bypass.log`) every
        `refs/remotes/REMOTE/...` tip that matches a `--for` glob and has no
        clean record in any worktree of this checkout: a push that took the
        `--no-verify` escape hatch, seen on the next fetch.  `--fetch` fetches
        first.  Always exits 0.
  scripts/checks-ledger.py --self-test
        Prove the behaviours on a throwaway repository: no record warns, a clean
        run stops the warning, a dirty run does not count, a new SHA (amend)
        warns again, and `require` refuses a push to `integration/*` without a
        clean build record for that sha (but not to other refs) and accepts the
        build shapes `heavy` actually writes, including one recorded in another
        worktree.

The registry is the CHECKS table: adding a check is one line.  Commands are
argv lists, run in the repository root.

Exit status: 0 success; a `run` returns its command's status even when that is
nonzero.  1 means a failed self-test or a refused push (`require`), 2 a usage
error or a tree that cannot be read.  `warn` and `audit` always exit 0, because
neither may block a push.  `require` exits 2 when it cannot answer, and
`.githooks/pre-push` turns that into a loud warning and lets the push through:
cannot-answer is a migration state, not a verdict, while exit 1 (a red record)
blocks.
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
# The record names `heavy` writes for a build, and `.githooks/pre-push` passes to
# `require`.  A `nix build` is named `heavy:nix-build:<attr>` (one record per
# attribute; scripts/touched-derivations.sh relies on that), so a bare
# `heavy:lake` pattern could never match it -- the refusal used to recommend
# `nix build` and then refuse the record it wrote.
GUARD_NAMES: tuple[str, ...] = ("heavy:lake", "heavy:nix-build:*", "heavy:nix")
# `require` reads every worktree of this checkout (`git worktree list`), because a
# sha built in one tree is the same sha when pushed from another.  Sibling
# checkouts of another clone on this machine are read too: this host keeps its
# lanes under /workspace/wt, and the coordinator pushes trains from a different
# tree than the lane that built them.
SIBLING_CHECKOUTS = "/workspace/wt/*"

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


def read_ledger(path: Path) -> list[dict]:
    """One ledger file, in file order.  Malformed lines are skipped: untrusted."""
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


def read_records(root: Path) -> list[dict]:
    """This worktree's ledger."""
    return read_ledger(ledger_path(root))


def worktree_roots(root: Path) -> list[Path]:
    """This tree, the repository's other worktrees, then the sibling checkouts.

    `git worktree list` is the authoritative set for this repository (the main
    checkout included, wherever it is).  The `/workspace/wt/*` glob covers a
    worktree of a *different clone* of the same repository: a commit sha is the
    same sha there, so a build record for it is the same evidence.  Entries that
    are not checkouts are skipped by the cheap `.git` probe rather than a `git`
    call per directory (there are hundreds here)."""
    roots: list[Path] = [root]
    proc = git(root, "worktree", "list", "--porcelain")
    if proc.returncode == 0:
        for line in proc.stdout.splitlines():
            if line.startswith("worktree "):
                candidate = Path(line[len("worktree "):].strip())
                if candidate not in roots:
                    roots.append(candidate)
    try:
        base, _, pattern = SIBLING_CHECKOUTS.rpartition("/")
        siblings = sorted(Path(base).glob(pattern))
    except OSError:
        siblings = []
    for sibling in siblings:
        if sibling not in roots and (sibling / ".git").exists():
            roots.append(sibling)
    return roots


def read_all_records(root: Path) -> list[dict]:
    """The records of every worktree that can explain this repository's shas.

    Each record carries the tree it was read from as `_worktree`, so a refusal
    can say where the evidence it found lives (and where a dirty build was
    dirty).  An unreadable *other* ledger is a warning, not a failure: the local
    one decides whether this tool can answer at all."""
    records: list[dict] = []
    for index, tree in enumerate(worktree_roots(root)):
        path = ledger_path(tree)
        try:
            found = read_ledger(path)
        except Error as exc:
            if index == 0:
                raise
            print(f"checks-ledger: warning: {exc}; continuing without it", file=sys.stderr)
            continue
        for record in found:
            record["_worktree"] = str(tree)
        records.extend(found)
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
    # `require` reads every worktree, so a build recorded elsewhere still lets this
    # tree push; say so, or `status` looks like a missing build.
    elsewhere = []
    for tree in worktree_roots(root)[1:]:
        try:
            theirs = read_ledger(ledger_path(tree))
        except Error:
            continue
        for record in theirs:
            if record["commit"] == commit and is_build_record(record) and is_clean(record):
                elsewhere.append(f"{record['name']} in {tree}")
    if elsewhere:
        print(
            f"checks-ledger: note: {len(elsewhere)} clean build record(s) for {commit[:7]}"
            f" in another worktree: {', '.join(elsewhere)}"
        )
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


# What a `/wiz` build compiles: the compiler executable and the test driver.  CI's
# strong build is `nix build .#wiz .#tests` (ci.yml) and `flake.nix`'s unwrapped
# buildPhase is `lake build wiz grail tests`; `scripts/agent-preamble` has the same
# rule for a local run (`lake build wiz tests`).  A bare `lake build` builds the
# default targets, which is what the packages do too.
FULL_LAKE_TARGETS = ("wiz", "tests")


def build_evidence(record: dict) -> str:
    """`build` when the record's own argv is a build of the whole tree, else why not.

    The *name* is not enough: `heavy` names a record after the program, so every
    shape below arrives as `heavy:lake` (or `heavy:nix-build:<attr>`, `heavy:nix`),
    and the argv is the evidence:

      * `lake test` compiles and links the test driver before it runs a case, so it
        is a build and a stronger one than `lake build wiz` (R5);
      * `lake build` with no target is the default build; with targets it must name
        both `wiz` and `tests`.  `lake build Wiz.Lexer` (one module) or `lake build
        wiz` alone is a `partial-build`, not evidence for the whole sha (A1);
      * `nix build` counts: every package in this flake either is, or depends on,
        `unwrapped`, whose buildPhase is `lake build wiz grail tests`.  Counting an
        attribute by name would need a fragile allowlist of a dependency graph;
      * `nix eval`, `lake exe`, a test binary run, ... are `not-a-build`: no builder
        ran.  A `bash -c 'lake build wiz tests'` wrapper is `not-a-build` too -- the
        element after `-c` is one string, and a shell script can run anything, so
        the matcher deliberately reads whole argv elements only (R2)."""
    argv = record_argv(record)
    if not argv:
        return "not-a-build"
    program = Path(argv[0]).name
    words = argv[1:]
    if program == "lake" and words[:1] == ["test"]:
        return "build"
    if "build" not in words:
        return "not-a-build"
    if program == "nix":
        return "build"
    targets = [
        word for word in words[words.index("build") + 1:]
        if word != "--" and not word.startswith("-")
    ]
    if targets and not set(FULL_LAKE_TARGETS) <= {t.split(":", 1)[0] for t in targets}:
        return "partial-build"
    return "build"


def is_build_record(record: dict) -> bool:
    return build_evidence(record) == "build"


def recent_history(root: Path, commit: str, limit: int = 200) -> set[str]:
    """The commits near `commit`'s own history, for telling `stale@` from `missing`.

    `require` reads every worktree on the machine, so *some* `heavy:*` record
    almost always exists -- for another branch, another train, another lane.  A
    record on an unrelated commit is not a stale attempt at this one: it is
    absent.  One `rev-list` per pushed sha answers it (a record older than
    `limit` commits back is not "the build before your amend" either)."""
    proc = git(root, "rev-list", f"--max-count={limit}", commit)
    if proc.returncode != 0:
        return {commit}
    return set(proc.stdout.split()) | {commit}


def required_state(records: list[dict], commit: str, patterns: list[str],
                   history: set[str] | None = None) -> tuple[str, dict | None]:
    """Why `commit` does or does not satisfy the requirement, and the record it came
    from: `("clean", record)` or a reason (`missing`, `dirty`, `failed`,
    `stale@COMMIT`, `not-a-build`, `partial-build`) with the latest record of a
    matching name."""
    def named(record: dict) -> bool:
        return any(fnmatch.fnmatchcase(record["name"], p) for p in patterns)

    # Newest first: the records come from many ledgers in directory order, so
    # `timestamp` (ISO-8601, so it sorts) is what says which run was last.
    here = sorted((r for r in records if r["commit"] == commit and named(r)),
                  key=lambda r: str(r.get("timestamp", "")))
    if here:
        for record in reversed(here):
            if is_clean(record) and is_build_record(record):
                return "clean", record
        latest = here[-1]
        if latest.get("exit") != 0:
            return f"failed (exit {latest.get('exit', '?')})", latest
        if latest.get("dirty") is not False:
            return "dirty", latest
        return build_evidence(latest), latest
    older = [r for r in records
             if named(r) and (history is None or r["commit"] in history)]
    if older:
        newest = max(older, key=lambda r: str(r.get("timestamp", "")))
        return f"stale@{newest['commit'][:7]}", newest
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


def dirty_paths(record: dict, limit: int = 8) -> str:
    """The uncommitted paths of the tree a `dirty` record came from (R4).

    `dirty` is any `git status --porcelain` output, which includes untracked files:
    a stray log or a probe file turns a real build of HEAD into a refusal.  Naming
    the paths is the difference between an obvious one-line fix and a mystery (and
    a `--no-verify`)."""
    tree = record.get("_worktree") or ""
    if not tree:
        return ""
    proc = git(Path(tree), "status", "--porcelain")
    if proc.returncode != 0:
        return f"\n  (could not read `git status` in {tree})"
    paths = []
    for line in proc.stdout.splitlines():
        if not line.strip():
            continue
        path = line[3:].strip() if len(line) > 3 else line.strip()
        if " -> " in path:  # a rename shows both names
            path = path.split(" -> ", 1)[1]
        paths.append(path)
    if not paths:
        return f"\n  {tree} is clean now; rebuild there to record a clean build"
    shown = ", ".join(paths[:limit])
    more = "" if len(paths) <= limit else f" (+{len(paths) - limit} more)"
    return (
        f"\n  {tree}: {shown}{more}"
        "\n  commit, stash or .gitignore them, then rebuild (a dirty build is not of the commit)"
    )


def require_refs(root: Path, names: list[str], ref_globs: list[str]) -> int:
    """`require --pre-push`: 0 when every pushed integration ref has a clean build
    record for its new sha, 1 when one does not (and says which and why)."""
    if not names:
        raise Error("require needs at least one --name")
    # Every worktree, not just this one: a lane builds in /workspace/wt/X and the
    # train is pushed from another tree (R3).  A sha is a sha.
    records = read_all_records(root)
    refused: list[tuple[str, str, str, dict | None]] = []
    histories: dict[str, set[str]] = {}
    for commit, remote_ref in pushed_refs(root, ref_globs):
        if commit not in histories:
            histories[commit] = recent_history(root, commit)
        detail, record = required_state(records, commit, names, histories[commit])
        if detail == "clean":
            where = record.get("_worktree")
            origin = ""
            if where and Path(where).resolve() != root.resolve():
                origin = f" in {where}"
            print(
                f"checks-ledger: {commit[:7]} -> {remote_ref}: clean build record"
                f" ({record['name']}, {shlex.join(record_argv(record))}){origin}",
                file=sys.stderr,
            )
            continue
        refused.append((commit, remote_ref, detail, record))
    if not refused:
        return 0
    for commit, remote_ref, detail, record in refused:
        where = ""
        if record is not None and record.get("_worktree"):
            where = f" (record from {record['_worktree']})"
        print(
            f"checks-ledger: refusing to push {commit} to {remote_ref}: {detail}{where}",
            file=sys.stderr,
        )
        if detail == "dirty" and record is not None:
            print(f"checks-ledger:{dirty_paths(record)}", file=sys.stderr)
    print(
        "checks-ledger: this exact sha has no clean build record, and evaluation is not"
        " a build (`nix eval` never runs the builder).  From a clean tree (no"
        " uncommitted or untracked files), build the sha you are pushing:"
        "\n  heavy --rsync -- lake build wiz tests      # a bare `lake build` (the"
        " default build) also counts"
        "\n  heavy --sshfs -- lake test                 # compiles and links, then"
        " runs the suite"
        "\n  heavy --sshfs -- nix build .#wiz .#tests --no-link"
        "\nA single target is not the whole sha: `lake build Wiz.Lexer` (or `lake build"
        " wiz` alone) is a partial build and is not evidence.",
        file=sys.stderr,
    )
    print(
        "checks-ledger: `heavy` names a record after the program it runs: `lake ...`"
        " -> heavy:lake, `nix build .#X` -> heavy:nix-build:.#X, and"
        " `bash -c '...'` -> heavy:bash.  A `-c` wrapper is not read as a build (its"
        " argv has no `build` element, and a shell script can run anything), so run"
        " the build directly; when a wrapper passes the words through as separate"
        " arguments, name the record yourself:"
        "\n  HEAVY_LEDGER_NAME=heavy:lake heavy --rsync -- env X=1 lake build wiz tests",
        file=sys.stderr,
    )
    print(
        "checks-ledger: a merge commit is a new sha, so build the merge result; a"
        " record made in any worktree of this checkout counts.  (`git push"
        " --no-verify` bypasses this; `audit` lists the remote tips afterwards that"
        " no ledger can explain.)",
        file=sys.stderr,
    )
    return 1


def audit_refs(root: Path, names: list[str], ref_globs: list[str], remote: str, fetch: bool) -> int:
    """`audit`: list remote-tracking tips that no ledger of this checkout explains.

    It cannot see a bypassed push itself (`--no-verify` never runs a hook), but the
    remote-tracking ref is the evidence afterwards: this ref, at this sha, has no clean
    record in any worktree's ledger (`require` reads them all, so `audit` must too, or
    it reports a build another tree holds as a bypass).  It is still a lead to check,
    not a verdict -- a checkout that is not a worktree of this one, or another machine,
    may hold the record -- so it is logged once per (ref, sha) to `.checks/bypass.log`,
    and never fails anything."""
    if fetch:
        proc = git(root, "fetch", "--quiet", remote)
        if proc.returncode != 0:
            print(f"checks-ledger: fetch {remote} failed: {proc.stderr.strip()}", file=sys.stderr)
    prefix = f"refs/remotes/{remote}/"
    listing = git(root, "for-each-ref", "--format=%(refname) %(objectname)", prefix)
    if listing.returncode != 0:
        raise Error(f"cannot list {prefix}")
    records = read_all_records(root)
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
        detail, _ = required_state(records, sha.strip(), names,
                                   recent_history(root, sha.strip()))
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
            f" record in any worktree's ledger ({detail});"
            f" logged to {LEDGER_DIR}/{BYPASS_FILE}",
            file=sys.stderr,
        )
    if not logged:
        print(f"checks-ledger: every {remote} ref matching {', '.join(ref_globs)}"
              " has a clean build record in some worktree's ledger")
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


def _require(root: Path, sha: str, remote_ref: str,
             names: tuple[str, ...] = GUARD_NAMES) -> subprocess.CompletedProcess[str]:
    """A pre-push line as git writes it, through `require` (stdin, exactly as the hook
    does it): `<local ref> <local sha> <remote ref> <remote sha>`."""
    stdin = f"{sha} refs/heads/local {remote_ref} {'0' * 40}\n"
    return _tool_run(root, "require", "--pre-push", *sum((["--name", n] for n in names), []),
                     "--for", INTEGRATION_REFS, stdin=stdin)


def _record(root: Path, name: str, sha: str, argv: list[str], *,
            code: int = 0, clean: bool = True) -> None:
    """A build record as `heavy` writes it (it never runs the command either)."""
    _tool_run(root, "record", "--name", name, "--commit", sha, "--exit", str(code),
              "--clean" if clean else "--dirty", "--", *argv, expect=0)


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
    """Every behaviour above, in a throwaway repository: the light-check reminder, the
    push guard (missing, dirty, failed, stale, not-a-build, partial-build, `lake test`,
    `nix build`, a record in another worktree, the untracked-path message), and the
    hook's cannot-answer choice."""
    source = Path(__file__).resolve()
    hook_source = source.parent.parent / ".githooks" / "pre-push"
    if not hook_source.is_file():
        print(f"checks-ledger: self-test needs {hook_source}", file=sys.stderr)
        return 1
    try:
        with tempfile.TemporaryDirectory(prefix="checks-ledger-selftest-") as tmp:
            # The repository sits one level down so a `git worktree add` sibling (the
            # cross-worktree test, R3) stays outside it.
            base = Path(tmp)
            root = base / "repo"
            root.mkdir()
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

            # 5b. The refusal's advice must be a command that works (R1): every name
            # `heavy` writes is passed by the hook, or the message recommends a build
            # whose record the guard then refuses.
            hook_text = (root / ".githooks" / "pre-push").read_text(encoding="utf-8")
            for name in GUARD_NAMES:
                _check(f"'{name}'" in hook_text,
                       f"the hook passes --name {name} (heavy writes that name)")

            # 6. `record` + `status` show a build record written elsewhere (what `heavy`
            # does after its Slurm job; the command is not run here), and it satisfies
            # the guard for that exact sha.
            third = _commit(root, "third")
            _record(root, "heavy:lake", third, ["lake", "build", "wiz", "tests"])
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
            _record(root, "heavy:lake", fourth, ["lake", "build", "wiz", "tests"],
                    clean=False)
            out = _require(root, fourth, "refs/heads/integration/train9")
            _check(out.returncode == 1 and "dirty" in (out.stdout + out.stderr),
                   "a dirty build record -> push refused (dirty)")

            # ... a failed build is not a build that passed.
            _record(root, "heavy:lake", fourth, ["lake", "build", "wiz", "tests"], code=2)
            out = _require(root, fourth, "refs/heads/integration/train9")
            _check(out.returncode == 1 and "failed" in (out.stdout + out.stderr),
                   "a failed build record -> push refused (failed)")

            # ... evaluation and a test binary run are not builds: no `build` element.
            _record(root, "heavy:lake", fourth, ["lake", "exe", "tests", "--", "=library"])
            out = _require(root, fourth, "refs/heads/integration/train9")
            _check(out.returncode == 1 and "not-a-build" in (out.stdout + out.stderr),
                   "a clean record of a non-build command -> push refused (not-a-build)")

            # ... a `bash -c` wrapper is not read as a build, even under the right
            # name (R2): the element after `-c` is one string, and a shell can run
            # anything.  The documented answer is HEAVY_LEDGER_NAME + no wrapper.
            _record(root, "heavy:lake", fourth,
                    ["bash", "-c", "lake build wiz tests"])
            out = _require(root, fourth, "refs/heads/integration/train9")
            _check(out.returncode == 1 and "not-a-build" in (out.stdout + out.stderr),
                   "a bash -c wrapper -> still not-a-build (the matcher is not loosened)")

            # ... a single target is not the whole sha (A1): the merge has to be built
            # as CI builds it, not as one file that happened to compile.
            _record(root, "heavy:lake", fourth, ["lake", "build", "Wiz.Lexer"])
            out = _require(root, fourth, "refs/heads/integration/train9")
            _check(out.returncode == 1 and "partial-build" in (out.stdout + out.stderr),
                   "lake build Wiz.Lexer -> refused as partial-build (A1)")
            _record(root, "heavy:lake", fourth, ["lake", "build", "wiz"])
            out = _require(root, fourth, "refs/heads/integration/train9")
            _check(out.returncode == 1 and "partial-build" in (out.stdout + out.stderr),
                   "lake build wiz (no tests) -> refused as partial-build (A1)")

            # ... `lake test` compiles and links the driver before it runs a case, so
            # it is a build, and the stronger evidence (R5).
            _record(root, "heavy:lake", fourth, ["lake", "test", "--", "=library"])
            out = _require(root, fourth, "refs/heads/integration/train9")
            _check(out.returncode == 0,
                   "a clean heavy:lake record of `lake test` -> push accepted (R5)")

            # 7b. The hook propagates the refusal, so a push cannot proceed by accident.
            _git(root, "update-ref", "refs/remotes/origin/integration/train9", first)
            hook = _hook_ref(root, fourth, "refs/heads/integration/train9")
            _check(hook.returncode == 0, "the hook accepts an integration push with a record")
            hook = _hook_ref(root, first, "refs/heads/integration/train9")
            _check(hook.returncode == 1 and "refusing to push" in hook.stdout + hook.stderr,
                   "the hook refuses an integration push without a record (exit 1)")

            # 7c. A `nix build` record counts (R1): heavy names it
            # `heavy:nix-build:<attr>`, which a bare `heavy:lake` pattern never saw.
            fifth = _commit(root, "fifth")
            _record(root, "heavy:nix-build:.#wiz", fifth,
                    ["nix", "build", ".#wiz", "--no-link"])
            out = _require(root, fifth, "refs/heads/integration/train9")
            _check(out.returncode == 0, "a heavy:nix-build:<attr> record -> push accepted (R1)")
            _check("heavy:nix-build" in (out.stdout + out.stderr),
                   "... and the accepted push names the nix record")

            # ... evaluation under a nix name is still not a build.
            sixth = _commit(root, "sixth")
            _record(root, "heavy:nix-build:.#wiz", sixth, ["nix", "eval", ".#wiz"])
            out = _require(root, sixth, "refs/heads/integration/train9")
            _check(out.returncode == 1 and "not-a-build" in (out.stdout + out.stderr),
                   "a heavy:nix-build record of `nix eval` -> refused (not-a-build)")

            # ... and a record named by hand (`HEAVY_LEDGER_NAME=heavy:nix`) is read too.
            _record(root, "heavy:nix", sixth, ["nix", "build", ".#tests", "--no-link"])
            out = _require(root, sixth, "refs/heads/integration/train9")
            _check(out.returncode == 0, "a heavy:nix record of `nix build` -> push accepted")

            # 7d. Built in one worktree, pushed from another (R3): the ledger is
            # per-worktree, so this is the coordinator's everyday flow.
            seventh = _commit(root, "seventh")
            side = base / "side"
            _git(root, "worktree", "add", "-q", "-b", "side", str(side))
            _record(side, "heavy:lake", seventh, ["lake", "build", "wiz", "tests"])
            _check(not any(r["commit"] == seventh for r in read_records(root)),
                   "the cross-worktree test's record is NOT in this worktree's ledger")
            out = _require(root, seventh, "refs/heads/integration/train9")
            _check(out.returncode == 0,
                   "a record in another worktree's .checks -> push accepted (R3)")
            _check(str(side) in (out.stdout + out.stderr),
                   "... and the accepted push says which worktree holds it")

            # 7e. A dirty record names the offending paths (R4): an untracked log is
            # the everyday case, and a refusal that does not say which file is a
            # --no-verify waiting to happen.
            eighth = _commit(root, "eighth")
            (root / "scratch-probe.log").write_text("noise\n", encoding="utf-8")
            _record(root, "heavy:lake", eighth, ["lake", "build", "wiz", "tests"],
                    clean=False)
            out = _require(root, eighth, "refs/heads/integration/train9")
            text = out.stdout + out.stderr
            _check(out.returncode == 1 and "scratch-probe.log" in text,
                   "a dirty record -> refused, and the refusal names the untracked file (R4)")
            (root / "scratch-probe.log").unlink()

            # 7f. "Cannot answer" warns and allows; a red record still blocks (R6).
            ledger = root / ".checks" / "records.jsonl"
            saved = ledger.read_text(encoding="utf-8")
            ledger.unlink()
            ledger.mkdir()  # read_text on a directory is an OSError -> exit 2
            hook = _hook_ref(root, seventh, "refs/heads/integration/train9")
            _check(hook.returncode == 0 and "could not answer" in hook.stdout + hook.stderr,
                   "an unreadable ledger -> the hook warns and allows the push (R6)")
            ledger.rmdir()
            ledger.write_text(saved, encoding="utf-8")
            hook = _hook_ref(root, first, "refs/heads/integration/train9")
            _check(hook.returncode == 1,
                   "... while a red record still blocks (exit 1)")

            # 8. `audit` logs a remote tip that no clean record explains: the trace a
            # `--no-verify` push leaves behind.
            _tool_run(root, "audit", "--for", "refs/heads/integration/*", expect=0)
            bypass = root / ".checks" / "bypass.log"
            _check(bypass.is_file() and first[:7] in bypass.read_text(encoding="utf-8"),
                   "audit logs a bypassed push (the remote tip has no record)")
            _check(_tool_run(root, "audit", "--for", "refs/heads/integration/*",
                             expect=0).returncode == 0,
                   "audit still exits 0 (it may never block a push)")

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
