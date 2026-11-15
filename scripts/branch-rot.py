#!/usr/bin/env python3
"""Classify stale branches so that branch hygiene is a five-minute monthly task.

Every local branch (and, with `--remote`, every `origin/*` tracking ref) is
placed in one of four buckets:

  redundant  its tip is an ancestor of the base branch, or every commit is
             patch-equivalent to one upstream (`git cherry` reports no `+`).
             A branch with merge commits is *not* called redundant: `git
             cherry` skips merges, so the answer would be unsound.
  in-flight  an open pull request exists for the branch (kept, never deleted).
  attic      unique commits, no open PR, and the tip is older than `--days`.
  needs-pr   unique commits and no open PR; the conservative default whenever
             the script is unsure.

The classifier is read-only.  Deleting is opt-in and needs both
`--delete-redundant` and `--apply`; it refuses a branch that is the current
branch, is checked out in any worktree, has an open PR, or whose PR state could
not be checked.

Usage
  scripts/branch-rot.py                     table, local branches
  scripts/branch-rot.py --limit 10          cap each bucket's rows
  scripts/branch-rot.py --remote            include origin/* refs
  scripts/branch-rot.py --days 30           attic threshold (default 30)
  scripts/branch-rot.py --json              machine-readable output
  scripts/branch-rot.py --no-gh             skip GitHub (PR state is "unknown")
  scripts/branch-rot.py --delete-redundant  dry run: list deletable branches
  scripts/branch-rot.py --delete-redundant --apply
  scripts/branch-rot.py --self-test         offline fixture, no network, no gh

Base branch: `origin/master` when it exists, else `master`; override with
`--base`.  Exit status: 0 clean, 1 self-test or git error, 2 usage error.
Python standard library only.
"""

from __future__ import annotations

import argparse
import json
import os
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path

BUCKETS = ("redundant", "needs-pr", "attic", "in-flight")
GH_FIELDS = "number,headRefName,url,isDraft,title"
SUBJECT_WIDTH = 58
# Never delete the default branches, even when a raw commit is used as --base
# and the local ref is not the checked-out one.
PROTECTED = {"master", "main"}


def run(cmd, cwd, timeout=120, env=None):
    """Run a command; return (status, stdout, stderr)."""
    try:
        proc = subprocess.run(
            [str(part) for part in cmd],
            cwd=str(cwd),
            capture_output=True,
            text=True,
            timeout=timeout,
            env=env,
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        return 1, "", str(exc)
    return proc.returncode, proc.stdout.strip(), proc.stderr.strip()


def git(repo, *args, timeout=120):
    """Run git in `repo`; return (status, stdout, stderr)."""
    return run(["git", "-C", str(repo), *args], repo, timeout=timeout)


def git_out(repo, *args):
    """Stdout of a git command, or "" on failure."""
    status, out, _ = git(repo, *args)
    return out if status == 0 else ""


def find_repo(start):
    status, out, _ = run(["git", "rev-parse", "--show-toplevel"], start)
    if status == 0 and out:
        return Path(out)
    fallback = Path(__file__).resolve().parent.parent
    status, out, _ = run(["git", "rev-parse", "--show-toplevel"], fallback)
    return Path(out) if status == 0 and out else fallback


def resolve_base(repo, requested):
    """Return (display name, full ref name, sha) for the base branch."""
    candidates = [requested] if requested else ["origin/master", "master"]
    for name in candidates:
        if not name:
            continue
        status, out, _ = git(repo, "rev-parse", "--verify", "-q", name)
        if status != 0 or not out:
            continue
        full = git_out(repo, "rev-parse", "--symbolic-full-name", name) or name
        return name, full, out
    if requested:
        raise SystemExit(f"branch-rot: base branch not found: {requested}")
    raise SystemExit("branch-rot: neither origin/master nor master exists")


def list_refs(repo, base_ref, include_remote):
    """refs as dicts: name, ref, kind, head, timestamp, subject."""
    patterns = ["refs/heads"]
    if include_remote:
        patterns.append("refs/remotes/origin")
    status, out, err = git(
        repo,
        "for-each-ref",
        "--format=%(refname)%00%(objectname)%00%(committerdate:unix)%00%(subject)",
        *patterns,
    )
    if status != 0:
        raise SystemExit(f"branch-rot: git for-each-ref failed: {err}")
    refs = []
    for line in out.splitlines():
        parts = line.split("\0")
        if len(parts) != 4:
            continue
        ref, head, stamp, subject = parts
        if ref == base_ref or ref == "refs/remotes/origin/HEAD":
            continue
        if ref.startswith("refs/heads/"):
            kind, name = "local", ref[len("refs/heads/"):]
        elif ref.startswith("refs/remotes/origin/"):
            kind, name = "remote", ref[len("refs/remotes/"):]
        else:
            continue
        try:
            timestamp = int(stamp)
        except ValueError:
            timestamp = 0
        refs.append(
            {
                "name": name,
                "ref": ref,
                "kind": kind,
                "head": head,
                "timestamp": timestamp,
                "subject": subject,
            }
        )
    return refs


def ancestor_refs(repo, base_sha, include_remote):
    """Refs whose tips are reachable from the base, in one git call."""
    patterns = ["refs/heads"]
    if include_remote:
        patterns.append("refs/remotes/origin")
    status, out, _ = git(
        repo,
        "for-each-ref",
        f"--merged={base_sha}",
        "--format=%(refname)",
        *patterns,
    )
    return set(out.splitlines()) if status == 0 else set()


def worktree_map(repo):
    """Branch name -> worktree path, from `git worktree list --porcelain`."""
    result, path = {}, ""
    for line in git_out(repo, "worktree", "list", "--porcelain").splitlines():
        if line.startswith("worktree "):
            path = line[len("worktree "):]
        elif line.startswith("branch refs/heads/"):
            result[line[len("branch refs/heads/"):]] = path
    return result


def current_branch(repo):
    """The checked-out branch of this worktree, or "" when detached."""
    return git_out(repo, "symbolic-ref", "--short", "-q", "HEAD")


def load_prs(repo, use_gh):
    """Open PRs as {headRefName: pr}; None means "unknown" (no gh / no auth)."""
    if not use_gh:
        return None, "disabled"
    gh = os.environ.get("GH", "gh")
    found = shutil.which(gh)
    if not found:
        return None, "unavailable (gh not found)"
    status, out, err = run(
        [
            found,
            "pr",
            "list",
            "--state",
            "open",
            "--limit",
            "2000",
            "--json",
            GH_FIELDS,
        ],
        repo,
        timeout=90,
    )
    if status != 0:
        detail = (err or out).splitlines()[0] if (err or out) else "failed"
        return None, f"unavailable ({detail})"
    try:
        prs = json.loads(out)
    except json.JSONDecodeError:
        return None, "unavailable (bad gh JSON)"
    if len(prs) >= 2000:
        # A truncated list could hide an open PR; refuse to guess.
        return None, "unavailable (open PR list truncated)"
    return {pr["headRefName"]: pr for pr in prs if pr.get("headRefName")}, "ok"


def redundancy(repo, base_sha, ref):
    """Is `ref` redundant (ancestor or patch-equivalent)?

    Returns a dict with `redundant`, `how`, `ahead`, `unique`, `merges`.
    Conservative: an unreadable branch, or one containing merge commits whose
    non-merge commits are all patch-equivalent, is NOT redundant.
    """
    info = {"redundant": False, "how": "unique", "ahead": 0, "unique": 0,
            "merges": 0}
    status, _, _ = git(repo, "merge-base", "--is-ancestor", ref, base_sha)
    if status == 0:
        info.update(redundant=True, how="ancestor")
        return info
    if status != 1:  # 1 means "not an ancestor"; anything else is an error
        info["how"] = "error"
        return info

    status, out, _ = git(repo, "rev-list", "--count", f"{base_sha}..{ref}")
    if status != 0:
        info["how"] = "error"
        return info
    try:
        info["ahead"] = int(out)
    except ValueError:
        info["how"] = "error"
        return info
    if info["ahead"] == 0:
        info.update(redundant=True, how="ancestor")
        return info

    status, out, _ = git(repo, "cherry", base_sha, ref)
    if status != 0:
        info["how"] = "cherry-failed"
        return info
    plus = sum(1 for line in out.splitlines() if line.startswith("+"))
    info["unique"] = plus
    status, out, _ = git(repo, "rev-list", "--count", "--merges",
                         f"{base_sha}..{ref}")
    if status == 0:
        try:
            info["merges"] = int(out)
        except ValueError:
            pass
    if plus == 0:
        if info["merges"] == 0:
            info.update(redundant=True, how="patch-equivalent")
        else:
            # git cherry ignores merges, so "no + lines" is not enough here.
            info["how"] = "has-merges"
    return info


def classify_refs(repo, base_sha, refs, ancestors, prs, days, trees, current,
                  now=None):
    """Classify refs; `prs` None means PR state is unknown."""
    now = time.time() if now is None else now
    rows = []
    for ref in refs:
        if ref["ref"] in ancestors:
            info = {"redundant": True, "how": "ancestor", "ahead": 0,
                    "unique": 0, "merges": 0}
        else:
            info = redundancy(repo, base_sha, ref["ref"])
        age = round(max(0.0, now - ref["timestamp"]) / 86400.0, 1)
        head_name = (
            ref["name"][len("origin/"):]
            if ref["kind"] == "remote" and ref["name"].startswith("origin/")
            else ref["name"]
        )
        if prs is None:
            pr_state = "unknown"
        elif head_name in prs:
            pr_state = "open"
        else:
            pr_state = "none"
        pr = prs.get(head_name) if prs else None

        if pr_state == "open":
            bucket = "in-flight"
        elif info["redundant"]:
            bucket = "redundant"
        elif age > days:
            bucket = "attic"
        else:
            bucket = "needs-pr"

        blockers = []
        if bucket == "redundant":
            if ref["kind"] != "local":
                blockers.append("remote-ref")
            if ref["kind"] == "local" and ref["name"] == current:
                blockers.append("current")
            if ref["kind"] == "local" and ref["name"] in trees:
                blockers.append("worktree")
            if ref["name"] in PROTECTED:
                blockers.append("protected")
            if pr_state == "open":
                blockers.append("open-pr")
            elif pr_state == "unknown":
                blockers.append("pr-state-unknown")

        rows.append(
            {
                "name": ref["name"],
                "ref": ref["ref"],
                "kind": ref["kind"],
                "head": ref["head"],
                "subject": ref["subject"],
                "age_days": age,
                "ahead": info["ahead"],
                "unique": info["unique"],
                "merges": info["merges"],
                "ancestor": info["how"] == "ancestor",
                "how": info["how"],
                "bucket": bucket,
                "pr_state": pr_state,
                "pr": (
                    {
                        "number": pr.get("number"),
                        "url": pr.get("url"),
                        "is_draft": pr.get("isDraft"),
                        "title": pr.get("title"),
                    }
                    if pr
                    else None
                ),
                "worktree": trees.get(ref["name"]),
                "current": ref["kind"] == "local" and ref["name"] == current,
                "deletable": bucket == "redundant" and not blockers,
                "blockers": blockers,
            }
        )
    return rows


def deletion_plan(repo, base_name, rows, apply):
    """Check live preconditions, then optionally `git branch -D`."""
    base_sha = git_out(repo, "rev-parse", base_name)
    trees = worktree_map(repo)
    current = current_branch(repo)
    results = []
    for row in rows:
        if row["bucket"] != "redundant" or row["kind"] != "local":
            continue
        blockers = []
        if row["name"] in PROTECTED:
            blockers.append("protected default branch")
        if row["name"] == current:
            blockers.append("current branch")
        if row["name"] in trees:
            blockers.append(f"checked out in {trees[row['name']]}")
        if row["pr_state"] == "open":
            blockers.append("open PR")
        elif row["pr_state"] == "unknown":
            blockers.append("PR state unknown")
        if not blockers:
            fresh = redundancy(repo, base_sha, row["ref"])
            if not fresh["redundant"]:
                blockers.append(f"no longer redundant ({fresh['how']})")
        if blockers:
            results.append(
                {"branch": row["name"], "status": "refused",
                 "reason": "; ".join(blockers)}
            )
            continue
        if not apply:
            results.append(
                {"branch": row["name"], "status": "would-delete",
                 "reason": row["how"]}
            )
            continue
        status, out, err = git(repo, "branch", "-D", "--", row["name"])
        if status == 0:
            results.append(
                {"branch": row["name"], "status": "deleted",
                 "reason": row["how"]}
            )
        else:
            results.append(
                {"branch": row["name"], "status": "refused",
                 "reason": (err or out).splitlines()[0] if (err or out) else
                 "git branch -D failed"}
            )
    return results


def fmt_age(days):
    if days < 1:
        return "<1d"
    return f"{days:.0f}d"


def truncate(text, width):
    return text if len(text) <= width else text[: width - 3] + "..."


def note_for(row):
    notes = []
    if row["current"]:
        notes.append("current")
    elif row["worktree"]:
        notes.append("wt")
    if row["pr_state"] == "unknown":
        notes.append("pr?")
    if "protected" in row["blockers"]:
        notes.append("protected")
    if row["how"] in ("has-merges", "cherry-failed", "error"):
        notes.append(row["how"])
    if not notes and row["bucket"] == "redundant":
        notes.append(row["how"])
    return ",".join(notes)


def print_table(rows, base_name, base_sha, gh_status, days, limit):
    counts = {bucket: 0 for bucket in BUCKETS}
    for row in rows:
        counts[row["bucket"]] += 1
    unmerged = sum(1 for row in rows if not row["ancestor"])
    deletable = sum(1 for row in rows if row["deletable"])
    print(f"base {base_name} ({base_sha[:8]}); attic threshold {days}d; "
          f"gh {gh_status}")
    print(f"{len(rows)} refs, {unmerged} not merged into base")
    print("  ".join(f"{bucket} {counts[bucket]}" for bucket in BUCKETS)
          + f"  deletable {deletable}")
    for bucket in BUCKETS:
        selected = [row for row in rows if row["bucket"] == bucket]
        shown = selected if limit <= 0 else selected[:limit]
        heading = f"\n{bucket} ({len(selected)})"
        if bucket == "redundant":
            heading += f", {deletable} deletable"
        if limit > 0 and len(selected) > limit:
            heading += f", showing {limit}"
        print(heading)
        if not shown:
            print("  (none)")
            continue
        width = max(len(row["name"]) for row in shown)
        print(f"  {'BRANCH'.ljust(width)}  {'AGE':>4}  {'AHEAD':>5}  "
              f"{'UNIQ':>4}  {'PR':>5}  {'NOTE':<12}  SUBJECT")
        for row in shown:
            pr = f"#{row['pr']['number']}" if row["pr"] else (
                "?" if row["pr_state"] == "unknown" else "-")
            print(f"  {row['name'].ljust(width)}  {fmt_age(row['age_days']):>4}  "
                  f"{row['ahead']:>5}  {row['unique']:>4}  {pr:>5}  "
                  f"{note_for(row):<12}  "
                  f"{truncate(row['subject'], SUBJECT_WIDTH)}")


def print_deletion(results, apply, as_json):
    deleted = [r for r in results if r["status"] in ("deleted", "would-delete")]
    refused = [r for r in results if r["status"] == "refused"]
    if as_json:
        return
    if not apply:
        print(f"\nwould delete {len(deleted)} redundant branches "
              "(re-run with --apply):")
        for result in deleted:
            print(f"  {result['branch']}  ({result['reason']})")
    else:
        print(f"\ndeleted {len(deleted)} redundant branches:")
        for result in deleted:
            print(f"  {result['branch']}  ({result['reason']})")
    if refused:
        print(f"kept {len(refused)}:")
        for result in refused:
            print(f"  {result['branch']}  ({result['reason']})")


def self_test():
    """Offline fixture: commits, a merge, a cherry-pick, a worktree."""
    failures = []

    def check(condition, message):
        if not condition:
            failures.append(message)

    tmp = Path(tempfile.mkdtemp(prefix="branch-rot-selftest-"))
    repo = tmp / "repo"
    wt = tmp / "wt"
    env = os.environ.copy()
    env.update(
        {
            "GIT_CONFIG_GLOBAL": os.devnull,
            "GIT_CONFIG_NOSYSTEM": "1",
            "GIT_AUTHOR_NAME": "Branch Rot Test",
            "GIT_AUTHOR_EMAIL": "branch-rot@example.invalid",
            "GIT_COMMITTER_NAME": "Branch Rot Test",
            "GIT_COMMITTER_EMAIL": "branch-rot@example.invalid",
            "GIT_MERGE_AUTOEDIT": "no",
        }
    )

    def g(*args, when=None, commit_when=None, check_status=True):
        active = env.copy()
        if when:
            active["GIT_AUTHOR_DATE"] = when
            active["GIT_COMMITTER_DATE"] = when
        if commit_when:
            active["GIT_COMMITTER_DATE"] = commit_when
        status, out, err = run(["git", "-C", str(repo), *args], repo,
                               env=active)
        if check_status and status != 0:
            raise RuntimeError(f"git {' '.join(args)} failed: {err or out}")
        return out

    def commit(filename, text, message, when=None):
        (repo / filename).write_text(text)
        g("add", "-A")
        g("commit", "-q", "-m", message, when=when)

    def exists(branch):
        status, _, _ = git(repo, "rev-parse", "--verify", "-q",
                           f"refs/heads/{branch}")
        return status == 0

    try:
        repo.mkdir()
        g("init", "-q", "-b", "master")
        commit("base.txt", "base\n", "base")

        # Ancestor of master: merged, so redundant.
        g("checkout", "-q", "-b", "feat-ancestor")
        commit("ancestor.txt", "ancestor\n", "ancestor work")
        g("checkout", "-q", "master")
        g("merge", "-q", "--no-ff", "-m", "merge feat-ancestor", "feat-ancestor")

        # Patch-equivalent: cherry-picked to master, not an ancestor.
        g("checkout", "-q", "-b", "feat-cherry", "master")
        commit("cherry.txt", "cherry\n", "cherry source")
        g("checkout", "-q", "master")
        # A different committer date keeps the cherry-pick a distinct object;
        # with identical metadata it would hash to the very same commit.
        g("cherry-pick", "feat-cherry", commit_when="2021-06-01T00:00:00Z")

        # Ordinary unmerged branch: needs a PR.
        g("checkout", "-q", "-b", "feat-unmerged", "master")
        commit("unmerged.txt", "unmerged\n", "unmerged work")

        # Old unmerged branch: attic.
        g("checkout", "-q", "-b", "feat-old", "master")
        commit("old.txt", "old\n", "old work", when="2020-01-01T00:00:00Z")

        # A merge commit on top of a patch-equivalent commit: `git cherry`
        # shows no `+`, but the branch is not redundant.  Conservative.
        g("checkout", "-q", "-b", "feat-merge", "master")
        commit("merge-source.txt", "merge source\n", "merge source")
        g("checkout", "-q", "master")
        g("cherry-pick", "feat-merge", commit_when="2021-06-02T00:00:00Z")
        g("checkout", "-q", "feat-merge")
        g("merge", "-q", "--no-ff", "-m", "merge master", "master")

        # A merge commit with no content of its own: `git cherry` prints
        # nothing (it skips merges), yet the branch is not redundant.
        tree = g("rev-parse", "master^{tree}")
        parent = g("rev-parse", "master")
        grandparent = g("rev-parse", "master^")
        empty_merge = g("commit-tree", tree, "-p", parent, "-p", grandparent,
                        "-m", "empty merge")
        g("update-ref", "refs/heads/feat-merge-only", empty_merge)

        # Open PR (injected; the self-test never calls gh).
        g("checkout", "-q", "-b", "feat-pr", "master")
        commit("pr.txt", "pr\n", "pr work")
        g("checkout", "-q", "master")

        # A worktree holding a redundant branch must be protected.
        g("worktree", "add", "-q", str(wt), "feat-cherry")
        # The default branch is protected by name, not only by being checked out.
        g("branch", "main", "feat-ancestor")

        base_name, base_ref, base_sha = resolve_base(repo, "master")
        refs = list_refs(repo, base_ref, include_remote=False)
        ancestors = ancestor_refs(repo, base_sha, include_remote=False)
        trees = worktree_map(repo)
        current = current_branch(repo)
        prs = {
            "feat-pr": {
                "number": 7,
                "headRefName": "feat-pr",
                "url": "https://example.invalid/pr/7",
                "isDraft": False,
                "title": "fixture PR",
            }
        }
        rows = classify_refs(repo, base_sha, refs, ancestors, prs, 30, trees,
                             current, now=time.time())
        by = {row["name"]: row for row in rows}

        check(by["feat-ancestor"]["bucket"] == "redundant",
              "merged branch is redundant")
        check(by["feat-ancestor"]["how"] == "ancestor",
              "merged branch is redundant by ancestry")
        check(by["feat-cherry"]["bucket"] == "redundant",
              "cherry-picked branch is redundant")
        check(by["feat-cherry"]["how"] == "patch-equivalent",
              "cherry-picked branch is patch-equivalent")
        check(by["feat-unmerged"]["bucket"] == "needs-pr",
              "unmerged branch needs a PR")
        check(by["feat-unmerged"]["how"] == "unique",
              "unmerged branch has unique commits")
        check(by["feat-old"]["bucket"] == "attic",
              "old unmerged branch is attic")
        check(by["feat-pr"]["bucket"] == "in-flight",
              "open PR branch is in-flight")
        check(by["feat-pr"]["pr"]["number"] == 7,
              "open PR number is reported")
        check(by["feat-merge"]["bucket"] == "needs-pr",
              "branch with a merge commit is not called redundant")
        check(by["feat-merge"]["merges"] >= 1,
              "branch merge commit is counted")
        check(by["feat-merge-only"]["bucket"] == "needs-pr",
              "content-free merge branch needs a PR")
        check(by["feat-merge-only"]["how"] == "has-merges",
              "content-free merge branch is reported conservatively")
        check(by["feat-cherry"]["worktree"] == str(wt),
              "worktree branch is marked")
        check(not by["feat-cherry"]["deletable"],
              "worktree branch is not deletable")
        check("worktree" in by["feat-cherry"]["blockers"],
              "worktree blocks deletion")
        check(by["feat-ancestor"]["deletable"],
              "plain redundant branch is deletable")
        check(not by["main"]["deletable"], "default branch is not deletable")
        check("protected" in by["main"]["blockers"],
              "default branch is protected")
        check(not by["feat-unmerged"]["deletable"],
              "needs-pr branch is not deletable")

        # Dry run deletes nothing.
        dry = deletion_plan(repo, base_name, rows, apply=False)
        check(any(r["branch"] == "feat-ancestor" and
                  r["status"] == "would-delete" for r in dry),
              "dry run lists the redundant branch")
        check(exists("feat-ancestor"), "dry run leaves the branch in place")

        # The current branch is protected.
        g("checkout", "-q", "feat-ancestor")
        live = deletion_plan(repo, base_name, rows, apply=True)
        check(any(r["branch"] == "feat-ancestor" and
                  r["status"] == "refused" for r in live),
              "current branch is refused")
        check(exists("feat-ancestor"), "current branch survives deletion")
        check(any(r["branch"] == "main" and r["status"] == "refused"
                  for r in live), "default branch is refused")
        check(exists("main"), "default branch survives deletion")

        # Worktree branch is protected.
        check(any(r["branch"] == "feat-cherry" and
                  r["status"] == "refused" for r in live),
              "worktree branch is refused")
        check(exists("feat-cherry"), "worktree branch survives deletion")

        # A plain redundant branch is deleted once it is not current.
        g("checkout", "-q", "master")
        live = deletion_plan(repo, base_name, rows, apply=True)
        check(any(r["branch"] == "feat-ancestor" and
                  r["status"] == "deleted" for r in live),
              "redundant branch is deleted")
        check(not exists("feat-ancestor"), "deleted branch is gone")
        check(exists("feat-unmerged"), "needs-pr branch is untouched")

        # JSON round-trips.
        payload = {"base": base_name, "branches": rows}
        check(json.loads(json.dumps(payload))["branches"][0]["name"] ==
              rows[0]["name"], "rows serialise to JSON")
    finally:
        shutil.rmtree(tmp, ignore_errors=True)

    if failures:
        for failure in failures:
            print(f"self-test FAIL: {failure}")
        print(f"self-test: {len(failures)} failure(s)")
        return 1
    print("self-test: ok (classification, JSON, worktree and current-branch "
          "guards)")
    return 0


def main(argv=None):
    parser = argparse.ArgumentParser(
        description="Classify stale branches (redundant, needs-pr, attic, "
                    "in-flight); read-only unless --delete-redundant --apply."
    )
    parser.add_argument("--base", help="base branch (default origin/master, "
                                       "else master)")
    parser.add_argument("--days", type=int, default=30,
                        help="attic threshold in days (default 30)")
    parser.add_argument("--remote", action="store_true",
                        help="include origin/* tracking refs")
    parser.add_argument("--json", action="store_true", help="JSON output")
    parser.add_argument("--no-gh", action="store_true",
                        help="do not query GitHub; PR state is unknown")
    parser.add_argument("--limit", type=int, default=0,
                        help="rows per bucket in the table (0 = all)")
    parser.add_argument("--delete-redundant", action="store_true",
                        help="delete redundant branches (dry run without "
                             "--apply)")
    parser.add_argument("--apply", action="store_true",
                        help="with --delete-redundant, actually delete")
    parser.add_argument("--self-test", action="store_true",
                        help="run the offline fixture and exit")
    args = parser.parse_args(argv)

    if args.self_test:
        return self_test()
    if args.apply and not args.delete_redundant:
        parser.error("--apply requires --delete-redundant")
    if args.days < 0:
        parser.error("--days must be non-negative")
    if args.limit < 0:
        parser.error("--limit must be non-negative")

    repo = find_repo(Path.cwd())
    base_name, base_ref, base_sha = resolve_base(repo, args.base)
    refs = list_refs(repo, base_ref, args.remote)
    ancestors = ancestor_refs(repo, base_sha, args.remote)
    trees = worktree_map(repo)
    current = current_branch(repo)
    if args.no_gh:
        prs, gh_status = None, "disabled"
    else:
        prs, gh_status = load_prs(repo, use_gh=True)
    rows = classify_refs(repo, base_sha, refs, ancestors, prs, args.days,
                         trees, current)

    deletion = None
    if args.delete_redundant:
        deletion = deletion_plan(repo, base_name, rows, args.apply)

    if args.json:
        counts = {bucket: 0 for bucket in BUCKETS}
        for row in rows:
            counts[row["bucket"]] += 1
        payload = {
            "generated": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
            "repo": str(repo),
            "base": {
                "name": base_name,
                "ref": base_ref,
                "head": base_sha,
            },
            "days": args.days,
            "remote": args.remote,
            "gh": gh_status,
            "counts": {
                **counts,
                "refs": len(rows),
                "unmerged": sum(1 for row in rows if not row["ancestor"]),
                "deletable": sum(1 for row in rows if row["deletable"]),
            },
            "branches": rows,
        }
        if deletion is not None:
            payload["deletion"] = {"applied": args.apply,
                                   "results": deletion}
        print(json.dumps(payload, indent=2))
    else:
        print_table(rows, base_name, base_sha, gh_status, args.days,
                    args.limit)
        if deletion is not None:
            print_deletion(deletion, args.apply, as_json=False)
    return 0


if __name__ == "__main__":
    sys.exit(main())
