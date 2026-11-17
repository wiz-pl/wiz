#!/usr/bin/env python3
"""Print and refresh the merge-stack ledger of wiz-pl/wiz.

A *stack* is a branch that merges several unmerged branches in dependency order
and is opened as one pull request (an integration PR); its component branches
stay local and their PRs are closed as folded.  Stacks are serialised: one open
PR per dependency chain, and only the PR at the head of a chain gets CI.

The ledger is JSON, kept outside the repository: `--ledger FILE`, else
$WIZ_STACK_LEDGER, else `stack-ledger.json` in the notes directory named by
`--notes DIR` or $WIZ_NOTES_DIR.  There is no default; without one of these the
script exits with status 2.  Curated fields -- `order`,
`chain`, `depends_on`, `after`, `next`, `note` -- are edited by hand; everything
under `facts` is derived from git and `gh` by this script.

`depends_on` names entries whose commits the branch contains (the PR body's
`Depends on:` line); `after` names entries that must merge first for scheduling
reasons only.  Both name another entry's `id`, and both are satisfied only when
that entry's `facts.state` is `merged`.

Usage
  scripts/stack-status.py                 the ledger as a table
  scripts/stack-status.py --next 5        the next five actions, with their gates
  scripts/stack-status.py --write         refresh `facts` in the ledger file
  scripts/stack-status.py --json          the refreshed ledger on stdout
  scripts/stack-status.py --check         exit 1 on a broken or unsafe ledger
  scripts/stack-status.py --no-gh         no GitHub calls (ledger + git only)
  scripts/stack-status.py --fetch         `git fetch origin` first

Exit status: 0 clean, 1 `--check` found a problem, 2 usage or ledger error.
"""
import argparse
import json
import os
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent


def resolve_ledger(ledger, notes):
    """`--ledger`, else $WIZ_STACK_LEDGER, else `stack-ledger.json` in `--notes` or
    $WIZ_NOTES_DIR; None when none of them is given."""
    if ledger is not None:
        return ledger
    env = os.environ.get("WIZ_STACK_LEDGER")
    if env:
        return Path(env)
    notes = notes or os.environ.get("WIZ_NOTES_DIR")
    if notes:
        return Path(notes) / "stack-ledger.json"
    return None

GH = os.environ.get("GH", "gh")
BAD = {"FAILURE", "CANCELLED", "TIMED_OUT", "ACTION_REQUIRED", "STARTUP_FAILURE"}
PENDING = {"QUEUED", "IN_PROGRESS", "PENDING", "WAITING", "REQUESTED"}


def run(cmd, cwd=REPO):
    """Run a command; return (exit status, stripped stdout)."""
    try:
        out = subprocess.run(
            cmd, cwd=str(cwd), capture_output=True, text=True, timeout=120
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        return 1, str(exc)
    return out.returncode, out.stdout.strip()


def git(*args):
    code, out = run(["git", "-C", str(REPO), *args])
    return out if code == 0 else ""


def git_ok(*args):
    return run(["git", "-C", str(REPO), *args])[0] == 0


def worktrees():
    """branch name -> worktree path, from `git worktree list --porcelain`."""
    result, path = {}, ""
    for line in git("worktree", "list", "--porcelain").splitlines():
        if line.startswith("worktree "):
            path = line[len("worktree "):]
        elif line.startswith("branch refs/heads/"):
            result[line[len("branch refs/heads/"):]] = path
    return result


def pr_facts(number):
    """One `gh pr view`; empty dict when gh is unavailable or the PR is gone."""
    code, out = run(
        [
            GH, "pr", "view", str(number), "-R", "wiz-pl/wiz", "--json",
            "number,state,isDraft,mergeable,mergeStateStatus,headRefOid,"
            "headRefName,statusCheckRollup,url,updatedAt",
        ]
    )
    if code != 0:
        return {}
    try:
        return json.loads(out)
    except json.JSONDecodeError:
        return {}


def ci_state(checks):
    conclusions = [c.get("conclusion") for c in checks if c.get("conclusion")]
    statuses = [c.get("status") for c in checks if c.get("status")]
    if any(c in BAD for c in conclusions):
        return "red"
    if any(s in PENDING for s in statuses):
        return "running"
    return "green" if checks else "none"


def head_for(entry, pr):
    """The commit the entry is about: the PR head when open, else the branch."""
    if pr and pr.get("headRefOid"):
        return pr["headRefOid"]
    branch = entry.get("branch", "")
    return (
        git("rev-parse", "--verify", "-q", f"refs/heads/{branch}")
        or git("rev-parse", "--verify", "-q", f"refs/remotes/origin/{branch}")
    )


def refresh(ledger, use_gh=True):
    master = git("rev-parse", "origin/master") or git("rev-parse", "master")
    trees = worktrees()
    entries = ledger["entries"]
    by_id = {e["id"]: e for e in entries}

    for entry in entries:
        branch = entry.get("branch", "")
        prev = entry.get("facts", {})
        if use_gh and entry.get("pr"):
            pr = pr_facts(entry["pr"])
        elif not use_gh and prev.get("pr_state"):
            pr = {
                "state": prev.get("pr_state"),
                "mergeable": prev.get("mergeable"),
                "isDraft": prev.get("is_draft"),
                "headRefOid": prev.get("pr_head"),
            }
        else:
            pr = {}
        head = head_for(entry, pr)
        local = git("rev-parse", "--verify", "-q", f"refs/heads/{branch}")
        facts = {
            "checked": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
            "head": head or None,
            "local_head": local or None,
            "pr_head": pr.get("headRefOid"),
            "pr_state": pr.get("state"),
            "mergeable": pr.get("mergeable"),
            "merge_state": pr.get("mergeStateStatus"),
            "is_draft": pr.get("isDraft"),
            "ci": (
                ci_state(pr.get("statusCheckRollup") or [])
                if use_gh else prev.get("ci", "none")
            ),
            "behind": (
                int(git("rev-list", "--count", f"{head}..{master}") or 0)
                if head else None
            ),
            "local_behind": (
                int(git("rev-list", "--count", f"{local}..{master}") or 0)
                if local else None
            ),
            "worktree": trees.get(branch),
            "url": pr.get("url"),
        }
        merged = bool(head) and git_ok("merge-base", "--is-ancestor", head, master)
        if pr.get("state") == "MERGED":
            merged = True
        facts["merged"] = merged
        facts["head_drift"] = bool(local and pr.get("headRefOid")
                                   and local != pr["headRefOid"])
        if entry.get("folded") and not pr:
            state = "folded"
        elif merged:
            state = "merged"
        elif pr.get("state") == "CLOSED":
            state = "closed"
        elif pr:
            state = "draft" if pr.get("isDraft") else (
                "conflict" if pr.get("mergeable") == "CONFLICTING" else "ready"
            )
        else:
            state = "local"
        facts["state"] = state
        entry["facts"] = facts

    for entry in entries:
        facts = entry["facts"]
        blocked = [
            dep for dep in entry.get("depends_on", [])
            if (by_id.get(dep, {}).get("facts", {}).get("state")) != "merged"
        ]
        waiting = [
            dep for dep in entry.get("after", [])
            if (by_id.get(dep, {}).get("facts", {}).get("state")) != "merged"
        ]
        facts["blocked_by"] = blocked
        facts["after_unmerged"] = waiting
        facts["gate"] = gate_for(entry, blocked, waiting)
    ledger["master"] = master
    ledger["updated"] = datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    return ledger


def gate_for(entry, blocked, waiting):
    facts = entry["facts"]
    state, ci = facts.get("state"), facts.get("ci")
    if state == "merged":
        return "landed"
    if state == "folded":
        return "folded into its parent; no PR"
    if state == "closed":
        return "PR closed; decide whether to reopen or drop it"
    if blocked:
        return "wait for " + ", ".join(blocked)
    if waiting:
        return "queued behind " + ", ".join(waiting)
    if facts.get("head_drift"):
        if facts.get("local_behind") == 0:
            return "local head is restacked (0 behind); push it, then wait for CI"
        return "restack the local branch, then push it (it is not the PR head)"
    if state == "conflict":
        return "restack on master (merge, never rebase), then push"
    if state == "local":
        if facts.get("behind"):
            return (
                f"restack on master ({facts['behind']} behind); "
                "open a PR when its turn comes"
            )
        return "local and restacked; open a PR when its turn comes"
    if ci == "red":
        return "CI failed; fix on the branch and push once"
    if ci == "running":
        return "wait for CI"
    if ci == "none":
        return "no checks yet; push or re-run CI"
    if state == "draft":
        return "mark ready when the merge checklist passes"
    return "merge"


def command_for(entry):
    facts = entry["facts"]
    pr, branch, wt = entry.get("pr"), entry.get("branch"), facts.get("worktree")
    where = f"git -C {wt}" if wt else "git"
    if facts.get("state") == "merged":
        return ""
    if entry.get("folded"):
        return f"{GH} pr close {pr} -R wiz-pl/wiz" if pr else ""
    if facts.get("blocked_by") or facts.get("after_unmerged"):
        return ""
    if facts.get("head_drift") and wt:
        if facts.get("local_behind") == 0:
            return f"{where} push origin HEAD:{branch}"
        return f"cd {wt} && git merge origin/master  # then push"
    if facts.get("state") == "conflict":
        return f"cd {wt} && git merge origin/master  # then push" if wt else ""
    if facts.get("state") == "local":
        if not wt:
            hint = REPO.parent / entry["id"]
            tail = "  # then merge origin/master" if facts.get("behind") else ""
            return f"git -C {REPO} worktree add {hint} {branch}{tail}"
        return f"{GH} pr create -R wiz-pl/wiz --base master --head {branch} --draft"
    if facts.get("ci") == "red" and pr:
        return f"{GH} pr view {pr} -R wiz-pl/wiz --json statusCheckRollup"
    if facts.get("ci") == "running" and pr:
        return f"{GH} pr checks {pr} -R wiz-pl/wiz"
    if facts.get("mergeable") == "CONFLICTING" and wt:
        return f"cd {wt} && git merge origin/master  # then push"
    if facts.get("is_draft") and pr:
        return f"{GH} pr ready {pr} -R wiz-pl/wiz"
    if facts.get("state") == "ready" and pr:
        return f"{GH} pr merge {pr} -R wiz-pl/wiz --merge"
    return ""


def table(ledger):
    rows = [
        ("#", "id", "PR", "branch", "deps", "state", "CI", "behind", "next"),
    ]
    for entry in ledger["entries"]:
        facts = entry.get("facts", {})
        rows.append(
            (
                str(entry.get("order") or "-"),
                entry["id"],
                f"#{entry['pr']}" if entry.get("pr") else "-",
                entry.get("branch", ""),
                ",".join(entry.get("depends_on", [])) or "-",
                facts.get("state", "?"),
                facts.get("ci", "?"),
                str(facts.get("behind") if facts.get("behind") is not None else "-"),
                entry.get("next", ""),
            )
        )
    widths = [max(len(row[i]) for row in rows) for i in range(len(rows[0]))]
    lines = []
    for n, row in enumerate(rows):
        cells = [cell.ljust(widths[i]) for i, cell in enumerate(row)]
        lines.append("  ".join(cells).rstrip())
        if n == 0:
            lines.append("  ".join("-" * width for width in widths))
    return "\n".join(lines)


def show_next(ledger, count):
    active = sorted(
        (e for e in ledger["entries"] if e.get("order")),
        key=lambda e: e["order"],
    )
    lines = []
    for entry in active[:count]:
        facts = entry["facts"]
        pr = f"#{entry['pr']}" if entry.get("pr") else "no PR"
        lines.append(
            f"{entry['order']}. {entry['id']} ({pr}, {entry.get('branch')})"
            f"\n   gate: {facts['gate']}"
        )
        cmd = command_for(entry)
        if cmd:
            lines.append(f"   run:  {cmd}")
    return "\n".join(lines)


def check(ledger):
    problems, warnings = [], []
    entries = ledger["entries"]
    by_id = {e["id"]: e for e in entries}
    orders = {}
    for entry in entries:
        eid = entry["id"]
        if not entry.get("branch"):
            problems.append(f"{eid}: no branch")
        if entry.get("order"):
            orders.setdefault(entry["order"], []).append(eid)
        for dep in entry.get("depends_on", []):
            if dep not in by_id:
                problems.append(f"{eid}: unknown dependency {dep!r}")
            elif (by_id[dep].get("order") or 10**6) >= (entry.get("order") or 10**6):
                problems.append(f"{eid}: dependency {dep} does not come earlier")
            if by_id.get(dep, {}).get("facts", {}).get("state") != "merged":
                if entry.get("facts", {}).get("state") == "ready":
                    problems.append(f"{eid}: its PR is ready while {dep} is unmerged")
        for dep in entry.get("after", []):
            if dep not in by_id:
                problems.append(f"{eid}: unknown ordering entry {dep!r}")
            elif (by_id[dep].get("order") or 10**6) > (entry.get("order") or 10**6):
                problems.append(f"{eid}: it is ordered before {dep} but comes after it")
        if entry.get("folded") and entry.get("facts", {}).get("pr_state") == "OPEN":
            problems.append(f"{eid}: folded but its PR is still open")
        if entry.get("facts", {}).get("head_drift"):
            warnings.append(f"{eid}: local branch is not the PR head")
    for order, ids in orders.items():
        if len(ids) > 1:
            problems.append(f"order {order} is shared by {', '.join(ids)}")
    chains = {}
    for entry in entries:
        facts = entry.get("facts", {})
        if entry.get("pr") and facts.get("state") in ("ready", "conflict"):
            chains.setdefault(entry.get("chain", entry["id"]), []).append(entry["id"])
    for chain, ids in chains.items():
        if len(ids) > 1:
            problems.append(
                f"chain {chain}: more than one PR meant to merge ({', '.join(ids)})"
            )
    return problems, warnings


def main(argv=None):
    parser = argparse.ArgumentParser(
        description="Print and refresh the merge-stack ledger of wiz-pl/wiz."
    )
    parser.add_argument("--ledger", type=Path, default=None,
                        help="the ledger file (default: $WIZ_STACK_LEDGER, else stack-ledger.json in the notes directory)")
    parser.add_argument("--notes", metavar="DIR", default=None,
                        help="the notes directory that holds stack-ledger.json (default: $WIZ_NOTES_DIR)")
    parser.add_argument("--write", action="store_true", help="update the ledger file")
    parser.add_argument("--json", action="store_true", help="print refreshed JSON")
    parser.add_argument("--next", type=int, metavar="N", help="the next N actions")
    parser.add_argument("--check", action="store_true", help="fail on unsafe ordering")
    parser.add_argument("--no-gh", action="store_true", help="no GitHub calls")
    parser.add_argument("--fetch", action="store_true", help="git fetch origin first")
    args = parser.parse_args(argv)

    args.ledger = resolve_ledger(args.ledger, args.notes)
    if args.ledger is None:
        print("stack-status: no ledger given: pass --ledger FILE or --notes DIR, "
              "or set WIZ_STACK_LEDGER or WIZ_NOTES_DIR", file=sys.stderr)
        return 2
    if not args.ledger.is_file():
        print(f"stack-status: no ledger at {args.ledger}", file=sys.stderr)
        return 2
    try:
        ledger = json.loads(args.ledger.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        print(f"stack-status: cannot read {args.ledger}: {exc}", file=sys.stderr)
        return 2
    if "entries" not in ledger:
        print("stack-status: ledger has no entries", file=sys.stderr)
        return 2

    if args.fetch:
        run(["git", "-C", str(REPO), "fetch", "origin"])
    ledger = refresh(ledger, use_gh=not args.no_gh)

    if args.write:
        args.ledger.write_text(
            json.dumps(ledger, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
        )
    if args.json:
        print(json.dumps(ledger, indent=2, ensure_ascii=False))
    elif args.next:
        print(show_next(ledger, args.next))
    else:
        print(table(ledger))
        print(
            f"\nmaster {ledger.get('master', '?')[:8]}  "
            f"checked {ledger.get('updated')}  ledger {args.ledger}"
        )

    problems, warnings = [], []
    if args.check:
        problems, warnings = check(ledger)
    for warning in warnings:
        print(f"stack-status: note: {warning}", file=sys.stderr)
    if problems:
        for problem in problems:
            print(f"stack-status: {problem}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
