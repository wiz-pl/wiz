#!/usr/bin/env python3
"""Fail when the release packet no longer describes the tree.

The release notes, the checklist and `release-manifest.json` are written by hand
at a candidate commit and then edited by later pull requests.  That is how 0.1
came to say "prepared at `672d3bfb`", quote pull-request and commit counts for a
tree that had already moved, and advertise a `*-src.tar.gz` that no script in
the tree can build.  This check makes those claims executable.  It is cheap: no
build, no dependency beyond Python 3, git and (for the PR counts) `gh`.

Checked files: `docs/release/*.md` and `docs/release/release-manifest.json`.

Checks
  candidate   Every candidate mention in the release docs and the manifest
              resolves to the same commit.  That commit is an ancestor of HEAD
              and is the commit the notes describe: its subject is the claimed
              "merge of #N", its committer date (and the manifest's
              `sourceDateEpoch`) is the claimed date, and the first commit the
              notes name is the root.  `--for-tag` additionally requires it to
              be HEAD, which is the tagging pull request's invariant.  The
              candidate must stay in one of the machine-readable forms
              ("Candidate commit: `<sha>`", "prepared ... at commit `<sha>`",
              "current candidate is `<sha>`", or a sentence-initial
              "At `<sha>`"); a file with no candidate mention fails.
  counts      Commit counts are `git rev-list --count`; pull-request counts are
              `gh pr list --state merged` filtered by merge-commit ancestry,
              so they do not depend on the clock.  A file may instead carry
                  <!-- release-counts: historical as of YYYY-MM-DD -->
              to say its numbers are a dated snapshot; they are then reported
              as historical and not verified.  The PR table in
              `v0.1-prs.md` is checked offline: its rows are unique, its merge
              commits are in the candidate range, and the row count agrees.
  artifacts   Every artifact the manifest advertises is a file in the tree, has
              a `producer` file that exists, or is explicit:
                  "status": "outstanding", "note": "why it is not here yet"
              Once `tag` is filled (the release run), an outstanding artifact
              or a null hash is a failure: an outstanding artifact cannot ship.
  checklist   A repository path named by a checkbox item exists, unless the
              item is unticked and its section says the work is outstanding
              ("unmerged", "not on master", ...).  A ticked item may never name
              a missing file: ticking is the claim that it exists.  Reviewed
              exceptions go in ALLOW with a reason, and an exception that no
              longer matches (because the file landed) is itself a failure.

What this cannot check
  * Network and `gh`: pull-request counts cannot be verified offline.  Without
    `gh`, or when it fails, the check exits 2 unless the counts are marked
    historical with a date.  `--offline` requests that behaviour explicitly.
  * The tag before it exists: before the tag there is nothing to resolve.  If
    the manifest names a tag and `--for-tag` is given but the tag does not
    exist, the tag equality is unverifiable (2), not wrong.  After the tag the
    same check verifies `tag -> candidate`.
  * Shallow clones: an unresolvable candidate or count base in a shallow clone
    is unverifiable (2), with advice to fetch history, not a wrong SHA.
  * Whether CI or a build passed.  The manifest's `checks` object records a
    claim; use the run id it gives.  This script only checks internal
    consistency and the tree, not the world.

Usage
  scripts/check-release-consistency.py              check this checkout
  scripts/check-release-consistency.py --self-test  run the built-in fixtures
  scripts/check-release-consistency.py --root DIR   check another checkout
  scripts/check-release-consistency.py --for-tag    require the candidate to be HEAD
  scripts/check-release-consistency.py --offline    do not call gh (see above)
  scripts/check-release-consistency.py --quiet      only problems and the summary
  scripts/check-release-consistency.py --repo OWNER/REPO  gh repository
                                                    (default: origin's GitHub remote)

Exit status: 0 clean (warnings allowed), 1 the packet is wrong, 2 unverifiable
(no full history, no `gh`/network, a tag that does not exist yet) or a usage
error.  When both a wrong answer and an unverifiable check are found, 1 wins.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from dataclasses import dataclass, field
from pathlib import Path

RELEASE_DIR = Path("docs/release")
MANIFEST_REL = RELEASE_DIR / "release-manifest.json"
CHECKLIST_REL = RELEASE_DIR / "v0.1-checklist.md"
PRS_REL = RELEASE_DIR / "v0.1-prs.md"

SHA = r"[0-9a-f]{7,40}"
DATE = r"\d{4}-\d{2}-\d{2}"

# Candidate mentions.  The sentence-initial "At `672d3bfb`", "on master at"
# and "through" forms catch the prose references as well as the formal lines;
# every one must name the same commit, or an edit updated only some of them.
CANDIDATE_PATTERNS = (
    re.compile(rf"Candidate commit:\s*`(?P<sha>{SHA})`"),
    re.compile(
        rf"prepared\s+from\s+`?master`?\s+at\s+commit\s+`(?P<sha>{SHA})`"
    ),
    re.compile(rf"current candidate is\s+`(?P<sha>{SHA})`"),
    # A sentence-initial "At `SHA`", or "on master at `SHA`", names the
    # candidate; a bare "at `SHA`" also matches unrelated trains ("measured on
    # the integration/selfhost train at `20877066`"), so it is not used.
    re.compile(rf"(?<![\w`])At\s+`(?P<sha>{SHA})`"),
    re.compile(rf"on\s+`?master`?\s+at\s+`(?P<sha>{SHA})`"),
    re.compile(rf"through\s+`(?P<sha>{SHA})`"),
    re.compile(rf"before\s+`(?P<sha>{SHA})`\s+\(the\s+merge of #\d+\)"),
)
PREVIOUS_PATTERNS = (
    re.compile(rf"previous candidate was\s+`(?P<sha>{SHA})`"),
    re.compile(rf"previous (?:draft's )?candidate\s+`(?P<sha>{SHA})`"),
    re.compile(rf"merged (?:after|since)\s+`(?P<sha>{SHA})`"),
    re.compile(rf"after\s+`(?P<sha>{SHA})`"),
    re.compile(rf"\bcandidate\s+`(?P<sha>{SHA})`"),
)
FIRST_PATTERNS = (
    re.compile(rf"first commit\s+`(?P<sha>{SHA})`"),
    re.compile(rf"from the first commit\s+`(?P<sha>{SHA})`"),
)
MERGE_OF_RE = re.compile(r"the\s+merge of #(?P<pr>\d+)", re.IGNORECASE)
CANDIDATE_DATE_RE = re.compile(
    rf"\((?P<date>{DATE}),\s*the\s+merge of #(?P<pr>\d+)\)"
)
PREVIOUS_DATE_RE = re.compile(rf"Since the (?P<date>{DATE}) candidate")

# Count claims.  Named by the quantity each pattern carries; a claim of kind
# "total" is about the whole history to the candidate, "range" about
# previous..candidate.
COUNT_PATTERNS = (
    (
        "total",
        re.compile(
            r"all\s+(?P<commits>[\d,]+)\s+commits\s+and\s+"
            r"(?P<prs>[\d,]+)\s+merged pull requests"
        ),
    ),
    (
        "range",
        re.compile(
            r"(?P<prs>[\d,]+)\s+merged pull requests\s+"
            r"\((?P<commits>[\d,]+)\s+commits\)"
        ),
    ),
    (
        "range",
        re.compile(
            r"(?P<commits>[\d,]+)\s+commits\s+and\s+"
            r"(?P<prs>[\d,]+)\s+merged pull requests\s+earlier"
        ),
    ),
    (
        "range",
        re.compile(
            r"(?P<prs>[\d,]+)\s+pull requests\s+and\s+"
            r"(?P<commits>[\d,]+)\s+commits\s+landed between"
        ),
    ),
    (
        "range",
        re.compile(
            r"(?:The\s+)?(?P<prs>[\d,]+)\s+pull requests\s+merged (?:after|into)"
        ),
    ),
    ("range", re.compile(r"lists those\s+(?P<prs>[\d,]+)\s+pull requests")),
)

HISTORICAL_RE = re.compile(
    rf"<!--\s*release-counts:\s*historical\s+as\s+of\s+(?P<date>{DATE})\s*-->",
    re.IGNORECASE,
)

PR_ROW_RE = re.compile(rf"^\|\s*#(?P<pr>\d+)\s*\|.*?`(?P<sha>{SHA})`\s*\|\s*$")

# A checkbox item is a line "- [ ] ..." or "- [x] ..." and its continuation
# lines.  A section is a "## " heading and the text before its first item.
ITEM_RE = re.compile(r"^(\s*)- \[(?P<mark>[ xX])\]\s+(?P<text>.*)$")
SECTION_RE = re.compile(r"^##\s+(?P<title>.*)$")
FENCE_RE = re.compile(r"^\s*(```|~~~)")

# Words that make a missing path in an *unticked* item an explicit promise to
# add it, rather than a stale reference.  They are deliberately few.
OUTSTANDING_WORDS = (
    "unmerged",
    "not on `master`",
    "not on master",
    "there is no",
    "does not exist",
    "excluded",
    "generated",
    "workflow writes",
    "writes to",
    "attached",
    "created at release time",
    "built at release time",
    "installed release tarball",
)

# Bare names the checklist uses as shorthand.  Resolve them, so the check does
# not have to guess whether `ci.yml` means the workflow.
BARE_NAMES = {
    "ci.yml": ".github/workflows/ci.yml",
    "release.yml": ".github/workflows/release.yml",
    "tower-init.sh": "scripts/tower-init.sh",
    "release-manifest.json": "docs/release/release-manifest.json",
}

ROOT_FILES = {
    "CHANGELOG.md",
    "COPYING.RUNTIME",
    "LICENSE",
    "README.md",
    "ROADMAP.md",
    "flake.lock",
    "flake.nix",
    "lake-manifest.json",
    "lakefile.lean",
    "lean-toolchain",
}

# Paths the checklist names as build outputs, local configuration or generated
# files.  They are not supposed to be checked in, so a missing one is not a
# broken reference; a ticked item may still name one (it names where a command
# writes), and the command is what the tick is about.
GENERATED = {
    ".lake": "the Lake build directory",
    "Tests/Groups.lean": "generated by the test driver",
    "grail.local.wiz": "local test configuration, not checked in",
    "wiz-toolchain.local": "local toolchain override, not checked in",
    "web/out": "web build output",
}


@dataclass(frozen=True)
class Allow:
    """A reviewed exception: `path` may be absent from this checkout."""

    path: str
    reason: str


# Keep this empty unless a path really is legitimately absent and the checklist
# does not already say so.  An entry whose path exists is reported as stale.
ALLOW: tuple[Allow, ...] = ()


@dataclass
class Report:
    problems: list[str] = field(default_factory=list)
    unverifiable: list[str] = field(default_factory=list)
    warnings: list[str] = field(default_factory=list)
    notes: list[str] = field(default_factory=list)
    checks: int = 0

    def wrong(self, message: str) -> None:
        self.problems.append(message)

    def cannot(self, message: str) -> None:
        self.unverifiable.append(message)

    def warn(self, message: str) -> None:
        self.warnings.append(message)

    def note(self, message: str) -> None:
        self.notes.append(message)

    def status(self) -> int:
        if self.problems:
            return 1
        if self.unverifiable:
            return 2
        return 0


@dataclass(frozen=True)
class Claim:
    path: str
    line: int
    kind: str  # "total" or "range"
    commits: int | None
    prs: int | None


@dataclass(frozen=True)
class Mention:
    path: str
    line: int
    sha: str
    kind: str  # "candidate", "previous", "first"


# --- git and gh -------------------------------------------------------------------


def git(root: Path, *args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["git", "-C", str(root), *args],
        capture_output=True,
        text=True,
    )


def is_git_checkout(root: Path) -> bool:
    result = git(root, "rev-parse", "--git-dir")
    return result.returncode == 0


def is_shallow(root: Path) -> bool:
    result = git(root, "rev-parse", "--is-shallow-repository")
    return result.stdout.strip() == "true"


def resolve(root: Path, sha: str) -> str | None:
    """The full commit SHA for `sha`, or None when it does not resolve."""
    result = git(root, "rev-parse", "--verify", "--quiet", f"{sha}^{{commit}}")
    if result.returncode != 0:
        return None
    return result.stdout.strip()


def commit_field(root: Path, sha: str, fmt: str) -> str:
    return git(root, "show", "-s", f"--format={fmt}", sha).stdout.strip()


def is_ancestor(root: Path, ancestor: str, descendant: str) -> bool:
    result = git(root, "merge-base", "--is-ancestor", ancestor, descendant)
    return result.returncode == 0


def rev_count(root: Path, spec: str) -> int:
    return int(git(root, "rev-list", "--count", spec).stdout.strip())


def github_repo(root: Path) -> str | None:
    result = git(root, "remote", "get-url", "origin")
    if result.returncode != 0:
        return None
    url = result.stdout.strip()
    match = re.search(r"github\.com[:/](?P<repo>[^/]+/[^/]+?)(?:\.git)?$", url)
    return match.group("repo") if match else None


def gh_merged_prs(
    root: Path, repo: str, limit: int = 1000
) -> tuple[list[dict] | None, str]:
    """Merged PRs, or (None, reason) when the answer cannot be verified."""
    exe = shutil.which("gh")
    if exe is None:
        return None, "gh is not installed"
    try:
        result = subprocess.run(
            [
                exe,
                "pr",
                "list",
                "-R",
                repo,
                "--state",
                "merged",
                "--limit",
                str(limit),
                "--json",
                "number,mergeCommit,mergedAt",
            ],
            cwd=root,
            capture_output=True,
            text=True,
            timeout=120,
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        return None, f"gh failed: {exc}"
    if result.returncode != 0:
        detail = " ".join(result.stderr.split())[:200]
        return None, f"gh exited {result.returncode}: {detail}"
    try:
        data = json.loads(result.stdout)
    except json.JSONDecodeError as exc:
        return None, f"gh returned invalid JSON: {exc}"
    if not isinstance(data, list):
        return None, "gh returned an unexpected document"
    if len(data) >= limit:
        return None, f"gh returned the {limit}-PR limit; raise it or page the query"
    return data, ""


# --- parsing helpers --------------------------------------------------------------


def release_docs(root: Path) -> list[Path]:
    directory = root / RELEASE_DIR
    if not directory.is_dir():
        return []
    return sorted(
        (path for path in directory.glob("*.md") if path.is_file()),
        key=lambda path: path.as_posix(),
    )


def read_text(root: Path, path: Path) -> str | None:
    try:
        return path.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError):
        return None


def rel(root: Path, path: Path) -> str:
    return path.relative_to(root).as_posix()


def mentions(root: Path) -> tuple[list[Mention], list[int]]:
    """Candidate, previous and first-commit mentions, and their line numbers."""
    found: list[Mention] = []
    unreadable: list[int] = []
    seen: set[tuple[str, int, str, str]] = set()
    for path in release_docs(root):
        text = read_text(root, path)
        if text is None:
            unreadable.append(1)
            continue
        for lineno, line in enumerate(text.splitlines(), 1):
            for kind, patterns in (
                ("candidate", CANDIDATE_PATTERNS),
                ("previous", PREVIOUS_PATTERNS),
                ("first", FIRST_PATTERNS),
            ):
                for pattern in patterns:
                    for match in pattern.finditer(line):
                        sha = match.group("sha")
                        key = (rel(root, path), lineno, sha, kind)
                        if key in seen:
                            continue
                        seen.add(key)
                        found.append(Mention(rel(root, path), lineno, sha, kind))
    return found, unreadable


def count_claims(root: Path) -> list[Claim]:
    claims: list[Claim] = []
    seen: set[tuple[str, int, int | None, int | None]] = set()
    for path in release_docs(root):
        text = read_text(root, path)
        if text is None:
            continue
        for lineno, line in enumerate(text.splitlines(), 1):
            for kind, pattern in COUNT_PATTERNS:
                match = pattern.search(line)
                if match is None:
                    continue
                groups = match.groupdict()
                commits = (
                    int(groups["commits"].replace(",", ""))
                    if groups.get("commits")
                    else None
                )
                prs = (
                    int(groups["prs"].replace(",", ""))
                    if groups.get("prs")
                    else None
                )
                key = (rel(root, path), lineno, commits, prs)
                if key in seen:
                    continue
                seen.add(key)
                claims.append(Claim(rel(root, path), lineno, kind, commits, prs))
    return claims


def historical_marker(root: Path) -> tuple[str, str] | None:
    for path in release_docs(root):
        text = read_text(root, path)
        if text is None:
            continue
        match = HISTORICAL_RE.search(text)
        if match is not None:
            return rel(root, path), match.group("date")
    return None


def pr_table(root: Path) -> tuple[list[tuple[int, int, str]], list[int]]:
    """Rows of v0.1-prs.md as (line, PR number, merge SHA), and unreadable lines."""
    path = root / PRS_REL
    text = read_text(root, path)
    if text is None:
        return [], [1]
    rows: list[tuple[int, int, str]] = []
    for lineno, line in enumerate(text.splitlines(), 1):
        match = PR_ROW_RE.match(line)
        if match is not None:
            rows.append((lineno, int(match.group("pr")), match.group("sha")))
    return rows, []


# --- the checks -------------------------------------------------------------------


def check_candidate(
    root: Path, manifest: dict, report: Report, for_tag: bool
) -> str | None:
    """Check the candidate mentions; return the full candidate SHA when known."""
    found, unreadable = mentions(root)
    if unreadable:
        report.cannot(
            "docs/release has a file that is not readable UTF-8; cannot check "
            "the candidate"
        )
        return None

    candidates = [m for m in found if m.kind == "candidate"]
    previous = [m for m in found if m.kind == "previous"]
    first = [m for m in found if m.kind == "first"]

    manifest_sha = manifest.get("commit")
    if not isinstance(manifest_sha, str) or not re.fullmatch(SHA, manifest_sha):
        report.wrong(
            f"{MANIFEST_REL}: commit must be a 7-40 character hex SHA, "
            f"got {manifest_sha!r}"
        )
    else:
        candidates.append(
            Mention(MANIFEST_REL.as_posix(), 0, manifest_sha, "candidate")
        )

    if not candidates:
        report.wrong(
            "no candidate commit is named in docs/release/*.md or "
            f"{MANIFEST_REL}"
        )
        return None

    resolved: dict[str, list[Mention]] = {}
    for mention in candidates:
        full = resolve(root, mention.sha)
        if full is None:
            if is_shallow(root):
                report.cannot(
                    f"{mention.path}:{mention.line}: {mention.sha} is not in this "
                    "shallow clone; fetch full history (git fetch --unshallow)"
                )
            else:
                report.wrong(
                    f"{mention.path}:{mention.line}: candidate {mention.sha} "
                    "does not resolve to a commit"
                )
            return None
        resolved.setdefault(full, []).append(mention)

    if len(resolved) > 1:
        detail = "; ".join(
            f"{full} ({', '.join(sorted({m.path for m in ms}))})"
            for full, ms in sorted(resolved.items())
        )
        report.wrong(f"the release files name different candidates: {detail}")
        return None

    candidate = next(iter(resolved))
    report.checks += 1
    report.note(
        f"candidate {candidate[:12]} named {len(resolved[candidate])} time(s) "
        "and consistent"
    )

    head = resolve(root, "HEAD")
    if head is None:
        report.cannot("HEAD does not resolve to a commit")
    elif not is_ancestor(root, candidate, head):
        report.wrong(
            f"candidate {candidate[:12]} is not an ancestor of HEAD "
            f"({head[:12]}); the notes describe a tree that is not in this history"
        )
    elif for_tag and head != candidate:
        behind = rev_count(root, f"{candidate}..HEAD")
        report.wrong(
            f"--for-tag: HEAD is {head[:12]}, but the candidate is "
            f"{candidate[:12]} ({behind} commit(s) ahead); the tag would describe "
            "a different tree"
        )
    elif head != candidate:
        ahead = rev_count(root, f"{candidate}..HEAD")
        report.warn(
            f"candidate {candidate[:12]} is {ahead} commit(s) behind HEAD "
            f"({head[:12]}); pass --for-tag at the tagging PR, or move the "
            "candidate and its counts"
        )

    subject = commit_field(root, candidate, "%s")
    subject_pr = re.search(r"Merge pull request #(\d+)", subject)
    for mention in candidates:
        line_text = ""
        text = read_text(root, root / mention.path) if mention.line else None
        if text is not None:
            line_text = text.splitlines()[mention.line - 1]
        merge = MERGE_OF_RE.search(line_text)
        if merge and subject_pr is not None:
            if merge.group("pr") != subject_pr.group(1):
                report.wrong(
                    f"{mention.path}:{mention.line}: says the candidate is the "
                    f"merge of #{merge.group('pr')}, but its subject is "
                    f"'{subject}'"
                )

    # The date and the merge number in the parenthetical "(DATE, the merge of #N)".
    expected_date = commit_field(root, candidate, "%cs")
    for path in release_docs(root):
        text = read_text(root, path)
        if text is None:
            continue
        for lineno, line in enumerate(text.splitlines(), 1):
            for match in CANDIDATE_DATE_RE.finditer(line):
                if match.group("date") != expected_date:
                    report.wrong(
                        f"{rel(root, path)}:{lineno}: candidate date "
                        f"{match.group('date')} is not its committer date "
                        f"{expected_date}"
                    )
                if subject_pr is not None and match.group("pr") != subject_pr.group(1):
                    report.wrong(
                        f"{rel(root, path)}:{lineno}: says the candidate is the "
                        f"merge of #{match.group('pr')}, but its subject is "
                        f"'{subject}'"
                    )
            for match in PREVIOUS_DATE_RE.finditer(line):
                if previous:
                    full = resolve(root, previous[0].sha)
                    if full is not None:
                        expected = commit_field(root, full, "%cs")
                        if match.group("date") != expected:
                            report.wrong(
                                f"{rel(root, path)}:{lineno}: previous candidate "
                                f"date {match.group('date')} is not its committer "
                                f"date {expected}"
                            )

    if first:
        roots = git(root, "rev-list", "--max-parents=0", candidate).stdout.split()
        for mention in first:
            full = resolve(root, mention.sha)
            if full is None:
                report.wrong(
                    f"{mention.path}:{mention.line}: first commit {mention.sha} "
                    "does not resolve"
                )
            elif full not in roots:
                report.wrong(
                    f"{mention.path}:{mention.line}: {mention.sha} is not the "
                    f"root commit of the candidate ({', '.join(s[:12] for s in roots)})"
                )

    epoch = manifest.get("sourceDateEpoch")
    expected_epoch = commit_field(root, candidate, "%ct")
    if epoch is None:
        report.wrong(f"{MANIFEST_REL}: sourceDateEpoch is not filled")
    elif str(epoch) != expected_epoch:
        report.wrong(
            f"{MANIFEST_REL}: sourceDateEpoch {epoch} is not the candidate's "
            f"committer time {expected_epoch}"
        )

    return candidate


def check_counts(
    root: Path,
    report: Report,
    candidate: str,
    offline: bool,
    repo: str | None,
) -> None:
    claims = count_claims(root)
    marker = historical_marker(root)
    if marker is not None:
        path, date = marker
        report.warn(
            f"{path}: counts are marked historical as of {date}; they are not "
            "verified against this tree"
        )
        report.note("historical counts are allowed, but they cannot be current")
        return
    if not claims:
        report.wrong(
            "no PR/commit counts are stated, and no "
            "'<!-- release-counts: historical as of YYYY-MM-DD -->' marker says "
            "they are historical"
        )
        return

    previous: str | None = None
    previous_mentions = [m for m in mentions(root)[0] if m.kind == "previous"]
    if previous_mentions:
        previous_shas = {resolve(root, m.sha) for m in previous_mentions}
        if None in previous_shas:
            missing = next(m for m in previous_mentions if resolve(root, m.sha) is None)
            if is_shallow(root):
                report.cannot(
                    f"the previous candidate {missing.sha} is not in this shallow "
                    "clone; fetch full history"
                )
                return
            report.wrong(
                f"{missing.path}:{missing.line}: previous candidate {missing.sha} "
                "does not resolve"
            )
            return
        previous_shas.discard(None)
        if len(previous_shas) > 1:
            report.wrong(
                "the release files name different previous candidates: "
                + ", ".join(sorted(s[:12] for s in previous_shas))
            )
            return
        previous = previous_shas.pop()
        if not is_ancestor(root, previous, candidate):
            report.wrong(
                f"the previous candidate {previous[:12]} is not an ancestor of "
                f"the candidate {candidate[:12]}; the range counts are undefined"
            )
            return

    total_commits = rev_count(root, candidate)
    range_commits = (
        rev_count(root, f"{previous}..{candidate}")
        if previous
        else total_commits
    )

    prs = None
    total_prs = None
    range_prs = None
    if not offline:
        if repo is None:
            report.cannot(
                "cannot find the GitHub repository from origin; pass --repo, or "
                "--offline to skip the PR counts"
            )
        else:
            prs, reason = gh_merged_prs(root, repo)
            if prs is None:
                report.cannot(
                    f"PR counts are unverifiable: {reason}. Fetch history and set "
                    "GH_TOKEN (CI: ${{ github.token }}), or mark the counts "
                    "historical with a date"
                )
            else:
                if is_shallow(root):
                    report.cannot(
                        "the checkout is shallow, so gh's merge commits cannot be "
                        "placed in the candidate's history"
                    )
                    prs = None
                else:
                    total_prs = 0
                    range_prs = 0
                    missing = 0
                    for pr in prs:
                        merge = (pr.get("mergeCommit") or {}).get("oid")
                        if not merge:
                            # A squash-merge or a PR with no merge commit cannot
                            # be in this history's merge-commit record.
                            continue
                        if resolve(root, merge) is None:
                            missing += 1
                            continue
                        if not is_ancestor(root, merge, candidate):
                            continue
                        total_prs += 1
                        if previous is None or not is_ancestor(root, merge, previous):
                            range_prs += 1
                    if missing:
                        report.note(
                            f"{missing} merged PR(s) name a merge commit absent "
                            "from this clone; they are newer than the candidate "
                            "unless history was rewritten"
                        )
    else:
        report.cannot(
            "PR counts are unverifiable with --offline; mark them historical "
            "with a date to accept that"
        )

    for claim in claims:
        if claim.commits is not None:
            expected = total_commits if claim.kind == "total" else range_commits
            if claim.commits != expected:
                where = (
                    "all history"
                    if claim.kind == "total"
                    else "the candidate range"
                )
                report.wrong(
                    f"{claim.path}:{claim.line}: claims {claim.commits} commits "
                    f"for {where}, but git rev-list says {expected}"
                )
        if claim.prs is not None and prs is not None:
            expected = total_prs if claim.kind == "total" else range_prs
            if expected is not None and claim.prs != expected:
                where = (
                    "all history"
                    if claim.kind == "total"
                    else "the candidate range"
                )
                report.wrong(
                    f"{claim.path}:{claim.line}: claims {claim.prs} merged pull "
                    f"requests for {where}, but gh says {expected}"
                )
    report.checks += 1
    report.note(
        f"counts: {total_commits} commits to the candidate, {range_commits} in "
        f"the range"
        + ("" if prs is None else f"; {total_prs} PRs total, {range_prs} in the range")
    )

    # The checked-in PR table is evidence that can be checked offline.
    rows, unreadable = pr_table(root)
    if unreadable:
        report.wrong(f"{PRS_REL}: cannot read the PR table")
    elif not rows:
        report.wrong(f"{PRS_REL}: has no PR rows")
    else:
        numbers = [pr for _, pr, _ in rows]
        if len(set(numbers)) != len(numbers):
            duplicates = sorted({n for n in numbers if numbers.count(n) > 1})
            report.wrong(
                f"{PRS_REL}: duplicate PR rows: "
                + ", ".join(f"#{n}" for n in duplicates)
            )
        for lineno, number, sha in rows:
            full = resolve(root, sha)
            if full is None:
                report.wrong(
                    f"{PRS_REL}:{lineno}: merge commit {sha} for #{number} does "
                    "not resolve"
                )
                continue
            if not is_ancestor(root, full, candidate):
                report.wrong(
                    f"{PRS_REL}:{lineno}: merge commit {sha} for #{number} is not "
                    "an ancestor of the candidate"
                )
            elif previous is not None and is_ancestor(root, full, previous):
                report.wrong(
                    f"{PRS_REL}:{lineno}: merge commit {sha} for #{number} is at "
                    "or before the previous candidate"
                )
            if prs is not None:
                match = next(
                    (p for p in prs if int(p.get("number", -1)) == number), None
                )
                if match is not None:
                    oid = (match.get("mergeCommit") or {}).get("oid")
                    if oid and not oid.startswith(sha.lower()):
                        report.wrong(
                            f"{PRS_REL}:{lineno}: #{number} names merge commit "
                            f"{sha}, but gh says {oid[:12]}"
                        )
        range_claim = next((c.prs for c in claims if c.kind == "range" and c.prs), None)
        if range_claim is not None and len(rows) != range_claim:
            report.wrong(
                f"{PRS_REL}: lists {len(rows)} pull requests, but the notes claim "
                f"{range_claim}"
            )
        report.note(f"PR table: {len(rows)} unique row(s), merge commits in range")
        report.checks += 1


def artifact_verdict(root: Path, name: object, entry: object) -> tuple[str, str]:
    """Return (verdict, detail) for one advertised artifact.

    verdict is "present", "outstanding", "producer" or "missing".
    """
    if not isinstance(name, str) or not name:
        return "missing", "the manifest entry has no name"
    if Path(name).is_absolute() or ".." in Path(name).parts:
        return "missing", f"{name!r}: the artifact name must be a path inside the tree"
    if not isinstance(entry, dict):
        return "missing", f"{name}: the manifest entry is not an object"
    for relative in (name, f"dist/{name}"):
        path = root / relative
        if path.is_file():
            return "present", relative
    status = entry.get("status")
    note = entry.get("note") or entry.get("reason")
    if status is not None and status != "outstanding":
        return "missing", (
            f"{name}: unknown status {status!r} (only 'outstanding' is allowed)"
        )
    if status == "outstanding":
        if not isinstance(note, str) or not note.strip():
            return "missing", (
                f"{name}: status is outstanding but there is no note saying why"
            )
        return "outstanding", note.strip()
    producer = entry.get("producer")
    if producer is None:
        return "missing", (
            f"{name}: not in the tree, no producer, and not marked "
            '"status": "outstanding"'
        )
    if not isinstance(producer, str) or not producer.strip():
        return "missing", f"{name}: producer is not a path"
    if Path(producer).is_absolute() or ".." in Path(producer).parts:
        return "missing", (
            f"{name}: producer {producer!r} must be a path inside the tree"
        )
    if not (root / producer).is_file():
        return "missing", f"{name}: producer {producer} does not exist"
    return "producer", producer


def check_artifacts(root: Path, manifest: dict, report: Report) -> None:
    tag = manifest.get("tag")
    tagged = tag is not None

    entries: list[tuple[str, object, object]] = []
    source = manifest.get("source")
    if isinstance(source, dict) and isinstance(source.get("tarball"), dict):
        tarball = source["tarball"]
        entries.append(("source.tarball", tarball.get("name"), tarball))
    artifacts = manifest.get("artifacts")
    if isinstance(artifacts, list):
        for index, entry in enumerate(artifacts):
            name = entry.get("name") if isinstance(entry, dict) else None
            entries.append((f"artifacts[{index}]", name, entry))
    elif artifacts is not None:
        report.wrong(f"{MANIFEST_REL}: artifacts must be an array")

    if not entries:
        report.wrong(f"{MANIFEST_REL}: no artifacts are advertised")
        return

    by_name: dict[str, list[tuple[str, object]]] = {}
    for where, name, entry in entries:
        verdict, detail = artifact_verdict(root, name, entry)
        if verdict == "missing":
            report.wrong(f"{MANIFEST_REL} {where}: {detail}")
        else:
            report.note(f"{MANIFEST_REL} {where}: {name} {verdict} ({detail})")
        if verdict == "outstanding" and tagged:
            report.wrong(
                f"{MANIFEST_REL} {where}: {name} is still outstanding, but tag "
                f"{tag!r} is filled; an outstanding artifact cannot ship"
            )
        if tagged and isinstance(entry, dict):
            for key in ("sha256", "size"):
                if entry.get(key) is None:
                    report.wrong(
                        f"{MANIFEST_REL} {where}: {name} has no {key}, but tag "
                        f"{tag!r} is filled"
                    )
        if isinstance(name, str):
            by_name.setdefault(name, []).append((where, entry))

    for name, duplicates in by_name.items():
        if len(duplicates) > 1:
            statuses = {
                entry.get("status") if isinstance(entry, dict) else None
                for _, entry in duplicates
            }
            if len(statuses) > 1:
                report.wrong(
                    f"{MANIFEST_REL}: {name} is advertised with different statuses: "
                    f"{sorted(str(s) for s in statuses)}"
                )
            report.warn(
                f"{MANIFEST_REL}: {name} is listed in more than one place "
                f"({', '.join(where for where, _ in duplicates)})"
            )

    if tagged:
        for key in ("generatedAt", "filledBy"):
            if manifest.get(key) is None:
                report.wrong(
                    f"{MANIFEST_REL}: {key} is null, but tag {tag!r} is filled"
                )
    report.checks += 1


def top_directories(root: Path) -> set[str]:
    directories = {path.name for path in root.iterdir() if path.is_dir()}
    directories.add(".github")
    return directories


def path_token(token: str, top: set[str]) -> str | None:
    """A repository-relative path named by a checklist token, or None."""
    token = token.strip("`'\"(),;:")
    token = token.rstrip(".")
    if not token:
        return None
    if token.startswith("/") or token.startswith("-"):
        return None
    if any(char in token for char in "*<>${}~|\\"):
        return None
    if token in BARE_NAMES:
        return BARE_NAMES[token]
    if token in ROOT_FILES:
        return token
    if "#" in token:
        token = token.split("#", 1)[0]
    if token.startswith("./"):
        token = token[2:]
    if "/" not in token:
        return None
    first = token.split("/", 1)[0]
    if first not in top:
        return None
    if token.endswith("/"):
        token = token.rstrip("/")
    return token


def checklist_items(text: str) -> list[tuple[int, bool, str, str]]:
    """Items as (line, ticked, item text, section preamble)."""
    lines = text.splitlines()
    starts = [index for index, line in enumerate(lines) if SECTION_RE.match(line)]
    items: list[tuple[int, bool, str, str]] = []
    for position, start in enumerate(starts):
        end = starts[position + 1] if position + 1 < len(starts) else len(lines)
        first_item = next(
            (index for index in range(start + 1, end) if ITEM_RE.match(lines[index])),
            end,
        )
        preamble = "\n".join(lines[start + 1 : first_item])
        index = first_item
        while index < end:
            match = ITEM_RE.match(lines[index])
            if match is None:
                index += 1
                continue
            item_start = index
            index += 1
            while index < end and ITEM_RE.match(lines[index]) is None:
                index += 1
            body = "\n".join(lines[item_start:index])
            items.append(
                (item_start + 1, match.group("mark").lower() == "x", body, preamble)
            )
    return items


def refs_in(text: str, top: set[str]) -> list[str]:
    found: list[str] = []

    def add(raw: str) -> None:
        token = path_token(raw, top)
        if token is not None:
            found.append(token)

    # A code span can be a command (`scripts/trust-ledger.sh --update`), so
    # split it and look at each word; a flag is not a path.
    for match in re.finditer(r"`([^`\n]+)`", text):
        for word in match.group(1).split():
            add(word)
    in_fence = False
    for line in text.splitlines():
        if FENCE_RE.match(line):
            in_fence = not in_fence
            continue
        if not in_fence:
            continue
        for raw in line.split():
            add(raw)
    return found


def check_checklist(root: Path, report: Report) -> None:
    path = root / CHECKLIST_REL
    text = read_text(root, path)
    if text is None:
        report.wrong(f"{CHECKLIST_REL}: cannot read the checklist")
        return

    top = top_directories(root)
    used_allow: set[int] = set()
    items = checklist_items(text)
    referenced = 0
    for line, ticked, body, preamble in items:
        for token in dict.fromkeys(refs_in(body, top)):
            referenced += 1
            exists = (root / token).exists()
            if token in GENERATED:
                report.note(
                    f"{CHECKLIST_REL}:{line}: {token} is a generated/local path "
                    f"({GENERATED[token]}), not a checked-in input"
                )
                continue
            allowed_index = next(
                (i for i, exception in enumerate(ALLOW) if exception.path == token),
                None,
            )
            if exists:
                if allowed_index is not None:
                    used_allow.add(allowed_index)
                    report.wrong(
                        f"ALLOW[{allowed_index}]: {token} exists now; remove the "
                        f"exception ({ALLOW[allowed_index].reason})"
                    )
                continue
            if ticked:
                report.wrong(
                    f"{CHECKLIST_REL}:{line}: ticked item names missing file "
                    f"{token}; a tick is the claim that it exists"
                )
                continue
            context = f"{preamble}\n{body}".lower()
            if any(word in context for word in OUTSTANDING_WORDS):
                report.note(
                    f"{CHECKLIST_REL}:{line}: {token} is missing and the section "
                    "marks the work outstanding"
                )
                continue
            if allowed_index is not None:
                used_allow.add(allowed_index)
                report.note(
                    f"{CHECKLIST_REL}:{line}: {token} is missing (reviewed: "
                    f"{ALLOW[allowed_index].reason})"
                )
                continue
            report.wrong(
                f"{CHECKLIST_REL}:{line}: unticked item names missing file {token} "
                "without saying the work is outstanding (or add a reviewed ALLOW "
                "entry)"
            )

    for index, exception in enumerate(ALLOW):
        if index not in used_allow:
            # It was used only if its path was referenced and missing; an
            # exception for a path the checklist no longer names is dead too.
            if exception.path not in text:
                report.wrong(
                    f"ALLOW[{index}]: {exception.path} is not named by the "
                    f"checklist ({exception.reason})"
                )
            elif (root / exception.path).exists():
                report.wrong(
                    f"ALLOW[{index}]: {exception.path} exists now; remove the "
                    f"exception ({exception.reason})"
                )

    report.checks += 1
    report.note(
        f"checklist: {len(items)} item(s), {referenced} path reference(s)"
    )


def check(root: Path, for_tag: bool, offline: bool, report: Report,
          repo: str | None) -> None:
    if not is_git_checkout(root):
        report.cannot(f"{root} is not a git checkout")
        return
    manifest_path = root / MANIFEST_REL
    try:
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        report.wrong(f"{MANIFEST_REL}: cannot read the manifest: {exc}")
        return
    if not isinstance(manifest, dict):
        report.wrong(f"{MANIFEST_REL}: the manifest is not an object")
        return

    if not offline and repo is None:
        repo = github_repo(root)

    candidate = check_candidate(root, manifest, report, for_tag)
    if candidate is not None:
        check_counts(root, report, candidate, offline, repo)
    check_artifacts(root, manifest, report)

    tag = manifest.get("tag")
    if isinstance(tag, str) and tag:
        resolved = resolve(root, tag)
        if resolved is None:
            report.cannot(
                f"{MANIFEST_REL}: tag {tag!r} does not exist in this checkout; "
                "tag equality is unverifiable before the tag is created (or "
                "when the clone did not fetch tags)"
            )
        elif candidate is not None and resolved != candidate:
            report.wrong(
                f"{MANIFEST_REL}: tag {tag!r} points at {resolved[:12]}, not "
                f"the candidate {candidate[:12]}"
            )
        else:
            report.note(f"tag {tag!r} points at the candidate")
    elif for_tag:
        report.note(
            "no tag is named yet, so tag equality is not checked; that is "
            "expected before the tag is created"
        )
    check_checklist(root, report)


# --- self-test --------------------------------------------------------------------


def _run_git(root: Path, *args: str) -> None:
    env = {
        "GIT_AUTHOR_NAME": "Fixture",
        "GIT_AUTHOR_EMAIL": "fixture@example.invalid",
        "GIT_COMMITTER_NAME": "Fixture",
        "GIT_COMMITTER_EMAIL": "fixture@example.invalid",
        "GIT_AUTHOR_DATE": "2026-11-17T21:16:02+0000",
        "GIT_COMMITTER_DATE": "2026-11-17T21:16:02+0000",
    }
    subprocess.run(
        ["git", "-C", str(root), *args],
        check=True,
        capture_output=True,
        text=True,
        env={**os.environ, **env},
    )


def self_test() -> int:
    failures: list[str] = []

    def check_equal(name: str, got: object, expected: object) -> None:
        if got != expected:
            failures.append(f"{name}: expected {expected!r}, got {got!r}")

    # Parsing: candidate, previous and first mentions.
    text = (
        "prepared from `master` at commit `672d3bfb` (2026-11-17, the merge of #471)\n"
        "Candidate commit: `672d3bfb8d20`\n"
        "The previous candidate was `ed9cff34`; at `672d3bfb` it says so.\n"
        "from the first commit `0c6fec97` through `672d3bfb`\n"
    )
    with tempfile.TemporaryDirectory(prefix="wiz-release-consistency-") as tmp:
        root = Path(tmp)
        (root / "docs" / "release").mkdir(parents=True)
        (root / "docs" / "release" / "fixture.md").write_text(text, encoding="utf-8")
        found, _ = mentions(root)
        kinds = [(m.kind, m.sha) for m in found]
        check_equal("candidate mentions", sorted(set(kinds)), sorted(set([
            ("candidate", "672d3bfb"),
            ("candidate", "672d3bfb8d20"),
            ("previous", "ed9cff34"),
            ("first", "0c6fec97"),
        ])))

        # Count claims of both kinds.
        (root / "docs" / "release" / "fixture.md").write_text(
            "all 2,761 commits and 385 merged pull requests\n"
            "114 merged pull requests (808 commits)\n"
            "is 808 commits and 114 merged pull requests earlier\n"
            "The 114 pull requests merged after `ed9cff34`\n",
            encoding="utf-8",
        )
        claims = count_claims(root)
        claim_key = lambda c: (c.kind, c.commits or 0, c.prs or 0)
        check_equal(
            "count claims",
            [(c.kind, c.commits, c.prs) for c in sorted(claims, key=claim_key)],
            sorted([
                ("total", 2761, 385),
                ("range", 808, 114),
                ("range", 808, 114),
                ("range", None, 114),
            ], key=lambda c: (c[0], c[1] or 0, c[2] or 0)),
        )

        # Historical marker.
        (root / "docs" / "release" / "fixture.md").write_text(
            "<!-- release-counts: historical as of 2026-11-17 -->\n",
            encoding="utf-8",
        )
        check_equal("historical marker", historical_marker(root),
                    ("docs/release/fixture.md", "2026-11-17"))

        # Artifact verdicts.
        (root / "scripts").mkdir()
        (root / "scripts" / "build.sh").write_text("#!/bin/sh\n", encoding="utf-8")
        (root / "x.tar.gz").write_text("fixture\n", encoding="utf-8")
        check_equal("artifact present",
                    artifact_verdict(root, "x.tar.gz", {})[0], "present")
        (root / "x.tar.gz").unlink()
        check_equal("artifact outstanding",
                    artifact_verdict(
                        root, "x.tar.gz",
                        {"status": "outstanding", "note": "unmerged work"},
                    ),
                    ("outstanding", "unmerged work"))
        check_equal("artifact outstanding needs a note",
                    artifact_verdict(root, "x.tar.gz", {"status": "outstanding"})[0],
                    "missing")
        check_equal(
            "artifact producer",
            artifact_verdict(root, "x.tar.gz", {"producer": "scripts/build.sh"}),
            ("producer", "scripts/build.sh"),
        )
        check_equal(
            "artifact producer must exist",
            artifact_verdict(root, "x.tar.gz", {"producer": "scripts/nope.sh"})[0],
            "missing",
        )
        check_equal("artifact with nothing",
                    artifact_verdict(root, "x.tar.gz", {})[0], "missing")
        check_equal("artifact name may not leave the tree",
                    artifact_verdict(root, "../x.tar.gz", {})[0], "missing")

        # Checklist: a missing path is a problem unless the unticked item says
        # the work is outstanding; a ticked item is always a problem.
        top = top_directories(root)
        item = "- [ ] `scripts/nope.py` is unmerged work\n"
        refs = refs_in(item, top)
        check_equal("checklist ref extraction", refs, ["scripts/nope.py"])
        check_equal("unticked + outstanding", any(
            word in ("unmerged\n" + item).lower() for word in OUTSTANDING_WORDS
        ), True)
        check_equal("ticked is not excused",
                    checklist_items(
                        "## Fixture\n\n- [x] `scripts/nope.py`\n"
                    )[0][1], True)

        # Git: a candidate two commits back, and counts.
        subprocess.run(["git", "init", "-q", str(root)], check=True)
        _run_git(root, "add", "-A")
        _run_git(root, "commit", "-q", "-m", "first")
        first_sha = resolve(root, "HEAD")
        (root / "a.txt").write_text("a\n", encoding="utf-8")
        _run_git(root, "add", "-A")
        _run_git(root, "commit", "-q", "-m", "Merge pull request #471 from x")
        candidate_sha = resolve(root, "HEAD")
        (root / "b.txt").write_text("b\n", encoding="utf-8")
        _run_git(root, "add", "-A")
        _run_git(root, "commit", "-q", "-m", "later")
        check_equal("ancestor", is_ancestor(root, candidate_sha, "HEAD"), True)
        check_equal("range count", rev_count(root, f"{first_sha}..{candidate_sha}"), 1)
        check_equal("root", git(root, "rev-list", "--max-parents=0",
                                candidate_sha).stdout.strip(), first_sha)
        check_equal("subject", commit_field(root, candidate_sha, "%s"),
                    "Merge pull request #471 from x")

    if failures:
        for failure in failures:
            print(f"self-test FAIL: {failure}", file=sys.stderr)
        return 1
    print("check-release-consistency self-test: ok (4 fixtures, git fixtures)")
    return 0


# --- command line -----------------------------------------------------------------


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Check that the release packet matches the tree.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
    )
    parser.add_argument(
        "--root",
        type=Path,
        default=Path(__file__).resolve().parent.parent,
        help="checkout to check (default: the one containing this script)",
    )
    parser.add_argument(
        "--for-tag",
        action="store_true",
        help="require the candidate to be HEAD (the tagging PR's invariant)",
    )
    parser.add_argument(
        "--offline",
        action="store_true",
        help="do not call gh; PR counts must be marked historical",
    )
    parser.add_argument(
        "--repo",
        default=None,
        help="GitHub OWNER/REPO for gh (default: origin's GitHub remote)",
    )
    parser.add_argument(
        "--self-test",
        action="store_true",
        help="run the built-in fixtures instead of reading the checkout",
    )
    parser.add_argument(
        "--quiet",
        action="store_true",
        help="print only problems and the summary when clean",
    )
    args = parser.parse_args(argv)

    if args.self_test:
        return self_test()

    root = args.root.resolve()
    report = Report()
    check(root, args.for_tag, args.offline, report, args.repo)

    if not args.quiet:
        for note in report.notes:
            print(f"ok: {note}")
    for warning in report.warnings:
        print(f"warning: {warning}")
    for problem in report.problems:
        print(f"wrong: {problem}")
    for problem in report.unverifiable:
        print(f"unverifiable: {problem}")

    status = report.status()
    summary = (
        f"{report.checks} check(s), {len(report.problems)} wrong, "
        f"{len(report.unverifiable)} unverifiable, {len(report.warnings)} warning(s)"
    )
    if status == 0:
        print(f"check-release-consistency: clean ({summary})")
    elif status == 1:
        print(f"\ncheck-release-consistency: FAILED ({summary})", file=sys.stderr)
    else:
        print(f"\ncheck-release-consistency: UNVERIFIABLE ({summary})", file=sys.stderr)
    return status


if __name__ == "__main__":
    sys.exit(main())
