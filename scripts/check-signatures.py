#!/usr/bin/env python3
"""Check commit and tag signatures for the repository's signing policy.

The policy is deliberately about *boundaries*: a commit that arrives on a
protected branch must either carry a signature this repository trusts, or be an
ancestor of a signed merge commit in the same range.  The second case is how a
pull request lands: GitHub (or a maintainer) signs the merge commit, and that
signature covers the tree and every commit the merge brings in.  Automation
worktrees therefore commit unsigned and never need a human key.

Examples
  scripts/check-signatures.py --range origin/master..HEAD
  scripts/check-signatures.py --rev HEAD
  scripts/check-signatures.py --tag v0.1.0
  scripts/check-signatures.py --gpg-key ~/.config/wiz/web-flow.gpg --range A..B

Trust inputs, all public:
  .github/allowed_signers   ssh-keygen allowed-signers lines (SSH signatures)
  .github/gpg/*.asc         exported public keys (GPG signatures)
  --gpg-key FILE            extra public key(s), e.g. GitHub's web-flow key

No private key is read, and the script never changes repository or user
configuration: it verifies with a temporary GNUPGHOME and a temporary copy of
the allowed-signers file.
"""

from __future__ import annotations

import argparse
import json
import os
import shutil
import subprocess
import sys
import tempfile
from dataclasses import dataclass, field
from pathlib import Path


@dataclass
class Result:
    sha: str
    subject: str
    kind: str | None  # "ssh", "gpg", or None when unsigned
    state: str  # signed, covered, unsigned, bad
    detail: str = ""


@dataclass
class Summary:
    commits: list[Result] = field(default_factory=list)
    tags: list[Result] = field(default_factory=list)
    errors: list[str] = field(default_factory=list)

    @property
    def failed(self) -> bool:
        return bool(self.errors) or any(
            r.state in {"unsigned", "bad"} for r in self.commits + self.tags
        )


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv)
    repo = Path(args.repo or ".").resolve()
    root = run_git(repo, "rev-parse", "--show-toplevel")
    if root.returncode != 0:
        return die(f"{repo} is not a git repository: {root.stderr.strip()}")
    root = Path(root.stdout.strip())

    allowed = Path(args.allowed_signers or root / ".github" / "allowed_signers")
    if args.allowed_signers and not allowed.is_file():
        return die(f"allowed-signers file not found: {allowed}")
    gpg_keys = discover_gpg_keys(root, args.gpg_key)

    with tempfile.TemporaryDirectory(prefix="wiz-signatures-") as tmp:
        tmpdir = Path(tmp)
        allowed_copy = tmpdir / "allowed_signers"
        allowed_copy.write_text(allowed.read_text() if allowed.is_file() else "")
        if args.check_key_files:
            problem = private_material(allowed, gpg_keys)
            if problem:
                return die(problem)

        gnupg = tmpdir / "gnupg"
        gnupg.mkdir(mode=0o700)
        if gpg_keys and shutil.which("gpg") is None:
            return die("gpg is not installed but --gpg-key/…/.github/gpg/*.asc was given")
        for key in gpg_keys:
            imported = subprocess.run(
                ["gpg", "--batch", "--no-tty", "--homedir", str(gnupg),
                 "--import", str(key)],
                text=True, capture_output=True,
            )
            if imported.returncode != 0:
                return die(
                    f"cannot import public key {key}:\n{imported.stderr.strip()}"
                )

        env = verification_env(gnupg, allowed_copy)
        summary = Summary()

        if args.range or args.rev:
            commits = collect_range(root, args.range, args.rev)
            summary.commits = check_commits(
                root, commits, env, allowed_copy, args.covered_by_signed_merge
            )

        for tag in args.tag:
            summary.tags.append(check_tag(root, tag, env, allowed_copy))

        return report(summary, args)


def parse_args(argv: list[str] | None) -> argparse.Namespace:
    p = argparse.ArgumentParser(
        description="Verify Wiz's commit and tag signing policy.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__.split("Examples", 1)[1] if "Examples" in __doc__ else None,
    )
    p.add_argument("--repo", help="repository to inspect (default: current directory)")
    p.add_argument(
        "--range",
        help="git revision range to check, e.g. BEFORE..AFTER or origin/master..HEAD",
    )
    p.add_argument(
        "--rev",
        action="append",
        default=[],
        help="check only this commit (repeatable); default with no --range/--rev: HEAD",
    )
    p.add_argument(
        "--tag",
        action="append",
        default=[],
        help="check that this annotated tag is signed (repeatable)",
    )
    p.add_argument(
        "--allowed-signers",
        help="allowed-signers file (default: .github/allowed_signers)",
    )
    p.add_argument(
        "--gpg-key",
        action="append",
        default=[],
        help="import this public key for GPG verification (repeatable)",
    )
    p.add_argument(
        "--no-covered-by-signed-merge",
        dest="covered_by_signed_merge",
        action="store_false",
        help="require every commit to be signed itself (no merge-commit seal)",
    )
    p.add_argument(
        "--check-key-files",
        action=argparse.BooleanOptionalAction,
        default=True,
        help="refuse to use a trust file that contains private key material",
    )
    p.add_argument(
        "--warn",
        action="store_true",
        help="report policy failures but exit 0 (for pull-request checks)",
    )
    p.add_argument("--json", action="store_true", help="print a JSON summary")
    p.add_argument("--quiet", action="store_true", help="only the summary line")
    args = p.parse_args(argv)
    if not args.range and not args.rev and not args.tag:
        args.rev = ["HEAD"]
    return args


def run_git(repo: Path, *args: str, env: dict[str, str] | None = None) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["git", "-C", str(repo), *args],
        text=True,
        capture_output=True,
        env=env,
    )


def discover_gpg_keys(root: Path, extra: list[str]) -> list[Path]:
    keys = [Path(p) for p in extra]
    directory = root / ".github" / "gpg"
    if directory.is_dir():
        keys.extend(sorted(p for p in directory.iterdir() if p.suffix in {".asc", ".gpg", ".pub"}))
    return keys


def private_material(allowed: Path, gpg_keys: list[Path]) -> str:
    """A public trust file that contains a private key is a leak, not a key."""
    files = ([allowed] if allowed.is_file() else []) + gpg_keys
    for path in files:
        try:
            text = path.read_text(errors="replace")
        except OSError:
            continue
        if "PRIVATE KEY" in text:
            return f"{path} looks like private key material; only public keys belong in the repository"
    return ""


def verification_env(gnupg: Path, allowed: Path) -> dict[str, str]:
    """Environment for reproducible verification.

    Nulling the global and system configuration keeps a developer's trust
    settings (or a CI runner's) from changing the verdict; the repository's
    local config is still read, and the two settings that matter are passed
    with -c by verify().
    """
    env = os.environ.copy()
    env["GNUPGHOME"] = str(gnupg)
    env["GIT_CONFIG_GLOBAL"] = os.devnull
    env["GIT_CONFIG_SYSTEM"] = os.devnull
    env["GIT_CONFIG_NOSYSTEM"] = "1"
    env["GIT_TERMINAL_PROMPT"] = "0"
    env["GPG_TTY"] = ""
    env["LC_ALL"] = "C"
    return env


def verify_command(repo: Path, allowed: Path, args: list[str]) -> list[str]:
    return [
        "git", "-C", str(repo),
        "-c", f"gpg.ssh.allowedSignersFile={allowed}",
        "-c", "gpg.ssh.program=ssh-keygen",
        "-c", "gpg.openpgp.program=gpg",
        "-c", "gpg.minTrustLevel=undefined",
        "-c", "log.showSignature=false",
        *args,
    ]


def collect_range(root: Path, rng: str | None, revs: list[str]) -> list[str]:
    if rng:
        proc = run_git(root, "rev-list", "--reverse", "--topo-order", rng)
        if proc.returncode != 0:
            raise SystemExit(f"bad revision range {rng!r}: {proc.stderr.strip()}")
        return proc.stdout.split()
    commits: list[str] = []
    for rev in revs:
        # `rev^!` is the commit itself, not its history.
        proc = run_git(root, "rev-list", "--reverse", "--topo-order", f"{rev}^!")
        if proc.returncode != 0:
            raise SystemExit(f"bad revision {rev!r}: {proc.stderr.strip()}")
        commits.extend(proc.stdout.split())
    return commits


def signature_kind(root: Path, sha: str) -> str | None:
    body = run_git(root, "cat-file", "commit", sha).stdout
    if not any(line.startswith("gpgsig") for line in body.splitlines()):
        return None
    if "BEGIN SSH SIGNATURE" in body:
        return "ssh"
    if "BEGIN PGP SIGNATURE" in body:
        return "gpg"
    return "unknown"


def check_commits(
    root: Path,
    commits: list[str],
    env: dict[str, str],
    allowed: Path,
    covered_by_signed_merge: bool,
) -> list[Result]:
    results: list[Result] = []
    signed_merges: list[str] = []

    for sha in commits:
        subject = run_git(root, "show", "-s", "--format=%s", sha).stdout.strip()
        kind = signature_kind(root, sha)
        if kind is None:
            results.append(Result(sha, subject, None, "unsigned"))
            continue
        proc = subprocess.run(
            verify_command(root, allowed, ["verify-commit", sha]),
            text=True, capture_output=True, env=env,
        )
        output = (proc.stdout + proc.stderr).strip()
        if proc.returncode == 0:
            results.append(Result(sha, subject, kind, "signed", output))
            parents = run_git(root, "rev-list", "--parents", "-n", "1", sha).stdout.split()
            if len(parents) > 2:
                signed_merges.append(sha)
        else:
            results.append(Result(sha, subject, kind, "bad", output))

    if covered_by_signed_merge and signed_merges and results:
        covered = set(
            run_git(root, "rev-list", *signed_merges).stdout.split()
        ) & {r.sha for r in results}
        for result in results:
            if result.state == "unsigned" and result.sha in covered:
                result.state = "covered"

    return results


def check_tag(root: Path, tag: str, env: dict[str, str], allowed: Path) -> Result:
    kind_proc = run_git(root, "cat-file", "-t", tag)
    if kind_proc.returncode != 0:
        return Result(tag, "", None, "bad", f"no such tag: {tag}")
    if kind_proc.stdout.strip() != "tag":
        return Result(tag, "", None, "bad", "lightweight tag (only annotated tags can be signed)")
    body = run_git(root, "cat-file", "tag", tag).stdout
    kind = "ssh" if "BEGIN SSH SIGNATURE" in body else (
        "gpg" if "BEGIN PGP SIGNATURE" in body else None
    )
    if kind is None:
        return Result(tag, "", None, "unsigned", "annotated tag without a signature")
    proc = subprocess.run(
        verify_command(root, allowed, ["tag", "-v", tag]),
        text=True, capture_output=True, env=env,
    )
    output = (proc.stdout + proc.stderr).strip()
    state = "signed" if proc.returncode == 0 else "bad"
    return Result(tag, "", kind, state, output)


def report(summary: Summary, args: argparse.Namespace) -> int:
    if args.json:
        print(json.dumps(
            {
                "commits": [r.__dict__ for r in summary.commits],
                "tags": [r.__dict__ for r in summary.tags],
                "errors": summary.errors,
                "ok": not summary.failed,
            },
            indent=2,
        ))
        return 0 if (not summary.failed or args.warn) else 1

    def line(text: str) -> None:
        if not args.quiet or text.startswith("checked "):
            print(text)

    annotations = os.environ.get("GITHUB_ACTIONS") == "true"
    for result in summary.commits:
        short = result.sha[:10]
        if result.state == "signed":
            line(f"  ok   {short} signed ({result.kind}): {result.subject}")
        elif result.state == "covered":
            line(f"  ok   {short} unsigned, covered by a signed merge commit: {result.subject}")
        elif result.state == "unsigned":
            msg = f"{short} is unsigned and no signed merge commit covers it: {result.subject}"
            if annotations:
                print(f"::{'warning' if args.warn else 'error'}::{msg}")
            line(f"  FAIL {msg}")
        else:
            msg = f"{short} has a bad or untrusted {result.kind} signature: {result.subject}"
            if annotations:
                print(f"::{'warning' if args.warn else 'error'}::{msg}")
            line(f"  FAIL {msg}")
            if result.detail:
                line(indent(result.detail))

    for result in summary.tags:
        if result.state == "signed":
            line(f"  ok   tag {result.sha} signed ({result.kind})")
        else:
            msg = f"tag {result.sha}: {result.detail or result.state}"
            if annotations:
                print(f"::{'warning' if args.warn else 'error'}::{msg}")
            line(f"  FAIL {msg}")

    for error in summary.errors:
        line(f"  ERROR {error}")

    signed = sum(r.state == "signed" for r in summary.commits)
    covered = sum(r.state == "covered" for r in summary.commits)
    failed = sum(r.state in {"unsigned", "bad"} for r in summary.commits) + sum(
        r.state in {"unsigned", "bad"} for r in summary.tags
    )
    line(
        f"checked {len(summary.commits)} commit(s) and {len(summary.tags)} tag(s): "
        f"{signed} signed, {covered} covered, {failed} failing"
    )
    if summary.failed:
        if args.warn:
            line("signature policy: warnings only (--warn)")
            return 0
        line("signature policy: FAILED (see docs/signing.md)")
        return 1
    return 0


def indent(text: str, prefix: str = "         ") -> str:
    return "\n".join(prefix + line for line in text.splitlines())


def die(message: str) -> int:
    print(f"check-signatures: {message}", file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main())
