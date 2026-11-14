#!/usr/bin/env python3
"""Self-test for scripts/check-signatures.py.

Creates throwaway repositories and throwaway SSH/GPG keys under a temporary
directory: no network, no personal key, no agent, and nothing is written to
the checkout.  Run it directly, or from the signatures CI job before the real
check:

    python3 scripts/test-check-signatures.py
"""

from __future__ import annotations

import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

CHECK = Path(__file__).with_name("check-signatures.py")
HERE = Path(__file__).resolve().parent


class Failure(AssertionError):
    pass


def run(cmd: list[str], cwd: Path | None = None, env: dict[str, str] | None = None) -> subprocess.CompletedProcess[str]:
    proc = subprocess.run(cmd, cwd=cwd, env=env, text=True, capture_output=True)
    if proc.returncode != 0:
        raise Failure(
            f"command failed ({proc.returncode}): {' '.join(cmd)}\n"
            f"stdout:\n{proc.stdout}\nstderr:\n{proc.stderr}"
        )
    return proc


def base_env(home: Path) -> dict[str, str]:
    env = os.environ.copy()
    env.update(
        HOME=str(home),
        GIT_CONFIG_GLOBAL=os.devnull,
        GIT_CONFIG_SYSTEM=os.devnull,
        GIT_CONFIG_NOSYSTEM="1",
        GIT_AUTHOR_NAME="Signature Test",
        GIT_AUTHOR_EMAIL="test@example.invalid",
        GIT_COMMITTER_NAME="Signature Test",
        GIT_COMMITTER_EMAIL="test@example.invalid",
        GIT_TERMINAL_PROMPT="0",
        LC_ALL="C",
    )
    return env


def git(repo: Path, *args: str, env: dict[str, str]) -> str:
    return run(["git", "-C", str(repo), *args], env=env).stdout


def checker(repo: Path, *args: str, env: dict[str, str], expect: int) -> str:
    proc = subprocess.run(
        [sys.executable, str(CHECK), "--repo", str(repo), *args],
        env=env, text=True, capture_output=True,
    )
    output = proc.stdout + proc.stderr
    if proc.returncode != expect:
        raise Failure(
            f"checker {' '.join(args)}: expected exit {expect}, got {proc.returncode}\n"
            f"--- output ---\n{output}"
        )
    return output


def ssh_key(path: Path, comment: str) -> Path:
    run([
        "ssh-keygen", "-q", "-t", "ed25519", "-a", "16", "-N", "", "-C", comment,
        "-f", str(path),
    ])
    return path


def new_repo(path: Path, signing_key: Path | None, env: dict[str, str]) -> Path:
    path.mkdir()
    git(path, "init", "-q", "-b", "master", env=env)
    git(path, "config", "user.name", "Signature Test", env=env)
    git(path, "config", "user.email", "test@example.invalid", env=env)
    if signing_key is not None:
        git(path, "config", "gpg.format", "ssh", env=env)
        git(path, "config", "user.signingkey", str(signing_key), env=env)
    return path


def commit(repo: Path, name: str, message: str, signed: bool, env: dict[str, str]) -> str:
    (repo / name).write_text(message + "\n")
    git(repo, "add", name, env=env)
    args = ["commit", "-q", "-m", message]
    if signed:
        args.insert(2, "-S")
    git(repo, *args, env=env)
    return git(repo, "rev-parse", "HEAD", env=env).strip()


def test_ssh(tmp: Path) -> None:
    env = base_env(tmp / "home-ssh")
    (tmp / "home-ssh").mkdir()
    key = ssh_key(tmp / "ssh-signing", "signature test <test@example.invalid>")
    repo = new_repo(tmp / "ssh-repo", key, env)
    (repo / ".github").mkdir()
    (repo / ".github" / "allowed_signers").write_text(
        f'test@example.invalid namespaces="git" {(tmp / "ssh-signing.pub").read_text().strip()}\n'
    )

    base = commit(repo, "base", "signed base", True, env)
    out = checker(repo, "--range", "HEAD^!", env=env, expect=0)
    assert "1 signed" in out, out

    unsigned = commit(repo, "unsigned", "unsigned tip", False, env)
    out = checker(repo, "--range", "HEAD^!", env=env, expect=1)
    assert "is unsigned" in out, out
    out = checker(repo, "--range", "HEAD^!", "--warn", env=env, expect=0)
    assert "warnings only" in out, out

    # A signed merge is the seal that lets a pull request's unsigned commits in.
    git(repo, "reset", "-q", "--hard", base, env=env)
    git(repo, "checkout", "-q", "-b", "feature", env=env)
    feature = commit(repo, "feature", "unsigned feature commit", False, env)
    git(repo, "checkout", "-q", "master", env=env)
    git(repo, "merge", "-q", "--no-ff", "-S", "feature", "-m", "signed merge", env=env)
    out = checker(repo, "--range", f"{base}..HEAD", env=env, expect=0)
    assert "covered by a signed merge commit" in out, out
    out = checker(repo, "--range", f"{base}..{feature}", env=env, expect=1)
    assert "is unsigned" in out, out
    out = checker(
        repo, "--range", f"{base}..HEAD", "--no-covered-by-signed-merge",
        env=env, expect=1,
    )
    assert "is unsigned" in out, out

    # Tags: annotated and signed passes; lightweight and unsigned annotated fail.
    git(repo, "tag", "-s", "v-signed", "-m", "signed tag", env=env)
    git(repo, "tag", "v-light", env=env)
    git(repo, "tag", "-a", "v-annotated", "-m", "unsigned annotated tag", env=env)
    assert "signed (ssh)" in checker(repo, "--tag", "v-signed", env=env, expect=0)
    assert "lightweight" in checker(repo, "--tag", "v-light", env=env, expect=1)
    assert "without a signature" in checker(repo, "--tag", "v-annotated", env=env, expect=1)

    # A signature from a key that is not in allowed_signers is not trusted.
    other = ssh_key(tmp / "other-signing", "other <other@example.invalid>")
    git(repo, "config", "user.signingkey", str(other), env=env)
    commit(repo, "other", "signed by an untrusted key", True, env)
    out = checker(repo, "--range", "HEAD^!", env=env, expect=1)
    assert "bad or untrusted" in out, out

    # A private key in a trust file is refused before verification.
    git(repo, "config", "user.signingkey", str(key), env=env)
    (repo / "private_signers").write_text(key.read_text())
    out = checker(
        repo, "--range", "HEAD^!", "--allowed-signers", str(repo / "private_signers"),
        env=env, expect=2,
    )
    assert "private key material" in out, out
    print("ok ssh: signed, unsigned, merge seal, tags, unknown key, secret guard")


def gpg_key(tmp: Path, env: dict[str, str]) -> tuple[Path, str]:
    home = tmp / "gnupg"
    home.mkdir(mode=0o700)
    env["GNUPGHOME"] = str(home)
    run([
        "gpg", "--batch", "--passphrase", "", "--quick-gen-key",
        "GPG Test <test@example.invalid>", "ed25519", "sign", "0",
    ], env=env)
    fpr = run(
        ["gpg", "--list-secret-keys", "--with-colons"], env=env
    ).stdout.split("fpr:::::::::")[1].split(":")[0]
    public = tmp / "gpg-public.asc"
    public.write_text(run(["gpg", "--armor", "--export", fpr], env=env).stdout)
    return public, fpr


def test_gpg(tmp: Path) -> None:
    env = base_env(tmp / "home-gpg")
    (tmp / "home-gpg").mkdir()
    public, fpr = gpg_key(tmp, env)
    repo = new_repo(tmp / "gpg-repo", None, env)
    git(repo, "config", "user.signingkey", fpr, env=env)
    git(repo, "config", "commit.gpgsign", "true", env=env)
    git(repo, "config", "tag.gpgSign", "true", env=env)
    commit(repo, "base", "gpg signed", True, env)

    out = checker(repo, "--range", "HEAD^!", "--gpg-key", str(public), env=env, expect=0)
    assert "signed (gpg)" in out, out
    out = checker(repo, "--range", "HEAD^!", env=env, expect=1)
    assert "no public key" in out.lower(), out

    # Public keys in .github/gpg/ are discovered without an option.
    (repo / ".github" / "gpg").mkdir(parents=True)
    shutil.copy(public, repo / ".github" / "gpg" / "test.asc")
    out = checker(repo, "--range", "HEAD^!", env=env, expect=0)
    assert "signed (gpg)" in out, out

    git(repo, "tag", "-s", "v-gpg", "-m", "gpg signed tag", env=env)
    out = checker(repo, "--tag", "v-gpg", "--gpg-key", str(public), env=env, expect=0)
    assert "signed (gpg)" in out, out
    print("ok gpg: commit, tag, public key directory, missing key")


def main() -> int:
    if shutil.which("ssh-keygen") is None:
        print("test-check-signatures: ssh-keygen is required", file=sys.stderr)
        return 2
    if shutil.which("gpg") is None:
        print("test-check-signatures: gpg is required", file=sys.stderr)
        return 2
    with tempfile.TemporaryDirectory(prefix="wiz-signatures-test-") as directory:
        tmp = Path(directory)
        try:
            test_ssh(tmp)
            test_gpg(tmp)
        except Failure as exc:
            print(f"FAIL: {exc}", file=sys.stderr)
            return 1
    print("test-check-signatures: all checks passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
