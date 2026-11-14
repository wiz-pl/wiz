#!/usr/bin/env python3
"""A deterministic source tarball of Wiz, with a manifest (attestation input).

    scripts/source-tarball.py [--root DIR] [--out DIR] [--mode git|tree|auto]
                             [--name NAME] [--revision REV] [--epoch SECONDS]

Writes three files to OUT (default: the current directory):

    wiz-<version>-src.tar.gz                 the source tree, one top directory
    wiz-<version>-src.tar.gz.manifest.json   canonical JSON (sorted keys, compact, no
                                             trailing newline): every path, its size,
                                             its SHA-256, and the tree digest
    wiz-<version>-src.tar.gz.sha256          the tarball's `sha256sum` line

The tarball is byte-for-byte reproducible for one git commit (and one gzip/zlib):
entries are sorted, every mtime is the source date epoch, uid/gid are 0 with empty
uname/gname, file modes are normalised to 0644 (0755 when executable) and directories
to 0755, and the gzip header carries the epoch and no file name. `SOURCE_DATE_EPOCH`
is honoured; without it the commit time is used, and outside a git checkout 0.

File selection. In `git` mode (`auto` when ROOT is inside a checkout) the file list is
`git ls-files`: tracked files only, so no untracked scratch file and no build output
can leak in. In `tree` mode every regular file under ROOT is included (Nix builds from
a filtered store path, which has no .git). Both modes drop the VCS and cache
directories, build outputs and the `drafts/` tree; see EXCLUDED_* below. The manifest
records the list exactly.

Exit status: 0 written, 2 usage or input error.
"""

from __future__ import annotations

import argparse
import gzip
import hashlib
import io
import json
import os
import re
import subprocess
import sys
import tarfile

SCHEMA = "wiz-source-tarball/v1"

# Directories (by any path component) that are never source: VCS and tool state,
# caches, package-manager and build directories.
EXCLUDED_DIRS = {
    ".git", ".lake", ".grail", ".wiz-cache", ".devenv", ".direnv", ".scratch",
    "node_modules", "__pycache__", ".mypy_cache", ".pytest_cache", ".venv",
    "dist", "out", "target", "cc-bundle", "bundle-downloads", "_build",
}

# Build outputs and other generated files (suffixes), and files a developer's tools
# write next to the sources. None of these is tracked today; they are excluded
# defensively so a dirty checkout cannot change a tarball.
EXCLUDED_SUFFIXES = (
    ".olean", ".ilean", ".o", ".obj", ".a", ".so", ".dylib", ".dll", ".lib",
    ".pyc", ".pyo", ".class", ".jar", ".hi", ".beam", ".exe", ".tmp", ".swp",
    ".swo", ".orig", ".rej",
)
EXCLUDED_FILES = {
    ".DS_Store", "grail.local.wiz", "wiz-toolchain.local", "Tests/Groups.lean",
    ".pre-commit-config.yaml",
}
# `web/out/` is a build directory; `drafts/` is wishful code the release does not build.
EXCLUDED_PREFIXES = ("drafts/", "web/out/")

_VERSION_RE = re.compile(r'def\s+version\s*:\s*String\s*:=\s*"([^"]+)"')


def die(msg: str) -> "NoReturn":  # type: ignore[name-defined]
    print(f"source-tarball: {msg}", file=sys.stderr)
    raise SystemExit(2)


def is_excluded(rel: str) -> bool:
    """True when the repository-relative path REL is not source."""
    parts = rel.split("/")
    if any(p in EXCLUDED_DIRS for p in parts[:-1]):
        return True
    base = parts[-1]
    if base in EXCLUDED_DIRS or rel in EXCLUDED_FILES or base in EXCLUDED_FILES:
        return True
    if base.startswith(".devenv"):
        return True
    if any(rel == p or rel.startswith(p) for p in EXCLUDED_PREFIXES):
        return True
    return base.endswith(EXCLUDED_SUFFIXES)


def git_files(root: str) -> list[str]:
    try:
        out = subprocess.run(
            ["git", "-C", root, "ls-files", "-z"],
            check=True, capture_output=True,
        ).stdout
    except (OSError, subprocess.CalledProcessError) as e:
        die(f"{root} is not a git checkout ({e}); use --mode tree")
    return [p for p in out.decode("utf-8", "surrogateescape").split("\0") if p]


def tree_files(root: str) -> list[str]:
    out: list[str] = []
    for dirpath, dirnames, filenames in os.walk(root):
        rel = os.path.relpath(dirpath, root)
        rel = "" if rel == "." else rel.replace(os.sep, "/")
        dirnames[:] = sorted(
            d for d in dirnames if not is_excluded(f"{rel}/{d}" if rel else d)
        )
        for name in sorted(filenames):
            path = f"{rel}/{name}" if rel else name
            if not is_excluded(path):
                out.append(path)
    return out


def checked_files(root: str, paths: list[str]) -> list[str]:
    """The source files among PATHS, in byte order of their names."""
    out = []
    for rel in (p for p in paths if not is_excluded(p)):
        full = os.path.join(root, *rel.split("/"))
        if os.path.islink(full):
            die(f"{rel}: symlinks are not supported in the source tarball")
        if not os.path.isfile(full):
            die(f"{rel}: tracked but missing (or not a regular file)")
        out.append(rel)
    return sorted(out, key=lambda p: p.encode("utf-8", "surrogateescape"))


def version_of(root: str) -> str:
    try:
        with open(os.path.join(root, "Wiz", "Version.lean"), encoding="utf-8") as f:
            m = _VERSION_RE.search(f.read())
    except OSError:
        m = None
    return m.group(1) if m else "0.0.0"


def git_epoch(root: str) -> int | None:
    try:
        out = subprocess.run(
            ["git", "-C", root, "log", "-1", "--format=%ct"],
            check=True, capture_output=True, text=True,
        ).stdout.strip()
        return int(out)
    except (OSError, ValueError, subprocess.CalledProcessError):
        return None


def source_date_epoch(arg: str | None, root: str) -> int:
    """The explicit epoch, else SOURCE_DATE_EPOCH, else the commit time, else 0."""
    if arg is not None:
        value = arg
    elif os.environ.get("SOURCE_DATE_EPOCH", "") != "":
        value = os.environ["SOURCE_DATE_EPOCH"]
    else:
        commit = git_epoch(root)
        return 0 if commit is None else commit
    try:
        epoch = int(value)
    except ValueError:
        die(f"source date epoch {value!r} is not an integer")
    if not 0 <= epoch < 2**33:
        die(f"source date epoch {epoch} is out of range")
    return epoch


def file_mode(full: str) -> int:
    return 0o755 if os.stat(full).st_mode & 0o111 else 0o644


def tar_info(name: str, mode: int, epoch: int, size: int = 0,
             kind: bytes = tarfile.REGTYPE) -> tarfile.TarInfo:
    ti = tarfile.TarInfo(name)
    ti.type = kind
    ti.mode = mode
    ti.size = size
    ti.mtime = epoch
    ti.uid = ti.gid = 0
    ti.uname = ti.gname = ""
    return ti


def write_tarball(path: str, prefix: str, root: str, files: list[str],
                  manifest_files: list[dict], epoch: int) -> None:
    # Every directory holding a file is an entry of its own, so an empty directory in
    # the checkout (none today) cannot change the result either.
    dirs = {prefix}
    for rel in files:
        parts = rel.split("/")[:-1]
        for i in range(1, len(parts) + 1):
            dirs.add(prefix + "/" + "/".join(parts[:i]))
    names = sorted(dirs | {prefix + "/" + f["path"] for f in manifest_files},
                   key=lambda n: n.encode("utf-8", "surrogateescape"))
    by_path = {f["path"]: f for f in manifest_files}

    with open(path, "wb") as raw:
        # gzip's own header must not carry the time or a file name (tarfile's w:gz
        # would); the stream is otherwise a function of the tar bytes and zlib.
        with gzip.GzipFile(fileobj=raw, mode="wb", compresslevel=9,
                           mtime=epoch, filename="") as gz:
            with tarfile.open(fileobj=gz, mode="w", format=tarfile.GNU_FORMAT) as tar:
                for name in names:
                    if name in dirs:
                        tar.addfile(tar_info(name, 0o755, epoch,
                                             kind=tarfile.DIRTYPE))
                        continue
                    rel = name[len(prefix) + 1:]
                    f = by_path[rel]
                    full = os.path.join(root, *rel.split("/"))
                    with open(full, "rb") as fh:
                        data = fh.read()
                    if hashlib.sha256(data).hexdigest() != f["sha256"]:
                        die(f"{rel}: changed while the tarball was built")
                    tar.addfile(tar_info(name, int(f["mode"], 8), epoch,
                                         size=len(data)), io.BytesIO(data))


def manifest_for(root: str, files: list[str]) -> tuple[list[dict], str, int]:
    entries, tree, total = [], hashlib.sha256(), 0
    for rel in files:
        full = os.path.join(root, *rel.split("/"))
        with open(full, "rb") as f:
            data = f.read()
        digest = hashlib.sha256(data).hexdigest()
        entries.append({
            "path": rel,
            "size": len(data),
            "sha256": digest,
            "mode": f"{file_mode(full):04o}",
        })
        tree.update(digest.encode() + b"  " + rel.encode() + b"\n")
        total += len(data)
    return entries, tree.hexdigest(), total


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(
        description="write a deterministic source tarball and its manifest")
    ap.add_argument("--root", default=".", help="the checkout or tree (default: .)")
    ap.add_argument("--out", default=".", help="where to write (default: .)")
    ap.add_argument("--mode", choices=("auto", "git", "tree"), default="auto",
                    help="file list: git ls-files (git) or every file (tree); "
                         "auto uses git when ROOT is inside a checkout")
    ap.add_argument("--name", help="top directory and file stem "
                                   "(default: wiz-<version>)")
    ap.add_argument("--revision", help="commit to record (default: git HEAD, else "
                                       "'unknown')")
    ap.add_argument("--epoch", help="mtime for every entry (default: "
                                    "SOURCE_DATE_EPOCH, the commit time, or 0)")
    args = ap.parse_args(argv)

    root = os.path.abspath(args.root)
    if not os.path.isdir(root):
        die(f"{args.root} is not a directory")
    mode = args.mode
    if mode == "auto":
        # `.git` is a directory in a clone and a file in a worktree; either is a checkout
        mode = "git" if os.path.exists(os.path.join(root, ".git")) else "tree"

    raw = git_files(root) if mode == "git" else tree_files(root)
    files = checked_files(root, raw)
    if not files:
        die(f"no source files under {root}")
    name = args.name or f"wiz-{version_of(root)}"
    revision = args.revision
    if revision is None:
        try:
            revision = subprocess.run(
                ["git", "-C", root, "rev-parse", "HEAD"],
                check=True, capture_output=True, text=True).stdout.strip()
        except (OSError, subprocess.CalledProcessError):
            revision = "unknown"
    epoch = source_date_epoch(args.epoch, root)

    outdir = os.path.abspath(args.out)
    os.makedirs(outdir, exist_ok=True)
    stem = f"{name}-src"
    tar_path = os.path.join(outdir, f"{stem}.tar.gz")
    manifest_path = tar_path + ".manifest.json"
    sha_path = tar_path + ".sha256"

    entries, tree_digest, total = manifest_for(root, files)
    write_tarball(tar_path, name, root, files, entries, epoch)

    with open(tar_path, "rb") as f:
        tarball_sha = hashlib.sha256(f.read()).hexdigest()
    tarball_size = os.path.getsize(tar_path)

    manifest = {
        "schema": SCHEMA,
        "name": name,
        "revision": revision,
        "sourceDateEpoch": epoch,
        "tarball": {"file": os.path.basename(tar_path),
                    "sha256": tarball_sha, "size": tarball_size},
        "tree": {"sha256": tree_digest, "files": len(entries), "bytes": total},
        "files": entries,
    }
    # Canonical JSON: sorted keys, compact separators, no trailing newline, so the
    # manifest's bytes (and therefore its SHA-256) depend only on its content.
    text = json.dumps(manifest, sort_keys=True, separators=(",", ":"))
    with open(manifest_path, "w", encoding="utf-8", newline="\n") as f:
        f.write(text)
    with open(sha_path, "w", encoding="utf-8", newline="\n") as f:
        f.write(f"{tarball_sha}  {os.path.basename(tar_path)}\n")

    print(tar_path)
    print(f"sha256 {tarball_sha}")
    print(f"tree {tree_digest} ({len(entries)} files, {total} bytes)")
    print(manifest_path)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
