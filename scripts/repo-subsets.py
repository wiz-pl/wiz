#!/usr/bin/env python3
"""Content hashes of the repository's build subsets, from the tracked files.

CI keys caches on "the whole tree" today (`hashFiles('**/*.lean', …)`), so a
documentation edit and a compiler edit look the same. A *subset* is a group of
paths whose content is one input: `lean` is everything `lake build wiz grail
tests` compiles, `runtime` is the C runtime those binaries embed, `docs` is the
prose. A subset's hash changes when a tracked file in it is added, removed,
renamed or edited, and does not change for any other subset's files.

This file is the only source of truth for the split. `.github/repo-subsets.json`
is generated from it and committed (so a cache key can be read without running
Python), and `--check` proves the committed copy still describes the tree:

  * a file's identity is its path and content: `sha256(file)` per tracked file,
    combined in byte-sorted path order over `"{sha256}  {path}\\n"` lines;
  * files come from `git ls-files`, so a gitignored file (`.lake`,
    `grail.local.wiz`, `scry/native/tree-sitter-c-sharp`, the generated
    `Tests/Groups.lean`) can never enter a hash;
  * no mtimes, directory entries or absolute paths enter, so two runs on one
    tree are byte-identical and a copy of the tree hashes the same;
  * the generated JSON is excluded from every subset (it lives in `.github/`,
    which is in `docs`): a file cannot hash itself.

`paths` in the JSON is the subset's pattern table, copied from this file, and
`files` is how many tracked files it matched; a change to either is drift. The
`git` field is `HEAD` when the subtrees' tracked content matches the commit and
`unstaged` otherwise; it is informational (it is not compared) because the JSON
is written before the commit that carries it.

A tracked path in no subset (scripts, tests fixtures that are not under
`Tests/`, `selfhost/`, …) enters no hash on purpose: add it to a subset only
when a cache or a build reads it.

Usage
  scripts/repo-subsets.py                print the current table (human readable)
  scripts/repo-subsets.py --write        regenerate .github/repo-subsets.json
  scripts/repo-subsets.py --check        fail when the JSON is stale
  scripts/repo-subsets.py --print NAME   print one subset's hash (for a shell)
  scripts/repo-subsets.py --self-test    prove the hashes' stability and locality
  scripts/repo-subsets.py --root DIR     use another checkout (the self-test)

Exit status: 0 clean, 1 stale (with `--check`), 2 usage or a tree it cannot read.

The pre-commit hook (`.githooks/pre-commit`, installed with
`git config core.hooksPath .githooks`) refreshes the JSON for you; CI cannot
rely on hooks, so `scripts/check-companion-lists.py` runs `--check` in
`docs_style`.
"""

from __future__ import annotations

import argparse
import contextlib
import hashlib
import io
import json
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
OUT = ".github/repo-subsets.json"
GENERATED_BY = "scripts/repo-subsets.py"

# The split. `dir/**` is the directory and everything below it; a bare name is
# one file. Keep this small: every subset should be one build input, and a file
# may belong to at most one (the script checks that).
SUBSETS: tuple[tuple[str, tuple[str, ...]], ...] = (
    (
        "lean",
        (
            "Wiz/**",
            "Grail/**",
            "WizMeta/**",
            "Main.lean",
            "Wiz.lean",
            "Grail.lean",
            "WizMeta.lean",
            "lakefile.lean",
            "lake-manifest.json",
            "lean-toolchain",
        ),
    ),
    ("runtime", ("runtime/**", "c/**")),
    ("wizlib", ("lib/**",)),
    ("packages", ("scry/**", "hdl/**", "tower/**")),
    ("tests", ("Tests/**", "web/**")),
    ("docs", ("docs/**", "README.md", "CHANGELOG.md", "AGENTS.md", ".github/**")),
)

# The generated file is inside `docs` and must not enter any hash.
EXCLUDE = frozenset({OUT})


class Error(Exception):
    """A tree this script cannot describe (exit 2)."""


def git(root: Path, *args: str) -> str:
    try:
        return subprocess.run(
            ["git", *args], cwd=root, capture_output=True, text=True, timeout=120
        ).stdout
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise Error(f"cannot run git {' '.join(args)}: {exc}") from exc


def tracked_files(root: Path) -> list[str]:
    """Every tracked path, relative to `root`, in byte order."""
    try:
        proc = subprocess.run(
            ["git", "ls-files", "-z"],
            cwd=root,
            capture_output=True,
            timeout=120,
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise Error(f"cannot list the tracked files: {exc}") from exc
    if proc.returncode != 0:
        raise Error(
            "not a git checkout (git ls-files failed); run inside the repository"
        )
    files = [p.decode("utf-8", "surrogateescape") for p in proc.stdout.split(b"\0") if p]
    return sorted(files, key=lambda p: p.encode("utf-8", "surrogateescape"))


def matches(path: str, pattern: str) -> bool:
    """`dir/**` is a subtree, anything else is one exact path."""
    if pattern.endswith("/**"):
        prefix = pattern[:-3]
        return path == prefix or path.startswith(prefix + "/")
    return path == pattern


def subset_files(files: list[str], patterns: tuple[str, ...]) -> list[str]:
    return [
        f for f in files if f not in EXCLUDE and any(matches(f, p) for p in patterns)
    ]


def file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    try:
        with path.open("rb") as handle:
            for chunk in iter(lambda: handle.read(1 << 20), b""):
                digest.update(chunk)
    except OSError as exc:
        raise Error(f"cannot read {path}: {exc}") from exc
    return digest.hexdigest()


def subset_sha256(root: Path, paths: list[str]) -> str:
    """sha256 over `"{file hash}  {path}\\n"` in byte-sorted path order."""
    digest = hashlib.sha256()
    for path in sorted(paths, key=lambda p: p.encode("utf-8", "surrogateescape")):
        digest.update(f"{file_sha256(root / path)}  {path}\n".encode())
    return digest.hexdigest()


def revision(root: Path) -> str:
    """`HEAD`, or `unstaged` when a tracked file differs from it."""
    head = git(root, "rev-parse", "--verify", "HEAD").strip()
    if not head:
        return "unstaged"
    # `--untracked-files=no`: the generated JSON is the only file we ignore by
    # name; an untracked file is not part of any subset (git ls-files).
    status = git(
        root,
        "status",
        "--porcelain",
        "--untracked-files=no",
        "--",
        ".",
        f":(exclude){OUT}",
    ).strip()
    return "unstaged" if status else head


def compute(root: Path) -> dict:
    """The JSON document for `root` (fresh, never read from disk)."""
    files = tracked_files(root)
    owner: dict[str, str] = {}
    subsets: dict[str, dict] = {}
    for name, patterns in SUBSETS:
        selected = subset_files(files, patterns)
        for path in selected:
            if path in owner:
                raise Error(
                    f"the subset table is ambiguous: {path} is in {owner[path]} and {name}"
                )
            owner[path] = name
        subsets[name] = {
            "paths": list(patterns),
            "files": len(selected),
            "sha256": subset_sha256(root, selected),
        }
    return {
        "generated_by": GENERATED_BY,
        "git": revision(root),
        "subsets": subsets,
    }


def render(document: dict) -> str:
    return json.dumps(document, sort_keys=True, indent=2) + "\n"


def read_document(root: Path) -> dict:
    path = root / OUT
    try:
        return json.loads(path.read_text())
    except FileNotFoundError as exc:
        raise Error(f"{OUT} is missing") from exc
    except (OSError, json.JSONDecodeError) as exc:
        raise Error(f"{OUT} is unreadable ({exc})") from exc


def stale_subsets(old: dict, new: dict) -> list[str]:
    """Subset names whose pattern table, file count or hash differ."""
    old_subsets = old.get("subsets")
    if not isinstance(old_subsets, dict):
        raise Error(f"{OUT} has no subsets object")
    names = set(old_subsets) | set(new["subsets"])
    stale = []
    for name in sorted(names):
        want = new["subsets"].get(name)
        have = old_subsets.get(name)
        if not isinstance(have, dict) or want is None:
            stale.append(name)
        elif (
            have.get("paths") != want["paths"]
            or have.get("files") != want["files"]
            or have.get("sha256") != want["sha256"]
        ):
            stale.append(name)
    return stale


def write(root: Path) -> int:
    document = compute(root)
    path = root / OUT
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(render(document))
    files = sum(s["files"] for s in document["subsets"].values())
    print(
        f"repo-subsets: wrote {OUT} "
        f"({len(document['subsets'])} subsets, {files} files, git {document['git']})"
    )
    return 0


def check(root: Path) -> int:
    old = read_document(root)
    new = compute(root)
    stale = stale_subsets(old, new)
    if stale:
        print(
            f"repo-subsets: {OUT} is stale for {', '.join(stale)}; "
            "run scripts/repo-subsets.py --write",
            file=sys.stderr,
        )
        return 1
    files = sum(s["files"] for s in new["subsets"].values())
    print(f"repo-subsets: current ({len(new['subsets'])} subsets, {files} files)")
    return 0


def summary(root: Path) -> int:
    document = compute(root)
    width = max(len(name) for name in document["subsets"])
    for name, subset in document["subsets"].items():
        print(
            f"{name:<{width}}  {subset['sha256']}  {subset['files']:>5} files  "
            f"{' '.join(subset['paths'])}"
        )
    print(f"git {document['git']}")
    return 0


# --- self-test ---------------------------------------------------------------------


FIXTURE = {
    "Wiz/A.lean": "def a := 1\n",
    "Wiz/B.lean": "def b := 2\n",
    "Tests/One.lean": "def one := 1\n",
    "lib/L.wiz": "def l := 1\n",
    "runtime/rt.h": "/* rt */\n",
    "c/socket.c": "/* socket */\n",
    "scry/s.wiz": "def s := 1\n",
    "hdl/h.wiz": "def h := 1\n",
    "docs/d.md": "# d\n",
    "README.md": "# r\n",
    ".github/workflow.yml": "on: push\n",
    ".github/repo-subsets.json": "{}\n",
    "scripts/other.py": "# no subset\n",
}


def fixture(root: Path) -> None:
    root.mkdir(parents=True, exist_ok=True)
    for path, text in FIXTURE.items():
        target = root / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(text)
    subprocess.run(["git", "init", "-q"], cwd=root, check=True)
    subprocess.run(["git", "add", "-A"], cwd=root, check=True)


def hashes(root: Path) -> dict[str, str]:
    return {name: s["sha256"] for name, s in compute(root)["subsets"].items()}


def self_test() -> int:
    failures: list[str] = []

    def expect(name: str, ok: bool, detail: str = "") -> None:
        if not ok:
            failures.append(f"{name}: {detail}" if detail else name)

    def changed(before: dict[str, str], after: dict[str, str]) -> list[str]:
        return sorted(n for n in before if before[n] != after[n])

    with tempfile.TemporaryDirectory(prefix="repo-subsets.") as tmp:
        base = Path(tmp) / "base"
        fixture(base)

        # 1. Three runs are byte-identical, and the JSON describes every subset.
        first = render(compute(base))
        second = render(compute(base))
        third = render(compute(base))
        expect("two runs are byte-identical", first == second and second == third)
        document = json.loads(first)
        expect(
            "every subset has files",
            all(s["files"] > 0 for s in document["subsets"].values()),
            str({n: s["files"] for n, s in document["subsets"].items()}),
        )
        expect(
            "the JSON is excluded from docs",
            all(OUT not in s["paths"] for s in document["subsets"].values())
            and document["subsets"]["docs"]["files"] == 3,
            str(document["subsets"]["docs"]),
        )

        def mutate(label: str, action) -> None:
            """Copy the fixture, apply `action`, and expect one subset to move."""
            case = Path(tmp) / label.replace(" ", "-")
            shutil.copytree(base, case)
            before = hashes(case)
            action(case)
            after = hashes(case)
            moved = changed(before, after)
            expect(f"{label} changes exactly one subset", len(moved) == 1, str(moved))
            return moved[0] if len(moved) == 1 else ""

        def add_tests(root: Path) -> None:
            (root / "Tests/New.lean").write_text("def new := 1\n")
            subprocess.run(["git", "add", "Tests/New.lean"], cwd=root, check=True)

        def edit_tests(root: Path) -> None:
            (root / "Tests/One.lean").write_text("def one := 2\n")

        def remove_lib(root: Path) -> None:
            (root / "lib/L.wiz").unlink()
            subprocess.run(["git", "rm", "-q", "--cached", "lib/L.wiz"], cwd=root, check=True)

        def rename_lean(root: Path) -> None:
            subprocess.run(["git", "mv", "Wiz/A.lean", "Wiz/C.lean"], cwd=root, check=True)

        def edit_runtime(root: Path) -> None:
            (root / "runtime/rt.h").write_text("/* rt 2 */\n")

        def edit_docs(root: Path) -> None:
            (root / "docs/d.md").write_text("# d2\n")

        def edit_json(root: Path) -> None:
            (root / ".github/repo-subsets.json").write_text('{"x": 1}\n')

        for label, action, subset in (
            ("add a Tests file", add_tests, "tests"),
            ("edit a Tests file", edit_tests, "tests"),
            ("remove a lib file", remove_lib, "wizlib"),
            ("rename a Wiz file", rename_lean, "lean"),
            ("edit the runtime", edit_runtime, "runtime"),
            ("edit a docs file", edit_docs, "docs"),
        ):
            moved = mutate(label, action)
            expect(f"{label} names {subset}", moved == subset, moved)

        # The generated JSON cannot affect any hash (it is excluded).
        case = Path(tmp) / "edit-the-json"
        shutil.copytree(base, case)
        before = hashes(case)
        edit_json(case)
        expect("editing the JSON changes no subset", changed(before, hashes(case)) == [])

        # 2. --write then --check is clean; one edit then --check names the subset.
        case = Path(tmp) / "check"
        shutil.copytree(base, case)
        write_quiet(case)
        expect("--write then --check is clean", check_quiet(case) == 0)
        edit_tests(case)
        code, text = check_text(case)
        expect("--check fails after an edit", code == 1, str(code))
        expect("--check names the stale subset", "stale for tests;" in text, text)

        # 3. A no-op --write is byte-identical (the hook can run on every commit).
        case = Path(tmp) / "idempotent"
        shutil.copytree(base, case)
        write_quiet(case)
        once = (case / OUT).read_bytes()
        write_quiet(case)
        expect("--write is idempotent", (case / OUT).read_bytes() == once)

    if failures:
        for failure in failures:
            print(f"self-test FAIL: {failure}", file=sys.stderr)
        return 1
    print("repo-subsets self-test: ok (stability, 6 mutations, JSON exclusion, --check)")
    return 0


def check_text(root: Path) -> tuple[int, str]:
    buffer = io.StringIO()
    with contextlib.redirect_stdout(buffer), contextlib.redirect_stderr(buffer):
        code = check(root)
    return code, buffer.getvalue()


def check_quiet(root: Path) -> int:
    with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(
        io.StringIO()
    ):
        return check(root)


def write_quiet(root: Path) -> int:
    with contextlib.redirect_stdout(io.StringIO()):
        return write(root)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Content hashes of the repository's build subsets."
    )
    parser.add_argument("--write", action="store_true",
                        help=f"regenerate {OUT}")
    parser.add_argument("--check", action="store_true",
                        help="fail when the committed JSON is stale")
    parser.add_argument("--print", metavar="NAME",
                        help="print one subset's hash and nothing else")
    parser.add_argument("--self-test", action="store_true",
                        help="prove the hashes' stability and locality")
    parser.add_argument("--root", metavar="DIR", default=None,
                        help="use another checkout (the self-test's fixtures)")
    args = parser.parse_args(argv)
    if args.write and args.check:
        parser.error("--write and --check are exclusive")
    root = Path(args.root).resolve() if args.root else ROOT

    try:
        if args.self_test:
            return self_test()
        if args.print:
            document = compute(root)
            subset = document["subsets"].get(args.print)
            if subset is None:
                print(
                    f"repo-subsets: unknown subset {args.print!r} "
                    f"(have {', '.join(document['subsets'])})",
                    file=sys.stderr,
                )
                return 2
            print(subset["sha256"])
            return 0
        if args.write:
            return write(root)
        if args.check:
            return check(root)
        return summary(root)
    except Error as exc:
        print(f"repo-subsets: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
