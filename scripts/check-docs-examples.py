#!/usr/bin/env python3
"""Check the Wiz code blocks and relative paths in Wiz's documentation.

The documentation is a reader's first contact with the language, and a stale snippet
teaches the wrong thing.  This check extracts the blocks that are marked as Wiz and
runs them through the real toolchain:

  ```wiz            a complete Wiz file: `wiz check` must accept it
  ```wiz check      the same, spelled out
  ```wiz run        a complete program (a `main`): `wiz run` must succeed, and when the
                    next fenced block is a plain/text/output block, its standard output
                    must match it (a leading `$ wiz run ...` line is ignored)
  ```wiz no-check   deliberately not checked: a fragment, an error demonstration, or a
                    block that needs the page's earlier definitions.  The reason belongs
                    in the prose or in a `-- ...` line right above the fence.

Other fenced blocks (shell commands, output, syntax diagrams, file trees) are not Wiz
blocks and are ignored.  A block marked `wiz` with no `import` line gets `import
Prelude` prepended: documentation snippets show the interesting part, and a snippet
that needs more says so itself.

Relative Markdown links and `examples/...` paths in inline code or prose are resolved
against the document (and the repository root for `examples/...`); a missing target is
reported.  Anchors are not checked, and globs such as `examples/hdl-verified-*.wiz` are
skipped.

Caching.  `--cache DIR` (default `.lake/docs-examples`) holds both Wiz's own
content-addressed elaboration cache (`--cache DIR/wiz`) and the checker's record of
blocks that passed, keyed by the block's text, its mode, the expected output, the
toolchain's version (and size/mtime) and a digest of `lib/`, `runtime/`, `c/` and the
checker.  A docs-only change therefore rechecks only the snippets that changed; a
toolchain or library change invalidates everything.  Successful results only are
recorded.  On CI the whole directory is restored/saved under a key derived from the
Lean sources that build `wiz` (see `.github/workflows/ci.yml`), so a docs-only run
starts warm.

Limits.  One block is 64 KiB and 2000 lines at most (`wiz check` is not a fuzz target),
and each command has a 120-second timeout; both are flags.  A block over a limit is a
failure rather than a silent skip, so a real example cannot hide by being large.

Usage
  scripts/check-docs-examples.py                 check this checkout
  scripts/check-docs-examples.py --self-test     run the built-in fixtures
  scripts/check-docs-examples.py --root DIR      check another checkout
  scripts/check-docs-examples.py --wiz PATH      use another `wiz` (default: PATH)
  scripts/check-docs-examples.py --no-cache      do not read or write the cache
  scripts/check-docs-examples.py --quiet         print only the summary when clean

Exit status: 0 clean, 1 problems (or a failing self-test), 2 usage error.

The fixtures in Tests/fixtures/docs-examples use a fake `wiz`, so `--self-test` needs
no build.  CI runs `--self-test` and then the check (job `docs_examples`).
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
from dataclasses import dataclass, field
from pathlib import Path
from urllib.parse import unquote

ROOT_FILES = ("README.md", "ROADMAP.md", "CHANGELOG.md")
CHECK_MODES = ("check", "run", "no-check")
DEFAULT_CACHE = Path(".lake/docs-examples")
MAX_BLOCK_BYTES = 64 * 1024
MAX_BLOCK_LINES = 2000
DEFAULT_TIMEOUT = 120
CACHE_VERSION = 1


# --------------------------------------------------------------------------------------
# Markdown


@dataclass
class Fence:
    """One fenced code block: 1-based opening line, info string and body lines."""

    path: Path
    line: int  # the opening fence
    info: str
    body: str
    end: int  # the closing fence (or the last line when unclosed)

    @property
    def mode(self) -> str | None:
        """`check`, `run`, `no-check`, or None when this is not a Wiz block."""
        parts = self.info.split()
        if not parts or parts[0] != "wiz":
            return None
        if len(parts) == 1:
            return "check"
        if len(parts) == 2 and parts[1] in CHECK_MODES:
            return parts[1]
        return "bad-marker"

    @property
    def marker_problem(self) -> str | None:
        if self.mode == "bad-marker":
            return (
                f"{self.path}:{self.line}: unknown Wiz block marker {self.info!r}: "
                "use `wiz`, `wiz check`, `wiz run` or `wiz no-check`"
            )
        return None


FENCE = re.compile(r"^( {0,3})(`{3,}|~{3,})(.*)$")


def parse_fences(path: Path, text: str) -> list[Fence]:
    """The fenced blocks of one Markdown document (CommonMark's basic fence rules)."""
    lines = text.splitlines()
    out: list[Fence] = []
    i = 0
    while i < len(lines):
        m = FENCE.match(lines[i])
        if m is None or (m.group(2)[0] == "`" and "`" in m.group(3)):
            i += 1
            continue
        indent, marker, info = len(m.group(1)), m.group(2), m.group(3).strip()
        j = i + 1
        while j < len(lines):
            close = re.match(r"^ {0,3}(`{3,}|~{3,})\s*$", lines[j])
            if close and close.group(1)[0] == marker[0] and len(close.group(1)) >= len(marker):
                break
            j += 1
        body_lines = lines[i + 1:j]
        body = "\n".join(
            line[indent:] if line[:indent].strip() == "" else line for line in body_lines
        )
        end = min(j + 1, len(lines))
        out.append(Fence(path, i + 1, info, body, end))
        i = j + 1
    return out


def _strip_expected_prompt(body: str) -> str:
    """Drop a leading `$ wiz run ...` (or `>`) line from an expected-output block."""
    lines = body.splitlines()
    while lines and not lines[0].strip():
        lines.pop(0)
    while lines and not lines[-1].strip():
        lines.pop()
    if lines and (lines[0].startswith("$ ") or lines[0].startswith("> ")):
        lines.pop(0)
    return "\n".join(lines)


def expected_output(fences: list[Fence], run: Fence) -> tuple[str | None, int | None]:
    """The plain block after a `wiz run` block, if it is visibly its output."""
    for f in fences:
        if f.path != run.path or f.line <= run.end:
            continue
        # only a block before the next Wiz block, and not one that starts another example
        if f.mode is not None:
            return None, None
        info = f.info.lower()
        first = next((line for line in f.body.splitlines() if line.strip()), "")
        if info in ("", "text", "output", "console") and (
            info in ("text", "output", "console")
            or first.startswith("$ ")
            or first.startswith("> ")
        ):
            return _strip_expected_prompt(f.body), f.line
        return None, None
    return None, None


# --------------------------------------------------------------------------------------
# Links and examples/ references


SCHEME = re.compile(r"^[A-Za-z][A-Za-z0-9+.-]*:")
LINK = re.compile(r"!?\[[^\]]*\]\(([^)\s]+)(?:\s+[\"'][^\"']*[\"'])?\)")
LINK_REF = re.compile(r"^ {0,3}\[[^\]]+\]:\s*(\S+)")
EXAMPLE_REF = re.compile(r"(?<![\w/.-])((?:\.\./)*examples/[\w./+-]+)")


def _relative_target(doc: Path, target: str) -> Path | None:
    """The local path a link points at, or None for an external/anchor-only link."""
    if not target or target.startswith("#") or SCHEME.match(target) or target.startswith("//"):
        return None
    target = target.strip("<>")
    target = target.split("#", 1)[0].split("?", 1)[0]
    if not target:
        return None
    target = unquote(target)
    return (doc.parent / target).resolve()


def check_paths(root: Path, paths: list[Path]) -> tuple[list[str], int, int]:
    """Problems, link count and `examples/...` reference count for `paths`."""
    problems: list[str] = []
    links = refs = 0
    for path in paths:
        try:
            text = path.read_text(encoding="utf-8")
        except UnicodeDecodeError as exc:
            problems.append(f"{path.relative_to(root)}: not UTF-8: {exc}")
            continue
        rel = path.relative_to(root).as_posix()
        found: set[str] = set()

        for lineno, line in enumerate(text.splitlines(), 1):
            targets = [m.group(1) for m in LINK.finditer(line)]
            m = LINK_REF.match(line)
            if m and (
                SCHEME.match(m.group(1))
                or m.group(1).startswith(("./", "../", "/", "#"))
                or "." in m.group(1)
                or "/" in m.group(1)
            ):
                # A citation such as `[PT22, PLT25]: there is ...` also looks like a
                # reference definition; a target with a dot, slash or scheme is a path.
                targets.append(m.group(1))
            for target in targets:
                links += 1
                resolved = _relative_target(path, target)
                if resolved is not None and not resolved.exists():
                    msg = f"{rel}:{lineno}: link target does not exist: {target}"
                    if msg not in found:
                        found.add(msg)
                        problems.append(msg)

        # `examples/foo.wiz` in prose or inline code.  Globs and line:column suffixes
        # are not paths; a match followed by `*`, `?` or `[` is part of a glob.
        for m in EXAMPLE_REF.finditer(text):
            token = m.group(1)
            after = text[m.end():m.end() + 1]
            token = token.rstrip(".,;:)")
            if after in ("*", "?", "["):
                continue
            if not token or token.endswith("-"):
                continue
            refs += 1
            if token.startswith("../"):
                target = (path.parent / token).resolve()
            else:
                target = (root / token).resolve()
            if not target.exists():
                lineno = text.count("\n", 0, m.start()) + 1
                msg = f"{rel}:{lineno}: examples reference does not exist: {token}"
                if msg not in found:
                    found.add(msg)
                    problems.append(msg)
    return problems, links, refs


# --------------------------------------------------------------------------------------
# Block checking


@dataclass
class Report:
    checked: int = 0
    cached: int = 0
    run: int = 0
    no_check: int = 0
    links: int = 0
    refs: int = 0
    problems: list[str] = field(default_factory=list)
    cache_hits: int = 0
    seconds: float = 0.0


def _implicit_prelude(body: str) -> str:
    if re.search(r"(?m)^\s*(?:import|import_c)\s", body):
        return body
    return "import Prelude\n" + body


def _too_big(body: str) -> str | None:
    if len(body.encode("utf-8")) > MAX_BLOCK_BYTES:
        return f"block is {len(body.encode('utf-8'))} bytes (limit {MAX_BLOCK_BYTES})"
    if len(body.splitlines()) > MAX_BLOCK_LINES:
        return f"block is {len(body.splitlines())} lines (limit {MAX_BLOCK_LINES})"
    return None


def _toolchain_id(wiz: str) -> str:
    """A version string that changes when the binary changes (cache invalidation)."""
    try:
        out = subprocess.run(
            [wiz, "--version"], capture_output=True, text=True, timeout=30
        )
        version = (out.stdout + out.stderr).strip()
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise SystemExit(f"check-docs-examples: cannot run {wiz}: {exc}") from exc
    path = shutil.which(wiz) or wiz
    try:
        st = os.stat(path)
        ident = f"{version}|{st.st_size}|{st.st_mtime_ns}"
    except OSError:
        ident = version
    return hashlib.sha256(ident.encode()).hexdigest()


def _cache_key(toolchain: str, sources: str, mode: str, source: str, expected: str | None) -> str:
    h = hashlib.sha256()
    for part in (toolchain, sources, mode, source, expected or ""):
        h.update(part.encode())
        h.update(b"\0")
    return h.hexdigest()


def _checkout_digest(root: Path) -> str:
    """A digest of the Wiz sources a snippet is elaborated against.

    The toolchain's version covers Lean changes; this covers the `.wiz` library, the
    runtime and C sources (which `wiz run` compiles), and the checker itself.  Without
    it a `lib/**` change would keep serving a snippet's cached pass.
    """
    h = hashlib.sha256()
    patterns = ("lib/**/*.wiz", "runtime/**", "c/**", "grail.local.wiz",
                "scripts/check-docs-examples.py")
    for pattern in patterns:
        for path in sorted(root.glob(pattern)):
            if not path.is_file():
                continue
            h.update(path.relative_to(root).as_posix().encode())
            h.update(b"\0")
            h.update(path.read_bytes())
            h.update(b"\0")
    return h.hexdigest()


def _load_cache(path: Path) -> dict:
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return {"version": CACHE_VERSION, "entries": {}}
    if data.get("version") != CACHE_VERSION or not isinstance(data.get("entries"), dict):
        return {"version": CACHE_VERSION, "entries": {}}
    return data


def _save_cache(path: Path, entries: dict) -> None:
    # The cache is a convenience, never a source of truth; keep it small (a docs tree
    # has hundreds of blocks, not millions).
    if len(entries) > 4000:
        entries = dict(sorted(entries.items(), key=lambda kv: kv[1].get("used", 0))[-4000:])
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(".json.tmp")
    tmp.write_text(json.dumps({"version": CACHE_VERSION, "entries": entries}, indent=0), encoding="utf-8")
    tmp.replace(path)


def _run_wiz(
    wiz: str, mode: str, path: Path, root: Path, cache: Path | None, timeout: int
) -> tuple[int, str, str]:
    cmd = [wiz, "run" if mode == "run" else "check"]
    if cache is not None:
        cmd += ["--cache", str(cache)]
    else:
        cmd += ["--no-cache"]
    cmd.append(str(path))
    try:
        result = subprocess.run(
            cmd, cwd=root, capture_output=True, text=True, timeout=timeout
        )
    except subprocess.TimeoutExpired:
        return 124, "", f"timed out after {timeout} s: {' '.join(cmd)}"
    return result.returncode, result.stdout, result.stderr


def _first_lines(text: str, limit: int = 8) -> list[str]:
    lines = [line.rstrip() for line in text.splitlines() if line.strip()]
    if len(lines) > limit:
        lines = lines[:limit] + ["..."]
    return lines


def check_blocks(
    root: Path,
    fences: list[Fence],
    wiz: str,
    cache_dir: Path | None,
    timeout: int,
    toolchain: str,
    sources: str,
) -> tuple[list[str], Report]:
    """Check every Wiz block; return problems and counts."""
    problems: list[str] = []
    report = Report()
    use_cache = cache_dir is not None
    cache_file = cache_dir / "results.json" if use_cache else None
    entries = _load_cache(cache_file)["entries"] if cache_file is not None and cache_file.exists() else {}
    new_entries: dict = {}
    started = time.monotonic()

    for fence in fences:
        problem = fence.marker_problem
        if problem is not None:
            problems.append(problem)
            continue
        mode = fence.mode
        if mode is None:
            continue
        rel = fence.path.relative_to(root).as_posix()
        if mode == "no-check":
            report.no_check += 1
            continue
        over = _too_big(fence.body)
        if over is not None:
            problems.append(f"{rel}:{fence.line}: {over}; mark the block `wiz no-check`")
            continue
        body = fence.body if mode == "run" else _implicit_prelude(fence.body)
        expected, expected_line = expected_output(fences, fence) if mode == "run" else (None, None)
        key = _cache_key(toolchain, sources, mode, body, expected)
        if use_cache and key in entries:
            report.checked += 1
            report.cached += 1
            report.cache_hits += 1
            if mode == "run":
                report.run += 1
            new_entries[key] = entries[key]
            new_entries[key]["used"] = int(time.time())
            continue

        with tempfile.TemporaryDirectory(prefix="wiz-docs-") as tmp:
            src = Path(tmp) / "snippet.wiz"
            src.write_text(body + "\n", encoding="utf-8")
            code, stdout, stderr = _run_wiz(wiz, mode, src, root, cache_dir / "wiz" if cache_dir else None, timeout)

        report.checked += 1
        if mode == "run":
            report.run += 1
        ok = code == 0
        detail = ""
        if mode == "run" and ok and expected is not None:
            got = stdout.strip()
            want = expected.strip()
            if got != want:
                ok = False
                detail = f"output differs from the block at line {expected_line}"
        if not ok:
            lines = [f"{rel}:{fence.line}: {mode} failed (exit {code})"]
            if detail:
                lines.append(f"  {detail}")
            if expected is not None and mode == "run" and code == 0:
                lines.append("  expected:")
                lines += ["    " + l for l in _first_lines(expected)]
            lines += ["  " + l for l in _first_lines(stdout + stderr)]
            problems.extend(lines)
            continue
        if use_cache:
            new_entries[key] = {
                "used": int(time.time()),
                "stdout": stdout if mode == "run" else "",
            }

    if cache_file is not None:
        _save_cache(cache_file, new_entries)
    report.seconds = time.monotonic() - started
    return problems, report


# --------------------------------------------------------------------------------------
# Driver


def doc_files(root: Path) -> list[Path]:
    files = [root / name for name in ROOT_FILES if (root / name).is_file()]
    docs = root / "docs"
    if docs.is_dir():
        files.extend(path for path in docs.rglob("*.md") if path.is_file())
    return sorted(set(files), key=lambda path: path.as_posix())


def run_check(
    root: Path,
    wiz: str,
    cache_dir: Path | None,
    timeout: int,
    quiet: bool = False,
    files: list[Path] | None = None,
) -> tuple[Report, list[str]]:
    files = files if files is not None else doc_files(root)
    if not files:
        raise SystemExit(f"check-docs-examples: {root} has no documentation")
    path_problems, links, refs = check_paths(root, files)
    fences: list[Fence] = []
    for path in files:
        try:
            text = path.read_text(encoding="utf-8")
        except UnicodeDecodeError:
            continue  # reported by check_paths
        fences.extend(parse_fences(path, text))
    toolchain = _toolchain_id(wiz)
    sources = _checkout_digest(root)
    block_problems, report = check_blocks(root, fences, wiz, cache_dir, timeout, toolchain, sources)
    report.links = links
    report.refs = refs
    report.problems = path_problems + block_problems
    return report, report.problems


def print_report(report: Report, problems: list[str], quiet: bool = False) -> int:
    if problems or not quiet:
        for problem in problems:
            print(problem)
    if problems:
        print(
            f"\ncheck-docs-examples: {len(problems)} problem(s); "
            f"{report.checked} checked ({report.cached} cached, {report.run} run), "
            f"{report.no_check} no-check; {report.links} links, {report.refs} example references",
            file=sys.stderr,
        )
        return 1
    print(
        f"check-docs-examples: clean ({report.checked} checked: {report.cached} cached, "
        f"{report.run} run; {report.no_check} no-check; {report.links} links, "
        f"{report.refs} example references; {report.seconds:.1f} s)"
    )
    return 0


# --------------------------------------------------------------------------------------
# Self-test


def _fixture_root() -> Path:
    return Path(__file__).resolve().parent.parent / "Tests" / "fixtures" / "docs-examples" / "site"


def _fixture_wiz() -> str:
    return str(
        Path(__file__).resolve().parent.parent
        / "Tests"
        / "fixtures"
        / "docs-examples"
        / "fake-wiz.sh"
    )


def self_test() -> int:
    failures: list[str] = []
    fixture = _fixture_root()
    wiz = _fixture_wiz()
    if not fixture.is_dir() or not os.path.exists(wiz):
        print(f"self-test FAIL: fixtures missing under {fixture}", file=sys.stderr)
        return 1
    with tempfile.TemporaryDirectory(prefix="wiz-docs-selftest-") as tmp:
        cache = Path(tmp) / "cache"
        report, problems = run_check(fixture, wiz, cache, 30)
        expected = [
            "docs/bad.md:3: link target does not exist: missing.md",
            "docs/bad.md:5: examples reference does not exist: examples/not-there.wiz",
        ]
        for want in expected:
            if not any(want in p for p in problems):
                failures.append(f"missing expected problem: {want}")
        if not any("unknown Wiz block marker" in p for p in problems):
            failures.append("an unknown `wiz` marker was not reported")
        if not any("check failed" in p for p in problems):
            failures.append("a failing `wiz check` was not reported")
        if not any("output differs" in p for p in problems):
            failures.append("a run block whose output differs was not reported")
        if report.checked != 4:
            failures.append(f"expected 4 checked blocks, got {report.checked}")
        if report.run != 2:
            failures.append(f"expected 2 run blocks, got {report.run}")
        if report.no_check != 1:
            failures.append(f"expected 1 no-check block, got {report.no_check}")
        if report.links != 6:
            failures.append(f"expected 6 links, got {report.links}")
        if report.refs != 4:
            failures.append(f"expected 4 example references, got {report.refs}")
        # A second run must be a cache hit (the fake wiz is not called again).  The
        # failing block is deliberately not cached.
        cached, _ = run_check(fixture, wiz, cache, 30)
        if cached.cache_hits != 2:
            failures.append(f"expected 2 cache hits, got {cached.cache_hits}")
        if cached.checked != 4:
            failures.append(f"cache run checked {cached.checked} blocks, expected 4")

        # The fake wiz rejects a block without an import unless the checker added the
        # implicit Prelude, so the good block also exercises that convention.
        # An unknown marker is a usage error, not a silently ignored block.
        bad = fixture / "docs" / "bad.md"
        bad_text = bad.read_text(encoding="utf-8")
        bad.write_text(bad_text + "\n```wiz wat\nx\n```\n", encoding="utf-8")
        try:
            _, extra = run_check(fixture, wiz, Path(tmp) / "cache2", 30)
            if not any("unknown Wiz block marker" in p for p in extra):
                failures.append("a `wiz wat` block was not reported after it was added")
        finally:
            bad.write_text(bad_text, encoding="utf-8")

    if failures:
        for failure in failures:
            print(f"self-test FAIL: {failure}", file=sys.stderr)
        return 1
    print("check-docs-examples self-test: ok (fixtures: blocks, output, links, cache)")
    return 0


# --------------------------------------------------------------------------------------
# CLI


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Check Wiz code blocks and relative links in the documentation."
    )
    parser.add_argument(
        "--root",
        type=Path,
        default=Path(__file__).resolve().parent.parent,
        help="checkout to check (default: the one containing this script)",
    )
    parser.add_argument("--wiz", default="wiz", help="the wiz executable (default: wiz on PATH)")
    parser.add_argument(
        "--cache",
        type=Path,
        default=DEFAULT_CACHE,
        help=f"cache directory (default: {DEFAULT_CACHE})",
    )
    parser.add_argument("--no-cache", action="store_true", help="do not read or write a cache")
    parser.add_argument(
        "--timeout", type=int, default=DEFAULT_TIMEOUT, help=f"seconds per block (default: {DEFAULT_TIMEOUT})"
    )
    parser.add_argument(
        "--self-test", action="store_true", help="run the built-in fixtures instead of reading files"
    )
    parser.add_argument("--quiet", action="store_true", help="print only the summary when clean")
    args = parser.parse_args(argv)

    if args.self_test:
        return self_test()
    if args.timeout <= 0:
        parser.error("--timeout must be positive")
    root = args.root.resolve()
    cache = None if args.no_cache else (root / args.cache if not args.cache.is_absolute() else args.cache)
    report, problems = run_check(root, args.wiz, cache, args.timeout, args.quiet)
    return print_report(report, problems, args.quiet)


if __name__ == "__main__":
    sys.exit(main())
