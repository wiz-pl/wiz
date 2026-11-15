#!/usr/bin/env python3
"""Turn a failed golden test into the diff a reviewer needs.

  scripts/golden-diff.py LOG|JSONL... [--case GROUP:CASE]... [options]

CI reports a golden failure as "expected X got Y" for one case, and the reviewer then
has to reproduce it. This script reads a run's test logs (the `*.log` and `*.jsonl`
files of a shard, or a local `lake test` log), finds the failing cases, and re-runs only
those cases with `grail test --update` in a **temporary copy** of the checkout. It prints
a Markdown report with a one-line-per-case summary and a unified diff of every
`.expected` file that changed. The checkout is never modified; the script never commits
or pushes.

A failing case is re-run only if it names a golden `.wiz` file (or its failure output
does, e.g. a `grail test` wrapper case). A `.wiz` is golden when it is under a
`Package.tests` root of some `grail.wiz` in the tree. A case that fails for any other
reason (a build error, a timeout, a runner failure) is reported as "not a golden case"
or "not diffed" and is **not** written to a `.expected` file: `grail test --update`
never records a failure either.

Options:
  --case GROUP:CASE     add a failing case (repeatable; for a local run)
  --grail PATH          the grail binary (default: .lake/build/bin/grail, then $GRAIL,
                        then grail on PATH)
  --repo DIR            the checkout to copy (default: this script's parent directory)
  --timeout SECS        the limit for each re-run (default: 300)
  --max-cases N         re-run at most N unique golden files (default: 12)
  --out FILE            write the report here instead of stdout
  --comment-out FILE    also write a comment-sized copy (at most 60000 bytes)
  --keep                keep the temporary copy and print its path
  --self-test           exercise the diff engine on synthetic expected/actual files
  --quiet               print only the report (no progress on stderr)

Exit status: 0 report produced (including "nothing to diff"), 1 the self-test failed,
2 a usage or setup error.

The diff is advisory. It is what `grail test --update` would write for the failing
cases, not a claim that the new output is correct; review it like any other change.
"""

from __future__ import annotations

import argparse
import difflib
import os
import re
import shutil
import subprocess
import sys
import tempfile
from dataclasses import dataclass, field
from pathlib import Path

MARKER = "<!-- wiz-golden-diff -->"
IGNORE = shutil.ignore_patterns(".git", ".lake", ".grail", "__pycache__", "node_modules")


@dataclass
class Failure:
    group: str
    case: str
    detail: str = ""
    source: str = ""


@dataclass
class Golden:
    """A `.wiz` under a package's tests root."""
    path: str   # relative to the checkout, POSIX
    package: str  # the package directory, relative to the checkout ("" is the root)
    rel: str    # the test's path relative to its package


@dataclass
class Result:
    failure: Failure
    status: str
    files: list[str] = field(default_factory=list)
    note: str = ""
    diff: str = ""


GROUP = re.compile(r"^── (.*) \(.*\)$")
FAIL = re.compile(r"^  ✗ (.*?)(?: \([\d.]+ s\))?$")
TESTS_LINE = re.compile(r'Package\.tests\s+"[^"]*"\s+"([^"]+)"')
WIZ = re.compile(r"(?:[A-Za-z0-9_.-]+/)*[A-Za-z0-9_.-]+\.wiz")


def parse_log(path: Path) -> list[Failure]:
    """The failing cases of one `tests` log (the format of Tests/Harness.lean)."""
    out: list[Failure] = []
    group = ""
    lines = path.read_text(encoding="utf-8", errors="replace").split("\n")
    for i, line in enumerate(lines):
        if m := GROUP.match(line):
            group = m.group(1)
        elif m := FAIL.match(line):
            detail = []
            for later in lines[i + 1:i + 8]:
                if not later.startswith("      "):
                    break
                detail.append(later.strip())
            out.append(Failure(group, m.group(1), " ".join(detail), path.name))
    return out


def parse_jsonl(path: Path) -> list[Failure]:
    """The failing cases of one `--timings` file (one JSON object per line)."""
    import json

    out: list[Failure] = []
    for n, line in enumerate(path.read_text(encoding="utf-8", errors="replace").split("\n"), 1):
        if not line.strip():
            continue
        try:
            r = json.loads(line)
        except json.JSONDecodeError as e:
            print(f"warning: {path}:{n}: {e}", file=sys.stderr)
            continue
        if not r.get("ok", True):
            out.append(Failure(str(r.get("group", "")), str(r.get("case", "")),
                               source=f"{path.name}:{n}"))
    return out


def failures_from(paths: list[Path]) -> list[Failure]:
    out: list[Failure] = []
    for p in paths:
        if p.suffix == ".jsonl":
            out += parse_jsonl(p)
        else:
            out += parse_log(p)
    return out


def tests_roots(repo: Path) -> list[tuple[Path, Path]]:
    """[(tests root, package root)] from every `grail.wiz` (skipping build caches)."""
    out = []
    for build in repo.rglob("grail.wiz"):
        if any(part in {".git", ".lake", ".grail"} for part in build.parts):
            continue
        try:
            text = build.read_text(encoding="utf-8", errors="replace")
        except OSError:
            continue
        for root in TESTS_LINE.findall(text):
            out.append(((build.parent / root).resolve(), build.parent.resolve()))
    return out


def find_golden(failure: Failure, repo: Path, roots: list[tuple[Path, Path]]) -> tuple[list[Golden], str]:
    """The golden tests a failure names, and a reason when it names none.

    A case name like `examples/tour/00-hello.wiz` is the test. A wrapper case (e.g.
    `grail test in tower/`) names its failing tests only in its output (`✗ tests/x.wiz`),
    so the output is searched too. A path is resolved against the checkout, then by
    suffix (`tests/x.wiz` -> `tower/tests/x.wiz`) when it is package-relative."""
    texts = [failure.case, failure.detail]
    seen: list[Path] = []
    for text in texts:
        for m in WIZ.finditer(text):
            raw = m.group(0)
            candidate = repo / raw
            if candidate.is_file():
                seen.append(candidate)
                continue
            # package-relative (`tests/pure.wiz`): the unique suffix in the checkout
            matches = [p for p in repo.rglob(Path(raw).name)
                       if p.is_file() and p.as_posix().endswith("/" + raw)]
            if len(matches) == 1:
                seen.append(matches[0])
    out: list[Golden] = []
    for path in {p.resolve() for p in seen}:
        rel = path.relative_to(repo.resolve()).as_posix()
        for root, package in roots:
            try:
                under = path.relative_to(root.resolve())
            except ValueError:
                continue
            out.append(Golden(
                path=rel,
                package=package.relative_to(repo.resolve()).as_posix() if package != repo.resolve() else "",
                rel=(Path(root.relative_to(package.resolve()).as_posix()) / under).as_posix()
                if root != package else under.as_posix()))
            break
    if out:
        return out, ""
    if failure.case.endswith(".wiz"):
        return [], f"{failure.case} is not under a Package.tests root"
    return [], "the case name and its output name no .wiz under a Package.tests root"


def unified(old: Path | None, new: Path, display: str) -> str:
    """A unified diff of two `.expected` files (`old` absent: a new file)."""
    old_text = old.read_text(encoding="utf-8", errors="replace") if old and old.exists() else ""
    new_text = new.read_text(encoding="utf-8", errors="replace")
    old_lines = old_text.splitlines(keepends=True)
    new_lines = new_text.splitlines(keepends=True)
    if old is None or not old.exists():
        old_lines = []
    out = difflib.unified_diff(old_lines, new_lines,
                               fromfile="/dev/null" if old is None or not old.exists() else f"a/{display}",
                               tofile=f"b/{display}", lineterm="\n")
    return "".join(out)


def last_error(output: str, limit: int = 240) -> str:
    """The most useful line of a failed re-run, for the summary."""
    lines = [l.strip() for l in output.split("\n") if l.strip()]
    for line in reversed(lines):
        if line.startswith("✗"):
            return line[:limit]
    for line in reversed(lines):
        if "error" in line.lower():
            return line[:limit]
    return (lines[-1] if lines else "(no output)")[:limit]


def update_one(tmp: Path, golden: Golden, grail: str, timeout: int, repo: Path) -> tuple[str, list[str], str, str]:
    """Re-run one golden test with `--update` in `tmp`; (status, changed files, note, diff)."""
    package = tmp / golden.package if golden.package else tmp
    cache = tmp / ".golden-diff-cache"
    cmd = [grail, "-C", str(package), "--std", str(tmp / "lib"),
           "--cache", str(cache), "test", "--update", "--test-timeout", str(timeout), golden.rel]
    env = dict(os.environ)
    env["TMPDIR"] = str(tmp / ".tmp")
    Path(env["TMPDIR"]).mkdir(parents=True, exist_ok=True)
    try:
        proc = subprocess.run(cmd, cwd=tmp, capture_output=True, text=True, timeout=timeout + 30, env=env)
        output = proc.stdout + proc.stderr
        code = proc.returncode
    except subprocess.TimeoutExpired as e:
        out = (e.stdout or "") + (e.stderr or "") if isinstance(e.stdout, str) else ""
        return "timeout", [], f"the re-run exceeded {timeout + 30} s", ""
    except OSError as e:
        return "failed", [], f"grail could not run: {e}", ""

    original = repo / (golden.path[:-len(".wiz")] + ".expected") if golden.path.endswith(".wiz") \
        else repo / golden.path
    display = original.relative_to(repo).as_posix()
    updated = (package / golden.rel).with_suffix(".expected")
    if not updated.exists():
        if code != 0:
            return "failed", [], last_error(output), ""
        return "no-change", [], "the re-run passed but wrote no .expected", ""
    before = original.read_bytes() if original.exists() else None
    after = updated.read_bytes()
    if before == after:
        if code != 0:
            return "failed", [], last_error(output), ""
        return "no-change", [], "the output already matches .expected", ""
    diff = unified(original if original.exists() else None, updated, display)
    note = "" if code == 0 else f"the re-run still exited {code} after writing the file"
    return "diff", [display], note, diff


def render(failures: list[Failure], results: list[Result], max_bytes: int = 0) -> str:
    changed = sorted({f for r in results for f in r.files})
    golden = sum(1 for r in results if r.status in {"diff", "no-change", "failed", "timeout"})
    out = [MARKER, "", "### Golden diff", "",
           f"**{len(failures)} failing case(s)** · {golden} golden · "
           f"{len(changed)} changed `.expected` file(s)", "",
           "| group | case | result | files |", "|---|---|---|---|"]
    names = {f"diff": "golden diff", "no-change": "no change",
             "failed": "not diffed (the re-run failed)",
             "timeout": "not diffed (timed out)",
             "non-golden": "not a golden case",
             "skipped": "not diffed (over the case limit)"}
    for r in results:
        files = ", ".join(f"`{f}`" for f in r.files) or "—"
        note = f" — {r.note}" if r.note else ""
        out.append(f"| {r.failure.group or '—'} | `{r.failure.case}` | {names.get(r.status, r.status)}{note} | {files} |")
    diffs = [r for r in results if r.diff]
    if diffs:
        out += ["", "The diff is advisory: it is what `grail test --update` writes for the failing "
                    "cases, made in a temporary copy. The bot never commits or pushes.", ""]
        out += ["<details open><summary>changed `.expected` files</summary>", "", "```diff"]
        out += [r.diff.rstrip("\n") for r in diffs]
        out += ["```", "", "</details>"]
    elif changed:
        out += ["", "The changed `.expected` file(s) are empty: there is no text to diff."]
    elif results:
        out += ["", "No `.expected` file changed."]
    text = "\n".join(out) + "\n"
    if max_bytes and len(text.encode()) > max_bytes:
        cut = text.encode()[:max_bytes].decode("utf-8", "ignore")
        if "```" in cut:
            cut += "\n\n(truncated; see the run's job summary for the whole diff.)"
        return cut
    return text


def self_test() -> int:
    """The diff engine on synthetic expected/actual files: added, changed, many, none."""
    tmp = Path(tempfile.mkdtemp(prefix="golden-diff-selftest-"))
    failures = []
    try:
        def pair(name: str, old: str, new: str) -> tuple[Path, Path, str]:
            oldp = tmp / "old" / name
            newp = tmp / "new" / name
            oldp.parent.mkdir(parents=True, exist_ok=True)
            newp.parent.mkdir(parents=True, exist_ok=True)
            oldp.write_text(old)
            newp.write_text(new)
            return oldp, newp, name

        o, n, name = pair("added.expected", "one\ntwo\n", "one\ntwo\nthree\n")
        d = unified(o, n, name)
        assert "+three" in d and "--- a/added.expected" in d, d
        failures.append(Failure("test", "added.expected"))
        results = [Result(failures[-1], "diff", [name], diff=d)]

        o, n, name = pair("changed.expected", "hello\n", "hallo\n")
        d = unified(o, n, name)
        assert "-hello" in d and "+hallo" in d, d
        failures.append(Failure("test", "changed.expected"))
        results.append(Result(failures[-1], "diff", [name], diff=d))

        o1, n1, name1 = pair("a.expected", "a\n", "a\nb\n")
        o2, n2, name2 = pair("b.expected", "x\n", "y\n")
        d = unified(o1, n1, name1) + unified(o2, n2, name2)
        assert "a/a.expected" in d and "a/b.expected" in d, d
        failures.append(Failure("test", "many"))
        results.append(Result(failures[-1], "diff", [name1, name2], diff=d))

        o, n, name = pair("same.expected", "same\n", "same\n")
        assert unified(o, n, name) == ""
        failures.append(Failure("test", "same"))
        results.append(Result(failures[-1], "no-change"))

        # the log reader and the tests-root mapping (no grail needed)
        log = tmp / "shard.log"
        log.write_text("── tour (docs/tour.md)\n  ✗ examples/tour/00-hello.wiz (0.1 s)\n"
                       "      examples/tour/00-hello.wiz: line 1\n")
        parsed = parse_log(log)
        assert len(parsed) == 1 and parsed[0].group == "tour" and \
            parsed[0].case == "examples/tour/00-hello.wiz", parsed

        mini = tmp / "mini"
        (mini / "tests").mkdir(parents=True)
        (mini / "grail.wiz").write_text(
            'import Grail\ndef package : Package := Package.new "t" |>\n'
            '  Package.tests "t" "tests"\n')
        (mini / "tests" / "x.wiz").write_text("import Prelude\n")
        roots = tests_roots(mini)
        golden, why = find_golden(Failure("t", "tests/x.wiz"), mini, roots)
        assert golden and golden[0].rel == "tests/x.wiz" and not why, (golden, why)

        text = render(failures, results)
        assert "**4 failing case(s)** · 4 golden · 4 changed" in text, text
        assert "+three" in text and "-hello" in text, text
        print("golden-diff self-test: ok (added line, changed text, multiple files, no diff, "
              "log parsing, tests-root mapping)")
        return 0
    except AssertionError as e:
        print(f"golden-diff self-test: FAILED\n{e}", file=sys.stderr)
        return 1
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(add_help=True, description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("logs", nargs="*", type=Path, help="test logs (*.log) or --timings files (*.jsonl)")
    ap.add_argument("--case", action="append", default=[], metavar="GROUP:CASE")
    ap.add_argument("--grail", default="")
    ap.add_argument("--repo", default="")
    ap.add_argument("--timeout", type=int, default=300)
    ap.add_argument("--max-cases", type=int, default=12)
    ap.add_argument("--out", type=Path)
    ap.add_argument("--comment-out", type=Path)
    ap.add_argument("--keep", action="store_true")
    ap.add_argument("--self-test", action="store_true")
    ap.add_argument("--quiet", action="store_true")
    a = ap.parse_args(argv)
    if a.self_test:
        return self_test()
    if a.timeout <= 0 or a.max_cases <= 0:
        print("golden-diff: --timeout and --max-cases must be positive", file=sys.stderr)
        return 2

    repo = Path(a.repo or Path(__file__).resolve().parent.parent).resolve()
    if not (repo / "grail.wiz").is_file():
        print(f"golden-diff: {repo} is not a checkout (no grail.wiz)", file=sys.stderr)
        return 2
    failures = failures_from(a.logs)
    for spec in a.case:
        group, _, case = spec.partition(":")
        failures.append(Failure(group, case or group, source="--case"))
    # the same case can appear in a log and in --case (or in several shard logs)
    unique: dict[tuple[str, str], Failure] = {}
    for f in failures:
        unique.setdefault((f.group, f.case), f)
    failures = list(unique.values())
    if not failures:
        text = (f"{MARKER}\n\n### Golden diff\n\nNo failing test cases in the logs"
                f"{' (' + ', '.join(p.name for p in a.logs) + ')' if a.logs else ''}.\n")
        if a.out:
            a.out.write_text(text)
        else:
            print(text, end="")
        return 0

    grail = a.grail or os.environ.get("GRAIL") or ""
    if not grail:
        local = repo / ".lake/build/bin/grail"
        grail = str(local) if local.is_file() else shutil.which("grail") or ""
    if not grail or not (Path(grail).is_file() or shutil.which(grail)):
        print("golden-diff: no grail binary (use --grail PATH or build .lake/build/bin/grail)",
              file=sys.stderr)
        return 2

    roots = tests_roots(repo)
    tmp = Path(tempfile.mkdtemp(prefix="golden-diff-"))
    shutil.copytree(repo, tmp / "repo", symlinks=True, ignore=IGNORE)
    work = tmp / "repo"
    if not a.quiet:
        print(f"golden-diff: {len(failures)} failing case(s); re-running in {work}", file=sys.stderr)
    results: list[Result] = []
    known: dict[str, Result] = {}
    budget = a.max_cases
    try:
        for f in failures:
            goldens, why = find_golden(f, repo, roots)
            if not goldens:
                results.append(Result(f, "non-golden", note=why))
                continue
            for g in goldens:
                if g.path in known:
                    r = known[g.path]
                    results.append(Result(f, r.status, list(r.files), r.note, r.diff))
                    continue
                if budget <= 0:
                    results.append(Result(f, "skipped", note=f"more than {a.max_cases} golden files"))
                    continue
                budget -= 1
                if not a.quiet:
                    print(f"golden-diff: {g.path} (grail test --update {g.rel})", file=sys.stderr)
                status, files, note, diff = update_one(work, g, grail, a.timeout, repo)
                r = Result(f, status, files, note, diff)
                known[g.path] = r
                results.append(r)
    finally:
        if a.keep:
            print(f"golden-diff: kept {tmp}", file=sys.stderr)
        else:
            shutil.rmtree(tmp, ignore_errors=True)

    text = render(failures, results)
    if a.comment_out:
        a.comment_out.write_text(render(failures, results, max_bytes=60000))
    if a.out:
        a.out.write_text(text)
        if not a.quiet:
            print(f"golden-diff: wrote {a.out}", file=sys.stderr)
    else:
        print(text, end="")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
