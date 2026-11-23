#!/usr/bin/env python3
"""Check the textual side of the test fixtures: `.expected` anchors and markers.

The test suite builds Wiz programs from Lean strings, and many of its expectations are
positions (`path:line:col`) and goldens (`.expected` beside a `-- test:` file). Both rot
silently when the source moves: a golden compares a whole transcript, so a comment added
above a `#eval` makes every later line red in a 400 s case; a Wasm case compared
`lib/IO.wiz:251:1` after the extern it names had moved to line 254 and stayed red until
someone read the shard. This script is the fast, named place for that class:

  * every `path:line[:col]` in an `.expected` file resolves to the golden's own `.wiz`
    (not another file), is in range, and points at a code line (not a blank line, a
    comment or a doc-comment tail);
  * every `path:line[:col]` in a `Tests/**/*.lean` string that names an existing
    repository file is checked the same way, and the line must declare a name the
    enclosing case mentions nearest to the anchor (the Wasm `Bytes.empty` anchor is the
    model). Anchors to a generated file (`main.wiz`, `input.wiz`, ...) are counted, not
    guessed: the `=fixtures` group compiles the builders that produce them;
  * every grail test suite (`Package.tests` in a `grail.wiz`) is marked consistently:
    a `-- test: skip` has a reason and no `.expected`, a `check`/`run` test has one, and
    the golden's first nonblank line is the shape its marker produces. `-- test:` is
    optional and means `check` (as `Grail.TestKind` says).

The suites are discovered from the current `grail.wiz` files, and the anchors from the
current `.expected` and `.lean` files, so a new fixture is covered without an edit here.

This is deliberately not a compiler: it needs no build, no `wiz`, no `cc` and no network.
The compile half is the `=fixtures` test group (`Tests/Groups/Fixtures.lean`), which
elaborates the long-case source builders with the same frontend helper the cases use and
reports a missing dependency through `skipMissing` (a failure unless the run explicitly
allows it). The docs fences are compiled by `scripts/check-docs-examples.py` in the
`docs_examples` job, not duplicated here.

Usage
  scripts/check-fixtures.py              check this checkout
  scripts/check-fixtures.py --self-test  run the built-in fixture trees
  scripts/check-fixtures.py --root DIR   check another checkout
  scripts/check-fixtures.py --quiet      print only problems and the summary

Exit status: 0 clean, 1 problems (or a failing self-test), 2 usage error.
"""

from __future__ import annotations

import argparse
import re
import sys
import tempfile
from dataclasses import dataclass, field
from pathlib import Path

# `path/to/file.wiz:12` or `path/to/file.wiz:12:3`. The look-behind keeps a URL or a
# dotted module name from being read as a path, and the extension is required.
ANCHOR = re.compile(r"(?<![\w/.-])([A-Za-z0-9_./-]+\.wiz):(\d+)(?::(\d+))?")
# A check message line: `path:line:col: severity: text` (`Grail.Elab.render`).
CHECK_MESSAGE = re.compile(r"^([^:\n]+\.wiz):(\d+):(\d+): (error|warning|info): ")
# A declaration line in a `.wiz` source, for the anchor's target: the keyword, the
# optional C spelling (`extern "sym" Name`), and the declared name.
DECL = re.compile(
    r"^\s*(?:private\s+|protected\s+|partial\s+|noncomputable\s+|@\[[^\]]*\]\s*)*"
    r"(?:def|axiom|extern|structure|inductive|theorem|lemma|opaque|abbrev|class|instance|"
    r"example|namespace|c_struct|glue|foreign_type)\s+"
    r"(?:\"[^\"]*\"\s+)?([A-Za-z_][A-Za-z0-9_'.]*)"
)
IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*")
CASE_START = re.compile(r"^\s{0,8}\{ name :=")
SKIP_DIRS = {".git", ".lake", ".build", "node_modules", "__pycache__"}


@dataclass
class Report:
    roots: list[tuple[Path, Path]] = field(default_factory=list)
    expected_files: int = 0
    expected_anchors: int = 0
    lean_repo_anchors: int = 0
    lean_generated_anchors: int = 0
    markers: int = 0
    problems: list[str] = field(default_factory=list)


# --------------------------------------------------------------------------------------
# Discovery


def _skip(path: Path) -> bool:
    return any(part in SKIP_DIRS for part in path.parts)


def test_roots(root: Path) -> list[tuple[Path, Path]]:
    """`(package root, tests directory)` for each `Package.tests` in a `grail.wiz`.

    A manifest's tests directory is the second string argument (`Package.tests "name"
    "dir"`). Nested packages under a tests directory are separate suites, so the walk
    stops at a directory with its own `grail.wiz`.
    """
    manifests = sorted(root.glob("*/grail.wiz"))
    if (root / "grail.wiz").is_file():
        manifests.insert(0, root / "grail.wiz")
    out: list[tuple[Path, Path]] = []
    seen: set[Path] = set()
    for manifest in manifests:
        try:
            text = manifest.read_text(encoding="utf-8")
        except OSError:
            continue
        for m in re.finditer(
                r"Package\.tests\s+\"([^\"]*)\"\s+\"([^\"]*)\"", text):
            tests = (manifest.parent / m.group(2)).resolve()
            if tests.is_dir() and tests not in seen:
                seen.add(tests)
                out.append((manifest.parent, tests))
    return sorted(out, key=lambda p: p[1].as_posix())


def walk_suite(directory: Path, suffix: str) -> list[Path]:
    """Every `suffix` file under `directory`, without entering a nested package."""
    out: list[Path] = []
    for path in sorted(directory.rglob(f"*{suffix}")):
        if _skip(path):
            continue
        # a subdirectory with its own grail.wiz is a package, not this suite's test
        parent = path.parent
        nested = False
        while parent != directory:
            if (parent / "grail.wiz").is_file():
                nested = True
                break
            parent = parent.parent
        if not nested:
            out.append(path)
    return out


def walk_tests(directory: Path) -> list[Path]:
    """Every `.wiz` test under `directory`, without entering a nested package."""
    return walk_suite(directory, ".wiz")


def marker_of(src: str) -> tuple[str, str]:
    """The `-- test:` kind (`check` when absent, as `Grail.TestKind`) and a skip's reason."""
    first = src.split("\n", 1)[0]
    if not first.startswith("-- test:"):
        return "check", ""
    kind = first[8:].strip()
    if kind == "skip":
        return "skip", ""
    if kind.startswith("skip "):
        return "skip", kind[5:].strip()
    words = kind.split()
    if words and words[0] in ("check", "run"):
        return words[0], ""
    return "unknown", kind


# --------------------------------------------------------------------------------------
# Anchor helpers


def code_mask(path: Path) -> list[bool] | None:
    """For each line of `path`: is it code (not blank, a line comment, or a block comment)?"""
    lines = file_lines(path)
    if lines is None:
        return None
    out: list[bool] = []
    depth = 0
    for line in lines:
        s = line.strip()
        if depth:
            depth = max(0, depth + s.count("/-") - s.count("-/"))
            out.append(False)
            continue
        if not s or s.startswith("--") or s.startswith("//"):
            out.append(False)
            continue
        opens, closes = s.count("/-"), s.count("-/")
        if opens:
            depth = max(0, opens - closes)
            out.append(False)
            continue
        out.append(True)
    return out


def resolve_anchor(exp: Path, rel: str, root: Path) -> Path | None:
    """The file an anchor in `exp` names, or None when it resolves nowhere.

    A golden's path is package-relative (`tests/cst.wiz` in `scry/`, `examples/x.wiz` in
    `hdl/`), so the nearest ancestor with a `grail.wiz` is tried first, then the golden's
    own directory and the checkout root.
    """
    candidates = []
    for ancestor in [exp.parent, *exp.parents]:
        if (ancestor / "grail.wiz").is_file():
            candidates.append(ancestor / rel)
            break
    candidates += [exp.parent / rel, root / rel]
    for candidate in candidates:
        if candidate.is_file():
            return candidate.resolve()
    return None


def file_lines(path: Path) -> list[str] | None:
    try:
        return path.read_text(encoding="utf-8").splitlines()
    except (OSError, UnicodeDecodeError):
        return None


def decl_lines(path: Path) -> dict[str, int]:
    """Declared name -> first line, for a `.wiz` file's declarations.

    Comment lines are skipped by `code_mask`, including a declaration-looking line
    inside a `/-! ... -/` documentation fence (`lib/IO.wiz`'s module doc contains a
    `def main` example).
    """
    out: dict[str, int] = {}
    lines = file_lines(path)
    mask = code_mask(path)
    if lines is None or mask is None:
        return out
    for i, (line, code) in enumerate(zip(lines, mask), 1):
        if not code:
            continue
        m = DECL.match(line)
        if m:
            out.setdefault(m.group(1), i)
    return out


# --------------------------------------------------------------------------------------
# Marker check


def check_markers(root: Path, report: Report) -> None:
    for _pkg, tests in report.roots:
        for stale in walk_suite(tests, ".expected"):
            if not stale.with_suffix(".wiz").exists():
                rel = stale.relative_to(root) if stale.is_relative_to(root) else stale
                report.problems.append(
                    f"{rel}: a golden with no .wiz beside it (a renamed or deleted test)")
        for wiz in walk_tests(tests):
            report.markers += 1
            rel = wiz.relative_to(root) if wiz.is_relative_to(root) else wiz
            try:
                src = wiz.read_text(encoding="utf-8")
            except (OSError, UnicodeDecodeError) as exc:
                report.problems.append(f"{rel}: cannot read: {exc}")
                continue
            kind, reason = marker_of(src)
            expected = wiz.with_suffix(".expected")
            if kind == "unknown":
                report.problems.append(
                    f"{rel}: unknown `-- test:` marker {reason!r} "
                    "(check, run, or skip REASON)")
                continue
            if kind == "skip":
                if not reason.strip():
                    report.problems.append(f"{rel}: -- test: skip needs a reason")
                if expected.exists():
                    report.problems.append(
                        f"{rel}: a skipped test has {expected.name}; "
                        "a skip is not compared, so a golden beside it is stale")
                continue
            if not expected.exists():
                report.problems.append(
                    f"{rel}: a {kind} test has no {expected.name} "
                    "(`grail test --update` writes it)")
                continue
            try:
                text = expected.read_text(encoding="utf-8")
            except (OSError, UnicodeDecodeError) as exc:
                report.problems.append(f"{expected}: cannot read: {exc}")
                continue
            first = next((line for line in text.splitlines() if line.strip()), "")
            if not first:
                continue
            message = CHECK_MESSAGE.match(first)
            if kind == "check" and not message:
                report.problems.append(
                    f"{rel}: its {expected.name} holds program output, but the test is "
                    f"a check test (no `-- test: run`): {first!r}")
            elif kind == "run" and message:
                report.problems.append(
                    f"{rel}: it says `-- test: run` but its {expected.name} holds check "
                    f"messages: {first!r}")


# --------------------------------------------------------------------------------------
# `.expected` anchors


def info_commands(path: Path) -> list[int]:
    """The lines of a `.wiz` file's message-producing commands (`#eval`, `#check`, ...)."""
    lines = file_lines(path)
    if lines is None:
        return []
    return [i for i, line in enumerate(lines, 1)
            if re.match(r"^\s*#(?:eval|check|reduce|print|erase)\b", line)]


def check_expected_anchors(root: Path, report: Report) -> None:
    for exp in sorted(root.rglob("*.expected")):
        if _skip(exp):
            continue
        report.expected_files += 1
        rel_exp = exp.relative_to(root) if exp.is_relative_to(root) else exp
        sibling = exp.with_suffix(".wiz")
        lines = file_lines(exp)
        if lines is None:
            report.problems.append(f"{rel_exp}: cannot read")
            continue
        anchored: list[int] = []
        for lineno, line in enumerate(lines, 1):
            for m in ANCHOR.finditer(line):
                report.expected_anchors += 1
                rel, at, col = m.group(1), int(m.group(2)), m.group(3)
                anchored.append(at)
                target = resolve_anchor(exp, rel, root)
                if target is None:
                    report.problems.append(
                        f"{rel_exp}:{lineno}: anchor {rel}:{at} resolves to no file")
                    continue
                if target != sibling.resolve():
                    shown = target.relative_to(root) if target.is_relative_to(root) else target
                    report.problems.append(
                        f"{rel_exp}:{lineno}: anchor {rel}:{at} names {shown}, "
                        f"not this golden's source {sibling.relative_to(root)}")
                    continue
                source_lines = file_lines(target)
                if source_lines is None or not 1 <= at <= len(source_lines):
                    count = 0 if source_lines is None else len(source_lines)
                    report.problems.append(
                        f"{rel_exp}:{lineno}: anchor {rel}:{at} is out of range "
                        f"({count} lines)")
                    continue
                source = source_lines[at - 1]
                mask = code_mask(target)
                if mask is None or not mask[at - 1]:
                    report.problems.append(
                        f"{rel_exp}:{lineno}: anchor {rel}:{at} points at a non-code line: "
                        f"{source.strip()!r}")
                if col is not None and not 1 <= int(col) <= len(source) + 1:
                    report.problems.append(
                        f"{rel_exp}:{lineno}: anchor {rel}:{at}:{col} has a column past "
                        f"the line ({len(source)} chars)")

        # A `check` golden whose messages are all `info` is the messages of the file's
        # `#eval`/`#check`/... commands, in order, one line each. Compare the anchors with
        # the current command lines: this catches a line inserted above a command even
        # when the shifted position is still a code line (the number is generated from
        # the source, not maintained here). A golden with an error or a warning is not
        # ordered this way (an error may point anywhere), so only the line is checked.
        if sibling.exists():
            kind, _ = marker_of(sibling.read_text(encoding="utf-8"))
        else:
            kind = ""
        nonblank = [line for line in lines if line.strip()]
        messages = [CHECK_MESSAGE.match(line) for line in nonblank]
        if (kind == "check" and messages
                and all(m is not None and m.group(4) == "info" for m in messages)):
            commands = info_commands(sibling)
            if anchored != commands:
                report.problems.append(
                    f"{rel_exp}: the info anchors are {anchored}, but "
                    f"{sibling.relative_to(root)}'s #eval/#check lines are {commands} "
                    "(a command was added, removed or moved without updating the golden)")


# --------------------------------------------------------------------------------------
# Lean-resident anchors


def case_block(lines: list[str], index: int) -> tuple[int, int]:
    """The lines of the `{ name := ... }` case around `index` (or a ±40-line window)."""
    start = index
    while start > 0 and not CASE_START.match(lines[start - 1]):
        start -= 1
    if start == index and not CASE_START.match(lines[index]):
        start = max(0, index - 40)
    end = index
    while end + 1 < len(lines) and not CASE_START.match(lines[end + 1]):
        if re.match(r"^\s{0,8}\]", lines[end + 1]):
            break
        end += 1
    if end == index:
        end = min(len(lines) - 1, index + 40)
    return start, end


def nearest_declaration(lines: list[str], anchor_line: int,
                        decls: dict[str, int]) -> str | None:
    """The declared name a case's text mentions closest to its anchor literal.

    `None` when the case mentions no declaration in the target file (the anchor is then
    only checked for being a code line).
    """
    if not decls:
        return None
    distances: dict[str, int] = {}
    for i, line in enumerate(lines, 1):
        for token in IDENT.findall(line):
            if token in decls:
                distances[token] = min(distances.get(token, 1 << 30),
                                       abs(i - anchor_line))
    if not distances:
        return None
    # nearest mention wins; a tie goes to the longer (dotted) name, so a case that
    # names `Bytes.empty` selects the extern at line 254, not the `Bytes` axiom above it
    return min(distances, key=lambda name: (distances[name], -len(name)))


def check_lean_anchors(root: Path, report: Report) -> None:
    tests = root / "Tests"
    if not tests.is_dir():
        return
    for lean in sorted(tests.rglob("*.lean")):
        if _skip(lean):
            continue
        lines = file_lines(lean)
        if lines is None:
            continue
        for i, line in enumerate(lines):
            for m in ANCHOR.finditer(line):
                rel, at, col = m.group(1), int(m.group(2)), m.group(3)
                target = root / rel
                if not target.exists():
                    # A fixture may generate the file in a temporary directory
                    # (`input.wiz`, `lib/M.wiz`); its line numbers are checked by the
                    # case that builds it, not guessed here.
                    report.lean_generated_anchors += 1
                    continue
                report.lean_repo_anchors += 1
                target_lines = file_lines(target)
                if target_lines is None or not 1 <= at <= len(target_lines):
                    count = 0 if target_lines is None else len(target_lines)
                    report.problems.append(
                        f"{lean.relative_to(root)}:{i + 1}: anchor {rel}:{at} is out of "
                        f"range ({count} lines)")
                    continue
                source = target_lines[at - 1]
                mask = code_mask(target)
                if mask is None or not mask[at - 1]:
                    report.problems.append(
                        f"{lean.relative_to(root)}:{i + 1}: anchor {rel}:{at} points at a "
                        f"non-code line: {source.strip()!r}")
                    continue
                if col is not None and not 1 <= int(col) <= len(source) + 1:
                    report.problems.append(
                        f"{lean.relative_to(root)}:{i + 1}: anchor {rel}:{at}:{col} has a "
                        f"column past the line ({len(source)} chars)")
                decls = decl_lines(target)
                start, end = case_block(lines, i)
                name = nearest_declaration(lines[start:end + 1], i + 1, decls)
                if name is not None:
                    decl = decls[name]
                    if decl != at:
                        report.problems.append(
                            f"{lean.relative_to(root)}:{i + 1}: anchor {rel}:{at} points at "
                            f"{source.strip()!r}, but this case names {name}, declared at "
                            f"{rel}:{decl}")


# --------------------------------------------------------------------------------------
# Driver


def run_check(root: Path) -> Report:
    report = Report(roots=test_roots(root))
    if not report.roots:
        report.problems.append(
            "no `Package.tests` in any grail.wiz (the test suites cannot be discovered)")
    check_markers(root, report)
    check_expected_anchors(root, report)
    check_lean_anchors(root, report)
    return report


def print_report(report: Report, quiet: bool) -> int:
    for problem in report.problems:
        print(problem)
    summary = (f"check-fixtures: {len(report.roots)} grail suite(s); "
               f"{report.markers} tests; {report.expected_files} .expected files, "
               f"{report.expected_anchors} anchors; {report.lean_repo_anchors} repository "
               f"anchors in Tests/ (+{report.lean_generated_anchors} generated-file anchors)")
    if report.problems:
        print(f"\n{summary}: {len(report.problems)} problem(s)", file=sys.stderr)
        return 1
    print(f"{summary}: clean")
    return 0


# --------------------------------------------------------------------------------------
# Self-test


GOOD_MANIFEST = ('import Grail\ndef package : Package := Package.new "site"\n'
                 '  |> Package.tests "examples" "examples"\n')
GOOD_WIZ = "import Prelude\ndef one : Nat := 1\n"
GOOD_TEST = "import Prelude\n#eval 1\n"
GOOD_EXPECTED = "examples/good.wiz:2:1: info: 1\n"
RUN_WIZ = '-- test: run\nimport IO\ndef main : IO Unit := IO.println "hi"\n'
SKIP_WIZ = "-- test: skip a fixture, not a test here\nimport Prelude\ndef x : Nat := 1\n"


def _write_tree(root: Path, files: dict[str, str]) -> None:
    for name, text in files.items():
        path = root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")


def self_test() -> int:
    failures: list[str] = []

    def expect(problems: list[str], want: str) -> None:
        if not any(want in p for p in problems):
            failures.append(f"missing expected problem: {want}")

    with tempfile.TemporaryDirectory(prefix="wiz-fixtures-selftest-") as tmp:
        base = Path(tmp)
        good = base / "good"
        _write_tree(good, {
            "grail.wiz": GOOD_MANIFEST,
            "examples/good.wiz": GOOD_TEST,
            "examples/good.expected": GOOD_EXPECTED,
            "examples/run.wiz": RUN_WIZ,
            "examples/run.expected": "hi\n",
            "examples/skip.wiz": SKIP_WIZ,
            "lib/IO.wiz": "def one : Nat := 1\n",
            "Tests/Groups/Wasm.lean":
                'def c : Case where\n  name := "an extern at its declaration"\n'
                '  run := fun _ =>\n    check ((e.splitOn "lib/IO.wiz:1:1").length > 1) e\n'
                '    check ((e.splitOn "`one`").length > 1) e\n',
        })
        report = run_check(good)
        for problem in report.problems:
            failures.append(f"good tree: unexpected problem: {problem}")
        if report.markers != 3:
            failures.append(f"good tree: expected 3 markers, got {report.markers}")
        if report.expected_anchors != 1:
            failures.append(f"good tree: expected 1 anchor, got {report.expected_anchors}")
        if report.lean_repo_anchors != 1:
            failures.append(f"good tree: expected 1 repository anchor, got "
                            f"{report.lean_repo_anchors}")

        bad = base / "bad"
        _write_tree(bad, {
            "grail.wiz": GOOD_MANIFEST,
            "examples/good.wiz": GOOD_TEST,
            "examples/good.expected": GOOD_EXPECTED,
            "examples/missing.wiz": GOOD_TEST,
            "examples/skip-with-golden.wiz": SKIP_WIZ,
            "examples/skip-with-golden.expected": "",
            "examples/skip-no-reason.wiz": "-- test: skip\n",
            "examples/unknown.wiz": "-- test: wat\n",
            "examples/run-check.wiz": RUN_WIZ,
            "examples/run-check.expected": "examples/run-check.wiz:3:1: info: one : Nat\n",
            "examples/check-output.wiz": GOOD_TEST,
            "examples/check-output.expected": "some program output\n",
            "examples/shift.wiz": "-- a comment\n#eval 1\n",
            "examples/shift.expected": "examples/shift.wiz:1:1: info: 1\n",
            "examples/range.wiz": GOOD_TEST,
            "examples/range.expected": "examples/range.wiz:99:1: info: 1\n",
            "examples/cmd-shift.wiz": "import Prelude\n#eval 1\n#eval 2\n",
            "examples/cmd-shift.expected": "examples/cmd-shift.wiz:3:1: info: 2\n",
            "examples/wrong.wiz": GOOD_TEST,
            "examples/wrong.expected": "examples/good.wiz:2:1: info: 1\n",
            "examples/orphan.expected": "",
            "lib/IO.wiz": "def one : Nat := 1\ndef two : Nat := 2\n",
            "Tests/Groups/Shift.lean":
                'def c : Case where\n  name := "a shifted anchor"\n'
                '  run := fun _ =>\n    check ((e.splitOn "lib/IO.wiz:2:1").length > 1) e\n'
                '    check ((e.splitOn "`one`").length > 1) e\n',
        })
        report = run_check(bad)
        problems = report.problems
        expect(problems, "a check test has no missing.expected")
        expect(problems, "a golden with no .wiz beside it")
        expect(problems, "a skipped test has skip-with-golden.expected")
        expect(problems, "skip needs a reason")
        expect(problems, "unknown `-- test:` marker")
        expect(problems, "it says `-- test: run` but its run-check.expected holds check")
        expect(problems, "its check-output.expected holds program output")
        expect(problems, "anchor examples/shift.wiz:1 points at a non-code line")
        expect(problems, "anchor examples/range.wiz:99 is out of range")
        expect(problems, "the info anchors are [3], but examples/cmd-shift.wiz's "
                         "#eval/#check lines are [2, 3]")
        expect(problems, "anchor examples/good.wiz:2 names")
        expect(problems, "but this case names one, declared at lib/IO.wiz:1")

        # The marker parser, on the timeout form `Grail.TestKind` accepts.
        if marker_of("-- test: run timeout 900\n") != ("run", ""):
            failures.append("marker parser: a run timeout was not read as run")
        if marker_of("-- test: skip on demand: a fixture\n") != (
                "skip", "on demand: a fixture"):
            failures.append("marker parser: a skip reason was not read")
        if marker_of("def one : Nat := 1\n") != ("check", ""):
            failures.append("marker parser: an absent marker was not read as check")

    if failures:
        for failure in failures:
            print(f"self-test FAIL: {failure}", file=sys.stderr)
        return 1
    print("check-fixtures self-test: ok "
          "(anchors, markers, skip reasons, generated-file anchors, shifted declarations)")
    return 0


# --------------------------------------------------------------------------------------
# CLI


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Check fixture `.expected` anchors and `-- test:` markers.")
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parent.parent,
                        help="checkout to check (default: the one containing this script)")
    parser.add_argument("--self-test", action="store_true",
                        help="run the built-in fixture trees instead of the checkout")
    parser.add_argument("--quiet", action="store_true",
                        help="print only problems and the summary")
    args = parser.parse_args(argv)
    if args.self_test:
        return self_test()
    root = args.root.resolve()
    if not root.is_dir():
        parser.error(f"--root is not a directory: {root}")
    return print_report(run_check(root), args.quiet)


if __name__ == "__main__":
    sys.exit(main())
