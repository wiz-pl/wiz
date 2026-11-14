#!/usr/bin/env python3
"""Fail on authoring-environment artefacts in Wiz's user-facing documentation.

The claudism cleanup (PR #283) removed absolute harness paths, agent role
names and status checkmarks from the docs.  This check keeps them out: it is
cheap (no build, no dependencies beyond Python 3) and runs in CI on every
push and pull request, including docs-only ones.

Checked files: README.md, ROADMAP.md and CHANGELOG.md when present, plus
docs/**/*.md.  (drafts/ and the source doc comments are not user-facing and
are out of scope.)

Rules
  workspace-path  an absolute /workspace/... path, e.g.
                  `/workspace/wiz-notes/foo.md`.  It names the machine that ran
                  an agent, not a checkout, so it cannot resolve for a reader.
                  Use a relative path (`wiz-notes/foo.md`, as most docs do).
  agent-role      an internal branch name (`agent/<name>`), or an AI worker
                  role ("agent mem-hunt", "the theory agent").  Provenance in
                  a development ledger is fine without the worker's name:
                  say what was found, or when.
  status-check    a status checkmark (U+2705, `✅`) in prose or a heading.
                  A heading or a status row already says what is done; the
                  checkmark is decoration and goes stale.
  user-decision   "the user's decision" / "the user's step" (also curly
                  apostrophes).  The docs are written for readers: say what
                  was decided and when ("decided 2026-11-13"), not who decided.
                  Ordinary possessives ("the user's file", "the user's
                  behaviour", "in the user's names") are not hits.

Code blocks and command examples are checked like any other line: /workspace
is specific to the authoring machine even in a shell command, so an example
should use a relative path or "$PWD".  There is no code-fence exemption (a
checkmark pasted into a fence should be `ok` or similar text anyway).

An exception must be reviewed and explicit.  Add an Allow entry to ALLOW
below with the file, rule, the exact text that makes the line acceptable, and
a reason.  The list is meant to stay tiny and is not a glob; an entry that
matches no line is itself an error, so it is removed when the text changes.
(This is also how a genuinely useful `/workspace` command example would be
handled, if one ever appears.)

Usage
  scripts/check-docs-style.py              check this checkout
  scripts/check-docs-style.py --self-test  run the built-in fixtures
  scripts/check-docs-style.py --root DIR   check another checkout
  scripts/check-docs-style.py --quiet      only print the summary

Exit status: 0 clean, 1 violations (or a failing self-test), 2 usage error.
CI runs `scripts/check-docs-style.py --self-test` and then the check itself
(.github/workflows/ci.yml, job `docs_style`).
"""

from __future__ import annotations

import argparse
import re
import sys
from dataclasses import dataclass
from pathlib import Path

ROOT_FILES = ("README.md", "ROADMAP.md", "CHANGELOG.md")


@dataclass(frozen=True)
class Rule:
    name: str
    description: str
    pattern: re.Pattern[str]


@dataclass(frozen=True)
class Allow:
    """A reviewed exception: `text` must occur in `path` on a `rule` hit."""

    path: str
    rule: str
    text: str
    reason: str


@dataclass(frozen=True)
class Hit:
    line: int
    rule: str
    match: str
    excerpt: str


# Keep this empty unless a line really is correct in context.  See the module
# docstring for the format and for why there is no blanket code-block exemption.
ALLOW: tuple[Allow, ...] = ()

RULES = (
    Rule(
        "workspace-path",
        "absolute /workspace/... path",
        # Not part of a URL (https://example.com/workspace/...) or of a
        # relative path like ../workspace/... or ~/workspace/...: the character
        # before the slash must not be a word character, slash, dot, dash or ~.
        re.compile(r"(?<![\w:/.\-~])/workspace(?![-\w])"),
    ),
    Rule(
        "agent-role",
        "internal branch name or AI worker role",
        re.compile(
            # agent/<name> (including in a GitHub URL)
            r"(?<![\w-])agent/[A-Za-z0-9][\w.-]*"
            # "agent mem-hunt" (but not "Agents share a machine" or the
            # technical "user agent string")
            r"|(?<![\w-])(?<!user\s)agent\s+[a-z][a-z0-9-]*"
            # "the theory agent", "the docs agent" (but not "the user agent")
            r"|(?<![\w-])the\s+(?!user\b)[a-z][a-z0-9-]*\s+agent\b",
            re.IGNORECASE,
        ),
    ),
    Rule(
        "status-check",
        "status checkmark (U+2705)",
        re.compile("\u2705"),
    ),
    Rule(
        "user-decision",
        '"the user\'s decision/step"',
        re.compile(
            r"(?<![\w-])(?:the|a|an)\s+user['\u2019]s\s+"
            r"(?:decision|decisions|step|steps)\b",
            re.IGNORECASE,
        ),
    ),
)


def in_scope(relpath: str) -> bool:
    """Is this repository-relative POSIX path one of the checked files?"""
    return relpath in ROOT_FILES or (
        relpath.startswith("docs/") and relpath.endswith(".md")
    )


def doc_files(root: Path) -> list[Path]:
    """The checked files of a checkout, sorted, without duplicates."""
    files = [root / name for name in ROOT_FILES if (root / name).is_file()]
    docs = root / "docs"
    if docs.is_dir():
        files.extend(path for path in docs.rglob("*.md") if path.is_file())
    return sorted(set(files), key=lambda path: path.as_posix())


def scan_text(
    text: str, path: str = "", allow: tuple[Allow, ...] = ()
) -> tuple[list[Hit], set[int]]:
    """Return (hits, indexes of `allow` entries used) for some document text.

    At most one hit per rule per line is reported (the first match), which is
    enough to fail the line and keeps the output readable.  A hit is suppressed
    only by an allow entry with the same path and rule whose text occurs on
    that line.
    """
    hits: list[Hit] = []
    used: set[int] = set()
    for lineno, line in enumerate(text.splitlines(), 1):
        for rule in RULES:
            match = rule.pattern.search(line)
            if match is None:
                continue
            suppressed = False
            for index, exception in enumerate(allow):
                if (
                    exception.path == path
                    and exception.rule == rule.name
                    and exception.text in line
                ):
                    used.add(index)
                    suppressed = True
                    break
            if suppressed:
                continue
            excerpt = " ".join(line.split())
            if len(excerpt) > 160:
                excerpt = excerpt[:157] + "..."
            hits.append(Hit(lineno, rule.name, match.group(0), excerpt))
    return hits, used


def describe(rule_name: str) -> str:
    for rule in RULES:
        if rule.name == rule_name:
            return rule.description
    return rule_name


def check(root: Path, quiet: bool = False) -> int:
    if not (root / "README.md").is_file() or not (root / "docs").is_dir():
        print(
            f"check-docs-style: {root} is not a Wiz checkout "
            "(README.md or docs/ is missing)",
            file=sys.stderr,
        )
        return 2

    files = doc_files(root)
    problems: list[str] = []
    used_allow: set[int] = set()

    for path in files:
        relpath = path.relative_to(root).as_posix()
        try:
            text = path.read_text(encoding="utf-8")
        except UnicodeDecodeError as exc:
            problems.append(f"{relpath}: not UTF-8: {exc}")
            continue
        hits, used = scan_text(text, relpath, ALLOW)
        used_allow |= used
        for hit in hits:
            problems.append(
                f"{relpath}:{hit.line}: {hit.rule} "
                f"({describe(hit.rule)}): {hit.match}\n    {hit.excerpt}"
            )

    # An exception that no longer matches anything is dead: report it, so the
    # allowlist cannot silently grow stale.
    for index, exception in enumerate(ALLOW):
        if index not in used_allow:
            problems.append(
                f"ALLOW[{index}]: stale exception for {exception.path} "
                f"({exception.rule}): {exception.text!r} matches no line "
                f"({exception.reason})"
            )

    if not quiet or problems:
        for problem in problems:
            print(problem)
    count = len(files)
    if problems:
        print(
            f"\ncheck-docs-style: {len(problems)} problem(s) "
            f"in {count} checked file(s)",
            file=sys.stderr,
        )
        return 1
    print(f"check-docs-style: clean ({count} checked file(s))")
    return 0


# (name, text, expected rule names in order)
FIXTURES: tuple[tuple[str, str, tuple[str, ...]], ...] = (
    ("clean prose", "The kernel checks definitions; the reader sees errors.\n", ()),
    (
        "absolute path",
        "See `/workspace/wiz-notes/foo.md`.\n",
        ("workspace-path",),
    ),
    (
        "absolute path in a code block is still checked",
        "```\ncd /workspace/wiz-lang\n```\n",
        ("workspace-path",),
    ),
    (
        "relative path",
        "See `wiz-notes/foo.md` and `../docs/index.md`.\n",
        (),
    ),
    (
        "workspace as an ordinary word",
        "## 11v: the outline, workspace symbols and folding\n",
        (),
    ),
    (
        "URL path is not a local path",
        "https://example.com/workspace/foo\n",
        (),
    ),
    (
        "home-relative workspace is not an absolute path",
        "cd ~/workspace/wiz-lang\n",
        (),
    ),
    (
        "internal branch name",
        "The fix is on `agent/docs-lint`.\n",
        ("agent-role",),
    ),
    (
        "internal branch in a URL",
        "https://github.com/wiz-pl/wiz/tree/agent/docs-lint\n",
        ("agent-role",),
    ),
    (
        "a different absolute name",
        "/workspace-wiz is a different directory name.\n",
        (),
    ),
    (
        "named agent",
        "Found by agent mem-hunt.\n",
        ("agent-role",),
    ),
    (
        "the <x> agent",
        "It was reviewed by the theory agent.\n",
        ("agent-role",),
    ),
    (
        "ordinary plural",
        "Agents share one machine; the agentless build is fine.\n",
        (),
    ),
    (
        "user agent header is technical",
        "Server and the User-Agent header\n",
        (),
    ),
    (
        "user agent string is technical",
        "The user agent string is logged, and the user agent sends it.\n",
        (),
    ),
    (
        "checkmark in a heading",
        "## 24e: notation for specifications \u2705\n",
        ("status-check",),
    ),
    (
        "checkmark in prose",
        "Done \u2705 yesterday.\n",
        ("status-check",),
    ),
    (
        "the user's decision",
        "**Decided by conversion (the user's decision).**\n",
        ("user-decision",),
    ),
    (
        "the user's step with a curly apostrophe",
        "this is the user\u2019s step\n",
        ("user-decision",),
    ),
    (
        "a user's file is ordinary",
        "a macro splices the user's own syntax\n",
        (),
    ),
    (
        "a user's behaviour is ordinary",
        "the user's behaviour is documented\n",
        (),
    ),
    (
        "one hit per rule per line",
        "/workspace/a and /workspace/b, then agent one and agent two\n",
        ("workspace-path", "agent-role"),
    ),
)

SCOPE_CASES: tuple[tuple[str, bool], ...] = (
    ("README.md", True),
    ("ROADMAP.md", True),
    ("CHANGELOG.md", True),
    ("docs/index.md", True),
    ("docs/stages/01-overview.md", True),
    ("drafts/feral/STATUS.md", False),
    ("docs/index.txt", False),
    ("web/README.md", False),
    ("scripts/check-docs-style.py", False),
)


def self_test() -> int:
    failures: list[str] = []
    for name, text, expected in FIXTURES:
        hits, _ = scan_text(text, "fixture.md")
        got = tuple(hit.rule for hit in hits)
        if got != expected:
            failures.append(f"{name}: expected {expected}, got {got}")

    for relpath, expected in SCOPE_CASES:
        got = in_scope(relpath)
        if got != expected:
            failures.append(f"scope {relpath}: expected {expected}, got {got}")

    # An exception suppresses only its own path, rule and text; and an unused
    # exception is detectable from the returned indexes.
    allow = (Allow("docs/x.md", "workspace-path", "/workspace/wiz-lang", "test"),)
    hits, used = scan_text("cd /workspace/wiz-lang\n", "docs/x.md", allow)
    if hits or used != {0}:
        failures.append(f"allowlist suppression: hits={hits}, used={used}")
    hits, used = scan_text("cd /workspace/wiz-lang\n", "docs/other.md", allow)
    if not hits or used:
        failures.append(f"allowlist must be path-specific: hits={hits}, used={used}")
    hits, used = scan_text("cd /workspace/elsewhere\n", "docs/x.md", allow)
    if not hits or used:
        failures.append(f"allowlist must be text-specific: hits={hits}, used={used}")

    if failures:
        for failure in failures:
            print(f"self-test FAIL: {failure}", file=sys.stderr)
        return 1
    print(
        f"check-docs-style self-test: ok "
        f"({len(FIXTURES)} fixtures, {len(SCOPE_CASES)} scope cases)"
    )
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Check Wiz's user-facing docs for authoring-environment artefacts."
    )
    parser.add_argument(
        "--root",
        type=Path,
        default=Path(__file__).resolve().parent.parent,
        help="checkout to check (default: the one containing this script)",
    )
    parser.add_argument(
        "--self-test",
        action="store_true",
        help="run the built-in fixtures instead of reading files",
    )
    parser.add_argument(
        "--quiet",
        action="store_true",
        help="print only the summary when clean",
    )
    args = parser.parse_args(argv)

    if args.self_test:
        return self_test()
    return check(args.root.resolve(), quiet=args.quiet)


if __name__ == "__main__":
    sys.exit(main())
