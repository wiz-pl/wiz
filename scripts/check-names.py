#!/usr/bin/env python3
"""Check Wiz declarations against the namespace compatibility allowlist.

The namespace model gives a module's declarations the module path as a prefix:
`lib/Scry/CstStore.wiz` is module `Scry.CstStore`, so `def lineIndexGo` becomes
`Scry.CstStore.lineIndexGo` and `def Scry.lineIndexGo` becomes
`Scry.CstStore.Scry.lineIndexGo`.  Stage 0 is behaviour-neutral: every
declaration that exists today has a row in `legacy-names.tsv` and keeps its
current absolute name until its migration batch deletes the row.

This check has two jobs:

  violations   A declaration whose current absolute name does not sit *under*
               its module's prefix (`Scry.CstStore.lineIndexGo`, not
               `Scry.lineIndexGo`).  These are the declarations the migration
               will rename.  A `__root__.` declaration is exempt: it is already
               at the true-global name it keeps.

  baseline     Every violation should have a row from `scripts/gen-legacy-names.py`.
               A row whose declaration has changed or vanished is **stale** and
               fails (the collision baseline's rule).  A declaration with no row
               is reported as unbaselined; `--strict-names` makes it an error.

The allowlist covers *every* declaration, not only the violating ones: a
name-preserving `def Scry.CstStore.f` also needs its row until batch 2 strips
the module prefix, or the default prefix would make it
`Scry.CstStore.Scry.CstStore.f`.  The checker therefore also reports
declarations with no row (they would move when the prefix flips), but in normal
mode that is a report, not a failure, exactly like a violation.

Modes
  normal          Print every unbaselined violation and a summary.  A row
                  suppresses the report (it is the compatibility exemption); a
                  stale row or a digest mismatch is still an error.
  --quiet         Summary only.  Exit 0 on today's tree (every declaration is
                  baselined).  This is the CI gate: it fails on a declaration
                  with no row (a new legacy name) and on a stale row, and on a
                  digest mismatch.
  --strict-names  Every violation is an error, whether or not it has a row, and
                  every declaration without a row is an error.  This is the
                  migration-completeness number, not a gate that is green today.

The baseline file is tab-separated, one row per declaration:
`module<TAB>name<TAB>reason<TAB>file<TAB>line`.  Lines starting with `#` are
comments.  A row with the wrong field count, an empty field, an unknown reason
class, a non-numeric line, or a duplicate `(module, name)` is a malformed
baseline (exit 2).  `--baseline FILE` uses another file (the fixtures do).

The allowlist is read by the elaborator from stage 3 on, so its digest is part of
the cache key.  `Wiz/LegacyNames.lean` carries the SHA-256 of this file; when the
default baseline is in use, a mismatch is an error, because a stale cache could
otherwise hide a name change.  `scripts/gen-legacy-names.py --update-digest`
refreshes it.

Usage
  scripts/check-names.py                  check the six roots against legacy-names.tsv
  scripts/check-names.py --quiet          summary; the CI gate
  scripts/check-names.py --strict-names   fail on every name outside its prefix
  scripts/check-names.py --baseline FILE  use another baseline
  scripts/check-names.py --root DIR       scan one module root (repeatable)
  scripts/check-names.py --self-test      run the fixtures and baseline cases

Exit status: 0 clean (reports are allowed), 1 a stale row, a digest mismatch, a
strict violation, or a failing self-test; 2 usage, I/O or malformed-baseline
error.

CI: add these two lines to the `docs_style` job's run step in
`.github/workflows/ci.yml` (after the `check-name-collisions.py` lines):
  python3 scripts/check-names.py --self-test
  python3 scripts/check-names.py --quiet
"""

from __future__ import annotations

import argparse
import hashlib
import re
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path

DECL_KEYWORDS = (
    "def",
    "inductive",
    "coinductive",
    "structure",
    "class",
    "instance",
    "axiom",
    "extern",
    "foreign_type",
    "c_struct",
    "glue",
)
BLOCK_KEYWORDS = ("namespace", "section", "mutual")

# Directories that never hold modules of the roots we scan.
SKIP_DIRS = {".git", ".lake", "node_modules", "__pycache__", "build", "dist", "drafts"}

MODIFIER_RE = re.compile(r"(private|sealed|local|partial)\b")
KEYWORD_RE = re.compile(r"(%s)\b" % "|".join(DECL_KEYWORDS + BLOCK_KEYWORDS))
NAME_RE = re.compile(r"([^\s:(\[\]]+)")
NAMESPACE_RE = re.compile(r"namespace\s+(\S+)")
SECTION_RE = re.compile(r"section\b(?:\s+\S+)?")
END_RE = re.compile(r"end\b(?:\s+(\S+))?")
OPEN_RE = re.compile(r"open\b")
IMPORT_RE = re.compile(r"^import\b\s+(\S+)")

ROOT_ESCAPE = "__root__"

# The reason classes of the namespace plan, §3.3.  `bare` covers a declaration
# with no dot; the other five are the plan's names for the dotted classes.
REASON_CLASSES = (
    "module-prefixed",
    "first-prefixed",
    "leaf-prefixed",
    "other-dotted",
    "principal",
    "bare",
)


@dataclass(frozen=True)
class Decl:
    """One declaration of a source name."""

    keyword: str
    source: str  # exactly as written: `x`, `Scry.x`, `__root__.x`
    module: str  # module name relative to its root
    namespace: str  # explicit `namespace` path (already root-resolved)
    path: str  # repository-relative path
    line: int  # 1-based
    private: bool
    local: bool

    @property
    def escaped(self) -> bool:
        return self.source == ROOT_ESCAPE or self.source.startswith(ROOT_ESCAPE + ".")

    @property
    def bare(self) -> str:
        """The written name with the `__root__.` escape removed."""
        return self.source[len(ROOT_ESCAPE) + 1 :] if self.source.startswith(ROOT_ESCAPE + ".") else self.source

    @property
    def full(self) -> str:
        """The absolute name the compiler gives this declaration today."""
        if self.escaped:
            return self.bare
        return (self.namespace + "." + self.source) if self.namespace else self.source

    @property
    def future_name(self) -> str:
        """The absolute name under the default module prefix, with no allowlist."""
        return self.full if self.escaped else self.module + "." + self.full


def blank_comments_and_strings(text: str) -> str:
    """Replace comments and double-quoted strings with spaces, keeping newlines.

    Line numbers therefore stay those of the original file.
    """
    out = list(text)
    n = len(text)

    def wipe(a: int, b: int) -> None:
        for k in range(a, min(b, n)):
            if out[k] != "\n":
                out[k] = " "

    i = 0
    while i < n:
        c = text[i]
        if text.startswith("--", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            wipe(i, j)
            i = j
        elif text.startswith("/-", i):
            depth = 0
            j = i
            while j < n:
                if text.startswith("/-", j):
                    depth += 1
                    j += 2
                elif text.startswith("-/", j):
                    depth -= 1
                    j += 2
                    if depth == 0:
                        break
                else:
                    j += 1
            wipe(i, j)
            i = j
        elif c == '"':
            j = i + 1
            while j < n:
                if text[j] == "\\":
                    j += 2
                    continue
                if text[j] == '"':
                    j += 1
                    break
                j += 1
            wipe(i, j)
            i = j
        else:
            i += 1
    return "".join(out)


def skip_space(line: str, pos: int) -> int:
    while pos < len(line) and line[pos] in " \t":
        pos += 1
    return pos


def skip_balanced(line: str, pos: int, open_ch: str = "(", close_ch: str = ")") -> int:
    """`line[pos]` is `open_ch`; return the index after its matching `close_ch`."""
    depth = 0
    while pos < len(line):
        if line[pos] == open_ch:
            depth += 1
        elif line[pos] == close_ch:
            depth -= 1
            if depth == 0:
                return pos + 1
        pos += 1
    return len(line)


def consume_modifiers(line: str) -> tuple[int, bool, bool]:
    """Skip leading modifiers; return (end position, saw `private`, saw `local`)."""
    pos = 0
    private = False
    local = False
    while True:
        pos = skip_space(line, pos)
        m = MODIFIER_RE.match(line, pos)
        if not m:
            return pos, private, local
        if m.group(1) == "private":
            private = True
        elif m.group(1) == "local":
            local = True
        pos = m.end()
        if m.group(1) == "partial":
            j = skip_space(line, pos)
            if j < len(line) and line[j] == "(":
                pos = skip_balanced(line, j)
            else:
                pos = j
        pos = skip_space(line, pos)
        if KEYWORD_RE.match(line, pos):
            return pos, private, local


def first_name(rest: str) -> str | None:
    """The first source-name token of a declaration's remainder."""
    m = NAME_RE.match(rest.lstrip())
    if not m:
        return None
    name = m.group(1)
    # `def f.{u}` writes universe parameters directly after the name.
    name = name.split(".{", 1)[0]
    return name or None


def parse_decl(line: str) -> tuple[str, str | None, bool, bool] | None:
    """Parse a top-level command line.

    Returns `(keyword, name, private, local)` for a declaration, `(block, name,
    private, local)` for `namespace`/`section`/`mutual`, `("end", name, False,
    False)` for `end`, and `("open", None, False, False)` for `open`.  `None`
    means no command starts here.
    """
    if not line or line[0] in " \t":
        return None

    m = END_RE.match(line)
    if m:
        return ("end", m.group(1), False, False)
    m = NAMESPACE_RE.match(line)
    if m:
        return ("namespace", m.group(1), False, False)
    if SECTION_RE.match(line):
        return ("section", None, False, False)
    if OPEN_RE.match(line):
        return ("open", None, False, False)

    pos, private, local = consume_modifiers(line)
    m = KEYWORD_RE.match(line, pos)
    if not m:
        return None
    keyword = m.group(1)
    rest = line[m.end() :]

    if keyword in BLOCK_KEYWORDS:
        return (keyword, None, private, local)

    if keyword == "instance":
        # `instance [(priority := n)] [name] binders : T`
        pos2 = skip_space(rest, 0)
        if pos2 < len(rest) and rest[pos2] == "(":
            pos2 = skip_space(rest, skip_balanced(rest, pos2))
        if pos2 >= len(rest) or rest[pos2] in ":[({":
            return ("instance", None, private, local)  # anonymous, no source name
        return ("instance", first_name(rest[pos2:]), private, local)

    if keyword in ("extern", "c_struct"):
        # `extern "sym" [(header := "h")] name : T`
        # Strings were blanked to spaces, so only the optional (...) remains.
        pos2 = skip_space(rest, 0)
        if pos2 < len(rest) and rest[pos2] == "(":
            pos2 = skip_space(rest, skip_balanced(rest, pos2))
        return (keyword, first_name(rest[pos2:]), private, local)

    return (keyword, first_name(rest), private, local)


def apply_namespace_path(stack: list[tuple[str, str | None, bool]], name: str) -> str:
    """The absolute namespace path after opening `name` on `stack`.

    A leading `__root__.` (Lean's `_root_.`) resets the path; otherwise the name
    is relative to the enclosing namespace.
    """
    if name == ROOT_ESCAPE:
        return ""
    if name.startswith(ROOT_ESCAPE + "."):
        return name[len(ROOT_ESCAPE) + 1 :]
    base = current_namespace(stack)
    return (base + "." + name) if base else name


def current_namespace(stack: list[tuple[str, str | None, bool]]) -> str:
    """The namespace path of the innermost open namespace on `stack`."""
    for kind, name, _ in reversed(stack):
        if kind == "namespace" and name is not None:
            return name
    return ""


def scan_file(path: Path, module: str, rel: str) -> tuple[list[Decl], list[str]]:
    """The declarations and `import` targets of one file."""
    try:
        text = path.read_text(encoding="utf-8-sig")
    except (OSError, UnicodeDecodeError) as exc:
        raise OSError(f"cannot read {rel}: {exc}") from exc
    lines = blank_comments_and_strings(text).splitlines()

    # ("namespace"|"section"|"mutual", resolved namespace name, private)
    stack: list[tuple[str, str | None, bool]] = []
    decls: list[Decl] = []
    imports: list[str] = []

    for lineno, line in enumerate(lines, start=1):
        m = IMPORT_RE.match(line)
        if m:
            imports.append(m.group(1))

        parsed = parse_decl(line)
        if parsed is None:
            continue
        kind, name, private, local = parsed

        if kind == "end":
            if not stack:
                continue
            if name:
                # `end Foo` closes the nearest matching namespace if there is one;
                # otherwise the innermost block.
                for index in range(len(stack) - 1, -1, -1):
                    if stack[index][0] == "namespace" and stack[index][1] == name:
                        del stack[index:]
                        break
                else:
                    stack.pop()
            else:
                stack.pop()
            continue

        if kind == "open":
            continue

        if kind in ("namespace", "section", "mutual"):
            resolved = apply_namespace_path(stack, name) if kind == "namespace" and name else None
            stack.append((kind, resolved, private))
            continue

        if name is None or name == "_":
            continue
        in_private_mutual = any(
            block_kind == "mutual" and block_private
            for block_kind, _, block_private in stack
        )
        private = private or in_private_mutual
        decls.append(
            Decl(
                keyword=kind,
                source=name,
                module=module,
                namespace=current_namespace(stack),
                path=rel,
                line=lineno,
                private=private,
                local=local,
            )
        )

    return decls, imports


@dataclass
class Scan:
    """Everything a check needs: declarations, and the files they came from."""

    decls: list[Decl]
    files: list[str]  # repository-relative paths

    @property
    def modules(self) -> dict[str, str]:
        return {decl.path: decl.module for decl in self.decls}


def collect(roots: list[Path], repo: Path) -> Scan:
    """Scan every `.wiz` file below `roots`, naming modules relative to each root."""
    repo = repo.resolve()
    scan = Scan(decls=[], files=[])
    seen: set[Path] = set()

    for root in roots:
        root = root.resolve()
        if not root.is_dir():
            raise OSError(f"{root} is not a directory")
        for hit in sorted(root.rglob("*.wiz")):
            if any(part in SKIP_DIRS for part in hit.relative_to(root).parts):
                continue
            resolved = hit.resolve()
            if resolved in seen:
                continue
            seen.add(resolved)

            module = ".".join(hit.relative_to(root).with_suffix("").parts)
            try:
                rel = resolved.relative_to(repo).as_posix()
            except ValueError:
                rel = resolved.as_posix()

            decls, _imports = scan_file(hit, module, rel)
            scan.decls.extend(decls)
            scan.files.append(rel)

    return scan


def under_module_prefix(decl: Decl) -> bool:
    """Does today's full name already sit under the module's own prefix?

    A name equal to the module path does not: the default prefix would make it
    `M.M` (the plan's principal-type case).  A `__root__` declaration is exempt
    from the whole rule and is handled by the caller.
    """
    return decl.full.startswith(decl.module + ".")


DEFAULT_ROOTS = ("lib", "scry/src", "scry/gen", "tower", "web", "selfhost")


def default_roots(repo: Path) -> list[Path]:
    """The library/tool roots the plan's baseline covers, present in `repo`."""
    present = [repo / name for name in DEFAULT_ROOTS if (repo / name).is_dir()]
    return present or [repo]



REPO = Path(__file__).resolve().parent.parent
DEFAULT_BASELINE = REPO / "legacy-names.tsv"
LEGACY_MODULE = REPO / "Wiz" / "LegacyNames.lean"
FIXTURES = Path(__file__).resolve().parent / "fixtures" / "names"
DIGEST_RE = re.compile(r'def digest : String :=\s*"([0-9a-f]*)"')


@dataclass(frozen=True)
class Row:
    module: str
    name: str
    reason: str
    path: str
    line: int

    @property
    def key(self) -> tuple[str, str]:
        return (self.module, self.name)


class BaselineError(Exception):
    """A baseline that cannot be used; `code` is the process exit status."""

    def __init__(self, message: str, code: int) -> None:
        super().__init__(message)
        self.code = code


@dataclass
class Result:
    violations: list[Decl]  # not under the module prefix, not `__root__`
    baselined: set[tuple[str, str]]  # violation keys that have a row
    missing: list[Decl]  # declarations (of any class) with no row
    stale: list[Row]  # rows whose declaration is gone
    declarations: int
    files: int


def load_baseline(path: Path) -> list[Row]:
    """Load and validate the allowlist; a malformed row is exit 2."""
    try:
        text = path.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError) as exc:
        raise BaselineError(f"{path}: cannot read: {exc}", 2)

    rows: list[Row] = []
    seen: dict[tuple[str, str], int] = {}
    for lineno, line in enumerate(text.splitlines(), start=1):
        if not line.strip() or line.startswith("#"):
            continue
        fields = line.split("\t")
        where = f"{path}:{lineno}"
        if len(fields) != 5:
            raise BaselineError(
                f"{where}: expected 5 tab-separated fields "
                "(module, name, reason, file, line), got %d" % len(fields),
                2,
            )
        module, name, reason, file, line_text = (field.strip() for field in fields)
        for field, value in (
            ("module", module),
            ("name", name),
            ("reason", reason),
            ("file", file),
            ("line", line_text),
        ):
            if not value:
                raise BaselineError(f"{where}: {field!r} is empty", 2)
        if reason not in REASON_CLASSES:
            raise BaselineError(
                f"{where}: unknown reason class {reason!r}; expected one of "
                + ", ".join(REASON_CLASSES),
                2,
            )
        try:
            line_no = int(line_text)
        except ValueError:
            raise BaselineError(f"{where}: line {line_text!r} is not an integer", 2)
        if line_no < 1:
            raise BaselineError(f"{where}: line must be positive", 2)
        key = (module, name)
        if key in seen:
            first_file, first_line, first_index = seen[key]
            # The tree has one duplicate module name (`Main` in `tower/` and
            # `selfhost/`): two packages, never loaded together, both keeping
            # `main`.  Accept that pair (same name and reason, different file)
            # and reject a real duplicate row.
            if file == first_file or reason != rows[first_index].reason:
                raise BaselineError(
                    f"{where}: duplicate row for {module}.{name} (first at line {first_line})",
                    2,
                )
        else:
            seen[key] = (file, lineno, len(rows))
        rows.append(Row(module, name, reason, file, line_no))
    return rows


def evaluate(decls: list[Decl], rows: list[Row]) -> Result:
    """Compare the declarations with the baseline."""
    keys = {row.key for row in rows}
    current: set[tuple[str, str]] = set()
    violations: list[Decl] = []
    missing: list[Decl] = []
    baselined: set[tuple[str, str]] = set()

    for decl in decls:
        if decl.escaped:
            continue  # a `__root__.` declaration is exempt and has no row
        key = (decl.module, decl.full)
        current.add(key)
        if not under_module_prefix(decl):
            violations.append(decl)
            if key in keys:
                baselined.add(key)
        if key not in keys:
            missing.append(decl)

    stale = [row for row in rows if row.key not in current]
    return Result(
        violations=violations,
        baselined=baselined,
        missing=missing,
        stale=stale,
        declarations=len(decls),
        files=len({decl.path for decl in decls}),
    )


def baseline_digest(rows: list[Row]) -> str:
    """SHA-256 of the allowlist's meaning: the sorted `(module, name, reason)` set.

    This matches `digest_of` in `scripts/gen-legacy-names.py`, and deliberately
    ignores the source path and line so that a line shift does not invalidate the
    cache.
    """
    lines = sorted(f"{row.module}\t{row.name}\t{row.reason}" for row in rows)
    return hashlib.sha256(("\n".join(lines) + "\n").encode("utf-8")).hexdigest()


def lean_digest(path: Path) -> str | None:
    """The digest constant in `Wiz/LegacyNames.lean`, or None if it is absent."""
    if not path.is_file():
        return None
    try:
        text = path.read_text(encoding="utf-8")
    except OSError as exc:
        raise BaselineError(f"{path}: cannot read: {exc}", 2)
    m = DIGEST_RE.search(text)
    return m.group(1) if m else None


def describe(decl: Decl) -> str:
    modifier = "private " if decl.private else ("local " if decl.local else "")
    return (
        f"{decl.path}:{decl.line}: {modifier}{decl.keyword} {decl.source} "
        f"(module {decl.module}, today `{decl.full}`, under the prefix `{decl.future_name}`)"
    )


def report(
    result: Result,
    rows: list[Row],
    roots: list[Path],
    quiet: bool,
    strict: bool,
    baseline_path: Path,
    digest_problem: str | None,
) -> int:
    by_key = {row.key: row for row in rows}
    baselined_count = sum(
        1 for decl in result.violations if (decl.module, decl.full) in by_key
    )
    unbaselined = len(result.violations) - baselined_count

    if not quiet:
        print("check-names: roots " + ", ".join(str(root) for root in roots))
        print(
            f"  {result.files} .wiz file(s), {result.declarations} declaration(s); "
            f"baseline {baseline_path} ({len(rows)} row(s))"
        )
        print(
            f"  outside the module prefix: {len(result.violations)} "
            f"({baselined_count} baselined, {unbaselined} unbaselined)"
        )
        for decl in result.violations:
            row = by_key.get((decl.module, decl.full))
            if row is not None and not strict:
                continue  # the row is the exemption; the summary counts it
            tag = f"legacy ({row.reason})" if row else "unbaselined"
            print(f"  [{tag}] {describe(decl)}")
        if result.missing and not strict:
            print(
                f"  {len(result.missing)} declaration(s) have no baseline row "
                "(regenerate legacy-names.tsv; the default prefix would move them)"
            )
        if strict and result.missing:
            for decl in result.missing:
                print(f"  [missing row] {describe(decl)}")
    else:
        print(
            f"check-names: {result.files} file(s), {result.declarations} declaration(s), "
            f"{len(rows)} baseline row(s), {len(result.violations)} outside the prefix "
            f"({unbaselined} unbaselined), {len(result.missing)} without a row"
        )

    if result.stale:
        print(f"baseline: {len(result.stale)} stale row(s):", file=sys.stderr)
        for row in result.stale:
            print(
                f"  {row.module}.{row.name} ({row.path}:{row.line}) matches no declaration; "
                "remove the row (or restore the name)",
                file=sys.stderr,
            )

    if digest_problem:
        print(f"cache digest: {digest_problem}", file=sys.stderr)

    problems = len(result.stale) + (1 if digest_problem else 0)
    if strict:
        problems += len(result.violations) + len(result.missing)
    elif quiet:
        problems += len(result.missing)

    if problems:
        if strict:
            detail = (
                f"strict: {len(result.violations)} declaration(s) outside the module "
                f"prefix, {len(result.missing)} without a row, {len(result.stale)} stale row(s)"
            )
        else:
            detail = (
                f"{len(result.missing)} declaration(s) without a row, "
                f"{len(result.stale)} stale row(s)"
            )
            if digest_problem:
                detail += ", digest mismatch"
        print(f"check-names: FAIL ({detail})", file=sys.stderr)
        return 1

    print(
        "check-names: clean "
        f"({result.declarations} declaration(s), {len(result.violations)} "
        f"reported outside the prefix, {baselined_count} baselined, "
        f"{len(result.missing)} without a row)"
    )
    return 0


# --- self-test ---------------------------------------------------------------

def write_baseline(path: Path, rows: list[tuple[str, str, str, str, int] | str]) -> None:
    """Write a fixture baseline.  A `str` is written literally, for malformed cases."""
    lines = []
    for row in rows:
        if isinstance(row, str):
            lines.append(row)
        else:
            lines.append("\t".join(str(field) for field in row))
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def analyse_case(name: str, baseline: list[tuple[str, str, str, str, int] | str] | None) -> tuple[Result, Path, list[Row]]:
    """Scan one fixture and load a temporary baseline for it."""
    case = FIXTURES / name
    scan = collect([case], FIXTURES)
    with tempfile.TemporaryDirectory() as td:
        path = Path(td) / "legacy-names.tsv"
        write_baseline(path, baseline or [])
        rows = load_baseline(path)
    return evaluate(scan.decls, rows), case, rows


def run_cli_io(argv: list[str]) -> tuple[int, str, str]:
    """Run `main` with stdout/stderr captured; for the self-test's exit codes."""
    import contextlib
    import io

    out, err = io.StringIO(), io.StringIO()
    with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
        try:
            code = main(argv)
        except SystemExit as exc:  # argparse errors
            code = int(exc.code or 0)
    return code, out.getvalue(), err.getvalue()


def run_cli(argv: list[str]) -> int:
    return run_cli_io(argv)[0]


def self_test() -> int:
    failures: list[str] = []

    # 1. A name under its prefix: module Thing, `def Thing.f`, with its row.
    under_row = ("Thing", "Thing.f", "module-prefixed", "under/Thing.wiz", 5)
    result, case, _ = analyse_case("under", [under_row])
    if result.violations or result.missing:
        failures.append(
            f"under: expected no violation and no missing row, got "
            f"{len(result.violations)} violation(s), {len(result.missing)} missing"
        )

    # 2. A dotted name outside the prefix: module Thing, `def Other.f`, no row.
    result, case, rows = analyse_case("dotted", None)
    if len(result.violations) != 1 or result.baselined:
        failures.append(
            f"dotted: expected one unbaselined violation, got "
            f"{len(result.violations)} ({len(result.baselined)} baselined)"
        )
    if len(result.missing) != 1:
        failures.append(f"dotted: expected one declaration without a row, got {len(result.missing)}")
    code = run_cli(["--root", str(case), "--baseline", str(FIXTURES / "no-such.tsv"), "--quiet"])
    if code != 2:
        failures.append(f"dotted: a missing --baseline exited {code}, expected 2")
    with tempfile.TemporaryDirectory() as td:
        empty = Path(td) / "legacy-names.tsv"
        write_baseline(empty, [])
        code = run_cli(["--root", str(case), "--baseline", str(empty)])
        if code != 0:
            failures.append(
                f"dotted: normal mode exited {code} on an unbaselined declaration, expected 0"
            )
        code = run_cli(["--root", str(case), "--baseline", str(empty), "--quiet"])
        if code != 1:
            failures.append(
                f"dotted: --quiet exited {code} on an unbaselined declaration, expected 1"
            )

    # 3. `__root__` is exempt: no violation, and it needs no row.
    result, case, _ = analyse_case("escape", None)
    if result.violations or result.missing:
        failures.append(
            f"escape: expected `__root__` to be exempt, got {len(result.violations)} "
            f"violation(s), {len(result.missing)} missing"
        )

    # 4. A baseline row suppresses the warning: same declaration as `dotted`,
    #    now baselined.  Normal mode is clean; strict mode still fails.
    row = ("Thing", "Other.f", "other-dotted", "dotted/Thing.wiz", 1)
    result, case, rows = analyse_case("dotted", [row])
    if len(result.violations) != 1 or (("Thing", "Other.f") not in result.baselined):
        failures.append(
            f"row: expected the row to baseline the violation, got "
            f"{len(result.baselined)} baselined of {len(result.violations)}"
        )
    if result.missing or result.stale:
        failures.append(
            f"row: expected no missing or stale rows, got "
            f"{len(result.missing)} missing, {len(result.stale)} stale"
        )
    with tempfile.TemporaryDirectory() as td:
        path = Path(td) / "legacy-names.tsv"
        write_baseline(path, [row])
        code = run_cli(["--root", str(case), "--baseline", str(path), "--quiet"])
        if code != 0:
            failures.append(f"row: the baselined warning exited {code}, expected 0")
        code, out, _ = run_cli_io(["--root", str(case), "--baseline", str(path)])
        if code != 0 or "Other.f" in out:
            failures.append(
                "row: a baselined declaration was not suppressed "
                f"(exit {code}, printed={('Other.f' in out)})"
            )
        code, out, _ = run_cli_io(
            ["--root", str(case), "--baseline", str(path), "--strict-names", "--quiet"]
        )
        if code != 1:
            failures.append(f"row: --strict-names exited {code}, expected 1")

    # 5. A stale row fails: the row names a declaration that is not there.
    stale = ("Thing", "Gone.missing", "other-dotted", "dotted/Thing.wiz", 1)
    result, case, _ = analyse_case("dotted", [stale])
    if len(result.stale) != 1:
        failures.append(f"stale: expected one stale row, got {len(result.stale)}")
    with tempfile.TemporaryDirectory() as td:
        path = Path(td) / "legacy-names.tsv"
        write_baseline(path, [stale])
        code = run_cli(["--root", str(case), "--baseline", str(path), "--quiet"])
        if code != 1:
            failures.append(f"stale: a stale row exited {code}, expected 1")

    # 6. Malformed rows are exit 2: field count, reason class, duplicate.
    malformed = [
        ("three fields", "Thing\tOther.f\tother-dotted"),
        ("reason", "Thing\tOther.f\tnot-a-class\tdotted/Thing.wiz\t1"),
        (
            "duplicate",
            [
                ("Thing", "Other.f", "other-dotted", "dotted/Thing.wiz", 1),
                ("Thing", "Other.f", "other-dotted", "dotted/Thing.wiz", 1),
            ],
        ),
    ]
    for label, rows in malformed:
        with tempfile.TemporaryDirectory() as td:
            path = Path(td) / "legacy-names.tsv"
            write_baseline(path, rows if isinstance(rows, list) else [rows])
            code = run_cli(["--root", str(FIXTURES / "dotted"), "--baseline", str(path), "--quiet"])
            if code != 2:
                failures.append(f"malformed ({label}): exited {code}, expected 2")

    # 7. The digest covers names and reasons, not the review-only path and line.
    base_rows = [Row("Thing", "Other.f", "other-dotted", "dotted/Thing.wiz", 1)]
    moved = [Row("Thing", "Other.f", "other-dotted", "dotted/Thing.wiz", 99)]
    renamed = [Row("Thing", "Other.g", "other-dotted", "dotted/Thing.wiz", 1)]
    if baseline_digest(base_rows) != baseline_digest(moved):
        failures.append("digest: a line-number change changed the semantic digest")
    if baseline_digest(base_rows) == baseline_digest(renamed):
        failures.append("digest: a name change did not change the semantic digest")

    # 8. The repository's baseline must exist, parse, and match the Lean constant.
    try:
        real = load_baseline(DEFAULT_BASELINE)
    except BaselineError as exc:
        failures.append(str(exc))
    else:
        if not real:
            failures.append(f"{DEFAULT_BASELINE}: has no rows")
        recorded = lean_digest(LEGACY_MODULE)
        if recorded is not None and recorded != baseline_digest(real):
            failures.append(
                f"{LEGACY_MODULE.relative_to(REPO)} records {recorded or '(empty)'}, "
                f"but the baseline is {baseline_digest(real)}"
            )

    if failures:
        for failure in failures:
            print(f"self-test FAIL: {failure}", file=sys.stderr)
        return 1
    print(
        "check-names self-test: ok (8 cases: name under its prefix, dotted name outside it, "
        "__root__ escape, baseline row suppresses the report, stale row, three malformed "
        "baselines, the semantic digest, the repository baseline)"
    )
    return 0


def main(argv: list[str] | None = None) -> int:
    repo = Path(__file__).resolve().parent.parent
    parser = argparse.ArgumentParser(
        description="Check declarations against the namespace compatibility allowlist."
    )
    parser.add_argument(
        "--root", type=Path, action="append", metavar="DIR",
        help="module root to scan (repeatable; default: lib, scry/src, scry/gen, tower, web, selfhost)",
    )
    parser.add_argument("--baseline", type=Path, metavar="FILE",
                        help="baseline file (default: legacy-names.tsv)")
    parser.add_argument("--quiet", action="store_true",
                        help="summary only; the CI gate")
    parser.add_argument("--strict-names", action="store_true",
                        help="fail on every declaration outside its module prefix")
    parser.add_argument("--self-test", action="store_true",
                        help="run the fixtures and baseline cases instead of reading the tree")
    args = parser.parse_args(argv)

    if args.self_test:
        return self_test()

    roots = [root.resolve() for root in (args.root or default_roots(repo))]
    for root in roots:
        if not root.is_dir():
            print(f"check-names: --root {root} is not a directory", file=sys.stderr)
            return 2

    baseline_path = (args.baseline or DEFAULT_BASELINE).resolve()
    if not baseline_path.is_file():
        print(f"check-names: baseline {baseline_path} is not a file", file=sys.stderr)
        return 2
    try:
        rows = load_baseline(baseline_path)
    except BaselineError as exc:
        print(f"check-names: {exc}", file=sys.stderr)
        return exc.code

    try:
        scan = collect(roots, repo)
    except OSError as exc:
        print(f"check-names: {exc}", file=sys.stderr)
        return 2
    if not scan.files:
        print(
            "check-names: no .wiz files found under " + ", ".join(str(root) for root in roots),
            file=sys.stderr,
        )
        return 2

    digest_problem: str | None = None
    if args.baseline is None:
        try:
            recorded = lean_digest(LEGACY_MODULE)
        except BaselineError as exc:
            print(f"check-names: {exc}", file=sys.stderr)
            return exc.code
        if recorded is not None:
            actual = baseline_digest(rows)
            if recorded != actual:
                digest_problem = (
                    f"{LEGACY_MODULE.relative_to(repo)} records {recorded or '(empty)'}, "
                    f"but {baseline_path.name} is {actual}; run "
                    "scripts/gen-legacy-names.py --update-digest"
                )

    result = evaluate(scan.decls, rows)
    return report(
        result, rows, roots, args.quiet, args.strict_names, baseline_path, digest_problem
    )


if __name__ == "__main__":
    sys.exit(main())
