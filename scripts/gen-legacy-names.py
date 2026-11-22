#!/usr/bin/env python3
"""Generate the namespace compatibility allowlist, `legacy-names.tsv`.

Wiz's default namespace will be the module path (`lib/Scry/CstStore.wiz` is
module `Scry.CstStore`, so `def lineIndexGo` becomes `Scry.CstStore.lineIndexGo`).
Stage 0 makes that change safe without a flag day: every declaration that exists
today gets one row in `legacy-names.tsv`, and the row says "this declaration
keeps its current absolute name until its migration batch deletes the row".
The file is the input to `scripts/check-names.py` and, from stage 3 on, to the
elaborator; its digest is mixed into the cache key (`Wiz/LegacyNames.lean`,
`Wiz/Cache.lean`, `Wiz/Frontend/Frontend.lean`).

The row format is one tab-separated line per declaration:

    module  the module name (path under its root, `/` -> `.`, no suffix)
    name    the absolute name the declaration has today, `__root__.` removed
    reason  the plan's class: module-prefixed, first-prefixed, leaf-prefixed,
            other-dotted, principal, or bare
    file    the repository-relative source path
    line    1-based line of the declaration

Rows are sorted by `(module, name)`, and the file is regenerated from the source,
so it is deterministic: two runs on the same tree produce the same bytes.

A `__root__.` declaration is not emitted: it already has the true-global name it
will keep, so it needs no compatibility row (and the plan's count predates
`__root__`).  A duplicate `(module, name)` inside one file is an error: the tree
cannot elaborate two declarations of one name in one module.  The one duplicate
module name in the tree (`Main` in `tower/Main.wiz` and `selfhost/Main.wiz`) is
two packages that never load together; both rows are emitted (same key, same
reason, different file), exactly as the plan records.

Roots: by default the six library/tool trees the plan's stage-0 gate names:
`lib/`, `scry/src/`, `scry/gen/`, `tower/`, `web/` and `selfhost/`.  `examples/`
and `drafts/` are out of scope (the plan: `examples/` is stage 9, `drafts/` is
not migrated); add one with `--root DIR`.  The module root for `scry/src` is
`scry/src`, so `scry/src/Scry/CstStore.wiz` is `Scry.CstStore`.

Usage
  scripts/gen-legacy-names.py                     write legacy-names.tsv
  scripts/gen-legacy-names.py --quiet             write it, print the summary only
  scripts/gen-legacy-names.py --check             fail if the file is stale
  scripts/gen-legacy-names.py --root DIR          scan another module root (repeatable)
  scripts/gen-legacy-names.py --out FILE          write somewhere else
  scripts/gen-legacy-names.py --print-digest      print the SHA-256 only
  scripts/gen-legacy-names.py --update-digest     update Wiz/LegacyNames.lean's digest

Exit status: 0 ok, 1 a duplicate declaration or a stale `--check`, 2 usage or
I/O error.

CI (add to the `docs_style` job's run step in `.github/workflows/ci.yml`):
  python3 scripts/check-names.py --self-test
  python3 scripts/check-names.py --quiet
The `--quiet` run fails on an unbaselined declaration and on a stale row (and on
a cache-digest mismatch), so a new declaration or a removed one cannot slip past
the baseline.  `--strict-names` is the migration-completeness gate; it is
expected to fail until stage 6.  `gen-legacy-names.py --check` is a local check
that the file is byte-identical to a fresh generation (line numbers included); it
need not run in CI.
"""

from __future__ import annotations

import argparse
import hashlib
import re
import sys
from collections import Counter
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
    rooted: bool = False  # inside `namespace __root__`: an explicitly global name

    @property
    def escaped(self) -> bool:
        return self.source == ROOT_ESCAPE or self.source.startswith(ROOT_ESCAPE + ".")

    @property
    def explicit_root(self) -> bool:
        """Written global: a `__root__.` name, or a `namespace __root__` body."""
        return self.escaped or self.rooted

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
        return self.full if self.explicit_root else self.module + "." + self.full


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


def apply_namespace_path(stack: list[tuple[str, str | None, bool, bool]], name: str) -> tuple[str, bool]:
    """The absolute path and rootedness after opening `name` on `stack`.

    A leading `__root__` (Lean's `_root_.`) resets the path and makes the block
    explicitly global; otherwise the name is relative to the enclosing namespace
    (and inherits the enclosing block's rootedness).
    """
    if name == ROOT_ESCAPE:
        return "", True
    if name.startswith(ROOT_ESCAPE + "."):
        return name[len(ROOT_ESCAPE) + 1 :], True
    base = current_namespace(stack)
    return ((base + "." + name) if base else name), enclosing_rooted(stack)


def enclosing_rooted(stack: list[tuple[str, str | None, bool, bool]]) -> bool:
    """Whether the innermost enclosing block was opened under `namespace __root__`."""
    return any(rooted for _, _, _, rooted in stack)


def current_namespace(stack: list[tuple[str, str | None, bool, bool]]) -> str:
    """The namespace path of the innermost open namespace on `stack`."""
    for kind, name, _, _ in reversed(stack):
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

    # ("namespace"|"section"|"mutual", resolved namespace name, private, rooted)
    stack: list[tuple[str, str | None, bool, bool]] = []
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
                # `end __root__` closes a `namespace __root__` block; otherwise `end Foo`
                # closes the nearest matching namespace if there is one, else the
                # innermost block.
                if name == ROOT_ESCAPE and stack[-1][0] == "namespace" and stack[-1][1] == "":
                    stack.pop()
                    continue
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
            if kind == "namespace" and name:
                resolved, rooted = apply_namespace_path(stack, name)
            else:
                resolved, rooted = None, enclosing_rooted(stack)
            stack.append((kind, resolved, private, rooted))
            continue

        if name is None or name == "_":
            continue
        in_private_mutual = any(
            block_kind == "mutual" and block_private
            for block_kind, _, block_private, _ in stack
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
                rooted=enclosing_rooted(stack),
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


def reason_class(decl: Decl) -> str:
    """The plan's reason class for keeping `decl` at its current name."""
    full = decl.full
    module = decl.module
    parts = module.split(".")
    leaf = parts[-1]

    if full == module or full == leaf:
        return "principal"
    if full.startswith(module + "."):
        return "module-prefixed"
    if len(parts) > 1 and full.startswith(parts[0] + "."):
        return "first-prefixed"
    if len(parts) > 1 and full.startswith(leaf + "."):
        return "leaf-prefixed"
    if "." in full:
        return "other-dotted"
    return "bare"


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
DEFAULT_OUT = REPO / "legacy-names.tsv"
LEGACY_MODULE = REPO / "Wiz" / "LegacyNames.lean"
HEADER = "# module\tname\treason\tfile\tline"
DIGEST_RE = re.compile(r'(def digest : String :=\s*")[0-9a-f]*(")')


def rows_for(roots: list[Path], repo: Path) -> tuple[list[tuple[str, str, str, str, int]], dict[str, int], list[str]]:
    """All baseline rows, per-root counts, and duplicate errors."""
    rows: list[tuple[str, str, str, str, int]] = []
    per_root: dict[str, int] = {}
    errors: list[str] = []
    seen: dict[tuple[str, str], tuple[str, str, int, str]] = {}

    for root in roots:
        scan = collect([root], repo)
        count = 0
        for decl in scan.decls:
            if decl.explicit_root:
                continue
            key = (decl.module, decl.full)
            reason = reason_class(decl)
            if key in seen:
                first_path, first_reason, first_line, _ = seen[key]
                if decl.path == first_path or reason != first_reason:
                    errors.append(
                        f"duplicate declaration {decl.module}.{decl.full}: "
                        f"{first_path}:{first_line} and {decl.path}:{decl.line}"
                    )
                    continue
                # Two packages with the same module name: both keep the same
                # absolute name, so both rows are legitimate (see the docstring).
            else:
                seen[key] = (decl.path, reason, decl.line, decl.path)
            rows.append(
                (decl.module, decl.full, reason_class(decl), decl.path, decl.line)
            )
            count += 1
        per_root[str(root.relative_to(repo)) if root.is_relative_to(repo) else str(root)] = count

    rows.sort(key=lambda row: (row[0], row[1]))
    return rows, per_root, errors


def render(rows: list[tuple[str, str, str, str, int]]) -> bytes:
    lines = [HEADER]
    for module, name, reason, path, line in rows:
        lines.append(f"{module}\t{name}\t{reason}\t{path}\t{line}")
    return ("\n".join(lines) + "\n").encode("utf-8")


def digest_of(rows: list[tuple[str, str, str, str, int]]) -> str:
    """SHA-256 of the allowlist's *meaning*: the sorted `(module, name, reason)` set.

    The file also carries the source path and line for review, but a line shift
    must not invalidate every cache entry: the digest covers names and reason
    classes only.  (The same function is in `scripts/check-names.py`.)
    """
    lines = sorted(f"{module}\t{name}\t{reason}" for module, name, reason, _, _ in rows)
    return hashlib.sha256(("\n".join(lines) + "\n").encode("utf-8")).hexdigest()


def summary(rows: list[tuple[str, str, str, str, int]], per_root: dict[str, int]) -> str:
    reasons = Counter(row[2] for row in rows)
    files = Counter(row[3] for row in rows)
    out = []
    for root, count in per_root.items():
        out.append(f"  {root}: {count} declaration(s)")
    out.append(f"  {len(rows)} row(s) in {len(files)} file(s)")
    for reason in REASON_CLASSES:
        if reasons[reason]:
            out.append(f"  {reason}: {reasons[reason]}")
    return "\n".join(out)


def update_digest(path: Path, digest: str) -> bool:
    """Rewrite the digest constant in `Wiz/LegacyNames.lean`; True if it changed."""
    try:
        text = path.read_text(encoding="utf-8")
    except OSError as exc:
        print(f"gen-legacy-names: cannot read {path}: {exc}", file=sys.stderr)
        raise SystemExit(2)
    new, count = DIGEST_RE.subn(lambda m: m.group(1) + digest + m.group(2), text, count=1)
    if count != 1:
        print(
            f"gen-legacy-names: {path} has no `def digest : String := \"...\"` line",
            file=sys.stderr,
        )
        raise SystemExit(2)
    if new != text:
        path.write_text(new, encoding="utf-8")
        return True
    return False


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Generate the namespace compatibility allowlist (legacy-names.tsv)."
    )
    parser.add_argument(
        "--root", type=Path, action="append", metavar="DIR",
        help="module root to scan (repeatable; default: lib, scry/src, scry/gen, tower, web, selfhost)",
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT, metavar="FILE",
                        help="output file (default: legacy-names.tsv)")
    parser.add_argument("--quiet", action="store_true", help="print the summary only")
    parser.add_argument("--check", action="store_true",
                        help="do not write; fail if the file differs from the tree")
    parser.add_argument("--print-digest", action="store_true",
                        help="print the SHA-256 of the generated bytes and exit")
    parser.add_argument("--update-digest", action="store_true",
                        help="also update the digest in Wiz/LegacyNames.lean")
    args = parser.parse_args(argv)

    if args.root:
        roots = [root.resolve() for root in args.root]
    else:
        roots = default_roots(REPO)

    for root in roots:
        if not root.is_dir():
            print(f"gen-legacy-names: --root {root} is not a directory", file=sys.stderr)
            return 2

    rows, per_root, errors = rows_for(roots, REPO)
    if errors:
        for error in errors:
            print(f"gen-legacy-names: {error}", file=sys.stderr)
        return 1

    data = render(rows)
    digest = digest_of(rows)

    if args.print_digest:
        print(digest)
        return 0

    out = args.out.resolve()
    if args.check:
        try:
            current = out.read_bytes()
        except OSError as exc:
            print(f"gen-legacy-names: cannot read {out}: {exc}", file=sys.stderr)
            return 1
        if current != data:
            print(
                f"gen-legacy-names: {out} is stale; run scripts/gen-legacy-names.py",
                file=sys.stderr,
            )
            return 1
        if not args.quiet:
            print(f"gen-legacy-names: {out} is up to date ({len(rows)} rows, sha256 {digest})")
        return 0

    try:
        out.write_bytes(data)
    except OSError as exc:
        print(f"gen-legacy-names: cannot write {out}: {exc}", file=sys.stderr)
        return 2

    if not args.quiet:
        print(f"gen-legacy-names: {out.relative_to(REPO) if out.is_relative_to(REPO) else out}")
    print(summary(rows, per_root))
    print(f"  sha256 {digest}")

    if args.update_digest:
        changed = update_digest(LEGACY_MODULE, digest)
        if not args.quiet:
            print(
                f"  Wiz/LegacyNames.lean: digest {'updated' if changed else 'already current'}"
            )
    return 0


if __name__ == "__main__":
    sys.exit(main())
