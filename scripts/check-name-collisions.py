#!/usr/bin/env python3
"""Syntactic name-collision check for Wiz's coming module namespaces.

Wiz has no per-module namespaces yet: every top-level declaration is a name in one
project-wide scope, so two modules that both declare `lineIndexGo` make the driver
unloadable ("declared by both module A and module B").  The namespaces Wiz is about
to get will make each file a module and prefix its declarations with the module
path (`lib/Scry/CstStore.wiz` -> `Scry.CstStore`, so `def lineIndexGo` becomes
`Scry.CstStore.lineIndexGo`).  This checker models both worlds:

  global     Declarations that would still be in the same scope *today*, when nothing
             is namespaced: two top-level `def x` in any two modules, two `def M.x`
             in any two modules, or a `__root__.x` beside any other `x`.  This is
             the class that has broken the driver (Msg vs Session, Scry.lineIndexGo
             in CstStore and TaintCmd).  It fails the check (exit 1).

  migration  Names already written dotted (`def Scry.lineIndexGo`).  Under the model
             such a name is *not* an escape hatch: it becomes
             `Scry.CstStore.Scry.lineIndexGo`, so the file needs `__root__.` or a
             rename when namespaces land.  Reported and counted, but does not fail
             the check yet (the tree has many).

The model, in full
------------------
* Every `.wiz` file below a `--root` is a module; the module name is the path
  relative to that root without `.wiz`, with `/` -> `.`.
* A top-level declaration is module-scoped by default in the coming model.  The
  `global` class deliberately does *not* apply that prefix: it reports what is
  global *today*, which is what the compiler sees before namespaces land.
* `__root__.foo` escapes to the global scope (Lean's `_root_.foo`).  It is reported
  in `global` as the name `foo`, beside any other declaration of `foo`; it is not
  a `migration` name.
* A dotted name (`def Scry.x`) is prefixed like any other name in the coming model,
  which is the `migration` finding.  It is *also* still a global name today, so two
  modules that write the same dotted name are a `global` collision.
* `private` declarations are already per module (the elaborator gives them a
  `_private.M...` kernel name), and a named `local instance` is found only in its
  module, so two modules' `private x` / `local instance i` do not collide.  Two in
  the same module and namespace do.
* The `global` class is deliberately project-wide and does not follow `import`
  lines: under "nothing is namespaced" any two modules are in one scope, so two
  independent entry-point modules that both define `main` are reported too.  That
  is the conservative model; a collision is certain only when one module imports
  the other, which the report leaves to the reader.

Recognised forms (one declaration per line, at column 0, as Wiz's layout requires)
-----------------------------------------------------------------------------------
  def, def with equations, partial def, mutual (defs and/or inductives), inductive,
  coinductive, structure, class, instance (named only; anonymous instances have no
  source name), axiom, extern, foreign_type, c_struct, glue.
  Wrapped by any of the modifiers `private`, `sealed`, `local`, `partial` (including
  `partial (default := w)`).

  namespace NAME ... end (also nested; declarations inside a `namespace` body are
  scoped by the namespace path), section ... end (transparent), open (ignored: it
  declares nothing).  A `namespace`/`section`/`mutual` block must end with `end`;
  the checker keeps a stack, so a declaration inside either body is not missed.

Ignored (documented non-goals)
------------------------------
  Constructors and projections (`T.c`, `S.f`, `S.mk`) are not enumerated: their
  compiler names are qualified by the type name, which *is* checked.  An explicit
  dotted declaration that happens to equal a generated constructor name is not
  detected.
  `syntax`, `notation`, `macro_rules`, `attribute`, `deriving`, `import`, `open`,
  `builtin`, `export`, `link_c`, `#check`/`#eval` and the other directives declare
  no source name (or only a grammar/tactic registration) and are ignored.
  Declarations indented inside a block are not top-level declarations in Wiz's
  layout and are not recognised.  Comments (`--`, `/- ... -/`, nested) and
  double-quoted string literals are blanked before scanning, so their contents do
  not create false declarations.

Usage
  scripts/check-name-collisions.py                 check lib/, scry/src/, selfhost/
  scripts/check-name-collisions.py --root DIR      check one module root (repeatable)
  scripts/check-name-collisions.py --quiet         summary only (collisions still shown)
  scripts/check-name-collisions.py --self-test     run the fixtures below

Exit status: 0 no `global` collisions (migration findings are allowed), 1 `global`
collisions or a failing self-test, 2 usage or I/O error.

CI: add these two lines to the `docs_style` job's run step in
.github/workflows/ci.yml (after the existing check-doc-links lines):
  python3 scripts/check-name-collisions.py --self-test
  python3 scripts/check-name-collisions.py --quiet
"""

from __future__ import annotations

import argparse
import re
import sys
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
# Forms that are not declarations but change the scope we are in.
BLOCK_KEYWORDS = ("namespace", "section", "mutual")

SKIP_DIRS = {".git", ".lake", "node_modules", "__pycache__", "build", "dist", "drafts"}

MODIFIER_RE = re.compile(r"(private|sealed|local|partial)\b")
KEYWORD_RE = re.compile(r"(%s)\b" % "|".join(DECL_KEYWORDS + BLOCK_KEYWORDS))
NAME_RE = re.compile(r"([^\s:(\[\]]+)")
NAMESPACE_RE = re.compile(r"namespace\s+(\S+)")
SECTION_RE = re.compile(r"section\b(?:\s+\S+)?")
END_RE = re.compile(r"end\b(?:\s+(\S+))?")
OPEN_RE = re.compile(r"open\b")


@dataclass(frozen=True)
class Decl:
    """One declaration of a source name."""

    keyword: str
    source: str  # exactly as written: `x`, `Scry.x`, `__root__.x`
    module: str
    namespace: str  # explicit `namespace` path, "" at top level
    path: str  # display path
    line: int
    private: bool
    local: bool

    @property
    def escaped(self) -> bool:
        return self.source.startswith("__root__.")

    @property
    def bare(self) -> str:
        return self.source[len("__root__.") :] if self.escaped else self.source

    @property
    def scope(self) -> str:
        """The effective *today* scope: explicit namespace, or the module if local."""
        if self.escaped:
            return ""
        if self.private or self.local:
            suffix = ("." + self.namespace) if self.namespace else ""
            return "module-local:" + self.module + suffix
        return self.namespace

    @property
    def key(self) -> tuple[str, str]:
        return (self.scope, self.bare)

    @property
    def migration(self) -> bool:
        """A dotted name that the module prefix would re-prefix."""
        return not self.escaped and "." in self.source

    @property
    def future_name(self) -> str:
        prefix = self.module + (("." + self.namespace) if self.namespace else "")
        return self.source if self.escaped else prefix + "." + self.source


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
        # A modifier must be followed by another modifier or a command keyword.
        nxt = KEYWORD_RE.match(line, pos)
        if nxt:
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
    False)` for `end`, and `("open", None, False, False)` for `open`.  `None` means
    no command starts here.
    """
    if not line or line[0] in " \t":
        return None

    # Blocks and directives are not declarations; handle them before modifiers.
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
        # `c_struct ["struct t"] [(header := "h")] T where ...`
        # Strings were blanked to spaces, so only the optional (...) remains.
        pos2 = skip_space(rest, 0)
        if pos2 < len(rest) and rest[pos2] == "(":
            pos2 = skip_space(rest, skip_balanced(rest, pos2))
        return (keyword, first_name(rest[pos2:]), private, local)

    return (keyword, first_name(rest), private, local)


def scan_file(path: Path, module: str, display: str) -> list[Decl]:
    try:
        text = path.read_text(encoding="utf-8-sig")
    except (OSError, UnicodeDecodeError) as exc:
        print(f"check-name-collisions: cannot read {display}: {exc}", file=sys.stderr)
        raise SystemExit(2)
    lines = blank_comments_and_strings(text).splitlines()

    # Stack of ("namespace"|"section"|"mutual", name, private).  A namespace name may
    # be dotted; `namespace A.B` pushes the two components as one name and joins them
    # into the namespace path.  `private` on a `mutual` block applies to its members.
    stack: list[tuple[str, str | None, bool]] = []
    decls: list[Decl] = []

    def namespace_path() -> str:
        parts: list[str] = []
        for kind, name, _ in stack:
            if kind == "namespace" and name:
                parts.append(name)
        return ".".join(parts)

    for lineno, line in enumerate(lines, start=1):
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
            stack.append((kind, name if kind == "namespace" else None, private))
            continue

        if name is None or name == "_":
            continue
        # `private mutual ... end` makes every member private to the module.
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
                namespace=namespace_path(),
                path=display,
                line=lineno,
                private=private,
                local=local,
            )
        )

    return decls


def module_root(hit: Path, roots: list[Path]) -> tuple[Path, str]:
    """The root that names `hit`, and its module path."""
    for root in roots:
        try:
            rel = hit.relative_to(root)
        except ValueError:
            continue
        return root, ".".join(rel.with_suffix("").parts)
    raise AssertionError(f"{hit} is not below any root")


def collect(roots: list[Path]) -> tuple[list[Decl], list[Path]]:
    files: list[Path] = []
    seen: set[Path] = set()
    for root in roots:
        for hit in sorted(root.rglob("*.wiz")):
            if any(part in SKIP_DIRS for part in hit.relative_to(root).parts):
                continue
            resolved = hit.resolve()
            if resolved in seen:
                continue
            seen.add(resolved)
            files.append(hit)

    decls: list[Decl] = []
    for hit in files:
        _, module = module_root(hit, roots)
        decls.extend(scan_file(hit, module, display(hit)))
    return decls, files


def group_collisions(decls: list[Decl]) -> dict[tuple[str, str], list[Decl]]:
    groups: dict[tuple[str, str], list[Decl]] = {}
    for decl in decls:
        groups.setdefault(decl.key, []).append(decl)
    return {key: found for key, found in groups.items() if len(found) > 1}


def describe_scope(scope: str) -> str:
    if scope == "":
        return "the global scope"
    if scope.startswith("module-local:"):
        return "the module-local scope of " + scope[len("module-local:") :]
    return f"namespace {scope}"


def display(path: Path) -> str:
    """`path` relative to the working directory when possible, for readable output."""
    try:
        return str(path.relative_to(Path.cwd()))
    except ValueError:
        return str(path)


def report(decls: list[Decl], files: list[Path], roots: list[Path], quiet: bool) -> int:
    collisions = group_collisions(decls)
    migrations = [decl for decl in decls if decl.migration]
    migration_files: dict[str, int] = {}
    for decl in migrations:
        migration_files[decl.path] = migration_files.get(decl.path, 0) + 1
    distinct = {decl.bare for decl in migrations}

    if not quiet:
        print("check-name-collisions: roots " + ", ".join(display(r) for r in roots))
        print(f"  {len(files)} .wiz file(s), {len(decls)} declaration(s)")

    if collisions:
        print(
            f"global: {len(collisions)} collision group(s), "
            f"{sum(len(v) for v in collisions.values())} declaration(s)"
        )
        # A collision is the failing class, so name the group even under --quiet.
        for (scope, name), found in sorted(collisions.items(), key=lambda kv: kv[0]):
            print(f"  '{name}' in {describe_scope(scope)}, declared {len(found)} time(s):")
            for decl in sorted(found, key=lambda d: (d.path, d.line)):
                modifier = "private " if decl.private else ("local " if decl.local else "")
                print(
                    f"    {decl.path}:{decl.line}: {modifier}{decl.keyword} "
                    f"{decl.source} (module {decl.module})"
                )
            print(
                "    fix: rename one of them; if the name really is global, spell it "
                f"`__root__.{name}` once namespaces land."
            )
    else:
        print("global: 0 collisions")

    if migrations:
        print(
            f"migration: {len(migrations)} dotted declaration(s) "
            f"({len(distinct)} distinct name(s)) in {len(migration_files)} file(s)"
        )
        if not quiet:
            for path, count in sorted(migration_files.items(), key=lambda kv: (-kv[1], kv[0])):
                print(f"  {path}: {count}")
            if migrations:
                sample = migrations[0]
                print(
                    f"  e.g. {sample.path}:{sample.line} `{sample.source}` would become "
                    f"`{sample.future_name}`"
                )
            print(
                "  These are names written dotted (`def Scry.x`); the namespace model would "
                "put them at module-prefix + source name, so each needs `__root__.x` or a "
                "rename when namespaces land."
            )
    else:
        print("migration: 0 dotted declarations")

    if collisions:
        print(
            f"check-name-collisions: FAIL "
            f"({len(collisions)} global collision group(s), "
            f"{len(migrations)} migration declaration(s) not failing)",
            file=sys.stderr,
        )
        return 1
    print(f"check-name-collisions: clean ({len(migrations)} migration declaration(s) reported)")
    return 0


FIXTURES = Path(__file__).resolve().parent / "fixtures" / "name-collisions"

# (case directory, expected global collision groups keyed by (scope, name),
#  expected migration count)
SELF_TEST_CASES: tuple[tuple[str, dict[tuple[str, str], int], int], ...] = (
    # Two modules declare the same top-level name: the pair that broke the driver.
    ("collide", {("", "shared"): 2}, 0),
    # `__root__.same` escapes into the global scope, beside `def same` elsewhere.
    ("root_escape", {("", "same"): 2}, 0),
    # A dotted name is not an escape hatch: it is one global name today (so the pair
    # collides) and it migrates to Module.Module.name.
    ("migration", {("", "Thing.name"): 2}, 2),
    # The member of a `mutual` block is seen, and `end` closes the mutual block and
    # not its surrounding namespace; the member and the later def stay in Mut.
    ("mutual", {("Mut", "loop"): 2}, 0),
    # Namespace bodies separate names; only the duplicate inside one namespace collides.
    ("namespace", {("A", "x"): 2}, 0),
    # Clean, and a private name in two modules is not a collision.
    ("clean", {}, 0),
)


def analyse_case(case: Path) -> tuple[dict[tuple[str, str], int], int]:
    decls, _ = collect([case])
    collisions = group_collisions(decls)
    groups = {key: len(found) for key, found in collisions.items()}
    migrations = sum(1 for decl in decls if decl.migration)
    return groups, migrations


def self_test() -> int:
    failures: list[str] = []
    for case_name, expected_groups, expected_migrations in SELF_TEST_CASES:
        case = FIXTURES / case_name
        if not case.is_dir():
            failures.append(f"{case_name}: fixture directory {case} is missing")
            continue
        groups, migrations = analyse_case(case)
        if groups != expected_groups:
            failures.append(f"{case_name}: expected global groups {expected_groups}, got {groups}")
        if migrations != expected_migrations:
            failures.append(
                f"{case_name}: expected {expected_migrations} migration declaration(s), "
                f"got {migrations}"
            )
    if failures:
        for failure in failures:
            print(f"self-test FAIL: {failure}", file=sys.stderr)
        return 1
    print(
        f"check-name-collisions self-test: ok ({len(SELF_TEST_CASES)} fixtures: "
        "colliding pair, __root__ escape, dotted migration, mutual block, namespace body, clean)"
    )
    return 0


def default_roots(repo: Path) -> list[Path]:
    candidates = [repo / "lib", repo / "scry" / "src", repo / "selfhost"]
    present = [root for root in candidates if root.is_dir()]
    return present or [repo]


def main(argv: list[str] | None = None) -> int:
    repo = Path(__file__).resolve().parent.parent
    parser = argparse.ArgumentParser(
        description="Check Wiz sources for global name collisions and namespace-migration names."
    )
    parser.add_argument(
        "--root",
        type=Path,
        action="append",
        metavar="DIR",
        help="module root to scan (repeatable; default: lib, scry/src, selfhost)",
    )
    parser.add_argument(
        "--self-test",
        action="store_true",
        help="run the built-in fixtures instead of reading files",
    )
    parser.add_argument(
        "--quiet",
        action="store_true",
        help="print only the summary and the collision groups",
    )
    args = parser.parse_args(argv)

    if args.self_test:
        return self_test()

    roots = [root.resolve() for root in (args.root or default_roots(repo))]
    for root in roots:
        if not root.is_dir():
            print(f"check-name-collisions: --root {root} is not a directory", file=sys.stderr)
            return 2

    decls, files = collect(roots)
    if not files:
        print(
            "check-name-collisions: no .wiz files found under "
            + ", ".join(display(root) for root in roots),
            file=sys.stderr,
        )
        return 2
    return report(decls, files, roots, args.quiet)


if __name__ == "__main__":
    sys.exit(main())
