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
             in CstStore and TaintCmd).  It fails the check (exit 1), except for
             groups listed in the baseline (below).

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
  is the conservative model; `--reachable` is the narrower one (below).

Baseline (`.github/name-collisions-baseline.json`)
---------------------------------------------------
The baseline records the global groups that exist today but cannot break a run:
its entries are between modules with no import path (independent programs or
bootstrap reimplementations).  Each entry has:

  module   the primary module (a repository-relative `.wiz` path, in `modules`)
  name     the collision name
  modules  the exact sorted set of modules whose declarations collide
  scope    optional; the effective scope ("" for the global scope)
  reason   why this cannot be loaded in one run; name the pair
  owner    who owns the two modules
  expires  YYYY-MM-DD; an expired entry is an error

`--quiet` fails only on a group that is not in the baseline.  A baseline entry
whose group is gone is a stale-baseline error (remove the entry), and an expired
entry is an error (renew it with a new reason).  A group whose module set changes
does not match its old entry, so it fails as unbaselined and the old entry is stale.
A partial `--root` scan does not call an entry stale when one of its modules is
outside the scan, but a baseline module that no longer exists is stale.

`--reachable`
-------------
With `--reachable`, a global group is reported only if two of its declarations can
be loaded in one program: some module (a program root, a driver) imports both,
transitively.  This is the intersection of the modules' transitive importers, so
`CstStore`/`TaintCmd` (TaintCmd imports CstStore) remains, while two independent
entry points do not.  The graph is built from `import` lines in the scanned `.wiz`
files; a module outside the roots is not resolved, and a program the Lean host
assembles from a source list (`Wiz/Selfhost.lean`) is not in the graph.  If a module
name occurs under more than one root, every candidate is an edge (conservative).
The default project-wide check remains the backstop for those.  The baseline does
not apply in this mode (it documents the project-wide model): `--reachable` is the
stricter gate.

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
  scripts/check-name-collisions.py --reachable     only groups that share an importer
  scripts/check-name-collisions.py --quiet         summary; fail only unbaselined groups
  scripts/check-name-collisions.py --self-test     run the fixtures and baseline cases
  scripts/check-name-collisions.py --no-baseline   ignore the baseline (strict)
  scripts/check-name-collisions.py --baseline FILE use another baseline file

Exit status: 0 clean (migration and baselined groups are allowed), 1 unbaselined
global collisions, a stale or expired baseline entry, or a failing self-test;
2 usage, I/O or malformed-baseline error.

CI: add these two lines to the `docs_style` job's run step in
.github/workflows/ci.yml (after the existing check-doc-links lines):
  python3 scripts/check-name-collisions.py --self-test
  python3 scripts/check-name-collisions.py --quiet

The baseline makes the `--quiet` run green today (12 entries); a stale or expired
entry is still a failure.  A second, stricter job (recommended; no baseline, import
graph only) is the truthful co-loadable check and is 0 today:
  python3 scripts/check-name-collisions.py --reachable --quiet
"""

from __future__ import annotations

import argparse
import datetime as dt
import json
import re
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
DEFAULT_BASELINE = REPO / ".github" / "name-collisions-baseline.json"

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
IMPORT_RE = re.compile(r"^import\b\s+(\S+)")
DATE_RE = re.compile(r"\d{4}-\d{2}-\d{2}")


@dataclass(frozen=True)
class Decl:
    """One declaration of a source name."""

    keyword: str
    source: str  # exactly as written: `x`, `Scry.x`, `__root__.x`
    module: str  # module name relative to its --root
    namespace: str  # explicit `namespace` path, "" at top level
    path: str  # display path
    rel: str  # repository-relative path (the baseline's identity)
    line: int
    private: bool
    local: bool
    rooted: bool = False  # inside `namespace __root__`: an explicitly global name

    @property
    def escaped(self) -> bool:
        return self.source.startswith("__root__.")

    @property
    def explicit_root(self) -> bool:
        """Written global: a `__root__.` name, or a `namespace __root__` body."""
        return self.escaped or self.rooted

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
        return not self.explicit_root and "." in self.source

    @property
    def future_name(self) -> str:
        if self.explicit_root:
            return (self.namespace + "." + self.source) if self.namespace else self.source
        prefix = self.module + (("." + self.namespace) if self.namespace else "")
        return prefix + "." + self.source


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


def scan_file(path: Path, module: str, display: str, rel: str) -> tuple[list[Decl], list[str]]:
    try:
        text = path.read_text(encoding="utf-8-sig")
    except (OSError, UnicodeDecodeError) as exc:
        print(f"check-name-collisions: cannot read {display}: {exc}", file=sys.stderr)
        raise SystemExit(2)
    lines = blank_comments_and_strings(text).splitlines()

    # Stack of ("namespace"|"section"|"mutual", name, private, rooted).  A namespace
    # name may be dotted; `namespace A.B` pushes the two components as one name and joins
    # them into the namespace path.  A `__root__` component is the absolute root: it
    # contributes nothing to the path, and the block is explicitly global (13v).
    # `private` on a `mutual` block applies to its members.
    stack: list[tuple[str, str | None, bool, bool]] = []
    decls: list[Decl] = []
    imports: list[str] = []

    def ns_component(name: str) -> str:
        if name == "__root__":
            return ""
        if name.startswith("__root__."):
            return name[len("__root__.") :]
        return name

    def namespace_path() -> str:
        parts: list[str] = []
        for kind, name, _, _ in stack:
            if kind == "namespace" and name:
                part = ns_component(name)
                if part:
                    parts.append(part)
        return ".".join(parts)

    def enclosing_rooted() -> bool:
        return any(rooted for _, _, _, rooted in stack)

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
                if name == "__root__" and stack[-1][0] == "namespace" and ns_component(stack[-1][1] or "") == "":
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
                rooted = enclosing_rooted() or name == "__root__" or name.startswith("__root__.")
            else:
                rooted = enclosing_rooted()
            stack.append((kind, name if kind == "namespace" else None, private, rooted))
            continue

        if name is None or name == "_":
            continue
        # `private mutual ... end` makes every member private to the module.
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
                namespace=namespace_path(),
                path=display,
                rel=rel,
                line=lineno,
                private=private,
                local=local,
                rooted=enclosing_rooted(),
            )
        )

    return decls, imports


@dataclass
class Scan:
    """Everything one run needs: declarations plus the import graph's raw material."""

    decls: list[Decl]
    files: list[str]  # repository-relative paths
    imports: dict[str, list[str]]  # rel -> imported module names
    modules: dict[str, list[str]]  # module name -> rels (a name may repeat across roots)


def collect(roots: list[Path], repo: Path) -> Scan:
    repo = repo.resolve()
    scan = Scan(decls=[], files=[], imports={}, modules={})
    seen: set[Path] = set()

    for root in roots:
        root = root.resolve()
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
            try:
                display = str(hit.relative_to(Path.cwd()))
            except ValueError:
                display = str(hit)

            decls, imports = scan_file(hit, module, display, rel)
            scan.decls.extend(decls)
            scan.files.append(rel)
            scan.imports[rel] = imports
            scan.modules.setdefault(module, []).append(rel)

    return scan


def group_collisions(decls: list[Decl]) -> dict[tuple[str, str], list[Decl]]:
    groups: dict[tuple[str, str], list[Decl]] = {}
    for decl in decls:
        groups.setdefault(decl.key, []).append(decl)
    return {key: found for key, found in groups.items() if len(found) > 1}


def import_edges(scan: Scan) -> dict[str, set[str]]:
    """rel -> the rels it imports, resolving `import A.B` against the scanned roots."""
    edges: dict[str, set[str]] = {rel: set() for rel in scan.files}
    for rel, names in scan.imports.items():
        for name in names:
            for target in scan.modules.get(name, ()):
                if target != rel:
                    edges[rel].add(target)
    return edges


def importer_closures(edges: dict[str, set[str]]) -> dict[str, set[str]]:
    """rel -> every rel that transitively imports it, including itself.

    Two declarations can be loaded in one program exactly when their importer sets
    intersect: that common module is a program root (or an intermediate) that pulls
    in both.
    """
    reverse: dict[str, set[str]] = {rel: set() for rel in edges}
    for src, targets in edges.items():
        for target in targets:
            reverse[target].add(src)

    closures: dict[str, set[str]] = {}
    for rel in edges:
        seen = {rel}
        stack = [rel]
        while stack:
            current = stack.pop()
            for importer in reverse.get(current, ()):
                if importer not in seen:
                    seen.add(importer)
                    stack.append(importer)
        closures[rel] = seen
    return closures


def reachable_collisions(
    collisions: dict[tuple[str, str], list[Decl]], importers: dict[str, set[str]]
) -> dict[tuple[str, str], list[Decl]]:
    """Keep the declarations of a group that share an importer with another member."""
    out: dict[tuple[str, str], list[Decl]] = {}
    for key, found in collisions.items():
        keep: set[Decl] = set()
        for index, left in enumerate(found):
            for right in found[index + 1 :]:
                if importers.get(left.rel, {left.rel}) & importers.get(right.rel, {right.rel}):
                    keep.add(left)
                    keep.add(right)
        if len(keep) >= 2:
            out[key] = sorted(keep, key=lambda d: (d.path, d.line))
    return out


@dataclass(frozen=True)
class BaselineEntry:
    module: str
    name: str
    modules: tuple[str, ...]  # sorted repository-relative paths
    scope: str
    reason: str
    owner: str
    expires: str

    @property
    def key(self) -> tuple[str, str, tuple[str, ...]]:
        return (self.scope, self.name, self.modules)


class BaselineError(Exception):
    """A baseline that cannot be used; `code` is the process exit status."""

    def __init__(self, message: str, code: int) -> None:
        super().__init__(message)
        self.code = code


def load_baseline(path: Path, today: dt.date | None = None) -> list[BaselineEntry]:
    """Load and validate the baseline; expired entries make it unusable (code 1)."""
    today = today or dt.date.today()
    try:
        raw_doc = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError) as exc:
        raise BaselineError(f"{path}: cannot read: {exc}", 2)
    except json.JSONDecodeError as exc:
        raise BaselineError(f"{path}: not JSON: {exc}", 2)

    if not isinstance(raw_doc, dict) or not isinstance(raw_doc.get("entries"), list):
        raise BaselineError(f'{path}: expected an object with an "entries" list', 2)

    out: list[BaselineEntry] = []
    seen: set[tuple[str, str, tuple[str, ...]]] = set()
    expired: list[str] = []
    for index, raw in enumerate(raw_doc["entries"]):
        where = f"{path}: entry {index}"
        if not isinstance(raw, dict):
            raise BaselineError(f"{where}: expected an object", 2)
        for field in ("module", "name", "modules", "reason", "owner", "expires"):
            if field not in raw:
                raise BaselineError(f"{where}: missing {field!r}", 2)
        module = raw["module"]
        name = raw["name"]
        modules = raw["modules"]
        scope = raw.get("scope", "")
        reason = raw["reason"]
        owner = raw["owner"]
        expires = raw["expires"]
        if not isinstance(module, str) or not module.strip():
            raise BaselineError(f"{where}: 'module' must be a non-empty string", 2)
        if not isinstance(name, str) or not name.strip():
            raise BaselineError(f"{where}: 'name' must be a non-empty string", 2)
        if not isinstance(scope, str):
            raise BaselineError(f"{where}: 'scope' must be a string", 2)
        if not isinstance(modules, list) or not modules or not all(
            isinstance(m, str) and m.strip() for m in modules
        ):
            raise BaselineError(f"{where}: 'modules' must be a non-empty list of paths", 2)
        if len(set(modules)) != len(modules):
            raise BaselineError(f"{where}: 'modules' repeats a path", 2)
        if module not in modules:
            raise BaselineError(f"{where}: 'module' {module!r} is not in 'modules'", 2)
        if not isinstance(reason, str) or not reason.strip():
            raise BaselineError(f"{where}: 'reason' must say why the group cannot load", 2)
        if not isinstance(owner, str) or not owner.strip():
            raise BaselineError(f"{where}: 'owner' must name who owns the modules", 2)
        if not isinstance(expires, str) or not DATE_RE.fullmatch(expires):
            raise BaselineError(f"{where}: 'expires' must be YYYY-MM-DD", 2)
        try:
            day = dt.date.fromisoformat(expires)
        except ValueError:
            raise BaselineError(f"{where}: invalid 'expires' date {expires!r}", 2)
        if day <= today:
            expired.append(f"{where}: {name!r} expired on {expires}")
        entry = BaselineEntry(
            module=module,
            name=name,
            modules=tuple(sorted(modules)),
            scope=scope,
            reason=reason,
            owner=owner,
            expires=expires,
        )
        if entry.key in seen:
            raise BaselineError(f"{where}: duplicate entry for {name!r}", 2)
        seen.add(entry.key)
        out.append(entry)

    if expired:
        raise BaselineError(
            "\n".join(expired)
            + "\n  renew each entry with a new reason, or remove it if the group is fixed",
            1,
        )
    return out


def apply_baseline(
    collisions: dict[tuple[str, str], list[Decl]],
    scan: Scan,
    entries: list[BaselineEntry],
    repo: Path,
) -> tuple[set[tuple[str, str, tuple[str, ...]]], list[BaselineEntry]]:
    """(matched keys, stale entries): exact name + scope + module-set matches.

    An entry is stale when its group is gone: all its modules are in this scan and
    the group is absent, or one of its module files no longer exists.  A module that
    exists but is outside a partial `--root` scan is not enough to call it stale.
    """
    current: dict[tuple[str, str, tuple[str, ...]], list[Decl]] = {}
    for (scope, name), found in collisions.items():
        modules = tuple(sorted({decl.rel for decl in found}))
        current[(scope, name, modules)] = found

    scanned = set(scan.files)
    matched: set[tuple[str, str, tuple[str, ...]]] = set()
    stale: list[BaselineEntry] = []
    for entry in entries:
        if entry.key in current:
            matched.add(entry.key)
            continue
        exists = all((repo / rel).exists() for rel in entry.modules)
        if not exists or all(rel in scanned for rel in entry.modules):
            stale.append(entry)
    return matched, stale


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


def find_entry(
    entries: list[BaselineEntry], key: tuple[str, str, tuple[str, ...]]
) -> BaselineEntry | None:
    for entry in entries:
        if entry.key == key:
            return entry
    return None


def print_group(
    key: tuple[str, str],
    found: list[Decl],
    co_keys: set[tuple[str, str]],
    entry: BaselineEntry | None,
) -> None:
    scope, name = key
    tags = ["co-loadable" if key in co_keys else "project-wide only"]
    if entry is not None:
        tags.append("baselined")
    tag_text = ", ".join(tags)
    print(
        f"  '{name}' in {describe_scope(scope)}, declared {len(found)} time(s) [{tag_text}]:"
    )
    for decl in sorted(found, key=lambda d: (d.path, d.line)):
        modifier = "private " if decl.private else ("local " if decl.local else "")
        print(
            f"    {decl.path}:{decl.line}: {modifier}{decl.keyword} "
            f"{decl.source} (module {decl.module})"
        )
    if entry is not None:
        print(f"    baselined until {entry.expires} ({entry.owner}): {entry.reason}")
    else:
        print(
            "    fix: rename one of them; if the name really is global, spell it "
            f"`__root__.{name}` once namespaces land."
        )


def report(
    scan: Scan,
    roots: list[Path],
    quiet: bool,
    reachable: bool,
    baseline_entries: list[BaselineEntry] | None,
    baseline_path: Path | None,
) -> int:
    collisions = group_collisions(scan.decls)
    importers = importer_closures(import_edges(scan))
    co_groups = reachable_collisions(collisions, importers)
    co_keys = set(co_groups)
    migrations = [decl for decl in scan.decls if decl.migration]
    migration_files: dict[str, int] = {}
    for decl in migrations:
        migration_files[decl.path] = migration_files.get(decl.path, 0) + 1
    distinct = {decl.bare for decl in migrations}

    matched: set[tuple[str, str, tuple[str, ...]]] = set()
    stale: list[BaselineEntry] = []
    if not reachable and baseline_entries is not None:
        matched, stale = apply_baseline(collisions, scan, baseline_entries, REPO)

    subject = co_groups if reachable else collisions
    matched_groups = {(scope, name) for scope, name, _modules in matched}
    failing = {
        key: found for key, found in subject.items() if key not in matched_groups
    }

    if not quiet:
        print("check-name-collisions: roots " + ", ".join(display(root) for root in roots))
        print(f"  {len(scan.files)} .wiz file(s), {len(scan.decls)} declaration(s)")
        if reachable:
            print("  model: --reachable (two declarations must share a transitive importer)")
            print("  baseline: not applied in --reachable mode")
        elif baseline_path is None:
            print("  baseline: none (strict project-wide check)")
        elif baseline_entries is None:
            print(f"  baseline: {display(baseline_path)} not found (strict project-wide check)")
        else:
            print(f"  baseline: {display(baseline_path)} ({len(baseline_entries)} entries)")

    if reachable:
        co_decls = sum(len(found) for found in co_groups.values())
        filtered = len(collisions) - len(co_groups)
        print(
            f"global: {len(co_groups)} co-loadable collision group(s), "
            f"{co_decls} declaration(s); {filtered} project-wide group(s) filtered"
        )
        filtered_keys = set(collisions) - set(co_groups)
        if not quiet and filtered_keys:
            names = ", ".join(sorted({name for _, name in filtered_keys}))
            print(f"  filtered as project-wide only (no common importer): {names}")
    else:
        baselined = len(matched)
        unbaselined = len(collisions) - baselined
        print(
            f"global: {len(collisions)} collision group(s), "
            f"{sum(len(found) for found in collisions.values())} declaration(s) "
            f"({baselined} baselined, {unbaselined} unbaselined; "
            f"{len(co_groups)} co-loadable)"
        )

    shown = failing if (quiet or reachable) else collisions
    for key, found in sorted(shown.items(), key=lambda kv: kv[0]):
        modules = tuple(sorted({decl.rel for decl in found}))
        entry = find_entry(baseline_entries or [], (key[0], key[1], modules))
        print_group(key, found, co_keys, entry)

    if stale:
        print(f"baseline: {len(stale)} stale entr{'y' if len(stale) == 1 else 'ies'}:")
        for entry in stale:
            print(
                f"  '{entry.name}' [{', '.join(entry.modules)}] matches no collision group; "
                "remove the entry (or restore the group)"
            )

    if migrations:
        print(
            f"migration: {len(migrations)} dotted declaration(s) "
            f"({len(distinct)} distinct name(s)) in {len(migration_files)} file(s)"
        )
        if not quiet:
            for path, count in sorted(migration_files.items(), key=lambda kv: (-kv[1], kv[0])):
                print(f"  {path}: {count}")
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

    problems = len(failing) + len(stale)
    if problems:
        kind = "co-loadable" if reachable else "unbaselined global"
        baseline_text = (
            "baseline not applied"
            if reachable
            else f"{len(stale)} stale baseline entr{'y' if len(stale) == 1 else 'ies'}"
        )
        print(
            f"check-name-collisions: FAIL ({len(failing)} {kind} group(s), "
            f"{baseline_text}, "
            f"{len(migrations)} migration declaration(s) not failing)",
            file=sys.stderr,
        )
        return 1
    if reachable:
        print(
            f"check-name-collisions: clean ({len(co_groups)} co-loadable group(s), "
            f"{len(collisions) - len(co_groups)} project-wide group(s) filtered, "
            f"{len(migrations)} migration declaration(s) reported)"
        )
    else:
        print(
            f"check-name-collisions: clean ({len(matched)} baselined group(s), "
            f"{len(co_groups)} co-loadable group(s), "
            f"{len(migrations)} migration declaration(s) reported)"
        )
    return 0


FIXTURES = Path(__file__).resolve().parent / "fixtures" / "name-collisions"

# (case directory, expected project-wide groups, expected reachable groups,
#  expected migration count)
SELF_TEST_CASES: tuple[
    tuple[str, dict[tuple[str, str], int], dict[tuple[str, str], int], int], ...
] = (
    # Two modules declare the same top-level name; no import path, so not reachable.
    ("collide", {("", "shared"): 2}, {}, 0),
    # `__root__.same` escapes into the global scope, beside `def same` elsewhere.
    ("root_escape", {("", "same"): 2}, {}, 0),
    # A dotted name is not an escape hatch: it is one global name today (so the pair
    # collides) and it migrates to Module.Module.name.
    ("migration", {("", "Thing.name"): 2}, {}, 2),
    # The member of a `mutual` block is seen, and `end` closes the mutual block and
    # not its surrounding namespace; the member and the later def stay in Mut.
    ("mutual", {("Mut", "loop"): 2}, {("Mut", "loop"): 2}, 0),
    # Namespace bodies separate names; only the duplicate inside one namespace collides.
    ("namespace", {("A", "x"): 2}, {("A", "x"): 2}, 0),
    # Clean, and a private name in two modules is not a collision.
    ("clean", {}, {}, 0),
    # x and y share the importer `all`; p imports q; z is independent.
    (
        "reachable",
        {("", "other"): 2, ("", "shared"): 3},
        {("", "other"): 2, ("", "shared"): 2},
        0,
    ),
)


def analyse_case(
    case: Path,
) -> tuple[dict[tuple[str, str], int], dict[tuple[str, str], int], int]:
    scan = collect([case], case)
    collisions = group_collisions(scan.decls)
    importers = importer_closures(import_edges(scan))
    reachable = reachable_collisions(collisions, importers)
    project = {key: len(found) for key, found in collisions.items()}
    co = {key: len(found) for key, found in reachable.items()}
    migrations = sum(1 for decl in scan.decls if decl.migration)
    return project, co, migrations


def write_baseline(path: Path, entries: list[dict]) -> None:
    path.write_text(json.dumps({"entries": entries}, indent=2) + "\n", encoding="utf-8")


def baseline_self_test() -> list[str]:
    """The valid/stale/expired/malformed cases, on the `collide` fixture."""
    failures: list[str] = []
    case = FIXTURES / "collide"
    scan = collect([case], case)
    collisions = group_collisions(scan.decls)
    valid = {
        "module": "a.wiz",
        "name": "shared",
        "modules": ["a.wiz", "b.wiz"],
        "scope": "",
        "reason": "fixture: the two modules are independent",
        "owner": "fixture",
        "expires": "2099-01-01",
    }

    with tempfile.TemporaryDirectory() as td:
        path = Path(td) / "baseline.json"

        write_baseline(path, [valid])
        try:
            entries = load_baseline(path, today=dt.date(2026, 1, 1))
        except BaselineError as exc:
            failures.append(f"valid baseline was rejected: {exc}")
            entries = []
        matched, stale = apply_baseline(collisions, scan, entries, case)
        if matched != {(("", "shared", ("a.wiz", "b.wiz")))}:
            failures.append(f"valid baseline did not match the group: matched={matched}")
        if stale:
            failures.append(f"valid baseline reported stale: {stale}")

        write_baseline(path, [dict(valid, name="missing")])
        entries = load_baseline(path, today=dt.date(2026, 1, 1))
        _, stale = apply_baseline(collisions, scan, entries, case)
        if not stale:
            failures.append("a baseline entry with no group was not stale")

        write_baseline(path, [dict(valid, modules=["a.wiz", "gone.wiz"], module="a.wiz")])
        entries = load_baseline(path, today=dt.date(2026, 1, 1))
        _, stale = apply_baseline(collisions, scan, entries, case)
        if not stale:
            failures.append("a baseline entry naming a missing module was not stale")

        # A group whose module set changes: the old entry is stale and the new group
        # is unbaselined (the caller fails it), rather than silently excusing it.
        write_baseline(
            path,
            [dict(valid, modules=["a.wiz", "b.wiz", "extra.wiz"])],
        )
        entries = load_baseline(path, today=dt.date(2026, 1, 1))
        matched, stale = apply_baseline(collisions, scan, entries, case)
        if matched or not stale:
            failures.append(
                "a baseline entry with a changed module set was not stale"
            )

        write_baseline(path, [dict(valid, expires="2020-01-01")])
        try:
            load_baseline(path, today=dt.date(2026, 1, 1))
        except BaselineError as exc:
            if exc.code != 1:
                failures.append(f"an expired baseline exited {exc.code}, expected 1")
        else:
            failures.append("an expired baseline was accepted")

        write_baseline(path, [{k: v for k, v in valid.items() if k != "owner"}])
        try:
            load_baseline(path, today=dt.date(2026, 1, 1))
        except BaselineError as exc:
            if exc.code != 2:
                failures.append(f"a malformed baseline exited {exc.code}, expected 2")
        else:
            failures.append("a baseline entry without an owner was accepted")

    return failures


def self_test() -> int:
    failures: list[str] = []
    for case_name, expected_project, expected_reachable, expected_migrations in SELF_TEST_CASES:
        case = FIXTURES / case_name
        if not case.is_dir():
            failures.append(f"{case_name}: fixture directory {case} is missing")
            continue
        project, reachable, migrations = analyse_case(case)
        if project != expected_project:
            failures.append(
                f"{case_name}: expected project groups {expected_project}, got {project}"
            )
        if reachable != expected_reachable:
            failures.append(
                f"{case_name}: expected reachable groups {expected_reachable}, got {reachable}"
            )
        if migrations != expected_migrations:
            failures.append(
                f"{case_name}: expected {expected_migrations} migration declaration(s), "
                f"got {migrations}"
            )
    failures.extend(baseline_self_test())
    # The repository's own baseline must load (owners, reasons, future expiry).
    try:
        real = load_baseline(DEFAULT_BASELINE)
    except (BaselineError, OSError) as exc:
        failures.append(f"{DEFAULT_BASELINE}: {exc}")
    else:
        if not real:
            failures.append(f"{DEFAULT_BASELINE}: has no entries")
    if failures:
        for failure in failures:
            print(f"self-test FAIL: {failure}", file=sys.stderr)
        return 1
    print(
        f"check-name-collisions self-test: ok ({len(SELF_TEST_CASES)} fixtures: "
        "colliding pair, __root__ escape, dotted migration, mutual block, namespace body, "
        "reachable import graph, clean; baseline valid/stale/expired/malformed)"
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
        help="run the fixtures and baseline cases instead of reading files",
    )
    parser.add_argument(
        "--quiet",
        action="store_true",
        help="summary only; fail only on groups not in the baseline",
    )
    parser.add_argument(
        "--reachable",
        action="store_true",
        help="only report groups whose declarations can share a transitive importer",
    )
    baseline_group = parser.add_mutually_exclusive_group()
    baseline_group.add_argument(
        "--baseline",
        type=Path,
        metavar="FILE",
        help="baseline file (default: .github/name-collisions-baseline.json)",
    )
    baseline_group.add_argument(
        "--no-baseline",
        action="store_true",
        help="ignore the baseline and fail on every global group",
    )
    args = parser.parse_args(argv)

    if args.self_test:
        return self_test()

    if args.reachable and args.baseline is not None:
        print(
            "check-name-collisions: --baseline documents the project-wide model and is "
            "not used with --reachable",
            file=sys.stderr,
        )
        return 2

    roots = [root.resolve() for root in (args.root or default_roots(repo))]
    for root in roots:
        if not root.is_dir():
            print(f"check-name-collisions: --root {root} is not a directory", file=sys.stderr)
            return 2

    baseline_entries: list[BaselineEntry] | None = None
    baseline_path: Path | None = None
    if not args.reachable and not args.no_baseline:
        baseline_path = (args.baseline or DEFAULT_BASELINE).resolve()
        if args.baseline is not None and not baseline_path.is_file():
            print(
                f"check-name-collisions: --baseline {baseline_path} is not a file",
                file=sys.stderr,
            )
            return 2
        if baseline_path.is_file():
            try:
                baseline_entries = load_baseline(baseline_path)
            except BaselineError as exc:
                print(f"check-name-collisions: {exc}", file=sys.stderr)
                return exc.code

    scan = collect(roots, repo)
    if not scan.files:
        print(
            "check-name-collisions: no .wiz files found under "
            + ", ".join(display(root) for root in roots),
            file=sys.stderr,
        )
        return 2
    return report(scan, roots, args.quiet, args.reachable, baseline_entries, baseline_path)


if __name__ == "__main__":
    sys.exit(main())
