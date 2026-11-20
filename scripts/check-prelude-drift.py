#!/usr/bin/env python3
"""Fail when the self-hosted frontend's embedded prelude drifts from `lib/Prelude.wiz`.

There are two preludes, and they are not meant to be equal:

* `lib/Prelude.wiz` is the host prelude. It is hand-written, and the host reads it
  from the toolchain's library root (`Module.toolchainLib`: `lib/` of a checkout, or
  `share/wiz/lib` of a Nix package, which `flake.nix` stages byte for byte).
* `selfhost/Frontend.wiz`'s `preludeText` is the self-hosted frontend's prelude: a
  hand-written, minimal *model* of the library's data types and functions, embedded as
  one single-line string literal. `import Prelude` in the self-hosted compiler resolves
  to it, and the WebAssembly playground compiles `selfhost/Frontend.wiz` and injects
  `import Prelude` (`web/selfhost-lsp-shim.js`), so the page's prelude is this copy.

The embedded copy is a subset by design. Its arithmetic is monomorphic
(`infixl " + " => Nat.add`, where the host goes through `HAdd`/`Add` and an instance),
it declares no classes, and it does not carry the transport names (`castRefl`,
`Eq.cast`, `Eq.subst`). Comparing bytes, or hashing
either file, would therefore fail forever, and generating the embedded copy from
`lib/Prelude.wiz` is impossible while the frontend cannot check the host prelude. What
*can* be compared is the semantic surface: the names a program may use, the kind of
value behind each name, and a type's constructors and fields.

This check is a ratchet on that surface:

1. coverage — every value declaration in the runtime part of `lib/Prelude.wiz` must
   appear in `preludeText` with the same kind and the same constructors/fields, unless
   it is listed in `EXEMPT` with a reason. So a PR that adds a name to the library
   prelude but not to the embedded copy fails here.
2. origin — every name in `preludeText` must be declared somewhere under `lib/`
   (or listed in `EMBEDDED_ONLY` with a reason). The page may not invent library
   surface, and a private helper added to the embedded copy needs a reviewed entry.
3. staleness — an `EXEMPT`, `EMBEDDED_ONLY` or `META_ROOTS` entry that matches nothing
   is an error, so the lists cannot rot into a blanket exemption. `META_ROOTS` is the
   set of namespaces after the runtime marker: a declaration appended at the end of the
   file is then a reviewed decision, not an escape from coverage.

It also reports the names `preludeText` *promotes*: names the page offers with only
`import Prelude` that the host library declares in another module (`List.map` and
`String.length` from `lib/Text.wiz`; the `IO`/`Std`/`Bytes` names). That direction is
reported, not failed: the self-hosted compiler's own sources use several of them, and
the remedy is to make the frontend load the library modules (workstream A1), not to
delete them here.

Usage
  scripts/check-prelude-drift.py              check this checkout
  scripts/check-prelude-drift.py --self-test  run the built-in fixtures
  scripts/check-prelude-drift.py --root DIR   check another checkout
  scripts/check-prelude-drift.py --verbose    list every name in every category
  scripts/check-prelude-drift.py --dump-embedded
                                              print the decoded `preludeText`

Exit status: 0 clean, 1 drift (or a failing self-test), 2 usage or parse error.
CI runs `--self-test` and then the check (`.github/workflows/ci.yml`, job
`prelude_drift`); docs/stages/21-bootstrap.md, "The two preludes", has the long form.
"""

from __future__ import annotations

import argparse
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

HOST_PRELUDE = "lib/Prelude.wiz"
FRONTEND = "selfhost/Frontend.wiz"
#: The runtime part of the host prelude ends here; everything after it is the
#: metaprogramming layer (reflected terms, tactics, macros, `Syntax` helpers), which
#: the self-hosted frontend does not need and cannot express. The marker is a real
#: line of lib/Prelude.wiz: moving or removing it is a parse error here, not a silent
#: change of what "runtime surface" means.
RUNTIME_END = "-- (end of the Boolean section)"

#: `preludeText` is loaded by the module loader (`moduleRootSourcesAs`) and by the
#: one-shot path (`checkFile`); at least one marker must still be present.
LOADER_MARKERS = ('ModSrc.mk "Prelude" "prelude" preludeText',
                   'String.codes preludeText')

#: Runtime declarations of `lib/Prelude.wiz` that are deliberately not in the
#: embedded prelude. Each is a reviewed decision, not an accident; the check fails if
#: an entry stops matching and names any missing declaration that is not here.
EXEMPT: dict[str, str] = {
    "castRefl": "a known gap: transport, a plain axiom over `=`/`cast` that the "
                "embedded model does not carry. The self-hosted sources do not use it; "
                "lib files that do are libdiff gaps. Adding it is a small follow-up.",
    "Eq.cast": "a known gap: transport, as `castRefl`",
    "Eq.subst": "a known gap: transport, as `castRefl`",
    "Eq.substBack": "a known gap: transport, as `castRefl`",
    "Nat.subFrom": "a known gap: the host's spelling of the recursor behind "
                   "`Nat.sub` (the embedded copy recurses on the second argument "
                   "directly); lib/Nat.wiz and lib/BitBlast.wiz use the name",
    "Nat.powFrom": "a known gap: the host's spelling of the recursor behind "
                   "`Nat.pow` (the embedded copy recurses on the exponent directly)",
    "pipe": "a known gap: `def pipe` and its `infixl` line are not in the embedded "
            "copy (the frontend supports `infixl`, so this is cheap to add); lib/ "
            "files that use `|>` are libdiff gaps",
    "apply": "a known gap, next to `pipe`: `def apply` and its `infixr` line (for `<|`) "
             "are not in the embedded copy; lib/ files that use `<|` are libdiff gaps",
    "outParam": "class plumbing (`outParam A` in a class declaration); the "
                "embedded prelude has no classes",
}

#: The namespaces of the host prelude's metaprogramming layer: the declarations after
#: `RUNTIME_END`. The boundary is a position in the file, so a declaration appended at
#: the end would otherwise escape the coverage check; this list makes an append a
#: reviewed decision. It is the roots the current file uses, and a root that no longer
#: appears is an error (the usual staleness rule).
META_ROOTS: set[str] = {
    "Append", "BinderKind", "CommandMacro", "CtorView", "Deriver", "Expr",
    "ExprView", "FieldView", "HAppend", "IndView", "List", "ListLit", "Macro",
    "MacroM", "Monad", "Monad1", "ParamView", "RewriteResult", "SatAnswer", "Simp",
    "String", "Syntax", "SyntaxF", "Tac", "Tactic", "TacticM", "PipeProj",
}

#: Names `preludeText` defines that `lib/` does not declare as identifiers. Every
#: other embedded name must be declared somewhere under `lib/` (invariant 2).
EMBEDDED_ONLY: dict[str, str] = {
    "Prod": "the kernel's product type (`×`); lib/ never declares it",
    "Nat.blt": "lib/Prelude.wiz:174 registers it as `builtin nat.blt := Nat.lt`, "
               "but the host has no identifier `Nat.blt` (verified: `#check` rejects "
               "it), so the page offers a name the host does not",
    "Bytes.width": "a helper of the embedded prelude's UTF-8 decoder (`bytesText`); the "
                "library's `Bytes` is a native `axiom` with `extern` operations",
    "Bytes.minWidth": "a helper of the embedded prelude's UTF-8 decoder (`bytesText`); the "
                "library's `Bytes` is a native `axiom` with `extern` operations",
    "Bytes.isScalar": "a helper of the embedded prelude's UTF-8 decoder (`bytesText`); the "
                "library's `Bytes` is a native `axiom` with `extern` operations",
    "Bytes.leadVal": "a helper of the embedded prelude's UTF-8 decoder (`bytesText`); the "
                "library's `Bytes` is a native `axiom` with `extern` operations",
    "Bytes.contOk": "a helper of the embedded prelude's UTF-8 decoder (`bytesText`); the "
                "library's `Bytes` is a native `axiom` with `extern` operations",
    "Bytes.contVal": "a helper of the embedded prelude's UTF-8 decoder (`bytesText`); the "
                "library's `Bytes` is a native `axiom` with `extern` operations",
    "Bytes.getAux": "a helper of the embedded prelude's Wiz model of `Bytes`; the "
                    "library's `Bytes` is a native `axiom` with `extern` operations",
    "Bytes.dropN": "as `Bytes.getAux`",
    "Bytes.takeN": "as `Bytes.getAux`",
    "Bytes.pushCp": "as `Bytes.getAux`",
    "Bytes.ofStringAux": "as `Bytes.getAux`",
    "Bytes.beforeNul": "as `Bytes.getAux`",
    "Bytes.decodeFrom": "as `Bytes.getAux`",
    "Bytes.contOp": "as `Bytes.getAux`",
    "Bytes.eqAux": "as `Bytes.getAux`",
    "String.data": "the embedded `String` is a `structure` whose field models the "
                   "host's `inductive String` constructor field; the host has no "
                   "`String.data` projection",
    "Prod.fst": "projection of the kernel's product type (`×`); lib/ never declares it",
    "Prod.snd": "projection of the kernel's product type (`×`); lib/ never declares it",
    "Prod.mk": "constructor of the kernel's product type (`×`); lib/ never declares it",
}

_WS = re.compile(r"\s+")
_DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?"
    r"(?:partial\s+|private\s+|sealed\s+|noncomputable\s+|local\s+)*"
    r"(def|inductive|coinductive|structure|c_struct|axiom|extern|class|abbrev|theorem|opaque|foreign_type)"
    r"\s+([A-Za-z_][A-Za-z0-9_.'!?]*)")
_EXTERN = re.compile(r'^extern\s+"(?:[^"\\]|\\.)*"\s+([A-Za-z_][A-Za-z0-9_.\'!?]*)')
_BUILTIN = re.compile(r"^builtin\s+([A-Za-z_][A-Za-z0-9_.'!?]*)\s*:=")
_MEMBER_CTOR = re.compile(r"^\|\s*(?:private\s+)?([A-Za-z_][A-Za-z0-9_']*)")
_MEMBER_FIELD = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:private\s+)?(?:[0-9ω]+\s+)?"
    r"([A-Za-z_][A-Za-z0-9_']*)\s*:")


class CheckError(Exception):
    """A usage or parse problem: the check cannot answer."""


@dataclass
class Decl:
    name: str
    kind: str
    line: int
    members: tuple[str, ...] = ()


@dataclass
class Surface:
    decls: list[Decl] = field(default_factory=list)
    registrations: dict[str, int] = field(default_factory=dict)

    def by_name(self) -> dict[str, Decl]:
        return {d.name: d for d in self.decls}

    def names(self) -> set[str]:
        out = {d.name for d in self.decls}
        for d in self.decls:
            # A constructor, a structure's `mk` and a structure's fields are all names
            # a program can use; a class's fields are its projections.
            if d.kind in ("inductive", "coinductive", "structure", "c_struct", "class"):
                out.update(f"{d.name}.{m}" for m in d.members)
            if d.kind in ("structure", "c_struct"):
                out.add(f"{d.name}.mk")
        return out


def strip_comments(text: str) -> str:
    """Blank out comments, keeping newlines (so line numbers survive). String
    literals are copied as-is: a `--` or `/-` inside one is not a comment."""
    out: list[str] = []
    i, n, depth = 0, len(text), 0
    while i < n:
        if depth:
            if text.startswith("/-", i):
                depth += 1
                out.extend("  ")
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                out.extend("  ")
                i += 2
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
            continue
        if text.startswith("/-", i):
            depth = 1
            out.extend("  ")
            i += 2
        elif text.startswith("--", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            out.extend(" " * (j - i))
            i = j
        elif text[i] == '"':
            j = i + 1
            while j < n:
                if text[j] == "\\":
                    j += 2
                elif text[j] == '"':
                    j += 1
                    break
                else:
                    j += 1
            out.append(text[i:j])
            i = j
        else:
            out.append(text[i])
            i += 1
    if depth:
        raise CheckError("unterminated block comment")
    return "".join(out)


def parse_wiz(text: str, where: str) -> Surface:
    """The top-level declarations of a Wiz source: value declarations, with an
    inductive's constructors or a structure's fields, and `builtin` registrations.

    This is a surface scanner, not a parser. It knows the line shape of the Wiz
    commands it needs and refuses a file whose shape it does not know, rather than
    guessing (a silent miss would make the check lie)."""
    raw = strip_comments(text).split("\n")
    surface = Surface()
    i = 0
    while i < len(raw):
        line = raw[i]
        if not line or line[0].isspace():
            i += 1
            continue
        if re.match(r"^(namespace|section)\b", line):
            raise CheckError(
                f"{where}:{i + 1}: `{line.split()[0]}` blocks are not handled by this "
                "checker; teach scripts/check-prelude-drift.py about them")
        if line in ("mutual", "end"):
            # A `mutual` block's declarations are top-level and at column 0; `end`
            # closes it. Both are transparent for the surface.
            i += 1
            continue
        b = _BUILTIN.match(line)
        if b:
            surface.registrations[b.group(1)] = i + 1
            i += 1
            continue
        e = _EXTERN.match(line)
        m = None if e else _DECL.match(line)
        if e:
            name, kind = e.group(1), "extern"
        elif m:
            name, kind = m.group(2), m.group(1)
            if name.endswith("."):
                name = name[:-1]
        else:
            i += 1
            continue
        members: list[str] = []
        if kind in ("inductive", "coinductive", "structure", "c_struct", "class"):
            j = i + 1
            while j < len(raw):
                u = raw[j]
                if u.strip() == "":
                    j += 1
                    continue
                if not u[0].isspace():
                    break
                s = u.strip()
                cm = _MEMBER_CTOR.match(s) if kind in ("inductive", "coinductive") else None
                if kind in ("inductive", "coinductive"):
                    # `| private mk` is not public surface.
                    if cm and not re.match(r"^\|\s*private\b", s):
                        members.append(cm.group(1))
                elif kind in ("structure", "c_struct", "class"):
                    fm = _MEMBER_FIELD.match(s)
                    if fm and not s.startswith("private "):
                        members.append(fm.group(1))
                j += 1
        surface.decls.append(Decl(name, kind, i + 1, tuple(members)))
        i += 1
    return surface


def decode_prelude_text(frontend: str, where: str) -> str:
    """The value of `def preludeText : String := "..."` in selfhost/Frontend.wiz.

    The literal is one line with `\\n` escapes; a literal split over several lines
    (a change of shape) is reported rather than guessed at."""
    m = re.search(r'^def preludeText : String := (".*")\s*$', frontend, re.M)
    if not m:
        raise CheckError(
            f"{where}: no single-line `def preludeText : String := \"…\"`. If the "
            "prelude moved or was split, update this check (and see "
            "docs/stages/21-bootstrap.md, 'The two preludes').")
    lit = m.group(1)
    out: list[str] = []
    i = 1
    while i < len(lit) - 1:
        c = lit[i]
        if c != "\\":
            out.append(c)
            i += 1
            continue
        nxt = lit[i + 1]
        out.append({"n": "\n", "t": "\t", "r": "\r", '"': '"', "\\": "\\"}.get(
            nxt, "\\" + nxt))
        i += 2
    return "".join(out)


def squash(s: str) -> str:
    return _WS.sub(" ", s).strip()


@dataclass
class Problem:
    invariant: str
    message: str


@dataclass
class Report:
    host: Surface
    embedded: Surface
    embedded_line: int
    runtime_line: int
    host_runtime: int = 0
    host_meta: int = 0
    covered: int = 0
    classes: list[Decl] = field(default_factory=list)
    exempted: list[Decl] = field(default_factory=list)
    stale_exempt: list[str] = field(default_factory=list)
    embedded_only: list[str] = field(default_factory=list)
    stale_embedded_only: list[str] = field(default_factory=list)
    meta_roots_stale: list[str] = field(default_factory=list)
    promoted: dict[str, list[str]] = field(default_factory=dict)
    problems: list[Problem] = field(default_factory=list)

    @property
    def ok(self) -> bool:
        return not self.problems


def compare(host_text: str, embedded_text: str, lib_texts: dict[str, str],
            embedded_line: int = 1, host_name: str = HOST_PRELUDE,
            exempt: dict[str, str] | None = None,
            embedded_only: dict[str, str] | None = None,
            meta_roots: set[str] | None = None) -> Report:
    """The whole check, on texts: used by the CLI and by `--self-test`."""
    exempt = EXEMPT if exempt is None else exempt
    embedded_only = EMBEDDED_ONLY if embedded_only is None else embedded_only
    meta_roots = META_ROOTS if meta_roots is None else meta_roots
    host = parse_wiz(host_text, host_name)
    host_lines = host_text.split("\n")
    boundary = next((i + 1 for i, l in enumerate(host_lines)
                     if l.strip() == RUNTIME_END), None)
    if boundary is None:
        raise CheckError(
            f"{host_name}: no `{RUNTIME_END}` line; it delimits the runtime surface. "
            "Restore it, or update this check deliberately.")
    embedded = parse_wiz(embedded_text, "preludeText")
    rep = Report(host=host, embedded=embedded, embedded_line=embedded_line,
                 runtime_line=boundary)
    emb = embedded.by_name()

    runtime = [d for d in host.decls if d.line < boundary]
    meta = [d for d in host.decls if d.line > boundary]
    rep.host_runtime = len(runtime)
    rep.host_meta = len(meta)
    used_meta = {d.name.split(".")[0] for d in meta}
    for d in meta:
        root = d.name.split(".")[0]
        if root not in meta_roots:
            rep.problems.append(Problem(
                "surface",
                f"{host_name}:{d.line}: {d.kind} {d.name} is after "
                f"`{RUNTIME_END}` but not in a known metaprogramming namespace. Move "
                "it before the marker (so coverage checks it), or extend META_ROOTS "
                "deliberately in scripts/check-prelude-drift.py."))
    rep.meta_roots_stale = sorted(set(meta_roots) - used_meta)

    # (1) coverage: same name, kind and members, or a reviewed exemption.
    missing: list[Decl] = []
    emb_names = embedded.names()
    for d in runtime:
        if d.kind == "class":
            rep.classes.append(d)
            continue
        e = emb.get(d.name)
        if e is None:
            if d.name not in emb_names:
                missing.append(d)
            else:
                # A structure's projection on the embedded side (`Char.code`) stands
                # in for the host's separate `def`; the name is the surface.
                rep.covered += 1
            continue
        # `structure` and `inductive` are the same surface when the host's members
        # are all visible in the embedded copy: the embedded prelude models `Char`
        # and `String` as structures, the host as one-constructor inductives.
        if e.kind != d.kind:
            if {d.kind, e.kind} != {"inductive", "structure"}:
                rep.problems.append(Problem(
                    "coverage",
                    f"{host_name}:{d.line}: {d.kind} {d.name} is {e.kind} {e.name} "
                    f"in preludeText ({FRONTEND}:{embedded_line})"))
            elif not {f"{d.name}.{m}" for m in d.members} <= emb_names:
                rep.problems.append(Problem(
                    "coverage",
                    f"{host_name}:{d.line}: {d.kind} {d.name} has "
                    f"({', '.join(d.members)}), which preludeText "
                    f"({FRONTEND}:{embedded_line}) does not all expose"))
            else:
                rep.covered += 1
        elif e.members != d.members:
            rep.problems.append(Problem(
                "coverage",
                f"{host_name}:{d.line}: {d.kind} {d.name} has "
                f"({', '.join(d.members)}), the embedded copy has "
                f"({', '.join(e.members)})"))
        else:
            rep.covered += 1
    matched_exempt = set()
    for d in missing:
        if d.name in exempt:
            matched_exempt.add(d.name)
            rep.exempted.append(d)
        else:
            rep.problems.append(Problem(
                "coverage",
                f"{host_name}:{d.line}: {d.kind} {d.name} is not in preludeText "
                f"({FRONTEND}:{embedded_line}). Add it there, or add a "
                "reviewed EXEMPT entry with a reason in "
                "scripts/check-prelude-drift.py."))
    rep.stale_exempt = sorted(set(exempt) - matched_exempt)

    # (2) origin: every embedded name is declared somewhere under lib/.
    declared: dict[str, tuple[str, int]] = {}
    for path in sorted(lib_texts):
        s = parse_wiz(lib_texts[path], path)
        for d in s.decls:
            declared.setdefault(d.name, (path, d.line))
            if d.kind in ("inductive", "coinductive", "structure", "c_struct", "class"):
                for mem in d.members:
                    declared.setdefault(f"{d.name}.{mem}", (path, d.line))
            if d.kind in ("structure", "c_struct"):
                declared.setdefault(f"{d.name}.mk", (path, d.line))
        for key, line in s.registrations.items():
            declared.setdefault(key, (path, line))
    for name in sorted(embedded.names()):
        owner = next((x for x in embedded.decls
                      if name == x.name or name.startswith(x.name + ".")),
                     Decl(name, "?", embedded_line))
        if name in declared:
            continue
        rep.embedded_only.append(name)
        if name in embedded_only:
            continue
        rep.problems.append(Problem(
            "origin",
            f"preludeText:{owner.line} ({FRONTEND}:{embedded_line}): "
            f"{owner.kind} {name} is not declared anywhere under lib/."
            " Add it to the library first, or add a reviewed EMBEDDED_ONLY entry "
            "with a reason in scripts/check-prelude-drift.py."))
    # An entry is "used" only if the name actually needs the exception: a name that
    # lib/ declares does not, even when the entry's text matches it.
    used_embedded_only = {n for n in embedded.names()
                          if n in embedded_only and n not in declared}
    rep.stale_embedded_only = sorted(set(embedded_only) - used_embedded_only)

    # (3) staleness of the reviewed lists.
    for name in rep.stale_exempt:
        rep.problems.append(Problem(
            "staleness",
            f"EXEMPT[{name!r}] matches no missing runtime declaration of "
            f"{host_name}; remove it (or fix the name)"))
    for name in rep.stale_embedded_only:
        rep.problems.append(Problem(
            "staleness",
            f"EMBEDDED_ONLY[{name!r}] matches no name in preludeText; remove it "
            "(or fix the name)"))
    for root in rep.meta_roots_stale:
        rep.problems.append(Problem(
            "staleness",
            f"META_ROOTS[{root!r}] matches no declaration after `{RUNTIME_END}`; "
            "remove it (or fix the root)"))

    # informational: names the page promotes (declared in lib, but not in Prelude).
    host_names = {d.name for d in host.decls} | set(host.registrations)
    for d in host.decls:
        if d.kind in ("inductive", "coinductive", "structure", "c_struct", "class"):
            host_names.update(f"{d.name}.{m}" for m in d.members)
        if d.kind in ("structure", "c_struct"):
            host_names.add(f"{d.name}.mk")
    for name in sorted(embedded.names()):
        if name in host_names:
            continue
        home = declared.get(name)
        if home is None:
            continue
        rep.promoted.setdefault(home[0], []).append(name)
    return rep


PAGE_NOTES: list[str] = []


def print_report(rep: Report, verbose: bool) -> None:
    print("prelude drift check")
    print(f"  host prelude   {HOST_PRELUDE} "
          f"({rep.host_runtime} runtime declarations, {rep.host_meta} metaprogramming "
          f"after `{RUNTIME_END}`)")
    print(f"  embedded       {FRONTEND}:{rep.embedded_line} (preludeText, "
          f"{len(rep.embedded.decls)} declarations)")
    for note in PAGE_NOTES:
        print(f"  page           {note}")
    print(f"  coverage       {rep.covered}/{rep.host_runtime} runtime declarations "
          f"embedded; {len(rep.classes)} classes and {len(rep.exempted)} other "
          "reviewed gaps")
    for d in rep.exempted:
        print(f"                   gap {d.kind} {d.name} ({HOST_PRELUDE}:{d.line}): "
              f"{squash(EXEMPT.get(d.name, ''))}")
    if verbose:
        print(f"                   embedded: "
              f"{', '.join(sorted(rep.embedded.by_name()))}")
    names = rep.embedded.names()
    print(f"  origin         {len(names) - len(rep.embedded_only)} names declared "
          f"under lib/; {len(rep.embedded_only)} embedded-only (reviewed)")
    for name in rep.embedded_only:
        print(f"                   own {name}: {squash(EMBEDDED_ONLY.get(name, ''))}")
    total = sum(len(v) for v in rep.promoted.values())
    print(f"  promoted       {total} names the page has with `import Prelude` that "
          f"{HOST_PRELUDE} does not declare")
    for path in sorted(rep.promoted):
        group = rep.promoted[path]
        shown = ", ".join(group) if verbose or len(group) <= 8 else ""
        print(f"                   {path}: {len(group)}" + (f" ({shown})" if shown else ""))
    if not rep.ok:
        print()
        print(f"DRIFT: {len(rep.problems)} problem(s)")
        for p in rep.problems:
            print(f"  [{p.invariant}] {p.message}")


def page_copy_note(root: Path) -> list[str]:
    """How the WebAssembly page gets this prelude, and a guard against a second copy.

    The page has no separate prelude: `web/build-playground.sh` concatenates
    `frontendFiles` (which includes `selfhost/Frontend.wiz`, whose `preludeText` is the
    embedded copy) and the page's shim prepends `import Prelude`. A `.wiz` file under
    `web/` whose name mentions prelude would be a second copy, which this check would
    not see: fail instead of silently comparing the wrong thing."""
    stray = sorted(str(p.relative_to(root)) for p in (root / "web").rglob("*.wiz")
                   if "prelude" in p.name.lower())
    if stray:
        raise CheckError(
            f"a page-local prelude copy appeared: {', '.join(stray)}. The page must "
            "use selfhost/Frontend.wiz's preludeText (web/build-playground.sh, "
            "web/selfhost-lsp-shim.js); delete the copy or extend this check.")
    notes = []
    build = (root / "web/build-playground.sh")
    shim = (root / "web/selfhost-lsp-shim.js")
    if build.is_file() and "frontendFiles" in build.read_text(encoding="utf-8"):
        notes.append("web/build-playground.sh compiles frontendFiles")
    if shim.is_file() and "import Prelude" in shim.read_text(encoding="utf-8"):
        notes.append("web/selfhost-lsp-shim.js injects `import Prelude`")
    return notes


def read_checkout(root: Path) -> tuple[str, str, dict[str, str], int]:
    host_path = root / HOST_PRELUDE
    front_path = root / FRONTEND
    for p in (host_path, front_path):
        if not p.is_file():
            raise CheckError(f"{p}: not found (run from a checkout, or pass --root)")
    frontend = front_path.read_text(encoding="utf-8")
    if not any(mark in frontend for mark in LOADER_MARKERS):
        raise CheckError(
            f"{FRONTEND}: preludeText is defined but the module loader no longer "
            f"mentions it (looked for {', '.join(LOADER_MARKERS)}). If the loader "
            "changed, update this check: the embedded copy it compares may be dead.")
    line = next(i + 1 for i, l in enumerate(frontend.split("\n"))
                if l.startswith("def preludeText : String"))
    if not (root / "lib").is_dir():
        raise CheckError(f"{root}/lib: not found (--root must name a checkout)")
    lib_texts = {str(p.relative_to(root)): p.read_text(encoding="utf-8")
                 for p in sorted((root / "lib").rglob("*.wiz"))}
    return (host_path.read_text(encoding="utf-8"),
            decode_prelude_text(frontend, FRONTEND), lib_texts, line)


# `--self-test` fixtures. They are deliberately small and local: the check's rules are
# what is under test, not the repository.
_FIXTURE_HOST = """\
inductive Nat where
  | zero
  | succ (n : Nat)
def Nat.add : Nat → Nat → Nat
  | .zero, n => n
  | .succ m, n => .succ (Nat.add m n)
-- (end of the Boolean section)
inductive Expr where
  | var (i : Nat)
"""
_FIXTURE_EMBEDDED = """\
inductive Nat where
  | zero
  | succ (n : Nat)
def Nat.add : Nat → Nat → Nat
  | .zero, n => n
  | .succ m, n => .succ (Nat.add m n)
"""
_FIXTURE_LIB = {"lib/Prelude.wiz": _FIXTURE_HOST}


def self_test() -> int:
    failures: list[str] = []

    def expect(name: str, ok: bool, detail: str = "") -> None:
        print(f"  {'ok  ' if ok else 'FAIL'} {name}")
        if not ok:
            failures.append(f"{name}{': ' + detail if detail else ''}")

    try:
        rep = compare(_FIXTURE_HOST, _FIXTURE_EMBEDDED, _FIXTURE_LIB,
                      exempt={}, embedded_only={}, meta_roots={"Expr"})
        expect("clean fixture passes", rep.ok, str([p.message for p in rep.problems]))
        expect("clean fixture covers the runtime surface", rep.covered == 2,
               f"covered {rep.covered}")

        drifted = _FIXTURE_HOST.replace(
            "def Nat.add", "def List.filter {A : Type} (p : A → Bool) : List A → List A\n"
            "  | .nil => .nil\ndef Nat.add")
        rep = compare(drifted, _FIXTURE_EMBEDDED, {"lib/Prelude.wiz": drifted},
                      exempt={}, embedded_only={}, meta_roots={"Expr"})
        expect("a new library name fails coverage",
               any("List.filter" in p.message for p in rep.problems))

        invented = _FIXTURE_EMBEDDED + "def Bytes.totallyNew : Nat := 0\n"
        rep = compare(_FIXTURE_HOST, invented, _FIXTURE_LIB,
                      exempt={}, embedded_only={}, meta_roots={"Expr"})
        expect("an invented embedded name fails origin",
               any("Bytes.totallyNew" in p.message for p in rep.problems))

        appended = _FIXTURE_HOST + "def Rat.add : Nat → Nat → Nat\n  | a, _ => a\n"
        rep = compare(appended, _FIXTURE_EMBEDDED,
                      {"lib/Prelude.wiz": appended},
                      exempt={}, embedded_only={}, meta_roots={"Expr"})
        expect("a runtime declaration after the marker fails",
               any(p.invariant == "surface" and "Rat.add" in p.message
                   for p in rep.problems))

        wrong_kind = _FIXTURE_EMBEDDED.replace("def Nat.add", "axiom Nat.add")
        rep = compare(_FIXTURE_HOST, wrong_kind, _FIXTURE_LIB,
                      exempt={}, embedded_only={}, meta_roots={"Expr"})
        expect("a changed kind fails coverage",
               any("is axiom" in p.message for p in rep.problems))

        wrong_ctor = _FIXTURE_EMBEDDED.replace("  | succ (n : Nat)\n", "")
        rep = compare(_FIXTURE_HOST, wrong_ctor, _FIXTURE_LIB,
                      exempt={}, embedded_only={}, meta_roots={"Expr"})
        expect("a lost constructor fails coverage",
               any("has (zero, succ)" in p.message for p in rep.problems))

        rep = compare(_FIXTURE_HOST, _FIXTURE_EMBEDDED, _FIXTURE_LIB,
                      exempt={"pipe": "test entry"}, embedded_only={}, meta_roots={"Expr"})
        expect("a stale exemption fails",
               any(p.invariant == "staleness" and "pipe" in p.message
                   for p in rep.problems))

        host_with_pred = _FIXTURE_HOST.replace(
            "def Nat.add",
            "def Nat.pred : Nat → Nat\n  | .zero => .zero\n  | .succ n => n\ndef Nat.add")
        rep = compare(host_with_pred, _FIXTURE_EMBEDDED,
                      {"lib/Prelude.wiz": host_with_pred},
                      exempt={"Nat.pred": "test entry"}, embedded_only={}, meta_roots={"Expr"})
        expect("an exemption for a missing declaration is clean",
               rep.ok, str([p.message for p in rep.problems]))

        rep = compare(_FIXTURE_HOST, _FIXTURE_EMBEDDED, _FIXTURE_LIB,
                      exempt={}, embedded_only={"Nat.add": "redundant"},
                      meta_roots={"Expr"})
        expect("an embedded-only entry for a declared name fails",
               any(p.invariant == "staleness" and "Nat.add" in p.message
                   for p in rep.problems))
    except CheckError as err:
        expect("fixtures run", False, str(err))

    print(f"  {len(failures)} failure(s)")
    return 1 if failures else 0


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(
        description="Compare the self-hosted frontend's embedded prelude "
                    "(preludeText) with lib/Prelude.wiz.")
    ap.add_argument("--root", type=Path, default=ROOT,
                    help="the checkout to check (default: this script's checkout)")
    ap.add_argument("--self-test", action="store_true",
                    help="run the built-in fixtures and exit")
    ap.add_argument("--verbose", action="store_true",
                    help="list every promoted and embedded name")
    ap.add_argument("--dump-embedded", action="store_true",
                    help="print the decoded preludeText and exit")
    ap.add_argument("--quiet", action="store_true", help="only the verdict")
    args = ap.parse_args(argv)

    try:
        if args.self_test:
            return self_test()
        PAGE_NOTES[:] = page_copy_note(args.root)
        host, embedded, libs, line = read_checkout(args.root)
        if args.dump_embedded:
            sys.stdout.write(embedded)
            return 0
        rep = compare(host, embedded, libs, embedded_line=line)
    except CheckError as err:
        print(f"check-prelude-drift: {err}", file=sys.stderr)
        return 2
    if not args.quiet:
        print_report(rep, args.verbose)
    if rep.ok:
        if not args.quiet:
            print("  ok: the embedded prelude's surface is in sync")
        return 0
    if args.quiet:
        for p in rep.problems:
            print(f"[{p.invariant}] {p.message}")
    return 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
