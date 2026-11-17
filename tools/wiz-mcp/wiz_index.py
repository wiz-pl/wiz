"""wiz_index: a read-only index of a Wiz library, for the MCP `search` and `doc` tools.

Two sources, both read-only:

* **The source scan** (always available, no `wiz` process): every `.wiz` file under
  the library roots is read and its top-level declarations are found by their
  header (`def`, `structure`, `inductive`, `class`, `instance`, `axiom`, `extern`,
  `lemma`, …), with the doc comment written just before it, the header's
  signature text, its file and line, and the constructors of an `inductive` and
  the fields of a `structure`. Files are re-read only when their size or mtime
  changes.
* **An elaborated index** (optional): the `api.json` that `wiz doc --lib -o DIR`
  writes (rows `{name, module, kind, sig, doc}`), given with `--doc-index`. Its
  signatures are the elaborated types (`Nat → Nat → Nat`), so type search is
  better; positions still come from the source scan. Building it takes minutes,
  so the server never builds it: a person or CI does, under the scheduler.

Type search is a heuristic ("unification-lite"), not unification: a type is split
into its top-level arrow components; type variables (single letters, Greek
letters, implicit binders) match any component consistently, `_` and `?x` in the
query are wildcards, and a match with the arguments in another order ranks
lower. Everything here is a pure function of the files, so it is easy to test.
"""

from __future__ import annotations

import json
import os
import re
from dataclasses import dataclass, field
from typing import Any, Iterable, Optional

#: Declaration keywords at the start of a line, after attributes and modifiers.
HEADER = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:private|protected|noncomputable|partial|unsafe|opaque)\s+)*"
    r"(def|lemma|theorem|abbrev|structure|class|inductive|coinductive|axiom|instance|extern)\b(.*)$"
)
NAME = re.compile(r"[^\s(){}\[\]:,⦃⦄]+")
IDENT = re.compile(r"[A-Za-z_Ͱ-Ͽἀ-῿][\w.'Ͱ-Ͽ₀-ₜ!?]*")
VARIABLE = re.compile(r"^(?:[a-zA-Z]|[Ͱ-Ͽἀ-῿])[0-9'₀-₉]*$")
MAX_SIG = 600


@dataclass
class Decl:
    name: str
    kind: str
    module: str
    file: str
    line: int  # 1-based
    sig: str = ""  # the header's signature text, or the elaborated type
    doc: str = ""
    parent: Optional[str] = None
    elaborated: bool = False

    def row(self, full_doc: bool = False) -> dict[str, Any]:
        doc = self.doc if full_doc else summary(self.doc)
        out = {
            "name": self.name,
            "kind": self.kind,
            "module": self.module,
            "signature": self.sig,
            "type": arrow_type(self.sig),
            "doc": doc,
            "file": self.file,
            "line": self.line,
        }
        if self.parent:
            out["parent"] = self.parent
        return out


def summary(doc: str, limit: int = 240) -> str:
    """The first paragraph of a doc comment, on one line."""
    first = doc.strip().split("\n\n", 1)[0]
    first = " ".join(first.split())
    return first if len(first) <= limit else first[: limit - 1] + "…"


# ---------------------------------------------------------------------------
# Scanning source


def _strip_line_comment(line: str) -> str:
    # `--` outside a string starts a comment (strings rarely hold `--` in headers).
    index = line.find("--")
    return line if index < 0 else line[:index]


def _clean_doc(text: str) -> str:
    lines = text.split("\n")
    stripped = [line.strip() for line in lines]
    return "\n".join(stripped).strip()


def scan_source(text: str, module: str, file: str) -> tuple[str, list[Decl]]:
    """The module doc (`/-! … -/`) and the top-level declarations of one file."""
    decls: list[Decl] = []
    module_doc = ""
    pending_doc: Optional[str] = None
    lines = text.split("\n")
    i = 0
    depth = 0  # nesting of ordinary block comments
    while i < len(lines):
        line = lines[i]
        if depth == 0 and (line.lstrip().startswith("/--") or line.lstrip().startswith("/-!")):
            is_module_doc = line.lstrip().startswith("/-!")
            body = []
            rest = line.lstrip()[3:]
            j = i
            while True:
                end = rest.find("-/")
                if end >= 0:
                    body.append(rest[:end])
                    break
                body.append(rest)
                j += 1
                if j >= len(lines):
                    break
                rest = lines[j]
            doc = _clean_doc("\n".join(body))
            if is_module_doc:
                if not module_doc:
                    module_doc = doc
            else:
                pending_doc = doc
            i = j + 1
            continue
        # ordinary block comments (they may nest)
        k = 0
        if depth or "/-" in line:
            while k < len(line):
                if line.startswith("/-", k):
                    depth += 1
                    k += 2
                elif line.startswith("-/", k) and depth:
                    depth -= 1
                    k += 2
                else:
                    k += 1
            if depth or line.lstrip().startswith("/-"):
                i += 1
                continue
        match = HEADER.match(line)
        if not match:
            if line.strip() and not line.startswith((" ", "\t")):
                pending_doc = None  # a doc comment belongs to the very next declaration
            i += 1
            continue
        kind, rest = match.group(1), match.group(2)
        start_line = i + 1
        # the header: this line and its indented continuation, up to `:=`/`where`/`|`
        header = _strip_line_comment(rest)
        j = i + 1
        while j < len(lines) and not re.search(r":=|\bwhere\b", header):
            nxt = lines[j]
            if not nxt.startswith((" ", "\t")) or nxt.lstrip().startswith(("|", "--")):
                break
            header += " " + _strip_line_comment(nxt).strip()
            j += 1
        header = re.split(r":=|\bwhere\b", header, maxsplit=1)[0]
        name, sig = _name_and_sig(kind, header)
        if kind == "extern":
            kind = "extern"
        decl = Decl(name or f"(instance) {sig.strip()[:80]}", kind, module, file, start_line,
                    sig=_squash(sig), doc=pending_doc or "")
        decls.append(decl)
        pending_doc = None
        # children: constructors of an inductive, fields of a structure/class
        k = j
        if kind in ("inductive", "coinductive", "structure", "class") and name:
            k = _children(lines, i + 1, decl, decls)
        i = max(i + 1, k if kind in ("inductive", "coinductive", "structure", "class") else i + 1)
    return module_doc, decls


def _squash(text: str) -> str:
    text = " ".join(text.split())
    return text if len(text) <= MAX_SIG else text[: MAX_SIG - 1] + "…"


def _name_and_sig(kind: str, header: str) -> tuple[Optional[str], str]:
    # universe parameters (`Inhabited.{u}`) are not part of the name
    header = re.sub(r"\.\{[^}]*\}", "", header.strip())
    if kind == "extern":
        header = re.sub(r'^"[^"]*"\s*', "", header)
    if kind == "instance":
        # `instance name : C T` or `instance {…} : C T` or `instance : C T`
        found = re.match(r"^([^\s:{}\[\]()]+)\s*(.*)$", header)
        if found and found.group(1) not in (":",) and not found.group(1).startswith(("{", "[", "(")):
            return found.group(1), found.group(2)
        return None, header
    found = NAME.match(header)
    if not found:
        return None, header
    return found.group(0), header[found.end():]


def _children(lines: list[str], start: int, parent: Decl, out: list[Decl]) -> int:
    """Constructors (`| c …`) and fields (`  x : T`) under a type; returns the next line."""
    j = start
    doc: Optional[str] = None
    while j < len(lines):
        raw = lines[j]
        if raw.strip() == "":
            j += 1
            continue
        if not raw.startswith((" ", "\t")) and not raw.startswith("|"):
            break
        text = raw.strip()
        if text.startswith("/--"):
            end = text.find("-/", 3)
            doc = _clean_doc(text[3:end]) if end >= 0 else _clean_doc(text[3:])
            j += 1
            continue
        if text.startswith("|"):
            found = NAME.match(text[1:].strip())
            if found:
                name = found.group(0).lstrip(".")
                sig = text[1:].strip()[found.end():]
                sig = _squash(_strip_line_comment(sig))
                if not _binders_and_rest(sig)[1].startswith(":"):
                    # `| succ (n : Nat)`: the result is the type itself, applied to its parameters
                    params = " ".join(_explicit_names(parent.sig))
                    sig = f"{sig} : {parent.name}{' ' + params if params else ''}".strip()
                out.append(Decl(f"{parent.name}.{name}", "constructor", parent.module, parent.file, j + 1,
                                sig=sig, doc=doc or "", parent=parent.name))
        else:
            field_match = re.match(r"^([^\s:(){}\[\]]+)\s*(?:\([^)]*\)\s*)*:\s*(.+)$", _strip_line_comment(text))
            if field_match and parent.kind in ("structure", "class") and not field_match.group(1).endswith("::"):
                out.append(Decl(f"{parent.name}.{field_match.group(1)}", "field", parent.module, parent.file, j + 1,
                                sig=": " + _squash(field_match.group(2)), doc=doc or "", parent=parent.name))
        doc = None
        j += 1
    return j


# ---------------------------------------------------------------------------
# Types


def _split_top(text: str, sep: str) -> list[str]:
    parts, depth, cur = [], 0, []
    i = 0
    while i < len(text):
        ch = text[i]
        if ch in "([{⦃":
            depth += 1
        elif ch in ")]}⦄":
            depth -= 1
        if depth == 0 and text.startswith(sep, i):
            parts.append("".join(cur).strip())
            cur = []
            i += len(sep)
            continue
        cur.append(ch)
        i += 1
    parts.append("".join(cur).strip())
    return parts


def _binders_and_rest(sig: str) -> tuple[list[tuple[str, str]], str]:
    """The leading binder groups of a header, as (bracket, contents), and what follows."""
    s = " ".join(sig.replace("->", "→").split())
    groups: list[tuple[str, str]] = []
    while s and s[0] in "({[⦃":
        close = {"(": ")", "{": "}", "[": "]", "⦃": "⦄"}[s[0]]
        depth, k = 0, 0
        for k, ch in enumerate(s):
            if ch == s[0]:
                depth += 1
            elif ch == close:
                depth -= 1
                if depth == 0:
                    break
        groups.append((s[0], s[1:k]))
        s = s[k + 1:].lstrip()
    return groups, s


def _explicit_names(sig: str) -> list[str]:
    """The names of a header's explicit `( … )` binders (a type's parameters)."""
    names: list[str] = []
    for bracket, group in _binders_and_rest(sig)[0]:
        if bracket == "(" and ":" in group:
            names += group.split(":", 1)[0].split()
    return names


def arrow_type(sig: str) -> str:
    """A header's signature as an arrow type: `(a b : T) {A : Type} : R` is `T → T → R`.

    Implicit `{…}`/`⦃…⦄` and instance `[…]` binders are dropped; an explicit
    binder group contributes its type once per name. An already-arrow signature
    (`: Nat → Nat`) is returned without its colon.
    """
    s = " ".join(sig.replace("->", "→").split())
    args: list[str] = []
    while s and s[0] in "({[⦃":
        close = {"(": ")", "{": "}", "[": "]", "⦃": "⦄"}[s[0]]
        depth, k = 0, 0
        for k, ch in enumerate(s):
            if ch == s[0]:
                depth += 1
            elif ch == close:
                depth -= 1
                if depth == 0:
                    break
        group, s = s[1:k], s[k + 1:].lstrip()
        if close != ")":
            continue
        names_ty = _split_top(group, " : ") if " : " in group else _split_top(group, ":")
        if len(names_ty) >= 2:
            names = names_ty[0].split()
            ty = ":".join(names_ty[1:]).strip()
            args += [ty] * max(1, len(names))
    if s.startswith(":"):
        s = s[1:].strip()
    result = s
    wrapped = [a if " → " not in a or (a.startswith("(") and _balanced(a[1:-1])) else f"({a})" for a in args]
    return " → ".join(wrapped + ([result] if result else [])) if args else result


def components(ty: str) -> list[str]:
    ty = " ".join(ty.replace("->", "→").split())
    while ty.startswith("(") and ty.endswith(")") and _balanced(ty[1:-1]):
        ty = ty[1:-1].strip()
    return [c for c in _split_top(ty, "→") if c]


def _balanced(text: str) -> bool:
    depth = 0
    for ch in text:
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
            if depth < 0:
                return False
    return depth == 0


def _tokens(component: str) -> list[str]:
    return re.findall(r"[()\[\]{}]|[^\s()\[\]{}]+", component)


def _is_wild(token: str) -> bool:
    return token == "_" or token.startswith("?")


def _is_var(token: str) -> bool:
    return bool(VARIABLE.match(token)) and token not in ("_",)


def _match_component(q: str, c: str, binding: dict[str, str]) -> bool:
    qt, ct = _tokens(q), _tokens(c)
    if len(qt) == 1 and (_is_wild(qt[0]) or _is_var(qt[0])):
        if _is_wild(qt[0]) and qt[0] == "_":
            return True
        bound = binding.get(qt[0])
        if bound is None:
            binding[qt[0]] = c
            return True
        return bound == c
    if len(qt) != len(ct):
        return False
    for a, b in zip(qt, ct):
        if _is_wild(a):
            continue
        if _is_var(a) and _is_var(b):
            bound = binding.get(a)
            if bound is None:
                binding[a] = b
            elif bound != b:
                return False
            continue
        if a != b:
            return False
    return True


def type_score(query: str, ty: str) -> int:
    """How well `ty` matches the type pattern `query` (0: not at all)."""
    if not ty:
        return 0
    q, c = components(query), components(ty)
    if " ".join(q) == " ".join(c):
        return 100
    if len(q) == len(c):
        binding: dict[str, str] = {}
        if all(_match_component(a, b, binding) for a, b in zip(q, c)):
            return 80
        # the same arguments in another order, the same result
        binding = {}
        if len(q) > 1 and _match_component(q[-1], c[-1], binding):
            rest = list(c[:-1])
            for a in q[:-1]:
                for k, b in enumerate(rest):
                    trial = dict(binding)
                    if _match_component(a, b, trial):
                        binding = trial
                        del rest[k]
                        break
                else:
                    break
            else:
                return 60
    # a suffix: the query is the type after some leading arguments
    if 1 < len(q) < len(c):
        binding = {}
        if all(_match_component(a, b, binding) for a, b in zip(q, c[-len(q):])):
            return 40
    # every constant of the query appears
    constants = {t for t in IDENT.findall(query) if not _is_var(t) and t != "_"}
    if constants and constants <= set(IDENT.findall(ty)):
        return 10
    return 0


# ---------------------------------------------------------------------------
# The index


#: Directories a workspace scan skips (build output, VCS, caches, dependencies).
SKIP_DIRS = {".git", ".lake", ".grail", ".scry-repl", "node_modules", "build", "dist", "result", "__pycache__"}
#: At most this many files per index (a guard against scanning a huge tree).
MAX_FILES = 5000


@dataclass
class LibraryIndex:
    roots: list[str]
    elaborated_file: Optional[str] = None
    #: a file is read only if this says so (the server passes its path confinement)
    allowed: Any = None
    _files: dict[str, tuple[int, int, str, list[Decl]]] = field(default_factory=dict)
    _elaborated: Optional[dict[str, dict[str, Any]]] = None
    _elaborated_stamp: Optional[tuple[int, int]] = None

    def modules(self) -> Iterable[tuple[str, str]]:
        """(module name, file) for every `.wiz` file under the roots."""
        count = 0
        for root in self.roots:
            for dirpath, dirnames, filenames in os.walk(root):  # never follows directory symlinks
                dirnames[:] = sorted(d for d in dirnames if not d.startswith(".") and d not in SKIP_DIRS)
                for filename in sorted(filenames):
                    if not filename.endswith(".wiz"):
                        continue
                    path = os.path.join(dirpath, filename)
                    if self.allowed is not None and not self.allowed(path):
                        continue  # a symlink out of the roots
                    count += 1
                    if count > MAX_FILES:
                        return
                    rel = os.path.relpath(path, root)[: -len(".wiz")]
                    yield rel.replace(os.sep, "."), path

    def refresh(self) -> None:
        seen = set()
        for module, path in self.modules():
            seen.add(path)
            try:
                st = os.stat(path)
            except OSError:
                continue
            cached = self._files.get(path)
            if cached and cached[0] == st.st_mtime_ns and cached[1] == st.st_size:
                continue
            try:
                with open(path, encoding="utf-8", errors="replace") as handle:
                    text = handle.read()
            except OSError:
                continue
            module_doc, decls = scan_source(text, module, path)
            self._files[path] = (st.st_mtime_ns, st.st_size, module_doc, decls)
        for path in list(self._files):
            if path not in seen:
                del self._files[path]
        self._load_elaborated()

    def _load_elaborated(self) -> None:
        if not self.elaborated_file:
            return
        if os.path.isdir(self.elaborated_file):
            self.elaborated_file = os.path.join(self.elaborated_file, "api.json")
        try:
            st = os.stat(self.elaborated_file)
        except OSError:
            self._elaborated = None
            return
        stamp = (st.st_mtime_ns, st.st_size)
        if stamp == self._elaborated_stamp:
            return
        with open(self.elaborated_file, encoding="utf-8") as handle:
            rows = json.load(handle)
        if isinstance(rows, dict):
            rows = rows.get("decls") or rows.get("rows") or []
        self._elaborated = {
            str(row.get("name")): row for row in rows if isinstance(row, dict) and row.get("name")
        }
        self._elaborated_stamp = stamp

    def decls(self) -> list[Decl]:
        out: list[Decl] = []
        for _, _, _, decls in self._files.values():
            out.extend(decls)
        if self._elaborated:
            for decl in out:
                row = self._elaborated.get(decl.name)
                if row:
                    sig = str(row.get("sig") or "")
                    if sig:
                        decl.sig = sig if sig.lstrip().startswith(":") else ": " + sig
                        decl.elaborated = True
                    if row.get("doc") and not decl.doc:
                        decl.doc = str(row["doc"])
        return out

    def module_doc(self, module: str) -> Optional[tuple[str, str, list[Decl]]]:
        for path, (_, _, doc, decls) in self._files.items():
            if decls and decls[0].module == module or (not decls and module_of(path, self.roots) == module):
                return path, doc, decls
        return None

    @property
    def source(self) -> str:
        return "elaborated" if self._elaborated else "source"


def module_of(path: str, roots: list[str]) -> Optional[str]:
    for root in roots:
        rel = os.path.relpath(path, root)
        if not rel.startswith(".."):
            return rel[: -len(".wiz")].replace(os.sep, ".")
    return None


def search(index: LibraryIndex, query: str, by: str = "name", limit: int = 20,
           kinds: Optional[set[str]] = None) -> tuple[list[dict[str, Any]], int]:
    """Ranked matches and the total number of matches."""
    scored: list[tuple[int, bool, int, str, Decl]] = []
    q = query.strip()
    ql = q.lower()
    for decl in index.decls():
        if kinds and decl.kind not in kinds:
            continue
        if by == "type":
            score = type_score(q, arrow_type(decl.sig))
        else:
            name = decl.name.lower()
            last = name.rsplit(".", 1)[-1]
            if name == ql or last == ql:
                score = 100
            elif last.startswith(ql) or name.startswith(ql):
                score = 70
            elif ql in name:
                score = 50
            elif _subsequence(ql, last):
                score = 20
            elif by == "text" and (ql in decl.doc.lower() or ql in decl.sig.lower()):
                score = 10
            else:
                score = 0
        if score:
            scored.append((-score, decl.module != "Prelude", len(decl.name), decl.name, decl))
    scored.sort(key=lambda item: item[:4])
    rows = []
    for neg, _, _, _, decl in scored[:limit]:
        row = decl.row()
        row["score"] = -neg
        rows.append(row)
    return rows, len(scored)


def _subsequence(needle: str, hay: str) -> bool:
    it = iter(hay)
    return len(needle) >= 3 and all(ch in it for ch in needle)
