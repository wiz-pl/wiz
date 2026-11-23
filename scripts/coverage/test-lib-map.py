#!/usr/bin/env python3
"""Static test-suite reach into `lib/*.wiz`.

This is a lexical map, not an execution profile: it answers "which library modules
and declarations does the checked-in test corpus name or import?" so a coverage
number can be read against a denominator. It is deliberately conservative about what
it claims:

  * `direct` means an `import M` line occurs in the corpus; `closure` means M is
    reachable through the import graph from those roots (lib, hdl/src, scry/src,
    selfhost and drafts/feral/lib modules are all in the graph).
  * `lex` counts a declaration when its **qualified** name (or its bare name, for the
    13% of declarations that are not qualified) occurs as a token anywhere in the
    corpus. Comments and doc prose still count, so this is an **upper bound**. The
    weaker `any` column (the last component of every name, so `get`/`map`/`size`
    match everywhere) is shown only to make the difference visible.
  * `groups` is the number of `Tests/Groups/*.lean` files that import the module or
    contain one of its qualified declaration names. Same lexical caveat.

Options:
  --root DIR     another checkout (default: the repository containing this script)
  --json         print the machine-readable map
  --markdown     print the two Markdown tables (module and group) and the summary
  --corpus LIST  comma-separated corpus roots (default:
                 Tests,examples,hdl/examples,drafts/feral)

Exit status: 0 the map was produced; 2 a root or file could not be read.
"""

from __future__ import annotations

import argparse
import collections
import json
import re
import sys
from pathlib import Path

DECL_KINDS = (
    "def",
    "theorem",
    "opaque",
    "abbrev",
    "class",
    "structure",
    "inductive",
    "axiom",
)
UNNAMED_KINDS = (
    "instance",
    "syntax",
    "macro",
    "elab",
    "builtin",
    "extern",
    "foreign",
    "primitive",
    "mutual",
)
PREFIXES = (
    "private",
    "protected",
    "noncomputable",
    "partial",
    "unsafe",
    "scoped",
    "local",
    "public",
)
DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:"
    + "|".join(PREFIXES)
    + r")\s+)*("
    + "|".join(DECL_KINDS + UNNAMED_KINDS)
    + r")\b\s*(.*)$"
)
IDENT = re.compile(r"^[A-Za-z_][A-Za-z0-9_'.]*$")
IMPORT = re.compile(r"^\s*import\s+([A-Za-z0-9_.]+)", re.M)
TOKEN = re.compile(r"[A-Za-z_][A-Za-z0-9_'.]*")

SUFFIXES = {".lean", ".wiz", ".expected", ".tsv", ".json", ".txt", ".md", ".c", ".h"}


def fail(msg: str) -> "NoReturn":  # type: ignore[name-defined]
    print(f"test-lib-map: {msg}", file=sys.stderr)
    raise SystemExit(2)


def declarations(path: Path) -> tuple[int, list[str]]:
    """(all declaration lines, named declarations) in one .wiz module."""
    total = 0
    named: list[str] = []
    for line in path.read_text(encoding="utf-8", errors="replace").splitlines():
        m = DECL.match(line)
        if not m:
            continue
        total += 1
        if m.group(1) not in DECL_KINDS:
            continue
        rest = m.group(2).strip()
        if not rest:
            continue
        name = rest.split()[0].rstrip(":=").strip()
        if IDENT.match(name):
            named.append(name)
    return total, named


def module_roots(root: Path) -> dict[str, Path]:
    """Import name -> source, exactly as `Tests/Loader.lean`'s loader sees the roots."""
    roots = [
        ("lib", ""),
        ("hdl/src", ""),
        ("scry/src", ""),
        ("drafts/feral/lib", ""),
        ("selfhost", ""),
    ]
    out: dict[str, Path] = {}
    for rel, pfx in roots:
        d = root / rel
        if not d.exists():
            continue
        for p in sorted(d.rglob("*.wiz")):
            name = ".".join(p.relative_to(d).with_suffix("").parts)
            out.setdefault(pfx + name, p)
    return out


def corpus_files(root: Path, corpus: list[str]) -> list[Path]:
    out: list[Path] = []
    for rel in corpus:
        d = root / rel
        if not d.exists():
            continue
        if d.is_file():
            if d.suffix in SUFFIXES:
                out.append(d)
        else:
            for p in d.rglob("*"):
                if p.is_file() and p.suffix in SUFFIXES:
                    out.append(p)
    return sorted(set(out))


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[2])
    ap.add_argument("--json", action="store_true")
    ap.add_argument("--markdown", action="store_true")
    ap.add_argument(
        "--corpus",
        default="Tests,examples,hdl/examples,drafts/feral",
        help="comma-separated corpus roots",
    )
    args = ap.parse_args()
    root = args.root.resolve()
    corpus_roots = [c.strip() for c in args.corpus.split(",") if c.strip()]

    lib = root / "lib"
    if not lib.exists():
        fail(f"{lib} does not exist (wrong --root?)")
    modules = module_roots(root)
    if not modules:
        fail("no .wiz modules found")

    # Declarations, per module.
    lib_modules: dict[str, dict] = {}
    all_decls: list[tuple[str, str]] = []
    for name, path in sorted(modules.items()):
        if not str(path).startswith(str(lib) + "/"):
            continue
        total, named = declarations(path)
        lib_modules[name] = {
            "file": str(path.relative_to(root)),
            "declarations": total,
            "named": len(named),
            "names": named,
        }
        all_decls += [(name, n) for n in named]

    # Corpus text and tokens.
    files = corpus_files(root, corpus_roots)
    text_parts: list[str] = []
    for p in files:
        try:
            text_parts.append(p.read_text(encoding="utf-8", errors="replace"))
        except OSError as exc:
            fail(f"cannot read {p}: {exc}")
    text = "\n".join(text_parts)
    tokens = collections.Counter(TOKEN.findall(text))
    token_set = set(tokens)

    imports = collections.Counter(IMPORT.findall(text))
    graph = {name: [i for i in IMPORT.findall(p.read_text(encoding="utf-8", errors="replace"))
                    if i in modules]
             for name, p in modules.items()}
    roots = [m for m in imports if m in modules]
    closure: set[str] = set()
    stack = list(roots)
    while stack:
        m = stack.pop()
        if m in closure:
            continue
        closure.add(m)
        stack += graph.get(m, [])

    # Per-module lexical hits: the strong metric uses the qualified name (or the
    # bare name when it has no dot); the weak one also accepts the last component.
    direct = {m for m in lib_modules if m in imports}
    for m, d in lib_modules.items():
        hit = 0
        any_hit = 0
        refs = 0
        for n in d["names"]:
            last = n.rsplit(".", 1)[-1]
            strong = n in token_set
            weak = strong or last in token_set
            if strong:
                hit += 1
                refs += tokens.get(n, 0)
            if weak:
                any_hit += 1
        d["lex"] = hit
        d["lex_any"] = any_hit
        d["refs"] = refs
        d["direct"] = m in direct
        d["closure"] = m in closure
        d["groups"] = 0

    # Group files: name/exercise/case count, and declarations they contain.
    groups = []
    group_dir = root / "Tests" / "Groups"
    for p in sorted(group_dir.glob("*.lean")) if group_dir.exists() else []:
        src = p.read_text(encoding="utf-8", errors="replace")
        gtok = set(TOKEN.findall(src))
        gimports = set(IMPORT.findall(src))
        # A group definition is `name := "…"` (at two spaces, or inside `{ … }`)
        # followed within a few lines by `exercise := "…"`; a case is `{ name := …,
        # run := …`. Look backwards from each exercise line so `parallel := true`
        # (grail) and `{ name :=` (scry-uaf) both work.
        names: list[tuple[str, str]] = []
        lines = src.splitlines()
        for i, line in enumerate(lines):
            if "exercise :=" not in line:
                continue
            for j in range(i - 1, max(i - 6, -1), -1):
                prev = lines[j]
                if "name :=" in prev and "run :=" not in prev:
                    names.append(
                        (
                            re.search(r'name := "([^"]+)"', prev).group(1),
                            re.search(r'exercise := "([^"]*)"', line).group(1),
                        )
                    )
                    break
        cases = len(re.findall(r"^    \{ name := |^  \{ name := ", src, re.M))
        touched = 0
        for m, d in lib_modules.items():
            if m in gimports or any(n in gtok for n in d["names"]):
                d["groups"] += 1
                touched += 1
        groups.append(
            {
                "file": str(p.relative_to(root)),
                "groups": names,
                "cases": cases,
                "lib_modules": touched,
            }
        )

    total_named = len(all_decls)
    total_lex = sum(1 for m, n in all_decls if n in token_set)
    total_any = sum(
        1
        for m, n in all_decls
        if n in token_set or n.rsplit(".", 1)[-1] in token_set
    )
    summary = {
        "root": str(root),
        "corpus_roots": corpus_roots,
        "corpus_files": len(files),
        "lib_modules": len(lib_modules),
        "lib_declarations": sum(d["declarations"] for d in lib_modules.values()),
        "lib_named_declarations": total_named,
        "lex_referenced": total_lex,
        "lex_percent": round(100.0 * total_lex / total_named, 1) if total_named else 0.0,
        "lex_any_referenced": total_any,
        "lex_any_percent": round(100.0 * total_any / total_named, 1) if total_named else 0.0,
        "direct_imports": len(direct),
        "closure_imports": sum(1 for m in lib_modules if m in closure),
        "group_files": len(groups),
        "group_definitions": sum(len(g["groups"]) for g in groups),
        "all_lib_sweep": "allLibSource" in text or "libModuleNames" in text,
    }
    result = {"summary": summary, "modules": lib_modules, "groups": groups}

    if args.json:
        print(json.dumps(result, indent=1, sort_keys=True))
        return 0

    if args.markdown:
        print("### Library modules\n")
        print("| module | file | decls | named | lex-hit | lex% | any-hit | direct | closure | group files |")
        print("|---|---|---:|---:|---:|---:|---:|:--:|:--:|---:|")
        for m in sorted(lib_modules):
            d = lib_modules[m]
            pct = 100.0 * d["lex"] / d["named"] if d["named"] else 0.0
            print(
                f"| `{m}` | `{d['file']}` | {d['declarations']} | {d['named']} | "
                f"{d['lex']} | {pct:.0f}% | {d['lex_any']} | "
                f"{'yes' if d['direct'] else ''} | "
                f"{'yes' if d['closure'] else ''} | {d['groups']} |"
            )
        print("\n### Test groups\n")
        print("| file | group(s) | cases | lib modules named |")
        print("|---|---|---:|---:|")
        for g in groups:
            gs = "; ".join(f"`{n}`" for n, _ in g["groups"]) or "—"
            print(f"| `{g['file']}` | {gs} | {g['cases']} | {g['lib_modules']} |")
        print("\n### Exercises named by the group definitions\n")
        for g in groups:
            for n, e in g["groups"]:
                print(f"- `{n}` ({g['file']}): {e}")
        print("\n### Summary\n")
        for k, v in summary.items():
            print(f"- `{k}`: {v}")
        return 0

    print(
        f"{summary['lib_modules']} lib modules, {summary['lib_declarations']} declaration "
        f"lines ({summary['lib_named_declarations']} named)"
    )
    print(
        f"corpus: {summary['corpus_files']} files from {', '.join(corpus_roots)}; "
        f"{summary['direct_imports']} lib modules imported directly, "
        f"{summary['closure_imports']} reachable through the import graph"
    )
    print(
        f"lexical declaration hits (qualified name): {summary['lex_referenced']}/"
        f"{summary['lib_named_declarations']} ({summary['lex_percent']}%) "
        "[upper bound: comments count]"
    )
    print(
        f"  weaker any-component hits: {summary['lex_any_referenced']}/"
        f"{summary['lib_named_declarations']} ({summary['lex_any_percent']}%)"
    )
    print(
        f"groups: {summary['group_definitions']} definitions in "
        f"{summary['group_files']} files"
    )
    print(f"all-lib elaboration sweep present: {summary['all_lib_sweep']}")
    print()
    print(f"{'module':28} {'named':>5} {'lex':>5} {'any':>5} {'grp':>4}  flags")
    for m in sorted(lib_modules):
        d = lib_modules[m]
        flags = ("direct " if d["direct"] else "") + ("closure" if d["closure"] else "")
        print(
            f"{m:28} {d['named']:5d} {d['lex']:5d} {d['lex_any']:5d} "
            f"{d['groups']:4d}  {flags}"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
