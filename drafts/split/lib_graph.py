#!/usr/bin/env python3
"""Print the import graph of a Wiz library root (the numbers in lib-split.md).

Usage: python3 drafts/split/lib_graph.py [ROOT]     (default: lib)

Edges are `import M` between modules under ROOT, ignoring doc-comment code blocks.
`wiz`'s own loader is a line scan that *does* read doc-comment imports
(Wiz/Module.lean, `importsOf`); pass --with-doc-blocks to see that superset.
"""

import argparse
import os
import re
import sys
from collections import Counter, defaultdict

IMPORT = re.compile(r"import\s+([A-Za-z0-9_.']+)")


def strip_blocks(src: str) -> str:
    out = []
    i = 0
    depth = 0
    while i < len(src):
        if src.startswith("/-", i):
            depth += 1
            i += 2
        elif src.startswith("-/", i) and depth:
            depth -= 1
            i += 2
        elif depth:
            i += 1
        else:
            out.append(src[i])
            i += 1
    return "".join(out)


def imports_of(text: str) -> list[str]:
    return [m.group(1) for line in text.split("\n") for m in [IMPORT.match(line.strip())] if m]


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("root", nargs="?", default="lib")
    ap.add_argument("--with-doc-blocks", action="store_true")
    ap.add_argument("--table", action="store_true", help="one row per module")
    args = ap.parse_args()

    mods = {}
    for dirpath, _, files in os.walk(args.root):
        for f in files:
            if f.endswith(".wiz"):
                p = os.path.join(dirpath, f)
                mods[os.path.relpath(p, args.root)[:-4].replace("/", ".")] = p

    edges = defaultdict(set)
    for name, path in mods.items():
        text = open(path, encoding="utf-8").read()
        if not args.with_doc_blocks:
            text = strip_blocks(text)
        for m in imports_of(text):
            if m in mods and m != name:
                edges[name].add(m)

    lines = {n: sum(1 for _ in open(p, encoding="utf-8")) for n, p in mods.items()}
    indeg = Counter()
    for a, bs in edges.items():
        for b in bs:
            indeg[b] += 1

    # Tarjan, iterative enough for a library this size.
    sys.setrecursionlimit(10000)
    index, low, onstack, stack, counter, sccs = {}, {}, {}, [], [0], []

    def strong(v):
        index[v] = low[v] = counter[0]
        counter[0] += 1
        stack.append(v)
        onstack[v] = True
        for w in edges.get(v, ()):
            if w not in index:
                strong(w)
                low[v] = min(low[v], low[w])
            elif onstack.get(w):
                low[v] = min(low[v], index[w])
        if low[v] == index[v]:
            comp = []
            while True:
                w = stack.pop()
                onstack[w] = False
                comp.append(w)
                if w == v:
                    break
            sccs.append(comp)

    for v in mods:
        if v not in index:
            strong(v)
    cycles = [sorted(c) for c in sccs if len(c) > 1]

    print(f"modules      {len(mods)}")
    print(f"edges        {sum(len(v) for v in edges.values())}")
    print(f"cycles       {len(cycles)} {cycles if cycles else ''}")
    print(f"lines        {sum(lines.values())}")
    print("roots        " + ", ".join(sorted(m for m in mods if not edges.get(m))))
    print("top in-degree " + ", ".join(f"{m} {c}" for m, c in indeg.most_common(10)))
    ext = sorted({m for bs in edges.values() for m in bs if m not in mods})
    print("missing/external imports " + (", ".join(ext) or "—"))
    if args.table:
        print()
        print("| module | lines | imports |")
        print("|---|---:|---|")
        for m in sorted(mods):
            print(f"| `{m}` | {lines[m]} | {', '.join('`' + x + '`' for x in sorted(edges[m])) or '—'} |")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
