#!/usr/bin/env python3
"""The host-side unsafe ledger: every escape from Lean's guarantees in the host Lean code.

The trust ledger (`scripts/trust-ledger.sh`, `.github/trust-baseline.tsv`) covers the Wiz
sources of lib/. This one covers the Lean that implements Wiz: the `.lean` files under
Wiz/, Tests/ and Grail/, and those at the root (Main.lean, ...). A use is a declaration
whose code (not its comments or strings) has one of

  unsafe, unsafeBaseIO, unsafeIO, unsafeEIO, unsafeCast,
  implemented_by (in `@[...]` or `attribute [...]`), extern (in `@[...]` or `attribute [...]`)

and the ledger (.github/host-unsafe.tsv) has one row per use: the file, the declaration,
the constructs it uses (sorted, comma-separated) and, in one line, the invariant that makes
it sound (why the impure or unchecked code can't change a result it must not).

  scripts/host-unsafe-ledger.py --check     fail (exit 1) on an unlisted use, a stale row
                                            (the use is gone or uses other constructs) or a
                                            row without an invariant
  scripts/host-unsafe-ledger.py --print     the uses found, as ledger rows (TSV)
  options: --root DIR (default: the repository), --ledger FILE (default: ROOT/.github/host-unsafe.tsv)

Exit status: 0 clean, 1 a mismatch, 2 a usage or ledger-format error.
"""
import os
import re
import sys

KINDS_WORD = ["unsafe", "unsafeBaseIO", "unsafeIO", "unsafeEIO", "unsafeCast"]
DIRS = ["Wiz", "Tests", "Grail"]
DECL_KW = ("def|theorem|opaque|instance|abbrev|structure|inductive|class|axiom|"
           "initialize|builtin_initialize|example|macro|elab|syntax")
HEADER = re.compile(
    r"^[ \t]*(?:@\[[^\]\n]*\][ \t]*)*"
    r"(?:(?:private|protected|noncomputable|partial|unsafe|nonrec)[ \t]+)*"
    r"(?P<kw>" + DECL_KW + r")\b[ \t]*(?P<name>[^\s(:\[{]*)", re.M)
ATTR_CMD = re.compile(r"^[ \t]*attribute[ \t]*\[(?P<attrs>[^\]\n]*)\][ \t]*(?P<names>[^\n]*)", re.M)
ATTR = re.compile(r"@\[(?P<attrs>[^\]]*)\]")
IDENT = re.compile(r"[A-Za-z0-9_'.!?À-￿]")


def blank(text):
    """`text` with comments and string/char literals replaced by spaces (newlines kept)."""
    out = list(text)
    n = len(text)

    def wipe(a, b):
        for k in range(a, min(b, n)):
            if out[k] != "\n":
                out[k] = " "

    def ident_before(i):
        return i > 0 and IDENT.match(text[i - 1]) is not None

    def string_end(i, interp):
        """`text[i]` is the opening quote; returns the index after the closing one."""
        j = i + 1
        while j < n:
            c = text[j]
            if c == "\\":
                j += 2
                continue
            if c == '"':
                return j + 1
            if interp and c == "{":
                j = code_end(j + 1, "}")
                continue
            j += 1
        return n

    def code_end(i, close):
        """Scan code from `i` up to the matching `close` (or the end): returns the index
        after it. Used for `{…}` inside an interpolated string (blanked with the string)."""
        depth = 0
        j = i
        while j < n:
            c = text[j]
            if text.startswith("--", j):
                k = text.find("\n", j)
                j = n if k < 0 else k
            elif text.startswith("/-", j):
                j = block_end(j)
            elif c == '"':
                j = string_end(j, interp_before(j))
            elif c in "([{":
                depth += 1
                j += 1
            elif c in ")]}":
                if depth == 0 and c == close:
                    return j + 1
                depth -= 1
                j += 1
            else:
                j += 1
        return n

    def block_end(i):
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
                    return j
            else:
                j += 1
        return n

    def interp_before(i):
        return i >= 2 and text[i - 1] == "!" and text[i - 2] in "smf" and not ident_before(i - 2)

    i = 0
    while i < n:
        c = text[i]
        if text.startswith("--", i):
            k = text.find("\n", i)
            k = n if k < 0 else k
            wipe(i, k)
            i = k
        elif text.startswith("/-", i):
            k = block_end(i)
            wipe(i, k)
            i = k
        elif c == '"':
            start = i - 2 if interp_before(i) else i
            k = string_end(i, interp_before(i))
            wipe(start, k)
            i = k
        elif c == "r" and not ident_before(i) and re.match(r'r#*"', text[i:]):
            hashes = len(re.match(r"r(#*)", text[i:]).group(1))
            close = '"' + "#" * hashes
            k = text.find(close, i + 2 + hashes)
            k = n if k < 0 else k + len(close)
            wipe(i, k)
            i = k
        elif c == "'" and not ident_before(i):
            m = re.match(r"'(\\u\{[0-9a-fA-F]+\}|\\x[0-9a-fA-F]{2}|\\.|[^\\'\n])'", text[i:])
            if m:
                wipe(i, i + m.end())
                i += m.end()
            else:
                i += 1
        else:
            i += 1
    return "".join(out)


def uses_in(path, rel):
    """The uses in one file: {declaration: set of constructs}, in order of appearance."""
    with open(path, encoding="utf-8") as f:
        code = blank(f.read())
    # declaration spans: a header, extended upwards over the attribute lines just above it
    lines_start = [0] + [m.end() for m in re.finditer("\n", code)]
    heads = []
    for m in HEADER.finditer(code):
        start = m.start()
        line = code.count("\n", 0, start)
        while line > 0:
            prev = code[lines_start[line - 1]:lines_start[line]].strip()
            if prev.startswith("@[") and prev.endswith("]"):
                line -= 1
                start = lines_start[line]
            else:
                break
        name = m.group("name") or f"({m.group('kw')})"
        heads.append((start, name))
    for m in ATTR_CMD.finditer(code):
        names = m.group("names").split()
        heads.append((m.start(), names[-1] if names else "(attribute)"))
    heads.sort()
    hits = []
    for kind in KINDS_WORD:
        for m in re.finditer(r"(?<![A-Za-z0-9_'.])" + kind + r"(?![A-Za-z0-9_'])", code):
            hits.append((m.start(), kind))
    for pat in (ATTR, ATTR_CMD):
        for m in pat.finditer(code):
            for kind in ("implemented_by", "extern"):
                if re.search(r"(?<![A-Za-z0-9_.])" + kind + r"\b", m.group("attrs")):
                    hits.append((m.start(), kind))
    found = {}
    for pos, kind in hits:
        owner = None
        for start, name in heads:
            if start <= pos:
                owner = name
            else:
                break
        if owner is None:
            owner = "(top)"
        found.setdefault(owner, set()).add(kind)
    return found


def scan(root):
    files = []
    for name in sorted(os.listdir(root)):
        if name.endswith(".lean") and os.path.isfile(os.path.join(root, name)):
            files.append(name)
    for d in DIRS:
        base = os.path.join(root, d)
        for dirpath, dirnames, filenames in os.walk(base):
            dirnames[:] = sorted(x for x in dirnames if not x.startswith("."))
            for fn in sorted(filenames):
                if fn.endswith(".lean"):
                    files.append(os.path.relpath(os.path.join(dirpath, fn), root))
    uses = {}
    for rel in files:
        for decl, kinds in uses_in(os.path.join(root, rel), rel).items():
            uses[(rel.replace(os.sep, "/"), decl)] = ",".join(sorted(kinds))
    return uses


def read_ledger(path):
    rows = {}
    errors = []
    if not os.path.exists(path):
        return rows, [f"no ledger {path}"]
    with open(path, encoding="utf-8") as f:
        for no, line in enumerate(f, 1):
            line = line.rstrip("\n")
            if not line.strip() or line.startswith("#"):
                continue
            parts = line.split("\t")
            if len(parts) != 4:
                errors.append(f"{path}:{no}: want 4 tab-separated fields (file, declaration, constructs, invariant), got {len(parts)}")
                continue
            file_, decl, kinds, inv = parts
            key = (file_, decl)
            if key in rows:
                errors.append(f"{path}:{no}: a second row for {file_} {decl}")
                continue
            rows[key] = (kinds, inv.strip(), no)
    return rows, errors


def main(argv):
    mode = None
    root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    ledger = None
    args = list(argv)
    while args:
        a = args.pop(0)
        if a in ("--check", "--print"):
            mode = a
        elif a == "--root" and args:
            root = args.pop(0)
        elif a == "--ledger" and args:
            ledger = args.pop(0)
        else:
            print(__doc__.strip().split("\n\n")[-2], file=sys.stderr)
            return 2
    if mode is None:
        print("host-unsafe-ledger: give --check or --print", file=sys.stderr)
        return 2
    ledger = ledger or os.path.join(root, ".github", "host-unsafe.tsv")
    uses = scan(root)
    if mode == "--print":
        for (file_, decl), kinds in sorted(uses.items()):
            print(f"{file_}\t{decl}\t{kinds}\tTODO: the invariant")
        return 0
    rows, errors = read_ledger(ledger)
    if errors:
        for e in errors:
            print(f"host-unsafe-ledger: {e}", file=sys.stderr)
        return 2
    unlisted = []
    stale = []
    no_inv = []
    for key, kinds in sorted(uses.items()):
        row = rows.get(key)
        if row is None:
            unlisted.append(f"{key[0]}\t{key[1]}\t{kinds}\tTODO: the invariant")
        elif row[0] != kinds:
            stale.append(f"{key[0]} {key[1]}: the row says {row[0]}, the code uses {kinds} (line {row[2]})")
        elif not row[1] or row[1].startswith("TODO"):
            no_inv.append(f"{key[0]} {key[1]} (line {row[2]})")
    for key, (kinds, _, no) in sorted(rows.items(), key=lambda kv: kv[1][2]):
        if key not in uses:
            stale.append(f"{key[0]} {key[1]}: no such use any more (line {no}); remove the row")
    ok = not (unlisted or stale or no_inv)
    if unlisted:
        print(f"host-unsafe-ledger: {len(unlisted)} use(s) not in {ledger}; add a row with the invariant that makes each sound:", file=sys.stderr)
        for u in unlisted:
            print("  " + u, file=sys.stderr)
    if stale:
        print(f"host-unsafe-ledger: {len(stale)} stale row(s):", file=sys.stderr)
        for s in stale:
            print("  " + s, file=sys.stderr)
    if no_inv:
        print(f"host-unsafe-ledger: {len(no_inv)} row(s) without an invariant:", file=sys.stderr)
        for s in no_inv:
            print("  " + s, file=sys.stderr)
    if ok:
        print(f"host-unsafe-ledger: clean ({len(uses)} uses, all listed)")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
