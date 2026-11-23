#!/usr/bin/env python3
"""Typed FFI/ABI audit for the `lib/` extern declarations (prototype, extern-ffi lane).

This is the smallest checkable slice of the model in `wiz-notes/extern-ffi.md`:

  * every `extern "sym" name : T` declaration is paired with its ledger
    `builtin extern:` row, and the ABI kinds are derived from the *Wiz type text*
    (not copied from the ledger) and compared with that row;
  * every unique C symbol gets a function-pointer assignment with the marshalled
    types (all classes: `n u f b p v s w`, plus `y/Y` and callbacks when present);
    the scalar class additionally gets `_Static_assert`s pinning the
    representation the marshalling assumes;
  * every pointer result's finalizer is declared `void f(void *)`;
  * `--manifest` records a SHA-256 of each declaration, C prototype, C definition
    and containing C file, so a C-source edit is a review trigger instead of an
    invisible change (`--verify` diffs a stored manifest).

The class that is *not* checked here is the reviewed part: C body semantics,
`w`/`s` ownership, `errno`/sentinel return conventions, blocking/threading, and
per-target availability (only the host C ABI is compiled). See the note.

Usage:
  scripts/extern-abi-check.py --list
  scripts/extern-abi-check.py --check [--cc CC] [--cflags "..."]
  scripts/extern-abi-check.py --self-test
  scripts/extern-abi-check.py --manifest .github/extern-abi.tsv
  scripts/extern-abi-check.py --verify .github/extern-abi.tsv

Exit status: 0 clean, 1 a mismatch, 2 usage/toolchain error.
"""
import argparse
import collections
import hashlib
import os
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LEDGER = os.path.join(ROOT, ".github", "trust-baseline.tsv")

DECL_RE = re.compile(
    r'^(?P<indent>[ \t]*)(?P<priv>private[ \t]+)?extern[ \t]+'
    r'"(?P<sym>[^"]+)"[ \t]*'
    r'(?:\(header[ \t]*:=[ \t]*"(?P<header>[^"]*)"\)[ \t]*)?'
    r'(?P<name>[A-Za-z_][A-Za-z0-9_.]*)[ \t]*:[ \t]*(?P<ty>.*)$')
EXTERN_ROW_RE = re.compile(r'^builtin extern:(?P<sym>[^:]+):(?P<kinds>[^:]*):'
                           r'(?P<result>[^:]+):(?P<io>[^:]+):(?P<header>[^:]*):(?P<fin>.*) := (?P<target>.+)$')
PROTO_RE = re.compile(r'^\s*(?:WIZ_API\s+)?'
                      r'(?P<ret>(?:(?:const|volatile|unsigned|signed|struct)\s+)*'
                      r'[A-Za-z_][A-Za-z0-9_]*(?:\s*\*)*)\s+'
                      r'(?P<sym>[A-Za-z_][A-Za-z0-9_]*)\s*\((?P<args>[^;{]*)\)\s*(?:;|\{)')
SCALAR_ATOMS = {"Nat": "n", "UInt64": "u", "Float64": "f", "Bool": "b",
                "Unit": "v", "String": "s"}
BOXED_ATOMS = {"Bytes": "w", "Str": "w", "StrMap": "w", "NatObj": "w",
               "StringObj": "w", "InternTable": "w", "Proto": "w", "Lock": "w",
               "Snapshot": "w", "U64": "w", "U32": "w", "U8": "w"}


# --------------------------------------------------------------------------- data

class Decl:
    def __init__(self, module, file, line, priv, sym, name, ty, header):
        self.module = module
        self.file = file
        self.line = line
        self.priv = priv
        self.sym = sym
        self.name = name
        self.ty = ty
        self.header = header
        self.kinds = None
        self.result = None
        self.io = None
        self.fin = ""
        self.reason = ""
        self.ledger_name = None
        self.proto = None          # (text, file, line)
        self.cdef = None           # (text, file, line)

    @property
    def key(self):
        return (self.module, self.ledger_name or self.name)

    def __str__(self):
        return "%s:%d %s (%s)" % (self.file, self.line, self.name, self.sym)


def read(path):
    with open(path, encoding="utf-8") as f:
        return f.read()


def parse_decls():
    out = []
    for dirpath, dirnames, filenames in os.walk(os.path.join(ROOT, "lib")):
        dirnames[:] = sorted(d for d in dirnames if d != ".lake")
        for fn in sorted(filenames):
            if not fn.endswith(".wiz"):
                continue
            path = os.path.join(dirpath, fn)
            module = os.path.relpath(path, os.path.join(ROOT, "lib"))[:-4].replace("/", ".")
            lines = read(path).splitlines()
            i = 0
            while i < len(lines):
                m = DECL_RE.match(lines[i])
                if not m:
                    i += 1
                    continue
                ty = m.group("ty").strip()
                j = i + 1
                # a continuation is indented and is not a comment or a new command
                while j < len(lines) and lines[j].startswith("  ") and \
                        not re.match(r'\s*(--|/-|\s*$)', lines[j]) and \
                        not re.match(r'\s*(private\s+)?(extern|def|axiom|structure|inductive|foreign_type|'
                                     r'link_c|link_lib|c_struct|import|namespace|end|attribute)\b', lines[j]):
                    ty += " " + lines[j].strip()
                    j += 1
                out.append(Decl(module, os.path.relpath(path, ROOT), i + 1,
                                bool(m.group("priv")), m.group("sym"), m.group("name"),
                                re.sub(r"\s+", " ", ty).strip(), m.group("header") or ""))
                i = j
    return out


def parse_ledger():
    rows = {}
    if not os.path.exists(LEDGER):
        return rows
    lines = read(LEDGER).splitlines()
    for line in lines[1:]:
        ps = line.split("\t")
        if len(ps) < 4:
            continue
        m = EXTERN_ROW_RE.match(ps[2])
        if not m:
            continue
        rows[(ps[0], ps[1])] = dict(sym=m.group("sym"), kinds=m.group("kinds"),
                                    result=m.group("result"), io=m.group("io"),
                                    header=m.group("header"), fin=m.group("fin"),
                                    reason=ps[3])
    return rows


def parse_foreign_types():
    out = set()
    for dirpath, dirnames, filenames in os.walk(os.path.join(ROOT, "lib")):
        dirnames[:] = [d for d in dirnames if d != ".lake"]
        for fn in filenames:
            if not fn.endswith(".wiz"):
                continue
            for line in read(os.path.join(dirpath, fn)).splitlines():
                m = re.match(r'\s*foreign_type\s+([A-Za-z_][A-Za-z0-9_.]*)', line)
                if m:
                    out.add(m.group(1).split(".")[-1])
    return out


# --------------------------------------------------------------- type -> kinds

def strip_outer(s):
    s = s.strip()
    while s.startswith("(") and s.endswith(")"):
        depth = 0
        for i, c in enumerate(s):
            if c == "(":
                depth += 1
            elif c == ")":
                depth -= 1
                if depth == 0 and i != len(s) - 1:
                    return s
        s = s[1:-1].strip()
    return s


def split_arrow(s):
    out, cur, depth, i = [], "", 0, 0
    while i < len(s):
        c = s[i]
        if c in "({[":
            depth += 1
        elif c in ")}]":
            depth -= 1
        if depth == 0 and c == "→":
            out.append(cur)
            cur = ""
            i += 1
            continue
        if depth == 0 and s.startswith("->", i):
            out.append(cur)
            cur = ""
            i += 2
            continue
        cur += c
        i += 1
    out.append(cur)
    return [x.strip() for x in out]


def atom_kind(a, foreign):
    a = strip_outer(a.strip())
    if a in SCALAR_ATOMS:
        return SCALAR_ATOMS[a]
    if a in foreign:
        return "p"
    if a in BOXED_ATOMS or a.startswith(("List ", "Option ", "Array ", "U64Map ",
                                         "MVar ", "Task ", "Chan ", "Owned ",
                                         "Pts ", "Loc ", "IntN ", "UIntN ")):
        return "w"
    # a Wiz data type, a type variable, a tuple: the value is passed as it is
    return "w"


def derive_kinds(ty, sym, foreign):
    """The ABI kinds of a declaration, derived from its Wiz type text.

    Mirrors `Command.lean`'s `extern` derivation for the forms in `lib/`: an
    implicit binder is erased at quantity 0 (`{0 w : Nat}`, or the default), and
    an ordinary type at `{ω w : Nat}`; an explicit binder is erased at quantity
    0; a function-typed parameter is a callback only for a non-`wiz_` symbol
    (runtime natives take closures as `w`); `IO` is separated from the result.
    """
    parts = split_arrow(ty)
    if not parts:
        return None, None, None
    res = parts[-1]
    io = False
    if res.startswith("IO ") or res.startswith("IO("):
        io = True
        res = res[2:].strip()
    res = strip_outer(res)
    kinds = []
    for p in parts[:-1]:
        p = p.strip()
        if p.startswith("{") and p.endswith("}"):
            inner = p[1:-1].strip()
            colon = inner.find(":")
            head = inner[:colon].strip() if colon >= 0 else inner
            q = re.match(r'^(\d+|ω|%[^ ]*)\s+', head)
            qty = q.group(1) if q else "0"
            names = head[len(q.group(0)):].split() if q else head.split()
            n = max(1, len(names))
            if qty == "0" or qty.startswith("%"):
                kinds.extend(["e"] * n)
            else:
                typ = inner[colon + 1:].strip()
                kinds.extend([atom_kind(typ, foreign)] * n)
            continue
        inner = p
        if p.startswith("(") and p.endswith(")"):
            inner = p[1:-1].strip()
            colon = -1
            depth = 0
            for i, c in enumerate(inner):
                if c in "({[":
                    depth += 1
                elif c in ")}]":
                    depth -= 1
                elif c == ":" and depth == 0:
                    colon = i
                    break
            if colon >= 0:
                head = inner[:colon].strip()
                q = re.match(r'^(\d+|ω)\s+', head)
                qty = q.group(1) if q else None
                names = head[len(q.group(0)):].split() if q else head.split()
                n = max(1, len(names))
                typ = inner[colon + 1:].strip()
                if qty == "0":
                    kinds.extend(["e"] * n)
                    continue
                if "→" in typ or "->" in typ:
                    k = "w" if sym.startswith("wiz_") else "callback"
                    kinds.extend([k] * n)
                    continue
                kinds.extend([atom_kind(typ, foreign)] * n)
                continue
            inner = strip_outer(inner)
        if "→" in inner or "->" in inner:
            kinds.append("w" if sym.startswith("wiz_") else "callback")
            continue
        kinds.append(atom_kind(inner, foreign))
    return "".join(kinds), atom_kind(res, foreign), io


def classify(kinds, result):
    chars = set(kinds) | {result}
    if "<" in chars:
        return "struct"
    if "k" in chars or "K" in chars:
        return "callback"
    if "Y" in chars:
        return "write-buffer"
    if "y" in chars:
        return "read-buffer"
    if "s" in chars:
        return "string"
    if "w" in chars:
        return "boxed"
    if chars <= set("nufbpve") and any(c in chars for c in "nufbp"):
        return "scalar"
    return "unit"


# --------------------------------------------------------------- C side lookup

def c_prototypes():
    """symbol -> (prototype text, file, line) from the runtime header and serial.c."""
    out = {}
    for rel in ("runtime/wiz_rt.h", "lib/serial.c"):
        path = os.path.join(ROOT, rel)
        if not os.path.exists(path):
            continue
        for i, line in enumerate(read(path).splitlines(), 1):
            m = PROTO_RE.match(line)
            if not m:
                continue
            sym = m.group("sym")
            text = line.strip()
            if sym not in out:
                out[sym] = (text, rel, i)
    return out


def find_cdef(sym, protos):
    """The definition text (with its body) of `sym`, from the runtime or a link_c file."""
    pat = re.compile(r'\b' + re.escape(sym) + r'\s*\(')
    candidates = []
    for dirpath, dirnames, filenames in os.walk(ROOT):
        dirnames[:] = [d for d in dirnames if d not in
                       (".git", ".lake", "build", "node_modules", "drafts")]
        for fn in filenames:
            if not fn.endswith((".c", ".inc")):
                continue
            path = os.path.join(dirpath, fn)
            rel = os.path.relpath(path, ROOT)
            if rel.startswith(("Tests/", "bench/", "examples/", "web/", "scry/")):
                continue
            candidates.append(rel)
    for rel in sorted(candidates):
        lines = read(os.path.join(ROOT, rel)).splitlines()
        for i, line in enumerate(lines):
            if not pat.search(line) or line.lstrip().startswith(("#", "//", "/*", "*")):
                continue
            # a prototype (ends in `;`) is not the definition
            if line.rstrip().endswith(";"):
                continue
            start = i
            # find the opening brace (on this line or a following line)
            j = i
            while j < len(lines) and "{" not in lines[j]:
                if ";" in lines[j]:
                    break
                j += 1
            if j >= len(lines) or "{" not in lines[j]:
                continue
            depth = 0
            body = []
            k = j
            started = False
            while k < len(lines):
                body.append(lines[k])
                depth += lines[k].count("{") - lines[k].count("}")
                if "{" in lines[k]:
                    started = True
                if started and depth <= 0:
                    break
                k += 1
            if not started or depth > 0:
                continue
            text = "\n".join(body)
            return (text, rel, start + 1)
    return None


def find_macro(sym):
    """A macro-generated symbol: the `#define` family and the invocation that makes it.

    `runtime/rt_words.inc` builds `wiz_word_add` etc. from `WIZ_WORD_BIN(add, …)`.
    The manifest records the macro body, not the expansion, and says so.
    """
    m = re.match(r'^wiz_word_(\w+)$', sym)
    if not m:
        return None
    suffix = m.group(1)
    path = os.path.join(ROOT, "runtime", "rt_words.inc")
    if not os.path.exists(path):
        return None
    lines = read(path).splitlines()
    inv = re.compile(r'^(WIZ_WORD_(?:BIN|ANY|CMP))\(%s,' % re.escape(suffix))
    for i, line in enumerate(lines):
        im = inv.match(line)
        if not im:
            continue
        # the nearest preceding `#define` of that family
        j = i
        while j >= 0 and not re.match(r'#define\s+' + im.group(1) + r'\b', lines[j]):
            j -= 1
        if j < 0:
            continue
        body = []
        k = j
        while k < len(lines):
            body.append(lines[k])
            if not lines[k].rstrip().endswith("\\"):
                break
            k += 1
        body.append(line)
        return ("\n".join(body), "runtime/rt_words.inc", j + 1)
    return None


def c_file_hash(rel):
    path = os.path.join(ROOT, rel)
    if not os.path.exists(path):
        return "-"
    return hashlib.sha256(read(path).encode()).hexdigest()


def normalize_c(s):
    return re.sub(r"\s+", " ", s).strip()


# ------------------------------------------------------------------ the checks

def load():
    decls = parse_decls()
    ledger = parse_ledger()
    foreign = parse_foreign_types()
    bad = []
    for d in decls:
        key = (d.module, d.name)
        if key not in ledger:
            key = (d.module, "_private.%s._0.%s" % (d.module, d.name))
        row = ledger.get(key)
        if row is None:
            bad.append("%s: no ledger `builtin extern:` row" % d)
            continue
        d.ledger_name = key[1]
        d.kinds, d.result, d.io = row["kinds"], row["result"], row["io"]
        d.fin = row["fin"]
        d.reason = row["reason"]
    return decls, ledger, foreign, bad


def derive_check(decls, foreign):
    bad = []
    for d in decls:
        if d.kinds is None:
            continue
        ks, res, io = derive_kinds(d.ty, d.sym, foreign)
        want_io = "io" if io else "pure"
        if ks != d.kinds or res != d.result or want_io != d.io:
            bad.append("%s: declaration derives %s->%s %s, ledger has %s->%s %s"
                       % (d, ks, res, want_io, d.kinds, d.result, d.io))
    return bad


def c_args(kinds):
    """The marshalled C parameter types for a kind string, or None if unsupported."""
    out = []
    for c in kinds:
        if c in ("e", "v"):
            continue
        if c in "nu":
            out.append("uint64_t")
        elif c == "f":
            out.append("double")
        elif c == "b":
            out.append("int")
        elif c == "p":
            out.append("void *")
        elif c == "s":
            out.append("const char *")
        elif c == "w":
            out.append("wiz_val")
        elif c == "y":
            out += ["const void *", "size_t"]
        elif c == "Y":
            out += ["void *", "size_t"]
        elif c in "kK":
            out += ["void *", "void *"]
        else:
            return None
    return out


def c_result(result):
    return {"n": "uint64_t", "u": "uint64_t", "f": "double", "b": "int",
            "p": "void *", "v": "void", "s": "const char *", "w": "wiz_val"}.get(result)


def check_c(decls, inject=None):
    """The generated C: every extern's prototype, plus the scalar representation asserts.

    The prototype half is a superset of `scripts/trust-ffi-audit.sh`'s list (it walks
    `lib/**`, including the five `lib/Scry/` declarations the old glob missed). The
    representation half is the new scalar check.
    """
    protos = c_prototypes()
    lines = ["/* generated by scripts/extern-abi-check.py: the extern ABI check */",
             "#define WIZ_API", "#include \"runtime/wiz_rt.h\"",
             "#if __has_include(<termios.h>)", "#include \"lib/serial.c\"", "#endif",
             "#include \"lib/Scry/quire_seal.c\"", ""]
    lines += [
        "_Static_assert(sizeof(wiz_val) == sizeof(uintptr_t), \"wiz_val is a uintptr_t\");",
        "_Static_assert(_Alignof(wiz_val) == _Alignof(uintptr_t), \"wiz_val alignment\");",
        "_Static_assert(sizeof(uint64_t) == 8, \"Nat and UInt64 are uint64_t\");",
        "_Static_assert(sizeof(int64_t) == 8, \"int64_t is 64 bits\");",
        "_Static_assert(sizeof(double) == 8, \"Float64 is a double\");",
        "_Static_assert(sizeof(int) == 4, \"Bool crosses as a 4-byte int\");",
        "_Static_assert(sizeof(size_t) <= sizeof(uint64_t), \"a length fits a uint64_t\");",
        "_Static_assert(sizeof(void *) <= sizeof(uint64_t), \"a pointer fits a uint64_t\");",
        "_Static_assert(WIZ_MAX_SMALL == (((uint64_t)1 << 62) - 1), \"the boxed scalar is 62 bits\");",
        "_Static_assert(WIZ_MAX_SMALL <= (UINTPTR_MAX >> 1), \"a boxed scalar survives the tag shift\");",
        "_Static_assert(WIZ_BOX(1) == 3 && WIZ_UNBOX(3) == 1, \"the tag bit is the low bit\");",
        ""]

    # finalizers: a `p` result's finalizer must be `void f(void *)`.
    fins = []
    for d in decls:
        if d.fin and d.fin not in fins:
            fins.append(d.fin)
    for i, fin in enumerate(sorted(fins)):
        if fin in protos:
            lines.append("static void (*chk_fin_%d)(void *) = %s;" % (i, fin))
        else:
            lines.append("extern void %s(void *);" % fin)
            lines.append("static void (*chk_fin_%d)(void *) = %s;" % (i, fin))
    if fins:
        lines.append("")

    seen = set()
    n = 0
    checked = 0
    skipped = []
    # the deliberate-failure control must hit a symbol that actually has a uint64_t
    inject_sym = None
    if inject == "width":
        with_u64 = [d.sym for d in decls if "n" in d.kinds or "u" in d.kinds]
        inject_sym = "wiz_u64_add" if any(d.sym == "wiz_u64_add" for d in decls) \
            else (with_u64[0] if with_u64 else None)
    for d in decls:
        if d.sym in seen:
            continue
        seen.add(d.sym)
        args = c_args(d.kinds)
        ret = c_result(d.result)
        if args is None or ret is None:
            skipped.append("%s (%s->%s)" % (d.sym, d.kinds, d.result))
            lines.append("/* %s: unsupported kinds %s->%s */" % (d.sym, d.kinds, d.result))
            continue
        params = ", ".join(args) if args else "void"
        if inject == "width" and d.sym == inject_sym and args:
            # deliberate failure: a 32-bit width where the ABI is 64-bit
            params = params.replace("uint64_t", "uint32_t", 1)
        if d.sym not in protos:
            lines.append("extern %s %s(%s);" % (ret, d.sym, params))
        lines.append("static %s (*chk_%d)(%s) = %s;" % (ret, n, params, d.sym))
        n += 1
        checked += 1
    if inject == "symbol":
        lines.append("static void (*chk_bad)(void) = wiz_no_such_symbol_xyz;")
    return "\n".join(lines) + "\n", checked, fins, protos, skipped


def run_cc(src, cc, cflags):
    with tempfile.TemporaryDirectory(prefix="extern-abi-") as td:
        path = os.path.join(td, "check.c")
        with open(path, "w", encoding="utf-8") as f:
            f.write(src)
        cmd = [cc, "-std=c11", "-fsyntax-only", "-I", ROOT,
               "-Werror=incompatible-pointer-types", "-Werror=implicit-function-declaration",
               "-Werror=int-conversion", "-Werror=return-type"] + cflags + [path]
        p = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        return p.returncode, p.stdout + p.stderr, cmd


def read_cflags():
    if os.environ.get("WIZ_CFLAGS"):
        return os.environ["WIZ_CFLAGS"].split()
    path = os.path.join(ROOT, "grail.local.wiz")
    if os.path.exists(path):
        m = re.search(r'Settings\.set "cflags" "([^"]*)"', read(path))
        if m:
            return m.group(1).split()
    return []


def do_check(decls, foreign, cc, cflags, inject=None, verbose=True):
    bad = derive_check(decls, foreign)
    src, checked, fins, protos, skipped = check_c(decls, inject)
    if bad:
        return 1, "\n".join(bad)
    # finalizers not in the public header: their definition must be `void f(void *)`
    missing_fin = []
    for fin in sorted(fins):
        if fin in protos:
            continue
        cdef = find_cdef(fin, protos)
        if cdef is None:
            missing_fin.append("%s: no C definition" % fin)
        elif not re.match(r'^.*\bvoid\s+%s\s*\(\s*(?:const\s+)?void\s*\*\s*\w*\s*\)'
                          % re.escape(fin), normalize_c(cdef[0])):
            missing_fin.append("%s: %s: not `void f(void *)`" % (fin, cdef[1] + ":" + str(cdef[2])))
    if missing_fin:
        return 1, "\n".join(missing_fin)
    rc, out, cmd = run_cc(src, cc, cflags)
    if rc != 0:
        return rc, "cc failed (%s):\n%s" % (" ".join(cmd), out)
    if verbose:
        print("extern-abi-check: %d declarations; %d unique symbols prototype-checked; "
              "%d finalizers; cc=%s" % (len(decls), checked, len(fins), cc))
        if skipped:
            print("extern-abi-check: %d symbols have unsupported kinds and were not "
                  "prototype-checked: %s" % (len(skipped), "; ".join(skipped)))
    return 0, ""


# --------------------------------------------------------------- the manifest

def manifest(decls, protos):
    out = ["# extern-abi-manifest-v1",
           "module\tdeclaration\tsymbol\tclass\tkinds\tresult\tio\tfinalizer\t"
           "wiz_type_sha256\tc_proto_sha256\tc_def_sha256\tc_source\tc_file_sha256"]
    for d in sorted(decls, key=lambda d: (d.module, d.name)):
        cls = classify(d.kinds, d.result) if d.kinds is not None else "?"
        wiz = hashlib.sha256(('extern "%s" %s : %s' % (d.sym, d.name, d.ty)).encode()).hexdigest()
        cdef = find_cdef(d.sym, protos)
        macro = None if cdef else find_macro(d.sym)
        proto = protos.get(d.sym)
        if proto is None and cdef is not None:
            proto = (cdef[0].splitlines()[0], cdef[1], cdef[2])
        if proto is None and macro is not None:
            proto = (macro[0].splitlines()[-1], macro[1], macro[2])
        if proto:
            ptext, pfile, pline = proto
            ph = hashlib.sha256(normalize_c(ptext).encode()).hexdigest()
        else:
            ph = "-"
        if cdef:
            dtext, dfile, dline = cdef
            dh = hashlib.sha256(normalize_c(dtext).encode()).hexdigest()
            src = "%s:%d" % (dfile, dline)
            fh = c_file_hash(dfile)
        elif macro:
            dtext, dfile, dline = macro
            dh = hashlib.sha256(normalize_c(dtext).encode()).hexdigest()
            src = "%s:%d (macro)" % (dfile, dline)
            fh = c_file_hash(dfile)
        else:
            dh, src, fh = "-", "-", "-"
        out.append("\t".join([d.module, d.ledger_name or d.name, d.sym, cls,
                              d.kinds if d.kinds is not None else "?",
                              d.result or "?", d.io or "?",
                              d.fin or "-", wiz, ph, dh, src, fh]))
    return "\n".join(out) + "\n"


def verify_manifest(decls, protos, path):
    if not os.path.exists(path):
        return 1, "%s: no such manifest (write one with --manifest)" % path
    live = manifest(decls, protos).splitlines()
    old = read(path).splitlines()
    if old and old[0] != live[0]:
        return 1, "%s: not an extern-abi manifest" % path
    def rows(lines):
        r = {}
        for line in lines[1:]:
            ps = line.split("\t")
            if len(ps) >= 2:
                r[(ps[0], ps[1])] = ps
        return r
    a, b = rows(old), rows(live)
    changed, added, removed = [], [], []
    for k, v in a.items():
        if k not in b:
            removed.append("%s/%s" % k)
        elif v != b[k]:
            changed.append("%s/%s" % k)
    for k in b:
        if k not in a:
            added.append("%s/%s" % k)
    if not (changed or added or removed):
        print("extern-abi-check: manifest is current (%d rows)" % len(a))
        return 0, ""
    msg = []
    if added:
        msg.append("new declarations (%d):\n  " % len(added) + "\n  ".join(sorted(added)))
    if removed:
        msg.append("removed declarations (%d):\n  " % len(removed) + "\n  ".join(sorted(removed)))
    if changed:
        msg.append("changed declarations (%d): review the new hash:\n  " % len(changed)
                   + "\n  ".join(sorted(changed)))
    return 1, "\n".join(msg)


# ---------------------------------------------------------------------- main

def main(argv):
    ap = argparse.ArgumentParser(add_help=True)
    ap.add_argument("--list", action="store_true", help="list every extern declaration")
    ap.add_argument("--check", action="store_true",
                    help="derive kinds, compile every prototype, and check the scalar ABI")
    ap.add_argument("--self-test", action="store_true", help="run --check and two deliberate failures")
    ap.add_argument("--manifest", metavar="FILE", help="write the ABI/provenance manifest")
    ap.add_argument("--verify", metavar="FILE", help="compare against a manifest")
    ap.add_argument("--cc", default=os.environ.get("CC") or "cc")
    ap.add_argument("--cflags", default=None)
    ap.add_argument("--inject", choices=("width", "symbol"), default=None,
                    help=argparse.SUPPRESS)
    args = ap.parse_args(argv)

    decls, ledger, foreign, load_bad = load()
    if load_bad:
        print("\n".join(load_bad), file=sys.stderr)
        return 1
    protos = c_prototypes()
    cflags = (args.cflags.split() if args.cflags else read_cflags())

    if args.list:
        print("module\tline\tdeclaration\tsymbol\tclass\tkinds\tresult\tio\tfinalizer\t"
              "c_definition\tcheap_checks\treviewed")
        for d in sorted(decls, key=lambda d: (d.module, d.line)):
            cls = classify(d.kinds, d.result)
            cdef = find_cdef(d.sym, protos)
            macro = None if cdef else find_macro(d.sym)
            if cdef:
                where = "%s:%d" % (cdef[1], cdef[2])
            elif macro:
                where = "%s:%d (macro)" % (macro[1], macro[2])
            else:
                where = "-"
            cheap = ["proto", "hash"]
            if cls == "scalar":
                cheap.append("scalar-abi")
            if d.fin:
                cheap.append("finalizer")
            reviewed = ["body"]
            if "w" in d.kinds or d.result == "w":
                reviewed.append("ownership-w")
            if "s" in d.kinds or d.result == "s":
                reviewed.append("ownership-s")
            if d.io == "io":
                reviewed.append("io/order")
            reviewed += ["returns", "per-target"]
            print("\t".join([d.module, str(d.line), d.ledger_name or d.name, d.sym, cls,
                             d.kinds, d.result, d.io, d.fin or "-", where,
                             ",".join(cheap), ",".join(reviewed)]))
        return 0

    if args.manifest:
        text = manifest(decls, protos)
        with open(args.manifest, "w", encoding="utf-8") as f:
            f.write(text)
        print("extern-abi-check: wrote %s (%d rows)" % (args.manifest, len(decls)))
        return 0

    if args.verify:
        rc, msg = verify_manifest(decls, protos, args.verify)
        if msg:
            print(msg, file=sys.stderr)
        return rc

    cc = args.cc
    if shutil.which(cc) is None:
        for cand in ("cc", "gcc", "clang"):
            if shutil.which(cand):
                cc = cand
                break
        else:
            print("extern-abi-check: no C compiler (tried %s); this check must not skip" % args.cc,
                  file=sys.stderr)
            return 2

    if args.self_test:
        rc, msg = do_check(decls, foreign, cc, cflags)
        if rc != 0:
            print("self-test: the normal check failed:\n" + msg, file=sys.stderr)
            return 1
        for inject, why in (("width", "a 32-bit parameter where the ABI is 64-bit"),
                            ("symbol", "a missing symbol")):
            rc, msg = do_check(decls, foreign, cc, cflags, inject=inject, verbose=False)
            if rc == 0:
                print("self-test: FAIL: %s was not caught" % why, file=sys.stderr)
                return 1
            print("self-test: ok: caught %s" % why)
        print("self-test: PASS (the checker compiles, and both deliberate failures are caught)")
        return 0

    if args.check or args.inject:
        rc, msg = do_check(decls, foreign, cc, cflags, inject=args.inject)
        if msg:
            print(msg, file=sys.stderr)
        return rc

    ap.print_help()
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
