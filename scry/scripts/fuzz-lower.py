#!/usr/bin/env python3
"""Structure-aware fuzzing for Scry's C parse -> lower -> taint pipeline.

The existing `scry/fuzz/run.py` fuzzes the vendored tree-sitter shim with
libFuzzer.  This driver fuzzes the **Wiz side** that sits above it: the
`scry-cst`/JSON loaders, `Scry.Native.toCstStore`, the `Scry.CstStore` columns,
`Scry.lowerTU` (C -> Wil) and the rule evaluation reached by `scry taint`.

It is a bug-finding tool, not a verifier.  A bounded run that finds nothing says
only that these inputs, on this machine, did not crash; it is not a safety
result.

Inputs are generated from a fixed seed and are reproducible from `(seed,
iteration)`; every finding is also copied to `build/fuzz-lower/findings/`.
Each execution runs in its own process group with a wall-clock timeout, a core
dump limit and a resident-memory cap, in a temporary directory.  Categories:

    crash   fatal signal (SIGSEGV, SIGBUS, SIGABRT, ...)
    hang    external timeout or the analyser's own `--timeout` (exit 124)
    oom     allocation failure / memory-cap kill / abort with an OOM message
    wrong   terminating, but an invariant on its output is violated
    refused a normal user-facing error (exit 1), counted, not a finding
    clean   exit 0 and the oracle accepted the output

Usage:

    # bounded CI run: ~120 executions, no minimisation
    python3 scry/scripts/fuzz-lower.py --ci

    # a longer discovery run
    python3 scry/scripts/fuzz-lower.py --iterations 1500 --seed 20261117 \\
        --out scry/build/fuzz-lower

    # replay the checked-in minimised inputs
    python3 scry/scripts/fuzz-lower.py --regressions-only

Exit status: 0 for a completed run (even with findings), 1 for a malformed
invocation or a missing `scry` binary, 2 for an internal harness failure.
`--fail-on-findings` turns a non-empty finding table into exit 1 for a nightly
gate.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import random
import re
import resource
import shutil
import signal
import subprocess
import sys
import tempfile
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import Iterable, Optional

ROOT = Path(__file__).resolve().parents[2]
SCRY_DIR = ROOT / "scry"
DEFAULT_SCRY = SCRY_DIR / ".grail" / "bin" / "scry"
FINDINGS_DIR = SCRY_DIR / "tests" / "fixtures" / "fuzz-regression"
SEED_DIRS = [SCRY_DIR / "bench" / "corpus", SCRY_DIR / "tests" / "fixtures",
             SCRY_DIR / "corpus", SCRY_DIR / "fuzz" / "lower" / "seeds"]

OOM_RE = re.compile(
    r"out of memory|OutOfMemory|std::bad_alloc|bad_alloc|heap exhausted|"
    r"Cannot allocate memory|allocation failed|MemoryError|GC_ALLOC|"
    r"failed to allocate|Cannot allocate",
    re.IGNORECASE,
)
CRASH_RE = re.compile(
    r"segmentation fault|SIGSEGV|SIGBUS|SIGABRT|SIGILL|SIGFPE|stack overflow|"
    r"stack smashing|assertion|internal error|panic|unreachable|"
    r"invalid memory|bus error",
    re.IGNORECASE,
)
# A short, deterministic fingerprint for stderr: numbers and addresses vary
# between runs and must not split one defect into several rows.
ADDR_RE = re.compile(r"0x[0-9a-fA-F]+")
NUM_RE = re.compile(r"\b\d{4,}\b")
STAT_RE = re.compile(r"\b(nodes|edges|errors|roots|bytes|max depth): (\d+)")
CAT_ORDER = ["crash", "hang", "oom", "wrong", "refused", "error", "stalled", "clean"]


# ---------------------------------------------------------------------------
# Command line


def parse_args(argv: Optional[list[str]] = None) -> argparse.Namespace:
    p = argparse.ArgumentParser(
        description="Fuzz Scry's C parse/lower/taint pipeline.")
    p.add_argument("--scry", default=os.environ.get("SCRY", str(DEFAULT_SCRY)),
                   help="the scry binary (default: scry/.grail/bin/scry)")
    p.add_argument("--iterations", type=int, default=300,
                   help="generated executions (default 300)")
    p.add_argument("--seed", type=int, default=20261117,
                   help="RNG seed; a run is reproducible from it (default 20261117)")
    p.add_argument("--timeout", type=float, default=5.0,
                   help="wall-clock seconds per execution (default 5)")
    p.add_argument("--memory-mb", type=int, default=2048,
                   help="resident-memory cap per execution, MiB (default 2048; "
                        "0 disables). The poller samples VmRSS every 10 ms and "
                        "kills the process group above the cap; RLIMIT_AS is "
                        "not used because the runtime reserves a much "
                        "larger virtual arena (VmPeak 1.5 GiB for a 4 MiB "
                        "parse here).")
    p.add_argument("--out", default=str(SCRY_DIR / "build" / "fuzz-lower"),
                   help="output directory (default scry/build/fuzz-lower)")
    p.add_argument("--markdown", default=str(SCRY_DIR / "bench" / "fuzz.md"),
                   help="write the findings table here (default scry/bench/fuzz.md)")
    p.add_argument("--ci", action="store_true",
                   help="bounded CI profile: 120 executions, 3 s, 2 GiB, no minimisation")
    p.add_argument("--regressions-only", action="store_true",
                   help="replay scry/tests/fixtures/fuzz-regression/*.c and exit")
    p.add_argument("--no-minimise", action="store_true",
                   help="do not delta-minimise findings")
    p.add_argument("--max-minimise-evals", type=int, default=30,
                   help="bounded delta-debug evaluations per finding (default 30)")
    p.add_argument("--fail-on-findings", action="store_true",
                   help="exit 1 when a finding is reported")
    p.add_argument("--keep", action="store_true",
                   help="keep the temporary run directory (debugging)")
    p.add_argument("--verbose", action="store_true",
                   help="print one line per execution")
    return p.parse_args(argv)


# ---------------------------------------------------------------------------
# Small utilities


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def say(msg: str) -> None:
    print(f"fuzz-lower: {msg}", file=sys.stderr, flush=True)


def norm_stderr(text: str, limit: int = 600) -> str:
    text = ADDR_RE.sub("<addr>", text)
    text = NUM_RE.sub("<num>", text)
    lines = [ln.strip() for ln in text.splitlines() if ln.strip()]
    # Prefer lines that name a fault; otherwise keep the first few.
    hits = [ln for ln in lines if CRASH_RE.search(ln) or OOM_RE.search(ln)
            or re.search(r"error|exception|fail", ln, re.IGNORECASE)]
    chosen = hits[:3] if hits else lines[:3]
    return " | ".join(chosen)[:limit]


def signal_name(rc: int) -> str:
    if rc >= 0:
        return ""
    try:
        return signal.Signals(-rc).name
    except ValueError:
        return f"SIG{-rc}"


def human_bytes(n: int) -> str:
    if n < 1024:
        return f"{n} B"
    if n < 1024 * 1024:
        return f"{n / 1024:.1f} KiB"
    return f"{n / (1024 * 1024):.1f} MiB"


# ---------------------------------------------------------------------------
# Corpus and generators


def load_seeds() -> tuple[list[bytes], list[Path]]:
    """C sources from the bench/tests/corpus trees, deduped by SHA-256."""
    seen: set[str] = set()
    seeds: list[bytes] = []
    paths: list[Path] = []
    for d in SEED_DIRS:
        if not d.is_dir():
            continue
        for p in sorted(d.rglob("*.c")):
            if "fuzz-regression" in p.parts:
                continue
            try:
                data = p.read_bytes()
            except OSError:
                continue
            # Mutating multi-megabyte files is slow and mostly repeats; the
            # pathological-size generators cover large inputs deliberately.
            if len(data) > 96 * 1024:
                data = data[:96 * 1024]
            h = sha(data)
            if h in seen:
                continue
            seen.add(h)
            seeds.append(data)
            paths.append(p)
    return seeds, paths


TOKENS = [
    b"{", b"}", b"(", b")", b"[", b"]", b";", b",", b"/*", b"*/", b"//",
    b"\"", b"'", b"\\", b"#if", b"#endif", b"#define", b"#include",
    b"NULL", b"sizeof", b"return", b"struct", b"union", b"enum",
    b"int", b"char", b"void", b"...", b"0x", b"1e", b"0b", b"__attribute__",
    b"\x00", b"\xff", b"\x7f",
]


def mutate(rng: random.Random, seeds: list[bytes]) -> bytes:
    data = bytearray(rng.choice(seeds) if seeds else b"int x;")
    for _ in range(rng.randint(1, 10)):
        op = rng.randrange(8)
        if op == 0 and data:                      # bit flip
            i = rng.randrange(len(data))
            data[i] ^= 1 << rng.randrange(8)
        elif op == 1 and data:                    # byte delete
            i = rng.randrange(len(data))
            del data[i:i + rng.randint(1, 16)]
        elif op == 2:                             # byte insert
            i = rng.randrange(len(data) + 1)
            n = rng.randint(1, 8)
            data[i:i] = bytes(rng.randrange(256) for _ in range(n))
        elif op == 3 and data:                    # duplicate a span
            i = rng.randrange(len(data))
            n = rng.randint(1, 64)
            data[i:i] = data[i:i + n]
        elif op == 4 and data:                    # splice another seed
            other = rng.choice(seeds) if seeds else b""
            if other:
                a = rng.randrange(len(data) + 1)
                b = rng.randrange(len(other) + 1)
                c = min(len(other), b + rng.randint(1, 256))
                data[a:a] = other[b:c]
        elif op == 5:                             # token insert
            i = rng.randrange(len(data) + 1)
            data[i:i] = rng.choice(TOKENS)
        elif op == 6 and data:                    # truncate
            data = data[:rng.randrange(len(data) + 1)]
        elif op == 7 and data:                    # repeat a prefix/suffix
            n = rng.randint(1, 8)
            data.extend(data[:rng.randint(1, max(1, len(data)))])
            if n == 0:
                data.clear()
    return bytes(data)


def gen_random(rng: random.Random) -> bytes:
    n = min(8192, max(1, int(2 ** rng.uniform(0, 13))))
    if rng.random() < 0.5:
        alphabet = (b"abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"
                    b"0123456789{}()[];,.*&|+-=<>!\"'/# \n\t")
        return bytes(rng.choice(alphabet) for _ in range(n))
    return bytes(rng.randrange(256) for _ in range(n))


def big(depth: int, limit: int = 2_000_000) -> int:
    return max(1, min(depth, limit))


def deep_src(variant: str, d: int) -> bytes:
    """One deeply nested source at exactly `d` levels, valid where possible."""
    d = big(d)
    if variant == "paren":
        return b"int f(void){return " + b"(" * d + b"1" + b")" * d + b";}"
    if variant == "unary":
        return b"int f(void){return " + b"-" * d + b"1;}"
    if variant == "binary":
        return b"int f(void){return 1" + b"+1" * d + b";}"
    if variant == "if":
        return b"int f(void){" + b"if(1)" * d + b"return 0;}"
    if variant == "blocks":
        return b"int f(void){" + b"{" * d + b"return 0;" + b"}" * d + b"}"
    if variant == "init":
        return b"int a[]=" + b"{" * d + b"0" + b"}" * d + b";"
    if variant == "calls":
        return b"int f(int);int g(void){return " + b"f(" * d + b"1" + b")" * d + b";}"
    if variant == "declarator":
        return b"int " + b"*" * d + b"p;"
    if variant == "subscript":
        return b"int a[1];int f(void){return a" + b"[0]" * d + b";}"
    if variant == "comma":
        return b"int f(void){return (1" + b",1" * d + b");}"
    if variant == "ternary":
        return b"int f(void){return " + b"1?" * d + b"1" + b":1" * d + b";}"
    if variant == "while":
        return b"int f(void){" + b"while(1)" * d + b"return 0;}"
    if variant == "cast":
        return b"int f(void){return " + b"(int*)" * d + b"0;}"
    if variant == "switch":
        return b"int f(int x){switch(x){" + b"case 1:" * d + b"break;}}"
    return b"struct S{int x;};int f(struct S *p){return p" + b"->x.x" * d + b";}"


DEEP_VARIANTS = [
    "paren", "unary", "binary", "if", "blocks", "init", "calls",
    "declarator", "subscript", "comma", "ternary", "while", "cast",
    "switch", "field",
]


def gen_deep(rng: random.Random) -> tuple[bytes, str]:
    """Deeply nested constructs: the Wiz lowerer is structurally recursive."""
    variant = rng.choice(DEEP_VARIANTS)
    depth = rng.choice([128, 512, 2048, 8192, 32768, 65536, 131072])
    d = big(depth)
    return deep_src(variant, d), f"deep:{variant}:{d}"


def gen_unterminated(rng: random.Random) -> tuple[bytes, str]:
    variant = rng.choice([
        "string", "char", "comment", "pp", "paren", "brace", "struct",
        "include", "prototype", "continuation", "raw",
    ])
    if variant == "string":
        src = b'char *s = "' + b"a" * rng.randint(1, 4096)
    elif variant == "char":
        src = b"char c = '" + b"a" * rng.randint(1, 64)
    elif variant == "comment":
        src = b"int f(void){/*" + b"x" * rng.randint(1, 4096)
    elif variant == "pp":
        src = b"#if 1\n" * rng.randint(1, 64) + b"int x;"
    elif variant == "paren":
        src = b"int f(void){return " + b"(" * rng.randint(1, 4096) + b"1;}"
    elif variant == "brace":
        src = b"int f(void){" + b"{" * rng.randint(1, 4096) + b"return 0;"
    elif variant == "struct":
        src = b"struct S {" + b"int x;" * rng.randint(1, 32)
    elif variant == "include":
        src = b'#include "' + b"h" * rng.randint(1, 256)
    elif variant == "prototype":
        src = b"int f(" + b"int," * rng.randint(1, 1024)
    elif variant == "continuation":
        src = b'char *s = "a\\' + b"\n" * rng.randint(1, 256)
    else:
        src = bytes(rng.randrange(256) for _ in range(rng.randint(1, 4096)))
    return src, f"unterminated:{variant}"


def path_src(variant: str, n: int) -> bytes:
    """One pathological-size source; `n` is the raw size knob."""
    if variant == "number":
        return b"int f(void){return " + b"1" * n + b";}"
    if variant == "hex":
        return b"int f(void){return 0x" + b"f" * n + b";}"
    if variant == "identifier":
        return b"int " + b"a" * n + b";"
    if variant == "params":
        count = min(n, 20000)
        return (b"int f(" + b",".join(b"int a%d" % i for i in range(count))
                + b"){return 0;}")
    if variant == "statements":
        count = min(n, 200000)
        return b"int f(void){" + b"a++;" * count + b"}"
    if variant == "decls":
        count = min(n, 100000)
        return b"".join(b"int a%d;" % i for i in range(count))
    if variant == "initlist":
        count = min(n, 200000)
        return b"int a[]={" + b",".join(b"1" for _ in range(count)) + b"};"
    if variant == "comment":
        return b"/*" + b"x" * n + b"*/\nint x;"
    if variant == "newlines":
        return b"\n" * n + b"int x;"
    if variant == "string":
        return b'char *s="' + b"a" * n + b'";'
    if variant == "deep-decl":
        return b"int " + b"*" * min(n, 100000) + b"p;"
    if variant == "include-path":
        return b'#include "' + b"a/" * min(n, 100000) + b'"\nint x;'
    return b"__attribute__((" + b"a," * min(n, 100000) + b"a)) int x;"


PATH_VARIANTS = [
    "number", "hex", "identifier", "params", "statements", "decls",
    "initlist", "comment", "newlines", "string", "deep-decl",
    "include-path", "attrs",
]


def gen_pathological(rng: random.Random) -> tuple[bytes, str]:
    variant = rng.choice(PATH_VARIANTS)
    n = rng.choice([1024, 8192, 65536, 262144, 1048576])
    return path_src(variant, n), f"pathological:{variant}:{n}"


# -- A small structured C generator: exercises the lowering paths that need
# valid syntax (declarations, assignments, calls, control flow), which random
# mutations reach rarely.

IDENT = ["x", "y", "z", "p", "q", "a", "b", "buf"]
BINOPS = ["+", "-", "*", "/", "%", "&", "|", "^", "<<", ">>", "==", "!=",
          "<", "<=", ">", ">=", "&&", "||"]


def gen_expr(rng: random.Random, depth: int) -> str:
    if depth <= 0 or rng.random() < 0.3:
        return rng.choice([
            rng.choice(IDENT), str(rng.choice([0, 1, 2, 7, 255, 65535])),
            '"s"', "'c'", "0", "1", "NULL", "sizeof(int)",
        ])
    kind = rng.randrange(12)
    e = lambda: gen_expr(rng, depth - 1)
    if kind == 0:
        return f"({e()})"
    if kind == 1:
        return f"{rng.choice(['-', '~', '!', '+'])}{e()}"
    if kind == 2:
        return f"{e()} {rng.choice(BINOPS)} {e()}"
    if kind == 3:
        return f"{e()} = {e()}"
    if kind == 4:
        return f"{rng.choice(IDENT)}[{e()}]"
    if kind == 5:
        return f"{rng.choice(IDENT)}.{rng.choice(IDENT)}"
    if kind == 6:
        return f"{rng.choice(IDENT)}->{rng.choice(IDENT)}"
    if kind == 7:
        return f"{rng.choice(['f', 'g', 'strcpy', 'memcpy'])}(" + \
               ",".join(e() for _ in range(rng.randint(0, 3))) + ")"
    if kind == 8:
        return f"({rng.choice(['int', 'char', 'unsigned', 'long'])}{e()})"
    if kind == 9:
        return f"{e()} ? {e()} : {e()}"
    if kind == 10:
        return f"{e()}, {e()}"
    return f"{e()}++"


def gen_stmt(rng: random.Random, depth: int) -> str:
    if depth <= 0:
        return rng.choice(["x++;", "y = x;", "return;", "f(x);", ";"])
    kind = rng.randrange(10)
    s = lambda: gen_stmt(rng, depth - 1)
    e = lambda: gen_expr(rng, depth - 1)
    if kind == 0:
        return f"{{ {s()} {s()} }}"
    if kind == 1:
        return f"if ({e()}) {s()} else {s()}"
    if kind == 2:
        return f"while ({e()}) {s()}"
    if kind == 3:
        return f"for (int i = 0; i < {rng.randint(1, 8)}; i++) {s()}"
    if kind == 4:
        return f"switch ({e()}) {{ case 1: {s()} break; default: {s()} }}"
    if kind == 5:
        return f"return {e()};"
    if kind == 6:
        return f"int {rng.choice(IDENT)} = {e()};"
    if kind == 7:
        return f"{e()};"
    if kind == 8:
        return "break;"
    return "continue;"


def gen_json(rng: random.Random) -> tuple[bytes, str]:
    """Deep/huge JSON fact stores.

    `parse --stats` and `scry facts` sniff a leading `{` and hand the text to
    `Scry.Facts.ofText` -> `Json.parse`, whose recursive descent has no depth
    limit. This is a secondary target (the C pipeline is the main one), but the
    same analyser process and the same sandbox apply.
    """
    variant = rng.choice(["array", "object", "mixed", "huge-array", "escapes"])
    d = big(rng.choice([128, 512, 2048, 8192, 32768, 65536, 131072]))
    if variant == "array":
        data = b"[" * d + b"0" + b"]" * d
    elif variant == "object":
        data = b'{"a":' * d + b"0" + b"}" * d
    elif variant == "mixed":
        data = (b'{"a":[' * (d // 2) + b"0" + b"]}" * (d // 2))
    elif variant == "huge-array":
        n = big(rng.choice([10000, 100000, 1000000]), 1_000_000)
        data = b"[" + b",".join(b"0" for _ in range(n)) + b"]"
    else:
        data = b'["' + b"\\u0041" * d + b'"]'
    return data, f"json:{variant}:{d}"


def gen_program(rng: random.Random) -> tuple[bytes, str]:
    funcs = []
    for i in range(rng.randint(1, 3)):
        body = " ".join(gen_stmt(rng, rng.randint(1, 4))
                        for _ in range(rng.randint(1, 5)))
        funcs.append(f"int f{i}(int x, int y, char *p) {{ {body} return 0; }}")
    src = ("struct S { int x; int y; };\n"
           "int f(int); int g(int);\n"
           + "\n".join(funcs) + "\n")
    return src.encode(), "program"


def gen_memory(rng: random.Random) -> tuple[bytes, str]:
    """Large single-node inputs: the `--max-nodes` cap does not bound memory.

    A string literal, a comment and a wide initialiser are one/few CST nodes,
    but the native store and the Wiz string arrays are linear in bytes with a
    large constant (measured: a 4 MiB literal parses at ~1.1 GiB RSS).
    """
    variant = rng.choice(["string", "comment", "initlist", "identifier"])
    n = rng.choice([2_097_152, 4_194_304, 8_388_608])
    if variant == "string":
        src = b'char *s="' + b"a" * n + b'";'
    elif variant == "comment":
        src = b"/*" + b"x" * n + b"*/\nint x;"
    elif variant == "identifier":
        src = b"int " + b"a" * n + b";"
    else:
        m = min(n, 4_000_000) // 2
        src = b"int a[]={" + b"1," * m + b"1};"
    return src, f"memory:{variant}:{n}"


def generate(rng: random.Random, seeds: list[bytes], iteration: int) -> tuple[bytes, str, str]:
    """Returns (bytes, mode, origin)."""
    # Weighted schedule: mutation and the structural classes dominate; a
    # structured program keeps the lowering paths exercised.
    r = rng.random()
    if r < 0.34:
        data, origin = mutate(rng, seeds), "mutate"
    elif r < 0.48:
        data, origin = gen_random(rng), "random"
    elif r < 0.68:
        data, origin = gen_deep(rng)
    elif r < 0.80:
        data, origin = gen_unterminated(rng)
    elif r < 0.92:
        data, origin = gen_pathological(rng)
    elif r < 0.95:
        data, origin = gen_program(rng)
    elif r < 0.98:
        data, origin = gen_memory(rng)
    else:
        data, origin = gen_json(rng)
    # Cover both the lowering path and the raw stats/fuzz-span paths. JSON
    # stores only exist for `facts`/`parse`; generated C goes to all three.
    if origin.startswith("json:"):
        mode = rng.choices(["facts", "parse"], weights=[3, 1])[0]
    else:
        mode = rng.choices(["taint", "taint-open", "parse", "span"],
                           weights=[6, 1, 2, 1])[0]
    return data, mode, origin


# ---------------------------------------------------------------------------
# Sandboxed execution


@dataclass
class Run:
    category: str
    rc: int
    sig: str
    timed_out: bool
    wall_ms: int
    cpu_ms: int
    peak_rss_mb: int
    stdout: str
    stderr: str
    reason: str = ""

    def signature(self) -> str:
        if self.category == "crash":
            return f"crash:{self.sig}"
        if self.category == "hang":
            return "hang:builtin" if self.reason.startswith("builtin") else "hang:external"
        if self.category == "oom":
            return "oom:" + (self.reason.split(":")[0] if self.reason else "abort")
        if self.category == "wrong":
            return "wrong:" + self.reason.split(":")[0]
        return self.category


def _limits():
    def pre() -> None:
        os.setsid()
        try:
            resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
        except (ValueError, OSError):
            pass
    return pre


def _rss_mb(pid: int) -> int:
    """Resident set size of `pid` in MiB, from /proc.

    The cap is on **resident** memory, not address space: the Wiz runtime
    reserves a much larger virtual arena (measured VmPeak 1.5 GiB for a
    4 MiB parse whose VmRSS is 459 MiB), so an address-space cap aborts an
    ordinary input with a SIGSEGV that looks exactly like an analyser
    crash.  RSS is what a policy limit means, and the poller can also see a
    blow-up before the kernel kills the process.
    """
    try:
        with open(f"/proc/{pid}/status", "rb") as f:
            for line in f:
                if line.startswith(b"VmRSS:"):
                    return int(line.split()[1]) // 1024
    except (OSError, ValueError, IndexError):
        pass
    return 0


def execute(cmd: list[str], data: bytes, args: argparse.Namespace,
            timeout: Optional[float] = None,
            tmpdir: Optional[Path] = None,
            mem_mb: Optional[int] = None) -> Run:
    """Run one generated input in a temp file under the sandbox.

    `mem_mb` overrides `args.memory_mb` for a verification run (0 = no cap).
    Stdout and stderr go to files, not pipes: a hung 30 MB JSON output must
    not fill a pipe and deadlock the poller.
    """
    timeout = args.timeout if timeout is None else timeout
    mem_mb = args.memory_mb if mem_mb is None else mem_mb
    keep = tmpdir is not None
    d = tmpdir or Path(tempfile.mkdtemp(prefix="scry-fuzz-lower-"))
    path, out_path, err_path = d / "input.c", d / "stdout", d / "stderr"
    p = None
    try:
        path.write_bytes(data)
        full = cmd + [str(path)]
        env = {"PATH": os.environ.get("PATH", "/usr/bin:/bin"),
               "HOME": str(d), "TMPDIR": str(d), "LC_ALL": "C"}
        start = time.monotonic()
        ru0 = resource.getrusage(resource.RUSAGE_CHILDREN)
        with open(out_path, "wb") as of, open(err_path, "wb") as ef:
            p = subprocess.Popen(
                full, cwd=str(SCRY_DIR), env=env, stdin=subprocess.DEVNULL,
                stdout=of, stderr=ef, preexec_fn=_limits(),
            )
            timed_out = False
            over_cap = False
            peak = 0
            deadline = start + timeout
            while True:
                rc = p.poll()
                if rc is not None:
                    break
                if p.pid:
                    peak = max(peak, _rss_mb(p.pid))
                if mem_mb > 0 and peak > mem_mb:
                    over_cap = True
                    break
                if time.monotonic() >= deadline:
                    timed_out = True
                    break
                time.sleep(0.01)
            if p.poll() is None:
                try:
                    os.killpg(p.pid, signal.SIGKILL)
                except (ProcessLookupError, PermissionError):
                    pass
            try:
                p.wait(timeout=5)
            except subprocess.TimeoutExpired:
                pass
        wall_ms = int((time.monotonic() - start) * 1000)
        ru1 = resource.getrusage(resource.RUSAGE_CHILDREN)
        cpu_ms = int(((ru1.ru_utime - ru0.ru_utime)
                      + (ru1.ru_stime - ru0.ru_stime)) * 1000)
        out = out_path.read_text("utf-8", "replace") if out_path.exists() else ""
        err = err_path.read_text("utf-8", "replace") if err_path.exists() else ""
        rc = p.returncode if p.returncode is not None else -9
    finally:
        if not keep:
            shutil.rmtree(d, ignore_errors=True)

    sig = signal_name(rc)
    # A process that died just below the cap died of the cap: the poller
    # samples every 10 ms and an allocation burst can cross the line first.
    # A timeout kill is *our* SIGKILL, not the kernel's: its RSS can be near
    # the cap while the run was simply too slow, so it must stay a hang.
    cap_death = (mem_mb > 0 and rc < 0 and not timed_out
                 and peak >= int(mem_mb * 0.9))
    if over_cap or cap_death:
        cat, reason = "oom", f"rss:{peak}mb"
    elif OOM_RE.search(err):
        # Wiz prints `wiz: out of memory` and exits 3 (not a signal), and the
        # GC can also abort after an allocation failure. Both are OOM.
        cat, reason = "oom", "message:" + norm_stderr(err, 80)
    elif timed_out:
        # Wall time under a loaded host is not evidence: a 3 s launch can
        # look like a 30 s hang. Only call it a hang when the process was
        # actually consuming CPU for a good share of the interval.
        if cpu_ms < 250 or cpu_ms * 4 < wall_ms:
            cat, reason = "stalled", "starvation"
        else:
            cat, reason = "hang", "timeout"
    elif rc == 124:
        cat = "hang"
        reason = "builtin:--timeout"
    elif rc < 0:
        if OOM_RE.search(err):
            cat, reason = "oom", "signal+oom-message"
        elif rc == -signal.SIGKILL:
            # Could be the kernel OOM killer or an external kill. Under a
            # cgroup, 137 usually means memory pressure; keep it separate.
            cat, reason = "oom", "sigkill"
        else:
            cat, reason = "crash", sig
    elif rc in (134, 133) or (rc >= 128 and OOM_RE.search(err)):
        if OOM_RE.search(err):
            cat, reason = "oom", "abort+oom-message"
        else:
            cat, reason = "crash", f"exit{rc}"
    elif rc == 0:
        cat, reason = "clean", ""
    elif rc == 1:
        cat, reason = "refused", norm_stderr(err)
    elif rc == 2:
        cat, reason = "error", norm_stderr(err)
    else:
        cat, reason = ("crash" if CRASH_RE.search(err) else "error"), f"exit{rc}"

    return Run(cat, rc, sig, timed_out, wall_ms, cpu_ms, peak, out, err, reason)


# ---------------------------------------------------------------------------
# Oracles


def walk_spans(obj, path=""):
    """Yield (path, start, stop) for dicts that carry a start/stop pair."""
    if isinstance(obj, dict):
        a, b = obj.get("start"), obj.get("stop")
        if isinstance(a, int) and isinstance(b, int):
            yield path, a, b
        for k, v in obj.items():
            yield from walk_spans(v, f"{path}.{k}")
    elif isinstance(obj, list):
        for i, v in enumerate(obj):
            yield from walk_spans(v, f"{path}[{i}]")


def oracle(mode: str, data: bytes, run: Run) -> Optional[str]:
    """Return a `wrong` reason for a terminating run, or None."""
    if run.rc != 0:
        return None
    if mode in ("taint", "taint-open"):
        text = run.stdout.strip()
        if not text:
            return "taint-json:empty"
        try:
            j = json.loads(text)
        except json.JSONDecodeError:
            return "taint-json:unparsable"
        for p, a, b in walk_spans(j):
            if b < a:
                return f"span:negative:{p}"
        return None
    if mode == "span":
        text = run.stdout.strip()
        try:
            j = json.loads(text)
        except json.JSONDecodeError:
            return "span-json:unparsable"
        need = ["bytes", "nodes", "edges", "errors", "root"]
        for k in need:
            if k not in j:
                return f"span-json:missing:{k}"
        if j["root"].get("stop", 0) > j["bytes"]:
            return "span:root-past-eof"
        if j["root"].get("start", 0) > j["root"].get("stop", 0):
            return "span:negative:root"
        if j["nodes"] < 1:
            return "span:no-nodes"
        return None
    if mode == "parse":
        if not STAT_RE.search(run.stdout):
            return "parse-stats:missing"
        st = {m.group(1): int(m.group(2)) for m in STAT_RE.finditer(run.stdout)}
        if st.get("nodes", 0) < 1:
            return "parse-stats:no-nodes"
        if st.get("max depth", 0) > st.get("nodes", 0):
            return "parse-stats:depth-gt-nodes"
        return None
    if mode == "facts":
        if "format:" not in run.stdout or not STAT_RE.search(run.stdout):
            return "facts-stats:missing"
        st = {m.group(1): int(m.group(2)) for m in STAT_RE.finditer(run.stdout)}
        if st.get("max depth", 0) > st.get("nodes", 0):
            return "facts-stats:depth-gt-nodes"
        return None
    return None


def differential(data: bytes, taint_run: Run, args: argparse.Namespace,
                 tmp: Optional[Path] = None) -> Optional[str]:
    """Compare parse --stats and fuzz-span on the same bytes.

    Both go through `Scry.Native.toCstStore`; a disagreement in nodes/edges/
    errors means one of the two store paths is wrong (or a column was read out
    of range and clamped), which is a `wrong-but-terminating` defect.
    """
    p = execute([args.scry, "parse", "--stats"], data, args,
                timeout=min(args.timeout, 3.0))
    if p.category != "clean":
        return None
    s = execute([args.scry, "fuzz-span", "--json"], data, args,
                timeout=min(args.timeout, 3.0))
    if s.category != "clean":
        return None
    try:
        j = json.loads(s.stdout)
    except json.JSONDecodeError:
        return None
    st = {m.group(1): int(m.group(2)) for m in STAT_RE.finditer(p.stdout)}
    if "max depth" in st:
        st.pop("max depth")
    for k in ("nodes", "edges", "errors", "bytes"):
        if k in st and k in j and st[k] != j[k]:
            return f"differential:parse-vs-span:{k}={st[k]}/{j[k]}"
    return None


# ---------------------------------------------------------------------------
# Minimisation


def minimise(data: bytes, mode: str, origin: str, args: argparse.Namespace,
             want: Run, budget: list[int]) -> tuple[bytes, int, bool]:
    """Delta-debug to a smaller input that keeps the same category/signature.

    Line chunks first (cheap for C sources), then byte chunks.  The evaluation
    budget is shared across the whole finding so a pathological hang cannot
    make minimisation unbounded.
    """
    target = (want.category, want.signature())

    def reproduces(candidate: bytes) -> bool:
        if budget[0] <= 0:
            return False
        budget[0] -= 1
        # Probe with the *same* budget and external timeout as the campaign:
        # a shorter probe can shrink a builtin timeout to an input that no
        # longer expires under the real budget, and the fixture would then be
        # a different (unreproducible) defect.
        r = execute([args.scry, *mode_cmd(mode, max(1, int(args.timeout)))],
                    candidate, args, timeout=args.timeout)
        if r.category == "wrong":
            # Keep the same oracle reason prefix; a different invariant is a
            # different defect.
            return r.category == target[0] and r.signature() == target[1]
        return (r.category, r.signature()) == target

    # A generated deep/pathological case has a known size knob. Bisect that
    # knob first: every candidate is valid C of the same shape, unlike byte
    # delta-debugging, which tends to turn `return 1` into `return1` and find
    # a different (parse-recovery) defect.
    parts = origin.split(":")
    if parts[0] == "deep" and len(parts) >= 3 and parts[1] in DEEP_VARIANTS:
        hi = int(parts[2])
        lo, best = 1, None
        while lo <= hi and budget[0] > 0:
            mid = (lo + hi) // 2
            cand = deep_src(parts[1], mid)
            if reproduces(cand):
                best, hi = cand, mid - 1
            else:
                lo = mid + 1
        if best is not None:
            return best, budget[0], best != data
    if (parts[0] == "pathological" and len(parts) >= 3
            and parts[1] in PATH_VARIANTS):
        hi = int(parts[2])
        lo, best = 1, None
        while lo <= hi and budget[0] > 0:
            mid = (lo + hi) // 2
            cand = path_src(parts[1], mid)
            if reproduces(cand):
                best, hi = cand, mid - 1
            else:
                lo = mid + 1
        if best is not None:
            return best, budget[0], best != data

    def ddmin(cur: bytes, split) -> bytes:
        n = 2
        while len(cur) >= 2 and budget[0] > 0:
            chunks = split(cur, n)
            if not chunks:
                break
            reduced = False
            for i in range(len(chunks)):
                cand = b"".join(chunks[:i] + chunks[i + 1:])
                if cand and reproduces(cand):
                    cur = cand
                    n = max(2, n - 1)
                    reduced = True
                    break
            if not reduced:
                if n >= len(cur):
                    break
                n = min(len(cur), n * 2)
        return cur

    def lines(b: bytes, n: int):
        ls = b.splitlines(keepends=True)
        if len(ls) < 2:
            return []
        step = max(1, (len(ls) + n - 1) // n)
        return [b"".join(ls[i:i + step]) for i in range(0, len(ls), step)]

    def bytes_(b: bytes, n: int):
        step = max(1, (len(b) + n - 1) // n)
        return [b[i:i + step] for i in range(0, len(b), step)]

    # Generated findings are almost always a repeated unit (a nesting level,
    # a statement, one digit, one comment byte).  Plain ddmin halves bytes and
    # needs ~log2(n) *sequential* successful removals; a deliberate run shrink
    # finds the minimal repeat count in ~log2(n) probes, which is the
    # difference between a 1 MiB fixture and a 200-byte one.
    patterns = [b"while(1)", b"if(1)", b"f(", b"p->x.x", b"->x.x", b"a++;",
                b"case 1:", b"int a", b"1,", b",1", b"{", b"}", b"(", b")",
                b"+1", b"-", b"*", b" ", b"\n", b"a", b"x", b"1", b"0"]

    def longest_run(b: bytes, pat: str) -> tuple[int, int]:
        """(start, count) of the longest contiguous run of `pat`."""
        L, best, i = len(pat), (0, 0), 0
        while i < len(b):
            j = b.find(pat, i)
            if j < 0:
                break
            n = 1
            while b.startswith(pat, j + n * L):
                n += 1
            if n > best[1]:
                best = (j, n)
            i = j + n * L
        return best

    def shrink_runs(cur: bytes) -> tuple[bytes, bool]:
        changed = False
        while budget[0] > 0 and len(cur) > 24:
            best_pat, best_start, best_n = b"", 0, 0
            for pat in patterns:
                st, n = longest_run(cur, pat)
                if n >= 2 and n * len(pat) > best_n * len(best_pat):
                    best_pat, best_start, best_n = pat, st, n
            if best_n < 2 or best_n * len(best_pat) < max(16, len(cur) // 8):
                break
            lo, hi = 1, best_n
            while lo < hi and budget[0] > 0:
                mid = (lo + hi) // 2
                cand = (cur[:best_start] + best_pat * mid
                        + cur[best_start + len(best_pat) * best_n:])
                if reproduces(cand):
                    hi = mid
                else:
                    lo = mid + 1
            if lo >= best_n:
                break
            cur = (cur[:best_start] + best_pat * lo
                   + cur[best_start + len(best_pat) * best_n:])
            changed = True
        return cur, changed

    cur = data
    if budget[0] > 0:
        cur, _ = shrink_runs(cur)
    if len(cur.splitlines()) > 1:
        cur = ddmin(cur, lines)
    if budget[0] > 0:
        cur = ddmin(cur, bytes_)
    return cur, budget[0], cur != data


def mode_cmd(mode: str, timeout_s: int) -> list[str]:
    if mode == "taint":
        # The analyser's own SIGALRM guard is strictly shorter than the
        # external one, so an expiry is attributable: `builtin:--timeout`
        # (a budget refusal) rather than an unbounded kill.
        inner = max(1, timeout_s - 1)
        return ["taint", "--allow-errors", "--json", "--timeout", str(inner)]
    if mode == "taint-open":
        # No analyser budget: the external sandbox is the only bound. This is
        # how a hang that the default 300 s contract would mask is found.
        return ["taint", "--allow-errors", "--json"]
    if mode == "parse":
        return ["parse", "--stats"]
    if mode == "facts":
        return ["facts"]
    return ["fuzz-span", "--json"]


# ---------------------------------------------------------------------------
# Run records and report


@dataclass
class Finding:
    fid: str
    category: str
    mode: str
    origin: str
    data: bytes
    run: Run
    iteration: int
    seed: int
    minimised: Optional[bytes] = None
    minimise_evals: int = 0
    minimised_changed: bool = False
    fixture: str = ""
    note: str = ""

    def key(self) -> tuple[str, str, str, str]:
        return (self.category, self.run.signature(), origin_class(self.origin),
                self.mode)


def slug(s: str) -> str:
    s = re.sub(r"[^a-zA-Z0-9_.-]+", "-", s)
    return s.strip("-")[:60]


def origin_class(origin: str) -> str:
    """The generator class without the numeric depth/size parameter."""
    return origin.rsplit(":", 1)[0] if origin[-1:].isdigit() else origin


def write_report(path: Path, findings: list[Finding], counts: dict[str, int],
                 args: argparse.Namespace, seeds: int, elapsed: float,
                 scry_version: str) -> None:
    by_origin: dict[str, int] = {}
    for f in findings:
        by_origin[f.origin.split(":")[0]] = by_origin.get(f.origin.split(":")[0], 0) + 1
    lines = []
    lines.append("# Scry parse/lower fuzz findings\n")
    lines.append(
        "This is a bounded bug search over the **Wiz side** of Scry: the native "
        "column store, `Scry.CstStore`, `Scry.lowerTU` (C -> Wil) and the taint "
        "pipeline reached by `scry taint`. It complements `scry/fuzz/run.py`, "
        "which fuzzes the vendored tree-sitter shim with libFuzzer. A run that "
        "finds nothing is not evidence of safety.\n")
    lines.append("## Reproduce\n")
    lines.append("```sh\n"
                 f"python3 scry/scripts/fuzz-lower.py --iterations {args.iterations} "
                 f"--seed {args.seed} --timeout {args.timeout:g} "
                 f"--memory-mb {args.memory_mb}\n"
                 "python3 scry/scripts/fuzz-lower.py --regressions-only\n"
                 "```\n")
    lines.append(f"* scry: `{scry_version}`")
    lines.append(f"* seed corpus: {seeds} C files from `bench/corpus`, "
                 "`tests/fixtures`, `corpus` and `fuzz/lower/seeds`")
    lines.append(f"* executions: {args.iterations}; wall time: {elapsed:.1f} s")
    lines.append(f"* per-run limits: {args.timeout:g} s, "
                 f"{args.memory_mb} MiB **resident** memory "
                 "(the kernel-killed process is reported as `oom`), core dumps off, "
                 "process group killed on timeout\n")
    lines.append("* categories: " + ", ".join(
        f"{c} {counts.get(c, 0)}" for c in CAT_ORDER) + "\n")
    if not findings:
        lines.append("## Findings\n\nNo crash, hang, OOM or oracle violation "
                     "in this bounded run.\n")
    else:
        lines.append("## Findings\n")
        lines.append("| id | category | mode | input | cpu/wall | peak RSS | signal | class | minimised | repro |")
        lines.append("|---|---|---|---|---|---|---|---|---|---|")
        for f in findings:
            m = f.minimised if f.minimised is not None else f.data
            repro = f"`{f.fixture}`" if f.fixture else \
                f"seed {f.seed} iter {f.iteration}"
            lines.append(
                f"| {f.fid} | {f.category} | {f.mode} | {human_bytes(len(f.data))} "
                f"| {f.run.cpu_ms}/{f.run.wall_ms} ms | {f.run.peak_rss_mb} MiB "
                f"| {f.run.sig or f.run.reason} "
                f"| {f.origin} | {human_bytes(len(m))} | {repro} |")
        lines.append("")
        lines.append("### Signatures and notes\n")
        for f in findings:
            lines.append(f"* **{f.fid}** `{f.run.signature()}` "
                         f"(sha256 `{sha(f.data)[:16]}`, cpu {f.run.cpu_ms} ms, "
                         f"wall {f.run.wall_ms} ms, peak RSS {f.run.peak_rss_mb} MiB)"
                         + (f" — {f.note}" if f.note else ""))
            err = norm_stderr(f.run.stderr, 300)
            if err:
                lines.append(f"  * stderr: `{err}`")
            lines.append(f"  * minimise: {f.minimise_evals} evaluation(s), "
                         f"{human_bytes(len(f.data))} -> "
                         f"{human_bytes(len(f.minimised if f.minimised is not None else f.data))}"
                         + (" (changed)" if f.minimised_changed else " (unchanged)"))
        lines.append("")
    lines.append("## Method\n")
    lines.append(
        "The generator mixes (a) byte/token mutations of the checked-in C "
        "corpus, (b) random bytes over a C-ish alphabet, (c) deeply nested "
        "expressions, declarations, initialisers, blocks and control flow "
        "(128 to 131 072 levels), (d) unterminated strings, comments, "
        "preprocessor conditionals and brackets, (e) pathological sizes "
        "(million-digit literals, 200 000-statement functions, 20 000 "
        "parameters, megabyte identifiers and comments), (f) small random "
        "but syntactically valid programs and (g) 2-8 MiB single-node inputs "
        "(one string literal, comment or wide initialiser) for the memory "
        "ratio. A small share also feeds deeply "
        "nested JSON fact stores to `scry facts`/`parse --stats` (the same "
        "loader process). Each input is run through one of "
        "`scry taint --allow-errors --json`, `scry parse --stats`, "
        "`scry facts` or `scry fuzz-span --json`; every tenth lowering run "
        "omits `--timeout` so the external sandbox is the only bound. A sample "
        "of clean runs is cross-checked between `parse --stats` and "
        "`fuzz-span --json` (same shim, two store paths), and every exit-0 JSON "
        "output is checked for malformed or negative spans. Findings are "
        "delta-minimised under the same sandbox after the campaign and "
        "deduplicated by category, fault signal and generator variant.\n")
    lines.append(
        "Hang classification uses **CPU time**, not wall time: the host is "
        "shared and a 300 ms launch can take 30 s to be scheduled. A run killed "
        "by the external timeout with less than a quarter of its interval on "
        "the CPU is counted as `stalled` (not a finding). The memory cap is on "
        "**resident** memory (VmRSS, sampled every 10 ms). RLIMIT_AS is not "
        "used: the runtime reserves a much larger virtual arena than it "
        "touches (VmPeak 1.5 GiB for a 4 MiB parse, VmRSS 459 MiB), so an "
        "address-space cap aborts an ordinary input with a SIGSEGV that looks "
        "exactly like a parser crash. A fatal signal "
        "at or above 90% of the RSS cap is reported as OOM, and a crash with "
        "the cap still in force is re-run once with the cap disabled; only a "
        "crash that reproduces without the cap is reported as `crash`.\n")
    lines.append("## Limits\n")
    lines.append(
        "* One machine, one binary, one RNG seed; a different build can behave "
        "differently. The counts are observations, not a coverage claim.\n"
        "* The RSS cap is a policy limit, not a proof: an input that exceeds "
        "it is reported as OOM even if the analyser would eventually succeed "
        "with a larger heap. Sampling every 10 ms can miss a short-lived "
        "allocation; a process that dies just below the cap is still treated "
        "as an OOM.\n"
        "* Minimisation is bounded (a shared evaluation budget); a minimised "
        "input can still contain irrelevant bytes and can exercise a different "
        "path from the original.\n"
        "* `wrong-but-terminating` checks are invariants on the output (valid "
        "JSON, spans ordered, parse/fuzz-span counts agree), not a semantic "
        "correctness oracle for taint results.\n")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


# ---------------------------------------------------------------------------
# Main


def scry_version(scry: str) -> str:
    try:
        p = subprocess.run([scry, "--version"], cwd=str(SCRY_DIR), text=True,
                           stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                           timeout=20)
        return p.stdout.strip().splitlines()[0] if p.stdout.strip() else "unknown"
    except (OSError, subprocess.TimeoutExpired):
        return "unknown"


def replay_regressions(args: argparse.Namespace) -> int:
    manifests = sorted(FINDINGS_DIR.glob("*.json"))
    cases = sorted(FINDINGS_DIR.glob("*.c"))
    if not cases:
        say(f"no regression fixtures in {FINDINGS_DIR.relative_to(ROOT)}")
        return 0
    meta: dict[str, dict] = {}
    for m in manifests:
        try:
            for e in json.loads(m.read_text()):
                meta[e.get("file", "")] = e
        except (OSError, json.JSONDecodeError):
            continue
    bad = 0
    print("id\tcategory\tmode\texpect\tresult")
    for p in cases:
        data = p.read_bytes()
        m = meta.get(p.name, {})
        mode = m.get("mode", "taint")
        expect = m.get("category", "")
        # Replay with the limits the fixture was minimised under: a fixture
        # minimised at a 3 s budget or a 256 MiB RSS cap does not reproduce
        # under an unlimited or 2 GiB run. `timeout_s` is recorded for new
        # manifests; the fallback is the minimisation budget.
        mem = m.get("memory_mb", args.memory_mb)
        limit = float(m.get("timeout_s", min(3.0, args.timeout)))
        r = execute([args.scry, *mode_cmd(mode, max(1, int(limit)))],
                    data, args, timeout=limit, mem_mb=mem)
        cat = oracle(mode, data, r) and "wrong" or r.category
        state = "ok"
        if expect and cat != expect:
            if cat == "clean":
                state = "fixed"
            elif {cat, expect} <= {"hang", "oom"}:
                # Both are non-terminating outcomes; the exact boundary can
                # move by one scheduling quantum under load.
                state = f"ok ({cat})"
            else:
                state = f"MISMATCH({cat})"
                bad += 1
        print(f"{p.stem}\t{cat}\t{mode}\t{expect or '-'}\t{state}")
    return 1 if bad else 0


def main(argv: Optional[list[str]] = None) -> int:
    args = parse_args(argv)
    if args.ci:
        args.iterations = min(args.iterations, 120)
        args.timeout = min(args.timeout, 3.0)
        args.memory_mb = min(args.memory_mb, 2048)
        args.no_minimise = True
    scry = str(Path(args.scry).resolve())
    if not Path(scry).is_file():
        say(f"scry binary not found: {scry}\n"
            "  build it with: (cd scry && grail build scry)")
        return 1
    # The Wiz runtime reserves a multi-gigabyte virtual arena; a cap on
    # address space would abort even `--version`. The cap is on RSS instead
    # (see `execute`), so there is nothing to probe for here.
    if args.regressions_only:
        return replay_regressions(args)

    out = Path(args.out)
    if not out.is_absolute():
        out = ROOT / out
    out.mkdir(parents=True, exist_ok=True)
    findings_dir = out / "findings"
    findings_dir.mkdir(exist_ok=True)

    seeds, seed_paths = load_seeds()
    say(f"{len(seeds)} seed file(s) from "
        + ", ".join(str(d.relative_to(ROOT)) for d in SEED_DIRS if d.is_dir()))
    rng = random.Random(args.seed)
    counts: dict[str, int] = {c: 0 for c in CAT_ORDER}
    findings: list[Finding] = []
    by_key: dict[tuple[str, str, str, str], Finding] = {}
    cap_checked: set[tuple[str, str]] = set()
    cap_induced: set[tuple[str, str]] = set()
    start = time.monotonic()
    version = scry_version(scry)

    for it in range(args.iterations):
        data, mode, origin = generate(rng, seeds, it)
        run = execute([scry, *mode_cmd(mode, max(1, int(args.timeout)))],
                      data, args)
        reason = oracle(mode, data, run) if run.category == "clean" else None
        if reason:
            run.category, run.reason = "wrong", reason
        # Periodic differential check; it is cheap relative to the whole run
        # and is the only semantic oracle that does not need ground truth.
        if run.category == "clean" and mode in ("taint", "taint-open") and it % 7 == 0:
            why = differential(data, run, args)
            if why:
                run.category, run.reason = "wrong", why
        # A fatal signal under RLIMIT_AS can be the runtime's response to a
        # failed allocation rather than a parser/lowering bug. Verify once per
        # crash class without the cap: if it no longer crashes there, every
        # event in that class is an OOM (with the signal in the note), not a
        # crash.
        if (run.category == "crash" and args.memory_mb > 0
                and run.sig in ("SIGSEGV", "SIGABRT")):
            k = (run.sig, origin.split(":")[0])
            if k not in cap_checked:
                cap_checked.add(k)
                v = execute([scry, *mode_cmd(mode, max(1, int(args.timeout)))],
                            data, args, timeout=min(args.timeout, 20.0), mem_mb=0)
                if v.category != "crash":
                    cap_induced.add(k)
            if k in cap_induced:
                run.category = "oom"
                run.reason = f"memory-cap:{run.sig}-without-cap"
        counts[run.category] = counts.get(run.category, 0) + 1
        if args.verbose:
            say(f"[{it:04d}] {mode:5s} {origin:28s} {run.category:7s} "
                f"{run.wall_ms:5d}ms {human_bytes(len(data))}")
        if run.category in ("crash", "hang", "oom", "wrong"):
            # An OOM is a property of the shared native store, not of the
            # subcommand: dedup across taint/parse/fuzz-span so one memory
            # blow-up does not become three near-identical fixtures.
            mode_key = "*" if run.category == "oom" else mode
            key = (run.category,
                   "hang" if run.category == "hang" else run.signature(),
                   origin_class(origin), mode_key)
            existing = by_key.get(key)
            if existing is not None:
                # Hold the smallest raw input for the class; minimisation is
                # run once at the end, after every iteration has been seen.
                if len(data) < len(existing.data):
                    existing.data, existing.run = data, run
                    existing.origin, existing.iteration = origin, it
                    existing.minimised = None
                    existing.minimised_changed = False
                continue
            fid = f"F{len(findings) + 1:03d}"
            f = Finding(fid, run.category, mode, origin, data, run, it, args.seed)
            by_key[key] = f
            findings.append(f)
            say(f"[{it:04d}] {fid} {run.category} {run.signature()} "
                f"{origin} {human_bytes(len(data))} {run.wall_ms}ms")
        if (it + 1) % 25 == 0:
            say(f"{it + 1}/{args.iterations} executions; "
                + ", ".join(f"{c}={counts[c]}" for c in CAT_ORDER if counts[c]))

    # Minimise one representative per class, then preserve the reproducible
    # artifact. This is after the campaign so a replacement candidate can be
    # the smallest input seen, not merely the first.
    for f in findings:
        note = ""
        if not args.no_minimise:
            budget = [args.max_minimise_evals]
            mini, left, changed = minimise(f.data, f.mode, f.origin, args, f.run, budget)
            if changed:
                # Confirm the smaller form in the same sandbox before it
                # becomes the regression fixture. A one-off memory-cap crash
                # must not be minimised into a different defect.
                v = execute([scry, *mode_cmd(f.mode, 4)],
                            mini, args, timeout=min(3.0, args.timeout))
                if f.run.category == "hang":
                    ok = v.category == "hang"
                else:
                    ok = (v.category, v.signature()) == (f.run.category, f.run.signature())
                if ok:
                    f.minimised, f.minimised_changed = mini, True
                else:
                    note = "minimised form did not reproduce; kept the original"
            f.minimise_evals = args.max_minimise_evals - left
        body = f.minimised if f.minimised is not None else f.data
        safe = slug(f"{f.fid}-{f.run.signature()}-{f.origin}")
        (findings_dir / f"{safe}.c").write_bytes(body)
        f.note = f"artifact `{safe}.c`" + (f"; {note}" if note else "")
        if args.no_minimise:
            say(f"{f.fid} not minimised (--no-minimise)")
        else:
            say(f"{f.fid} minimised {human_bytes(len(f.data))} -> "
                f"{human_bytes(len(body))} in {f.minimise_evals} eval(s)")

    elapsed = time.monotonic() - start
    # Regression fixtures: copy minimised crash/hang/oom/wrong inputs.
    if findings:
        FINDINGS_DIR.mkdir(parents=True, exist_ok=True)
    manifest = []
    written: set[str] = set()
    for f in findings:
        # A fixture is the minimised bytes if they still reproduce, else the
        # original. `minimise` already verified the minimised form.
        body = f.minimised if f.minimised is not None else f.data
        name = f"fuzz-regression-{slug(f.run.signature() + '-' + f.origin)}.c"
        (FINDINGS_DIR / name).write_bytes(body)
        written.add(name)
        f.fixture = f"scry/tests/fixtures/fuzz-regression/{name}"
        manifest.append({
            "file": name, "category": f.category, "mode": f.mode,
            "signature": f.run.signature(), "origin": f.origin,
            "sha256": sha(body), "bytes": len(body),
            "wall_ms": f.run.wall_ms, "peak_rss_mb": f.run.peak_rss_mb,
            "memory_mb": args.memory_mb,
            "timeout_s": 3.0 if f.category == "hang" else min(5.0, args.timeout),
            "seed": f.seed, "iteration": f.iteration,
            "scry": version,
        })
    if manifest:
        # A regenerated set must not leave fixtures from an older run with no
        # manifest row (they would replay with the wrong mode).
        for old in FINDINGS_DIR.glob("fuzz-regression-*.c"):
            if old.name not in written:
                old.unlink()
        (FINDINGS_DIR / "manifest.json").write_text(
            json.dumps(manifest, indent=2) + "\n", encoding="utf-8")

    report = {
        "format": "scry-fuzz-lower", "version": 1, "seed": args.seed,
        "iterations": args.iterations, "scry": version,
        "limits": {"timeout_s": args.timeout, "memory_mb_rss": args.memory_mb,
                   "minimise_evals": args.max_minimise_evals},
        "seeds": len(seeds), "elapsed_s": round(elapsed, 2),
        "counts": counts,
        "findings": [
            {"id": f.fid, "category": f.category, "mode": f.mode,
             "origin": f.origin, "signature": f.run.signature(),
             "bytes": len(f.data), "wall_ms": f.run.wall_ms,
             "cpu_ms": f.run.cpu_ms, "peak_rss_mb": f.run.peak_rss_mb,
             "minimised_bytes": len(f.minimised) if f.minimised is not None else None,
             "minimise_evals": f.minimise_evals,
             "sha256": sha(f.data), "fixture": f.fixture,
             "seed": f.seed, "iteration": f.iteration,
             "stderr": norm_stderr(f.run.stderr)}
            for f in findings
        ],
    }
    (out / "report.json").write_text(json.dumps(report, indent=2) + "\n",
                                     encoding="utf-8")
    write_report(Path(args.markdown), findings, counts, args, len(seeds),
                 elapsed, version)
    say(f"done: {args.iterations} executions in {elapsed:.1f}s; "
        + ", ".join(f"{c}={counts[c]}" for c in CAT_ORDER)
        + f"; report {Path(args.markdown).relative_to(ROOT) if Path(args.markdown).is_relative_to(ROOT) else args.markdown}")
    if args.fail_on_findings and findings:
        return 1
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except KeyboardInterrupt:
        say("interrupted")
        sys.exit(130)
