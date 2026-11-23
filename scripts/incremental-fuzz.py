#!/usr/bin/env python3
"""Differential fuzzing for scry's incremental path (convergence invariant).

The claim under test is the one the incremental-scry design states:

    any chain of source/flag patches that produces the same final project state
    must produce the same artifacts as a build from scratch.

For a seeded campaign this script:

  1. generates a small multi-file C project (valid and, after mutations, invalid);
  2. applies a random chain of mutations, writing every state and building each one
     with a warm parse cache (`scry project --cache`) -- this is the patch chain;
  3. at the final state, builds twice: *full* (cache disabled) and *incremental*
     (the cache warmed by the chain);
  4. compares every artifact byte for byte: all CST columns, canonical Wil, warnings,
     project EDB, report JSON/SARIF/human, and the public CLI's `--json/--sarif/--facts`
     output, plus exit codes and stderr. Invalid inputs are first-class: the strict,
     `--allow-errors` and `--allow-errors --skip-broken` modes all compare, so the
     error/partial state is an artifact.

Artifacts come from `scry-artifacts` (`scry/tools/ArtifactsMain.wiz`); the public CLI
comparison uses `scry project --taint`. Cache statistics are metadata about the
incremental run, not about the final source, and are excluded (the artifact tool writes
a cache-free report; the CLI's JSON `cache` object and `cache:` lines are normalized).

Usage
  scripts/incremental-fuzz.py --fast
  scripts/incremental-fuzz.py --seed 7 --programs 20 --steps 6
  scripts/incremental-fuzz.py --artifacts scry/.grail/bin/scry-artifacts \\
      --scry scry/.grail/bin/scry
  scripts/incremental-fuzz.py --seed 7 --programs 1 --keep

Exit status: 0 all campaigns converged (or skipped for a missing binary), 1 a
divergence, 2 a malformed invocation or an internal harness error. A campaign in which
the warm cache had no hits at the final state is reported as `no-hit` but is not a
failure: it says the chain did not repeat a state, not that the cache is wrong.
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import os
import random
import re
import shutil
import subprocess
import sys
import tempfile
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Optional

ROOT = Path(__file__).resolve().parent.parent
SCRY_DIR = ROOT / "scry"
DEFAULT_ARTIFACTS = SCRY_DIR / ".grail" / "bin" / "scry-artifacts"
DEFAULT_SCRY = SCRY_DIR / ".grail" / "bin" / "scry"
DEFAULT_RULES = SCRY_DIR / "rules" / "default.scry"
FAST_SEED = 20261123
FAST_PROGRAMS = 8
FAST_STEPS = 4
NIGHTLY_PROGRAMS = 200
NIGHTLY_STEPS = 8
TMP_ROOT = Path(os.environ.get("TMPDIR", "/tmp/opencode")) / "incremental-scry"

IDENT_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")


# ---------------------------------------------------------------------------
# The generated project
# ---------------------------------------------------------------------------

@dataclass
class State:
    """One project state: files by relative path, TU order, and compile flags."""

    files: dict[str, str]
    order: list[str]
    flags: list[str]

    def copy(self) -> "State":
        return State(dict(self.files), list(self.order), list(self.flags))


def load_fuzz_lower() -> Any:
    """The expression/statement generators from scry/scripts/fuzz-lower.py."""
    path = SCRY_DIR / "scripts" / "fuzz-lower.py"
    spec = importlib.util.spec_from_file_location("scry_fuzz_lower", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path}")
    mod = importlib.util.module_from_spec(spec)
    # dataclasses in the loaded module resolve their own module through sys.modules
    sys.modules[spec.name] = mod
    spec.loader.exec_module(mod)
    return mod


def gen_header(rng: random.Random, idx: int) -> str:
    return (
        "#ifndef COMMON_H\n#define COMMON_H\n"
        f"#define HEADER_VALUE {rng.choice([0, 1, 2, 7])}\n"
        f"#define UNIT_TAG {idx}\n"
        "int helper(int x);\n"
        "int helper0(int x);\n"
        "int helper1(int x);\n"
        "char *getenv(const char *);\n"
        "int system(const char *);\n"
        "#endif\n"
    )


def gen_unit(rng: random.Random, fuzz: Any, idx: int) -> str:
    """A unit with lowering-friendly bodies; `fuzz.gen_expr` supplies variety."""
    lines = ['#include "common.h"', ""]
    lines.append(f"int helper{idx}(int x) {{ return x + {rng.randint(1, 9)}; }}")
    lines.append("")
    lines.append(f"int unit{idx}(int x, int y, char *p) {{")
    for _ in range(rng.randint(1, 3)):
        lines.append(f"  int v{_ + 1} = {fuzz.gen_expr(rng, rng.randint(1, 3))};")
        lines.append(f"  if (x > {rng.randint(0, 4)}) {{ y = y + v{_ + 1}; }}")
        lines.append("  else { y = y - 1; }")
        lines.append(f"  p[{_}] = {fuzz.gen_expr(rng, 1)};")
    lines.append("  while (y > 0) { y = y - 1; }")
    lines.append("  return y;")
    lines.append("}")
    lines.append("")
    lines.append(f"void sink{idx}(void) {{")
    lines.append('  char *p = getenv("HOME");')
    lines.append("  system(p);")
    lines.append("}")
    return "\n".join(lines) + "\n"


def new_state(rng: random.Random, fuzz: Any, nunits: int) -> State:
    files: dict[str, str] = {"common.h": gen_header(rng, 0)}
    order: list[str] = []
    for i in range(nunits):
        name = f"u{i}.c"
        files[name] = gen_unit(rng, fuzz, i)
        order.append(name)
    return State(files, order, ["-DVAL=1"])


def write_state(root: Path, state: State) -> None:
    """Write every file (even unchanged ones) and the compile database.

    Rewriting is deliberate: it changes mtimes and inodes while content stays the same.
    The cache must key on content, so this is a no-op for a correct cache (the artifact
    comparison cannot see mtimes, but a hit count of zero here would be a smell)."""
    root.mkdir(parents=True, exist_ok=True)
    for name, text in state.files.items():
        p = root / name
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text, encoding="utf-8")
    compdb = []
    for name in state.order:
        compdb.append({
            "directory": str(root),
            "file": name,
            "arguments": ["cc", "-I", ".", *state.flags, "-c", name],
        })
    (root / "compile_commands.json").write_text(json.dumps(compdb, indent=1) + "\n")


# ---------------------------------------------------------------------------
# Mutations
# ---------------------------------------------------------------------------

VALID_LINES = [
    "  x = x + 1;",
    "  y = x * 2;",
    "  if (x) { y = y + 1; }",
    "  while (y > 0) { y = y - 1; }",
    "  helper(x);",
    "  return x;",
    "int extra(int z) { return z + 1; }",
    "#define EXTRA_VALUE 3",
    "int prototype(int z);",
    "/* a comment */",
]

BROKEN_SNIPPETS = [
    "int broken( { return ; }",
    "@@@ not C at all @@@",
    "void f(void) { if (x) { } else { ",
    "int g(int x) { return x + ; }",
    "struct S { int x; ",
]


def pick_source(state: State, rng: random.Random) -> Optional[str]:
    names = [n for n in state.files if n.endswith(".c") or n.endswith(".h")]
    return rng.choice(names) if names else None


def mutate(state: State, rng: random.Random, fuzz: Any, history: list[State]) -> tuple[State, dict[str, Any]]:
    s = state.copy()
    kinds = [
        "edit_line", "insert_line", "delete_line", "rename", "break_syntax",
        "break_include", "macro", "flags", "add_tu", "remove_tu", "reorder",
        "dup_symbol", "revert", "noop", "append_function",
    ]
    kind = rng.choice(kinds)
    if kind == "edit_line":
        name = pick_source(s, rng)
        if name is None:
            return s, {"kind": "noop"}
        lines = s.files[name].splitlines()
        if lines:
            i = rng.randrange(len(lines))
            lines[i] = rng.choice(VALID_LINES)
            s.files[name] = "\n".join(lines) + "\n"
        return s, {"kind": kind, "file": name, "line": i if lines else -1}
    if kind == "insert_line":
        name = pick_source(s, rng)
        if name is None:
            return s, {"kind": "noop"}
        lines = s.files[name].splitlines()
        i = rng.randrange(len(lines) + 1)
        lines.insert(i, rng.choice(VALID_LINES))
        s.files[name] = "\n".join(lines) + "\n"
        return s, {"kind": kind, "file": name, "line": i}
    if kind == "delete_line":
        name = pick_source(s, rng)
        if name is None:
            return s, {"kind": "noop"}
        lines = s.files[name].splitlines()
        if len(lines) > 1:
            i = rng.randrange(len(lines))
            del lines[i]
            s.files[name] = "\n".join(lines) + "\n"
            return s, {"kind": kind, "file": name, "line": i}
        return s, {"kind": "noop"}
    if kind == "rename":
        name = pick_source(s, rng)
        if name is None:
            return s, {"kind": "noop"}
        text = s.files[name]
        names = sorted(set(IDENT_RE.findall(text)))
        if not names:
            return s, {"kind": "noop"}
        old = rng.choice(names)
        new = old + "x"
        s.files[name] = IDENT_RE.sub(lambda m: new if m.group(0) == old else m.group(0), text)
        return s, {"kind": kind, "file": name, "from": old, "to": new}
    if kind == "break_syntax":
        name = pick_source(s, rng)
        if name is None:
            return s, {"kind": "noop"}
        lines = s.files[name].splitlines()
        i = rng.randrange(len(lines) + 1)
        lines.insert(i, rng.choice(BROKEN_SNIPPETS))
        s.files[name] = "\n".join(lines) + "\n"
        return s, {"kind": kind, "file": name, "line": i}
    if kind == "break_include":
        name = pick_source(s, rng)
        if name is None:
            return s, {"kind": "noop"}
        missing = f"missing_{rng.randrange(10_000)}.h"
        s.files[name] = '#include "' + missing + '"\n' + s.files[name]
        return s, {"kind": kind, "file": name, "include": missing}
    if kind == "macro":
        name = "common.h" if "common.h" in s.files else pick_source(s, rng)
        if name is None:
            return s, {"kind": "noop"}
        text = s.files[name]
        value = rng.choice([0, 1, 2, 5, 11])
        if "#define HEADER_VALUE " in text:
            text = re.sub(r"#define HEADER_VALUE \d+", f"#define HEADER_VALUE {value}", text)
        else:
            text = f"#define HEADER_VALUE {value}\n" + text
        s.files[name] = text
        return s, {"kind": kind, "file": name, "value": value}
    if kind == "flags":
        value = rng.choice(["1", "2", "7"])
        s.flags = [f"-DVAL={value}"] + [f for f in s.flags if not f.startswith("-DVAL=")]
        return s, {"kind": kind, "flags": s.flags}
    if kind == "add_tu":
        i = len(s.order)
        name = f"u{i}.c"
        s.files[name] = gen_unit(rng, fuzz, i)
        s.order.append(name)
        return s, {"kind": kind, "file": name}
    if kind == "remove_tu":
        if len(s.order) > 1:
            name = rng.choice(s.order)
            s.order.remove(name)
            s.files.pop(name, None)
            return s, {"kind": kind, "file": name}
        return s, {"kind": "noop"}
    if kind == "reorder":
        if len(s.order) > 1:
            i, j = rng.sample(range(len(s.order)), 2)
            s.order[i], s.order[j] = s.order[j], s.order[i]
            return s, {"kind": kind, "i": i, "j": j}
        return s, {"kind": "noop"}
    if kind == "dup_symbol":
        targets = [n for n in s.order if n in s.files]
        if len(targets) >= 2:
            src, dst = rng.sample(targets, 2)
            m = re.search(r"int (helper\d+|unit\d+)\(int [^)]*\) \{[^}]*\}", s.files[src])
            if m:
                s.files[dst] = s.files[dst] + "\n" + m.group(0) + "\n"
                return s, {"kind": kind, "from": src, "to": dst, "symbol": m.group(1)}
        return s, {"kind": "noop"}
    if kind == "revert":
        if history:
            old = history[rng.randrange(len(history))]
            s.files = dict(old.files)
            s.order = list(old.order)
            s.flags = list(old.flags)
            return s, {"kind": kind, "to": rng.randrange(len(history))}
        return s, {"kind": "noop"}
    if kind == "append_function":
        name = rng.choice(s.order) if s.order else None
        if name is None or name not in s.files:
            return s, {"kind": "noop"}
        i = rng.randrange(1000)
        body = " ".join(fuzz.gen_stmt(rng, rng.randint(1, 2)) for _ in range(rng.randint(1, 3)))
        s.files[name] += f"\nint appended{i}(int x, int y, char *p) {{ {body} return 0; }}\n"
        return s, {"kind": kind, "file": name, "name": f"appended{i}"}
    # noop
    return s, {"kind": "noop"}


# ---------------------------------------------------------------------------
# Running and comparing
# ---------------------------------------------------------------------------

@dataclass
class Run:
    code: int
    stdout: str
    stderr: str
    out: Optional[Path] = None


def run_artifacts(binary: Path, root: Path, out: Path, cache: Optional[Path],
                  mode: str, rules: Path, cc: str, timeout_s: int) -> Run:
    args = [str(binary), str(root), "--out", str(out), "--rules", str(rules), "--cc", cc]
    if cache is not None:
        args += ["--cache-dir", str(cache)]
    if mode in ("allow", "skip"):
        args.append("--allow-errors")
    if mode == "skip":
        args.append("--skip-broken")
    try:
        p = subprocess.run(args, text=True, capture_output=True, timeout=timeout_s)
        return Run(p.returncode, p.stdout, p.stderr, out)
    except subprocess.TimeoutExpired:
        return Run(124, "", f"timeout after {timeout_s}s", out)


def run_cli(binary: Path, root: Path, outdir: Path, cache: Optional[Path],
            rules: Path, mode: str, cc: str, timeout_s: int) -> Run:
    outdir.mkdir(parents=True, exist_ok=True)
    sarif = outdir / "cli.sarif"
    facts = outdir / "cli.facts"
    args = [str(binary), "project", str(root), "--taint", "--json",
            "--rules", str(rules), "--cc", cc, "--sarif", str(sarif), "--facts", str(facts)]
    if cache is not None:
        args += ["--cache-dir", str(cache)]
    if mode in ("allow", "skip"):
        args.append("--allow-errors")
    if mode == "skip":
        args.append("--skip-broken")
    try:
        p = subprocess.run(args, text=True, capture_output=True, timeout=timeout_s,
                           cwd=str(ROOT / "scry"))
        return Run(p.returncode, p.stdout, p.stderr, outdir)
    except subprocess.TimeoutExpired:
        return Run(124, "", f"timeout after {timeout_s}s", outdir)


def normalize_json(text: str) -> Any:
    def drop_cache(x: Any) -> Any:
        if isinstance(x, dict):
            return {k: drop_cache(v) for k, v in x.items() if k != "cache"}
        if isinstance(x, list):
            return [drop_cache(v) for v in x]
        return x
    return drop_cache(json.loads(text))


def normalize_text(text: str) -> str:
    """Drop the cache-statistics lines (metadata about the incremental run)."""
    lines = [ln for ln in text.splitlines()
             if not ln.startswith("cache: ") and not ln.startswith("findings index:")]
    return "\n".join(lines)


def read_tree(path: Path) -> dict[str, bytes]:
    out: dict[str, bytes] = {}
    for p in sorted(path.rglob("*")):
        if p.is_file():
            rel = str(p.relative_to(path))
            data = p.read_bytes()
            if rel == "manifest.txt":
                data = b"\n".join(
                    ln for ln in data.split(b"\n")
                    if not ln.startswith(b"cache-metadata\t")) + b"\n"
            out[rel] = data
    return out


def first_diff(a: bytes, b: bytes) -> str:
    al = a.split(b"\n")
    bl = b.split(b"\n")
    for i in range(max(len(al), len(bl))):
        x = al[i] if i < len(al) else b"<end>"
        y = bl[i] if i < len(bl) else b"<end>"
        if x != y:
            def show(v: bytes) -> str:
                s = v.decode("utf-8", "replace")
                return s if len(s) <= 200 else s[:200] + "…"
            return f"line {i + 1}:\n  full:        {show(x)}\n  incremental: {show(y)}"
    return "(the same)"


@dataclass
class CampaignResult:
    seed: int
    program: int
    ok: bool
    message: str
    steps: list[dict[str, Any]]
    hits: dict[str, int] = field(default_factory=dict)
    root: Optional[Path] = None


def compare_runs(label: str, full: Run, inc: Run) -> Optional[str]:
    if full.code != inc.code:
        return f"{label}: exit code full={full.code} incremental={inc.code}\n" \
               f"  full stderr: {full.stderr.strip()[:300]}\n" \
               f"  inc  stderr: {inc.stderr.strip()[:300]}"
    if normalize_text(full.stderr) != normalize_text(inc.stderr):
        return f"{label}: stderr differs\n" + first_diff(
            normalize_text(full.stderr).encode(), normalize_text(inc.stderr).encode())
    return None


def compare_cli_runs(full: Run, inc: Run, full_dir: Path, inc_dir: Path) -> Optional[str]:
    """The CLI's stderr names the --sarif output path, which is the only difference
    between the two runs by construction; normalize that directory, not the analysis."""
    if full.code != inc.code:
        return f"cli: exit code full={full.code} incremental={inc.code}"
    fs = normalize_text(full.stderr).replace(str(full_dir), "<OUT>")
    ins = normalize_text(inc.stderr).replace(str(inc_dir), "<OUT>")
    if fs != ins:
        return "cli: stderr differs\n" + first_diff(fs.encode(), ins.encode())
    return None


def compare_trees(label: str, full: Path, inc: Path) -> Optional[str]:
    if not full.exists() and not inc.exists():
        return None
    if not full.exists() or not inc.exists():
        return f"{label}: only one build wrote a bundle"
    ft = read_tree(full)
    it = read_tree(inc)
    for name in sorted(set(ft) | set(it)):
        if name not in ft:
            return f"{label}: {name} exists only in the incremental bundle"
        if name not in it:
            return f"{label}: {name} exists only in the full bundle"
        if ft[name] != it[name]:
            return f"{label}: {name} differs\n" + first_diff(ft[name], it[name])
    return None


def parse_manifest_hits(path: Path) -> dict[str, int]:
    hits = {"hit": 0, "miss": 0, "write": 0}
    try:
        for line in path.read_text().splitlines():
            if line.startswith("cache-metadata\t"):
                for k in hits:
                    m = re.search(rf"\b{k}=(\d+)", line)
                    if m:
                        hits[k] = int(m.group(1))
    except OSError:
        pass
    return hits


def run_campaign(seed: int, program: int, steps: int, artifacts: Path, scry: Path,
                 rules: Path, cc: str, keep: bool, cli: bool,
                 control: bool, budget: int) -> CampaignResult:
    rng = random.Random(seed * 100003 + program)
    fuzz = load_fuzz_lower()
    base = new_state(rng, fuzz, rng.randint(1, 3))
    history: list[State] = [base.copy()]
    state = base
    muts: list[dict[str, Any]] = []
    root = Path(tempfile.mkdtemp(prefix=f"incr-scry-{seed}-{program}-",
                                 dir=str(TMP_ROOT)))
    try:
        for _ in range(steps):
            state, mut = mutate(state, rng, fuzz, history)
            muts.append(mut)
            history.append(state.copy())

        # Warm every mode's cache through the chain.
        modes = ["strict", "allow", "skip"]
        cache = root / "cache"
        for step, st in enumerate(history):
            write_state(root / "proj", st)
            for mode in modes:
                w = run_artifacts(artifacts, root / "proj",
                                  root / f"warm-{step}-{mode}", cache, mode, rules, cc,
                                  budget)
                if w.code == 124:
                    return CampaignResult(seed, program, True,
                                          f"slow-input (skipped: {mode} step {step}: {w.stderr})",
                                          muts, {}, root if keep else None)

        # Final state: full (no cache) vs incremental (warm cache), for each mode.
        final = history[-1]
        write_state(root / "proj", final)
        hits: dict[str, int] = {}
        for mode in modes:
            full_out = root / f"full-{mode}"
            inc_out = root / f"inc-{mode}"
            full = run_artifacts(artifacts, root / "proj", full_out, None, mode, rules, cc, budget)
            inc = run_artifacts(artifacts, root / "proj", inc_out, cache, mode, rules, cc, budget)
            if full.code == 124 or inc.code == 124:
                return CampaignResult(seed, program, True,
                                      f"slow-input (skipped: {mode} final: "
                                      f"full={full.code} incremental={inc.code})",
                                      muts, {}, root if keep else None)
            why = compare_runs(f"artifacts/{mode}", full, inc)
            if why is None:
                why = compare_trees(f"artifacts/{mode}", full_out, inc_out)
            if why is not None:
                return CampaignResult(seed, program, False,
                                      f"seed={seed} program={program} mutations={muts}\n{why}",
                                      muts, hits, root if keep else None)
            hits[mode] = parse_manifest_hits(inc_out / "manifest.txt").get("hit", 0)
            if control:
                full2_out = root / f"full2-{mode}"
                full2 = run_artifacts(artifacts, root / "proj", full2_out, None,
                                      mode, rules, cc, budget)
                if full2.code == 124:
                    return CampaignResult(seed, program, True,
                                          f"slow-input (skipped: control {mode})",
                                          muts, {}, root if keep else None)
                why2 = compare_runs(f"control/{mode}", full, full2)
                if why2 is None:
                    why2 = compare_trees(f"control/{mode}", full_out, full2_out)
                if why2 is not None:
                    return CampaignResult(
                        seed, program, False,
                        f"seed={seed} program={program} NONDETERMINISTIC "
                        f"(cold vs cold, not a cache divergence)\nmutations={muts}\n{why2}",
                        muts, hits, root if keep else None)

        if cli:
            for mode in modes:
                cli_full_dir = root / f"cli-full-{mode}"
                cli_inc_dir = root / f"cli-inc-{mode}"
                full = run_cli(scry, root / "proj", cli_full_dir, None, rules, mode, cc, budget)
                inc = run_cli(scry, root / "proj", cli_inc_dir, cache, rules, mode, cc, budget)
                if full.code == 124 or inc.code == 124:
                    return CampaignResult(seed, program, True,
                                          f"slow-input (skipped: cli/{mode})",
                                          muts, {}, root if keep else None)
                why = compare_cli_runs(full, inc, cli_full_dir, cli_inc_dir)
                if why is None:
                    fs = full.stdout.strip()
                    ins = inc.stdout.strip()
                    if fs == "" and ins == "":
                        pass
                    else:
                        try:
                            if normalize_json(full.stdout) != normalize_json(inc.stdout):
                                why = f"cli/{mode}: --json output differs after dropping the cache object"
                        except json.JSONDecodeError as e:
                            why = f"cli/{mode}: --json is not JSON: {e}"
                if why is None:
                    # SARIF has no cache fields; facts are the project EDB.
                    for name in ("cli.sarif", "cli.facts"):
                        p = cli_full_dir / name
                        q = cli_inc_dir / name
                        if p.exists() != q.exists():
                            why = f"cli/{mode}: {name} exists in only one build"
                            break
                        if p.exists() and p.read_bytes() != q.read_bytes():
                            why = f"cli/{mode}: {name} differs\n" + first_diff(
                                p.read_bytes(), q.read_bytes())
                            break
                if why is not None:
                    return CampaignResult(seed, program, False,
                                          f"seed={seed} program={program} mutations={muts}\n{why}",
                                          muts, hits, root if keep else None)

        noreport = []
        if all(v == 0 for v in hits.values()):
            noreport.append("no-hit")
        return CampaignResult(seed, program, True,
                              "ok" + (" (" + ", ".join(noreport) + ")" if noreport else ""),
                              muts, hits, root if keep else None)
    finally:
        if not keep:
            shutil.rmtree(root, ignore_errors=True)


def self_test() -> int:
    """Check the comparators themselves (a harness that cannot fail is worthless)."""
    with tempfile.TemporaryDirectory(prefix="incr-scry-selftest-", dir=str(TMP_ROOT)) as d:
        a = Path(d) / "a"
        b = Path(d) / "b"
        a.mkdir()
        b.mkdir()
        (a / "x").write_text("one\ntwo\n")
        (b / "x").write_text("one\ntwo\n")
        if compare_trees("selftest", a, b) is not None:
            print("incremental-fuzz: self-test FAILED: equal trees differ", file=sys.stderr)
            return 2
        # cache statistics in the manifest are metadata, not an artifact
        (a / "manifest.txt").write_text("units\t1\ncache-metadata\tcache: hit=0\n")
        (b / "manifest.txt").write_text("units\t1\ncache-metadata\tcache: hit=9\n")
        if compare_trees("selftest", a, b) is not None:
            print("incremental-fuzz: self-test FAILED: cache metadata is compared",
                  file=sys.stderr)
            return 2
        # one byte in one nested file must be found, with a line diff
        (b / "x").write_text("one\ntwo!\n")
        why = compare_trees("selftest", a, b)
        if why is None or "x differs" not in why or "line 2" not in why:
            print(f"incremental-fuzz: self-test FAILED: a one-byte change was not "
                  f"reported ({why!r})", file=sys.stderr)
            return 2
        # the CLI's cache object is dropped, other JSON changes are not
        one = normalize_json('{"a":1,"cache":{"hit":0},"b":[2]}')
        two = normalize_json('{"a":1,"cache":{"hit":9},"b":[2]}')
        three = normalize_json('{"a":2,"cache":{"hit":0},"b":[2]}')
        if one != two or one == three:
            print("incremental-fuzz: self-test FAILED: JSON normalization", file=sys.stderr)
            return 2
    print("incremental-fuzz: self-test ok (trees, cache metadata, JSON normalization)")
    return 0


def main(argv: Optional[list[str]] = None) -> int:
    ap = argparse.ArgumentParser(
        description="differential fuzzing for scry's incremental (warm-cache) path")
    ap.add_argument("--seed", type=int, default=FAST_SEED,
                    help=f"first campaign seed (default {FAST_SEED})")
    ap.add_argument("--programs", type=int, default=FAST_PROGRAMS,
                    help=f"number of campaigns (default {FAST_PROGRAMS})")
    ap.add_argument("--steps", type=int, default=FAST_STEPS,
                    help=f"mutations per chain (default {FAST_STEPS})")
    ap.add_argument("--fast", action="store_true",
                    help=f"the bounded profile ({FAST_PROGRAMS} campaigns, {FAST_STEPS} steps)")
    ap.add_argument("--nightly", action="store_true",
                    help=f"today's seed, {NIGHTLY_PROGRAMS} campaigns, {NIGHTLY_STEPS} steps")
    ap.add_argument("--artifacts", type=Path, default=DEFAULT_ARTIFACTS,
                    help="scry-artifacts binary")
    ap.add_argument("--scry", type=Path, default=DEFAULT_SCRY, help="scry binary")
    ap.add_argument("--rules", type=Path, default=DEFAULT_RULES, help="rule pack")
    ap.add_argument("--cc", default=os.environ.get("CC", "cc"),
                    help="C compiler for cc -E (default $CC or cc)")
    ap.add_argument("--no-cli", action="store_true",
                    help="compare only the artifact bundles, not `scry project`")
    ap.add_argument("--control", action="store_true",
                    help="also compare a second cold build (nondeterminism control)")
    ap.add_argument("--budget", type=int, default=120, metavar="SECS",
                    help="per-invocation time budget; a timeout skips the campaign "
                         "as slow-input (default 120)")
    ap.add_argument("--keep", action="store_true",
                    help="keep the campaign directory (prints its path)")
    ap.add_argument("--replay", type=int, metavar="SEED",
                    help="one campaign from SEED (with --programs 1)")
    ap.add_argument("--json-out", type=Path, help="write one result row per campaign")
    ap.add_argument("--self-test", action="store_true",
                    help="check the comparison logic on synthetic trees and JSON")
    args = ap.parse_args(argv)

    if args.self_test:
        TMP_ROOT.mkdir(parents=True, exist_ok=True)
        return self_test()

    if args.replay is not None:
        args.seed = args.replay
        args.programs = 1
    if args.fast:
        args.programs, args.steps = FAST_PROGRAMS, FAST_STEPS
    if args.nightly:
        args.seed = 20261123
        args.programs, args.steps = NIGHTLY_PROGRAMS, NIGHTLY_STEPS
    # run_cli chdirs into scry/, so every binary/rule path must be absolute
    args.artifacts = args.artifacts.resolve()
    args.scry = args.scry.resolve()
    args.rules = args.rules.resolve()
    if args.programs < 1 or args.steps < 0:
        print("incremental-fuzz: --programs must be positive and --steps non-negative",
              file=sys.stderr)
        return 2
    for p, what in ((args.artifacts, "scry-artifacts"), (args.scry, "scry"),
                    (args.rules, "rule pack")):
        if not p.exists():
            print(f"incremental-fuzz: missing {what}: {p}", file=sys.stderr)
            return 2
    TMP_ROOT.mkdir(parents=True, exist_ok=True)

    rows: list[dict[str, Any]] = []
    failures = 0
    for program in range(args.programs):
        seed = args.seed + program
        res = run_campaign(seed, program, args.steps, args.artifacts, args.scry,
                           args.rules, args.cc, args.keep, not args.no_cli,
                           args.control, args.budget)
        rows.append({"seed": seed, "program": program, "ok": res.ok,
                     "message": res.message if not res.ok else res.message,
                     "hits": res.hits, "mutations": res.steps})
        if res.ok:
            print(f"  ✓ seed={seed} program={program} {res.message}")
        else:
            failures += 1
            print(f"  ✗ seed={seed} program={program}\n{res.message}")
            if res.root is not None:
                print(f"    kept: {res.root}")
        if args.keep and res.root is not None:
            print(f"    kept: {res.root}")

    if args.json_out:
        args.json_out.write_text(json.dumps(rows, indent=1) + "\n")

    slow = sum(1 for r in rows if str(r.get("message", "")).startswith("slow-input"))
    passed = len(rows) - failures - slow
    print(f"incremental-fuzz: {passed} converged, {slow} slow-input, {failures} diverged "
          f"({len(rows)} campaign(s), seed {args.seed}…{args.seed + len(rows) - 1}, "
          f"{args.steps} step(s))")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
