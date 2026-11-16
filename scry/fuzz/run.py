#!/usr/bin/env python3
"""Coverage-guided fuzzing for scry's C front end.

The target is the vendored tree-sitter shim (`native/ts_shim.c`): libFuzzer mutates C
sources, the harness checks the struct-of-arrays contract, and the driver minimises and
deduplicates artifacts before writing a `dynamic` evidence report next to a static
`scry bench` report.

This is a bug-finding tool, not a verifier.  A bounded run that finds no crash says only
that this tool, on this machine, in this many executions, did not observe one.  It is not
evidence of safety, and it says nothing about the Wiz analysis pipeline above the shim.

Usage:

    python3 scry/fuzz/run.py --build --runs 20000 --time 30 \
        --static scry/build/bench.json --out scry/build/fuzz

Missing clang/libFuzzer or a missing `scry` binary is a clean skip (exit 0) with the
reason in the report; a malformed command is exit 2.
"""

from __future__ import annotations

import argparse
import glob
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Iterable, Optional


ROOT = Path(__file__).resolve().parents[2]
SCRY = ROOT / "scry"
FUZZ = SCRY / "fuzz"
BUILD = SCRY / "build" / "fuzz"

SANITIZERS = "fuzzer,address,undefined"
BASE_CFLAGS = [
    f"-fsanitize={SANITIZERS}",
    "-fno-sanitize-recover=undefined",
    "-fno-omit-frame-pointer",
    "-g",
    "-O1",
    "-std=c11",
    "-D_GNU_SOURCE",
    "-Wall",
    "-Wextra",
]
# ts_shim.c is the production shim, which links both grammars (`scry_parse` takes "c"
# or "c_sharp"), so the target links both too. Each grammar's parser.c/scanner.c finds
# its own `tree_sitter/*.h` beside it (quoted includes), so no per-grammar -I is needed.
SOURCES = ["ts_shim_fuzz.c", "../native/tree-sitter/lib/src/lib.c",
           "../native/tree-sitter-c/src/parser.c",
           "../native/tree-sitter-c-sharp/src/parser.c",
           "../native/tree-sitter-c-sharp/src/scanner.c"]

TARGET = BUILD / "ts_shim_fuzz"
FRAME_RE = re.compile(
    r"^\s*#(\d+)\s+0x[0-9a-fA-F]+\s+in\s+(.+?)\s+(\S+?):(\d+)(?::(\d+))?\s*$",
    re.MULTILINE,
)
ADDR_RE = re.compile(r"0x[0-9a-fA-F]+")
NUM_RE = re.compile(r"\b\d{4,}\b")


# ---------------------------------------------------------------------------
# Small utilities


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def rel(path: Path) -> str:
    try:
        return str(path.resolve().relative_to(ROOT))
    except ValueError:
        return str(path.resolve())


def run(cmd: list[str], *, cwd: Path = ROOT, timeout: Optional[int] = None,
        env: Optional[dict[str, str]] = None) -> subprocess.CompletedProcess[str]:
    return subprocess.run(cmd, cwd=str(cwd), text=True, errors="replace",
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                          timeout=timeout, env=env)


def say(msg: str) -> None:
    print(f"fuzz: {msg}", file=sys.stderr)


# ---------------------------------------------------------------------------
# Toolchain


def clang_version(cc: str) -> str:
    try:
        p = run([cc, "--version"], timeout=20)
    except (OSError, subprocess.TimeoutExpired):
        return ""
    return (p.stdout or p.stderr).splitlines()[0] if (p.stdout or p.stderr) else ""


def has_fuzzer_runtime(cc: str) -> bool:
    try:
        p = run([cc, "-print-resource-dir"], timeout=20)
    except (OSError, subprocess.TimeoutExpired):
        return False
    if p.returncode != 0:
        return False
    root = Path(p.stdout.strip())
    hits = list(root.glob("lib/*/libclang_rt.fuzzer*.a"))
    if not hits:
        hits = list(root.glob("**/libclang_rt.fuzzer*.a"))
    return bool(hits)


def find_clang(explicit: Optional[str]) -> Optional[str]:
    if explicit:
        p = explicit if Path(explicit).exists() else shutil.which(explicit)
        return p if p and has_fuzzer_runtime(p) else None
    env = os.environ.get("SCRY_FUZZ_CC")
    if env and Path(env).exists() and has_fuzzer_runtime(env):
        return env
    path = shutil.which("clang")
    if path and has_fuzzer_runtime(path):
        return path
    # The development machine keeps toolchains in /nix/store without a clang on
    # PATH.  Prefer a version-sorted candidate that actually ships libFuzzer.
    candidates = sorted(glob.glob("/nix/store/*clang-wrapper-*/bin/clang"), reverse=True)
    for cand in candidates:
        if has_fuzzer_runtime(cand):
            return cand
    return None


def build_target(cc: str, *, quiet: bool = False) -> subprocess.CompletedProcess[str]:
    BUILD.mkdir(parents=True, exist_ok=True)
    cmd = [cc, *BASE_CFLAGS] + [
        "-I", str(SCRY / "native" / "tree-sitter" / "lib" / "src"),
        "-I", str(SCRY / "native" / "tree-sitter-c" / "src"),
        *[str(FUZZ / s) for s in SOURCES],
        "-o", str(TARGET),
    ]
    if not quiet:
        say("building " + TARGET.name)
    return run(cmd, timeout=300)


def find_scry_binary(explicit: Optional[str]) -> Optional[Path]:
    if explicit:
        p = Path(explicit)
        if not p.is_absolute():
            p = (ROOT / p).resolve()
        return p if p.exists() else None
    env = os.environ.get("SCRY_FUZZ_SCRY")
    if env:
        p = Path(env)
        if not p.is_absolute():
            p = (ROOT / p).resolve()
        if p.exists():
            return p
    for cand in (SCRY / ".grail" / "bin" / "scry", ROOT / ".lake" / "build" / "bin" / "scry"):
        if cand.exists():
            return cand
    return None


# ---------------------------------------------------------------------------
# Corpus


@dataclass
class Seed:
    path: Path
    sha: str
    cases: list[str] = field(default_factory=list)


def seed_paths(static_report: Optional[dict]) -> list[Path]:
    paths: list[Path] = []
    for pat in ("bench/corpus/**/*.c", "tests/fixtures/**/*.c",
                "corpus/**/*.c", "fixtures/*.c"):
        paths.extend(sorted(SCRY.glob(pat)))
    if static_report:
        root = Path(static_report.get("corpus", {}).get("root", "bench/corpus"))
        if not root.is_absolute():
            root = SCRY / root
        for case in static_report.get("cases", []):
            f = case.get("file")
            if not f:
                continue
            p = (root / f).resolve()
            if p.exists() and p.suffix == ".c":
                paths.append(p)
    return paths


def make_seeds(static_report: Optional[dict]) -> list[Seed]:
    seen: dict[str, Seed] = {}
    cases_by_file: dict[str, list[str]] = {}
    if static_report:
        root = Path(static_report.get("corpus", {}).get("root", "bench/corpus"))
        if not root.is_absolute():
            root = SCRY / root
        for case in static_report.get("cases", []):
            f = case.get("file")
            if f:
                p = (root / f).resolve()
                cases_by_file.setdefault(str(p), []).append(case.get("id", ""))
    for p in seed_paths(static_report):
        try:
            rp = str(p.resolve())
            if rp not in seen:
                seen[rp] = Seed(p, sha256_file(p), cases_by_file.get(rp, []))
        except OSError:
            continue
    return list(seen.values())


def install_corpus(seeds: list[Seed]) -> Path:
    corpus = BUILD / "corpus"
    if corpus.exists():
        shutil.rmtree(corpus)
    corpus.mkdir(parents=True)
    for s in seeds:
        shutil.copyfile(s.path, corpus / s.sha)
    return corpus


# ---------------------------------------------------------------------------
# libFuzzer


def fuzz_command(binary: Path, corpus: Path, artifacts: Path, *, runs: int,
                 seconds: int, seed: int, max_len: int) -> list[str]:
    return [
        str(binary), str(corpus),
        f"-runs={runs}",
        f"-max_total_time={seconds}",
        f"-seed={seed}",
        f"-max_len={max_len}",
        "-timeout=10",
        "-rss_limit_mb=2048",
        "-detect_leaks=1",
        f"-artifact_prefix={artifacts}/",
        "-print_final_stats=1",
    ]


def parse_stats(trace: str) -> dict:
    out: dict[str, object] = {}
    m = re.search(r"Done (\d+) runs", trace)
    if m:
        out["runs"] = int(m.group(1))
    m = re.search(r"stat::average_exec_per_sec:\s+(\d+)", trace)
    if m:
        out["exec_per_s"] = int(m.group(1))
    m = re.search(r"stat::peak_rss_mb:\s+(\d+)", trace)
    if m:
        out["rss_mb"] = int(m.group(1))
    for key, pat, cast in (
        ("coverage", r"cov: (\d+)", int),
        ("features", r"ft: (\d+)", int),
        ("corpus_units", r"corp: (\d+)/(\d+)", int),
    ):
        m = re.search(pat, trace)
        if m:
            out[key] = cast(m.group(1))
    return out


def artifacts_in(path: Path) -> list[Path]:
    if not path.exists():
        return []
    return sorted(p for p in path.iterdir()
                  if p.is_file() and (p.name.startswith("crash-")
                                      or p.name.startswith("timeout-")
                                      or p.name.startswith("oom-")
                                      or p.name.startswith("leak-")))


def artifact_kind(path: Path, trace: str) -> str:
    if "SCRY-FUZZ INVARIANT" in trace:
        return "invariant"
    if "AddressSanitizer" in trace:
        return "asan"
    if "runtime error:" in trace:
        return "ubsan"
    if path.name.startswith("leak-") or "LeakSanitizer" in trace:
        return "leak"
    if path.name.startswith("timeout-"):
        return "timeout"
    if path.name.startswith("oom-"):
        return "oom"
    if "libFuzzer" in trace:
        return "libfuzzer"
    return "unknown"


def frames(trace: str) -> list[dict]:
    out: list[dict] = []
    for m in FRAME_RE.finditer(trace):
        func, file, line, col = m.group(2), m.group(3), int(m.group(4)), m.group(5)
        out.append({
            "function": func.strip(),
            "file": os.path.basename(file),
            "line": line,
            "column": int(col) if col else None,
            "kind": "native-source",
        })
    return out[:8]


def signature(trace: str, kind: str) -> tuple[str, str]:
    """A deterministic dedup key and a one-line summary for a crash/UB trace.

    Addresses, thread ids and PID-like numbers are removed: the same fault at the
    same source site must group even when ASan prints a different heap address.
    """
    text = trace.replace("\r\n", "\n")
    detail = ""
    summary = ""

    m = re.search(r"(?:ERROR|WARNING): AddressSanitizer: ([A-Za-z0-9_-]+)", text)
    if m:
        detail = m.group(1)
        summary = f"AddressSanitizer: {detail}"
    if not detail:
        m = re.search(r"runtime error: ([^\n]+)", text)
        if m:
            detail = NUM_RE.sub("<n>", ADDR_RE.sub("<addr>", m.group(1)))
            summary = "UndefinedBehaviorSanitizer: " + detail
    if not detail:
        m = re.search(r"SCRY-FUZZ INVARIANT: ([^\n]+)", text)
        if m:
            detail = ADDR_RE.sub("<addr>", m.group(1))
            summary = "shim invariant: " + detail
    if not detail:
        m = re.search(r"ERROR: libFuzzer: ([^\n]+)", text)
        if m:
            detail = m.group(1)
            summary = "libFuzzer: " + detail
    if not detail:
        if kind == "timeout":
            summary = "libFuzzer timeout"
        elif kind == "oom":
            summary = "libFuzzer out-of-memory"
        elif kind == "leak":
            summary = "LeakSanitizer leak"
        else:
            summary = "fuzzer failure"

    fs = frames(text)
    top = "|".join(f"{f['function']}@{f['file']}:{f['line']}" for f in fs[:3])
    sig = f"{kind}:{detail}|{top}" if top else f"{kind}:{detail}"
    return sig, summary


def input_offset(trace: str) -> Optional[int]:
    m = re.search(r"input_offset=(\d+)", trace)
    return int(m.group(1)) if m else None


def dedup(items: list[dict]) -> list[dict]:
    """Keep the smallest artifact per signature, deterministic by sha."""
    best: dict[str, dict] = {}
    for it in items:
        sig = it["signature"]
        cur = best.get(sig)
        if cur is None or (it["bytes"], it["sha256"]) < (cur["bytes"], cur["sha256"]):
            best[sig] = it
    return sorted(best.values(), key=lambda x: (x["signature"], x["sha256"]))


def replay(binary: Path, artifact: Path, *, timeout: int = 20) -> tuple[int, str]:
    (BUILD / "artifacts").mkdir(parents=True, exist_ok=True)
    try:
        p = run([str(binary), "-runs=1",
                 f"-artifact_prefix={BUILD / 'artifacts'}/", str(artifact)],
                timeout=timeout)
        return p.returncode, (p.stdout or "") + (p.stderr or "")
    except subprocess.TimeoutExpired as e:
        out = ""
        if isinstance(e.stdout, str):
            out += e.stdout
        if isinstance(e.stderr, str):
            out += e.stderr
        return 124, out


def minimize(binary: Path, artifact: Path, out: Path, *, runs: int,
             timeout: int = 30) -> tuple[Path, str]:
    out.parent.mkdir(parents=True, exist_ok=True)
    try:
        p = run([str(binary), "-minimize_crash=1", f"-runs={runs}",
                 f"-timeout=10", f"-exact_artifact_path={out}", str(artifact)],
                timeout=timeout)
        trace = (p.stdout or "") + (p.stderr or "")
    except subprocess.TimeoutExpired:
        trace = ""
    if out.exists() and out.stat().st_size > 0:
        return out, trace
    shutil.copyfile(artifact, out)
    return out, trace


# ---------------------------------------------------------------------------
# scry span mapping


def scry_span(scry: Optional[Path], artifact: Path, offset: Optional[int]) -> dict:
    if scry is None:
        return {"status": "skipped",
                "reason": "scry binary not built (build scry or pass --scry)"}
    try:
        data = artifact.read_bytes()
    except OSError as e:
        return {"status": "skipped", "reason": f"cannot read artifact: {e}"}
    if b"\0" in data:
        return {"status": "skipped",
                "reason": "artifact contains NUL; the Wiz text read would truncate it"}
    try:
        data.decode("ascii")
    except UnicodeDecodeError:
        return {"status": "skipped",
                "reason": "artifact is not ASCII; byte and character columns differ"}
    cmd = [str(scry), "fuzz-span", str(artifact), "--json"]
    if offset is not None:
        cmd += ["--offset", str(offset)]
    try:
        p = run(cmd, cwd=SCRY, timeout=60)
    except (OSError, subprocess.TimeoutExpired) as e:
        return {"status": "error", "reason": str(e)}
    if p.returncode != 0:
        return {"status": "error", "reason": (p.stderr or "").strip()[-500:]}
    try:
        return {"status": "ok", "input": json.loads(p.stdout)}
    except json.JSONDecodeError as e:
        return {"status": "error", "reason": f"invalid JSON from scry: {e}"}


# ---------------------------------------------------------------------------
# Static report and corpus sweep


def load_static(path: Optional[Path]) -> tuple[Optional[dict], str]:
    if path is None:
        return None, "no --static report"
    if not path.exists():
        return None, f"{path} does not exist"
    try:
        return json.loads(path.read_text()), ""
    except (OSError, json.JSONDecodeError) as e:
        return None, f"cannot read {path}: {e}"


def static_cases(static_report: Optional[dict]) -> list[dict]:
    if not static_report:
        return []
    out = []
    root = Path(static_report.get("corpus", {}).get("root", "bench/corpus"))
    if not root.is_absolute():
        root = SCRY / root
    for case in static_report.get("cases", []):
        f = case.get("file", "")
        p = (root / f).resolve() if f else None
        out.append({
            "id": case.get("id", ""),
            "suite": case.get("suite", ""),
            "cwe": case.get("cwe", ""),
            "file": f,
            "path": str(p) if p else "",
            "expect": case.get("expect", ""),
            "outcome": case.get("outcome", ""),
            "findings": case.get("findings", 0),
        })
    return out


def sweep(static_report: Optional[dict], binary: Path) -> tuple[list[dict], list[dict]]:
    """Run each static case through the harness once.

    Returns (per-case statuses, dynamic crashes).  A clean case is still not a
    proof: one execution per case and ASan/UBSan only.
    """
    statuses: list[dict] = []
    crashes: list[dict] = []
    for case in static_cases(static_report):
        p = Path(case["path"]) if case["path"] else None
        if p is None or not p.exists():
            statuses.append({**{k: case[k] for k in ("id", "file", "outcome", "findings")},
                             "dynamic": "skipped", "reason": "file not found"})
            continue
        code, trace = replay(binary, p)
        if code == 0:
            statuses.append({**{k: case[k] for k in ("id", "file", "outcome", "findings")},
                             "dynamic": "clean", "runs": 1})
            continue
        kind = artifact_kind(p, trace)
        sig, summary = signature(trace, kind)
        statuses.append({**{k: case[k] for k in ("id", "file", "outcome", "findings")},
                         "dynamic": "crash", "signature": sig})
        crashes.append({
            "kind": kind,
            "artifact": str(p),
            "sha256": sha256_file(p),
            "bytes": p.stat().st_size,
            "signature": sig,
            "summary": summary,
            "trace": trace,
            "case": case["id"],
            "from": "corpus-sweep",
        })
    return statuses, crashes


# ---------------------------------------------------------------------------
# Report


def evidence_entry(scry: Optional[Path], item: dict, idx: int) -> dict:
    artifact = Path(item["artifact"])
    min_path = Path(item.get("minimized", item["artifact"]))
    off = input_offset(item.get("trace", ""))
    span = scry_span(scry, min_path, off)
    return {
        "id": f"dyn-{idx:03d}",
        "kind": "dynamic",
        "oracle": "libFuzzer + AddressSanitizer + UndefinedBehaviorSanitizer",
        "artifact_kind": item["kind"],
        "artifact": rel(artifact),
        "minimized": rel(min_path),
        "bytes": min_path.stat().st_size if min_path.exists() else item["bytes"],
        "sha256": sha256_file(min_path) if min_path.exists() else item["sha256"],
        "signature": item["signature"],
        "summary": item["summary"],
        "frames": frames(item.get("trace", "")),
        "input_offset": off,
        "scry": span,
        "static_case": item.get("case"),
        "reproduce": f"{rel(TARGET)} {rel(min_path)}",
    }


def write_report(out: Path, report: dict) -> None:
    out.mkdir(parents=True, exist_ok=True)
    (out / "dynamic.json").write_text(json.dumps(report, indent=2, sort_keys=False) + "\n")
    (out / "dynamic.md").write_text(markdown(report))


def markdown(r: dict) -> str:
    d = r.get("dynamic", {})
    s = r.get("static", {})
    lines = [
        "# scry dynamic evidence",
        "",
        f"Status: **{r.get('status')}**" + (f" ({r.get('reason')})" if r.get("reason") else ""),
        "",
        "This report is produced by a bounded coverage-guided fuzz run. It is not a",
        "soundness or safety result: no crash in this run does not prove the absence of",
        "one outside the tested corpus, executions and sanitizer set.",
        "",
        "## Run",
        "",
        f"* engine: {r.get('tool', {}).get('engine', '')}",
        f"* sanitizers: {', '.join(r.get('tool', {}).get('sanitizers', []))}",
        f"* clang: `{r.get('tool', {}).get('clang', '')}`",
        f"* seed: {r.get('seed')}",
        f"* bounds: {r.get('bounds', {}).get('runs')} runs / "
        f"{r.get('bounds', {}).get('seconds')} s",
        f"* seeds: {r.get('corpus', {}).get('seeds', 0)} unique C files",
        f"* coverage: {d.get('stats', {}).get('coverage', 'n/a')} edges, "
        f"{d.get('stats', {}).get('features', 'n/a')} features",
        f"* artifacts: {d.get('counts', {}).get('artifacts', 0)}; "
        f"unique signatures: {d.get('counts', {}).get('unique', 0)}; "
        f"deduplicated: {d.get('counts', {}).get('dropped', 0)}",
        "",
        "Reproduce:",
        "",
        "```sh",
        r.get("command", ""),
        "```",
        "",
    ]
    if s.get("present"):
        st = s.get("summary", {})
        sw = s.get("corpus_sweep", {})
        lines += [
            "## Static findings next to the dynamic evidence",
            "",
            f"Static report: `{s.get('path')}` "
            f"(cases {st.get('cases', 'n/a')}, findings {st.get('findings', 'n/a')}).",
            "",
            f"Corpus sweep: {sw.get('clean', 0)} clean, {sw.get('crash', 0)} crash, "
            f"{sw.get('skipped', 0)} skipped of {sw.get('cases', 0)} cases "
            "(one run per case under the same sanitizers).",
            "",
            "| case | outcome | findings | dynamic |",
            "|---|---|---:|---|",
        ]
        for c in s.get("cases", []):
            lines.append(f"| `{c.get('id')}` | {c.get('outcome')} | {c.get('findings')} | "
                         f"{c.get('dynamic')} |")
        lines.append("")
    else:
        lines += ["## Static findings", "",
                  f"No static report: {s.get('reason', 'not supplied')}.", ""]
    lines += ["## Dynamic findings", ""]
    if d.get("findings"):
        for f in d["findings"]:
            lines += [
                f"### `{f['id']}`: {f['summary']}",
                "",
                f"* artifact: `{f['minimized']}`",
                f"* signature: `{f['signature']}`",
                f"* scry span: {json.dumps(f.get('scry'))}",
                f"* reproduce: `{f['reproduce']}`",
                "",
            ]
    else:
        lines += [
            "None in this bounded run. This is **not** a safety claim; see the limits",
            "below.",
            "",
        ]
    lines += ["## Limits", "", r.get("limits", ""), ""]
    return "\n".join(lines)


# ---------------------------------------------------------------------------
# Driver


def self_test() -> int:
    t1 = ("==1==ERROR: AddressSanitizer: heap-buffer-overflow on address 0x602000000010\n"
          "    #0 0x401234 in ts_node_end_byte /x/tree-sitter/lib/src/node.c:120:7\n"
          "    #1 0x401111 in count_walk /x/native/ts_shim.c:88:3\n")
    t2 = t1.replace("0x602000000010", "0x604000000020").replace("0x401234", "0x409999")
    s1, _ = signature(t1, "asan")
    s2, _ = signature(t2, "asan")
    assert s1 == s2, (s1, s2)
    assert len(frames(t1)) == 2
    assert input_offset("SCRY-FUZZ INVARIANT: x (node=3, input_offset=42)") == 42
    a = {"signature": "s", "bytes": 9, "sha256": "b"}
    b = {"signature": "s", "bytes": 3, "sha256": "a"}
    assert dedup([a, b]) == [b]
    print("fuzz driver selftest: ok")
    return 0


def main(argv: Optional[list[str]] = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--build", action="store_true", help="build the libFuzzer target")
    ap.add_argument("--runs", type=int, default=20000, help="execution bound (default 20000)")
    ap.add_argument("--time", type=int, default=30, help="wall-clock bound in seconds (default 30)")
    ap.add_argument("--seed", type=int, default=20261115, help="libFuzzer RNG seed")
    ap.add_argument("--max-len", type=int, default=262144, help="maximum input bytes")
    ap.add_argument("--cc", help="clang with libFuzzer (else PATH or /nix/store)")
    ap.add_argument("--scry", help="scry binary for span mapping (else .grail/bin/scry)")
    ap.add_argument("--static", help="static `scry bench --json` report to place beside")
    ap.add_argument("--out", default=str(BUILD), help="report directory (default scry/build/fuzz)")
    ap.add_argument("--clean", action="store_true", help="remove prior corpus/artifacts first")
    ap.add_argument("--no-minimize", action="store_true", help="do not minimise artifacts")
    ap.add_argument("--minimize-runs", type=int, default=20000,
                    help="libFuzzer run bound while minimising")
    ap.add_argument("--no-sweep", action="store_true", help="do not run the static corpus sweep")
    ap.add_argument("--fail-on-finding", dest="fail", action="store_true", default=True,
                    help="exit 1 when a dynamic finding is reported (default)")
    ap.add_argument("--no-fail-on-finding", dest="fail", action="store_false")
    ap.add_argument("--self-test", action="store_true", help="check the driver's pure functions")
    args = ap.parse_args(argv)

    if args.self_test:
        return self_test()

    out_dir = Path(args.out)
    if args.static:
        static_path = Path(args.static)
    else:
        candidate = SCRY / "build" / "bench.json"
        static_path = candidate if candidate.exists() else None
    static_report, static_reason = load_static(static_path)

    cc = find_clang(args.cc)
    if cc is None:
        report = {
            "format": "scry-dynamic-evidence",
            "version": 1,
            "kind": "dynamic",
            "status": "skipped",
            "reason": "no clang with libFuzzer and ASan/UBSan found (set SCRY_FUZZ_CC)",
            "tool": {"engine": "libFuzzer", "sanitizers": ["address", "undefined"]},
            "static": {"present": False, "reason": static_reason},
            "dynamic": {"counts": {"artifacts": 0, "unique": 0, "dropped": 0},
                        "findings": [], "stats": {}},
            "limits": "No fuzzing ran: the toolchain was unavailable. A clean skip is not a result.",
        }
        write_report(out_dir, report)
        say("SKIP: " + report["reason"])
        return 0

    if args.clean:
        for p in (BUILD / "corpus", BUILD / "artifacts", BUILD / "minimized"):
            if p.exists():
                shutil.rmtree(p)
    BUILD.mkdir(parents=True, exist_ok=True)
    (BUILD / "artifacts").mkdir(exist_ok=True)
    (BUILD / "minimized").mkdir(exist_ok=True)

    if args.build or not TARGET.exists():
        p = build_target(cc)
        if p.returncode != 0:
            sys.stderr.write((p.stdout or "") + (p.stderr or ""))
            say("build failed")
            return 2

    seeds = make_seeds(static_report)
    if not seeds:
        say("no seed C files found")
        return 2
    corpus = install_corpus(seeds)
    artifacts = BUILD / "artifacts"
    say(f"{len(seeds)} unique seeds; running {args.runs} executions / {args.time}s")

    fc = fuzz_command(TARGET, corpus, artifacts, runs=args.runs,
                      seconds=args.time, seed=args.seed, max_len=args.max_len)
    try:
        p = run(fc, timeout=args.time + 60)
        fuzz_trace = (p.stdout or "") + (p.stderr or "")
        fuzz_code = p.returncode
    except subprocess.TimeoutExpired as e:
        fuzz_trace = "" if e.stderr is None else str(e.stderr)
        fuzz_code = 124

    raw: list[dict] = []
    for art in artifacts_in(artifacts):
        min_path = art
        replay_code, trace = replay(TARGET, art)
        if not args.no_minimize and replay_code != 0:
            min_path, mtrace = minimize(TARGET, art, BUILD / "minimized" / art.name,
                                        runs=args.minimize_runs)
            if min_path != art:
                _, trace = replay(TARGET, min_path)
            elif mtrace:
                trace = mtrace
        kind = artifact_kind(art, trace)
        sig, summary = signature(trace, kind)
        raw.append({
            "kind": kind,
            "artifact": str(art),
            "minimized": str(min_path),
            "sha256": sha256_file(min_path),
            "bytes": min_path.stat().st_size,
            "signature": sig,
            "summary": summary,
            "trace": trace,
        })

    sweep_cases: list[dict] = []
    sweep_crashes: list[dict] = []
    if not args.no_sweep and static_report:
        sweep_cases, sweep_crashes = sweep(static_report, TARGET)
        for c in sweep_crashes:
            # A static case crashing is rarer than a fuzz artifact but follows the
            # same path: keep a minimised copy, then dedup by signature.
            c["minimized"] = c["artifact"]
            if not args.no_minimize:
                mp, _ = minimize(TARGET, Path(c["artifact"]),
                                 BUILD / "minimized" / ("case-" + Path(c["artifact"]).name),
                                 runs=args.minimize_runs)
                c["minimized"] = str(mp)
                c["bytes"] = mp.stat().st_size if mp.exists() else c["bytes"]
                c["sha256"] = sha256_file(mp) if mp.exists() else c["sha256"]
        raw.extend(sweep_crashes)

    unique = dedup(raw)
    dynamic_findings = [evidence_entry(find_scry_binary(args.scry), it, i + 1)
                        for i, it in enumerate(unique)]

    stats = parse_stats(fuzz_trace)
    stats.setdefault("runs", args.runs)
    fuzz_failed = fuzz_code != 0 and not raw
    status = "error" if fuzz_failed else ("findings" if dynamic_findings else "clean")
    reason = ""
    if fuzz_failed:
        reason = f"libFuzzer exited {fuzz_code} without an artifact; see the run log"
    cases = []
    sweep_by_id = {c["id"]: c for c in sweep_cases}
    for c in static_cases(static_report):
        sc = sweep_by_id.get(c["id"], {})
        cases.append({
            "id": c["id"], "suite": c["suite"], "cwe": c["cwe"],
            "file": c["file"], "expect": c["expect"], "outcome": c["outcome"],
            "findings": c["findings"], "dynamic": sc.get("dynamic", "skipped"),
        })
    sw_counts = {
        "cases": len(cases),
        "clean": sum(1 for c in cases if c["dynamic"] == "clean"),
        "crash": sum(1 for c in cases if c["dynamic"] == "crash"),
        "skipped": sum(1 for c in cases if c["dynamic"] == "skipped"),
    }
    overall = (static_report or {}).get("overall", {})
    static_section = {
        "present": static_report is not None,
        "path": rel(static_path) if static_path else None,
        "reason": static_reason,
        "summary": {
            "cases": (static_report or {}).get("corpus", {}).get("cases"),
            "findings": (static_report or {}).get("path_validity", {}).get("findings"),
            "overall": overall,
        },
        "corpus_sweep": sw_counts,
        "cases": cases,
    }

    command = ("python3 scry/fuzz/run.py --build --runs {runs} --time {time} "
               "--seed {seed} --static {static} --out {out}").format(
        runs=args.runs, time=args.time, seed=args.seed,
        static=rel(static_path) if static_path else "<static-report>",
        out=rel(out_dir))
    report = {
        "format": "scry-dynamic-evidence",
        "version": 1,
        "kind": "dynamic",
        "status": status,
        "reason": reason,
        "tool": {
            "name": "scry-fuzz",
            "engine": "libFuzzer",
            "sanitizers": ["address", "undefined"],
            "clang": clang_version(cc),
            "target": rel(TARGET),
            "target_sha256": sha256_file(TARGET) if TARGET.exists() else None,
        },
        "command": command,
        "bounds": {"runs": args.runs, "seconds": args.time, "max_len": args.max_len},
        "seed": args.seed,
        "corpus": {"seeds": len(seeds), "units": len(seeds),
                   "root": rel(corpus)},
        "static": static_section,
        "dynamic": {
            "counts": {"artifacts": len(raw), "unique": len(unique),
                       "dropped": len(raw) - len(unique)},
            "stats": stats,
            "findings": dynamic_findings,
        },
        "limits": (
            "The target is the C shim and tree-sitter-c, not the Wiz taint pipeline. "
            "One bounded run with ASan/UBSan cannot prove the absence of a crash, a "
            "memory error or undefined behaviour outside the executed inputs; it is "
            "dynamic evidence, not a safety claim. Minimisation and dedup are "
            "best-effort and stack signatures are textual. Static findings are "
            "case-level and are not comparable alert-for-alert with a crash."
        ),
        "note": ("A bounded run that finds no crash is not evidence of safety. "
                 "See limits."),
    }
    write_report(out_dir, report)

    say(f"status {report['status']}: {len(dynamic_findings)} unique dynamic finding(s), "
        f"{len(raw)} artifact(s), {sw_counts['clean']}/{sw_counts['cases']} static cases clean")
    if dynamic_findings and args.fail:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
