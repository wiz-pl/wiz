#!/usr/bin/env python3
"""Measure the peak resident set size (RSS) of the compiler's fixed corpus.

The time benchmarks (`scripts/stdlib-bench.py`, `scripts/fixpoint.sh`) answer "how
long"; this one answers "how much". A build that peaks at 5 GiB is killed by a
memory cgroup on a 4 GiB runner whatever its wall time was, and a self-check that
retains 10 GB fails at an arbitrary later step, so the peak has to be measured
directly.

    scripts/mem-bench.py                     # run the corpus, write bench/mem-bench.json
    scripts/mem-bench.py --update            # ... and record bench/mem-baseline.json

    scripts/mem-bench.py --check             # compare with the baseline, exit 1 on a
                                             # regression (> +25 %) or a hard cap
    scripts/mem-bench.py --check --tolerance 40
    scripts/mem-bench.py --only check-prelude --reps 5
    scripts/mem-bench.py --self-test         # test the thresholds on synthetic series

Peak RSS is sampled every `--interval` seconds (default 0.02) as the sum of the
process tree's RSS, and the root's `VmHWM` is read on every sample too: a build fans
out into `cc`, `as`, `ld`, so the compiler alone is not the whole peak. A sampling
peak can miss a spike shorter than the interval; treat a number as ±5 % (the same
caveat as `scripts/fixpoint.sh`). `os.wait4`'s `ru_maxrss` is used as a per-run floor
for a process that starts and exits inside one interval.

Two independent limits, both checked:

* **relative** — peak above the baseline's peak by more than `--tolerance` percent
  (default 25, read from the baseline unless overridden). RSS moves with the GC and
  the allocator, so the gate is deliberately looser than the time gate.
* **hard cap** — the corpus entry's `cap_mib`, a budget rather than a comparison
  (`check-prelude` must fit under 1 GiB, say). The cap is checked on the measured
  peak; `--scope` additionally runs each invocation inside
  `systemd-run --user --scope -p MemoryMax=CAP`, so the kernel enforces it live and
  an over-cap run exits 137 instead of merely failing afterwards.

The checks are cold: `--no-cache` is passed, because a warm content-addressed cache
hides the elaboration a CI runner does on every build. The self-hosted checker is
built once as preparation (not measured as part of the corpus): its *run* is the
peak this harness guards (413 MiB after the `inlineTm` fix; 10.7 GB before it).

Machine caveat: absolute RSS depends on the C compiler, the GC, the page size and
what else shares the machine. The checked-in baseline was recorded on the 27 GiB
development host with ~20 concurrent agents; use the relative limit and the caps to
decide, and re-record (`--update`) after a deliberate change.
"""
import argparse
import json
import os
import platform
import re
import resource
import shutil
import statistics
import subprocess
import sys
import tempfile
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
KIB = 1024
MIB = 1024

CHECKER_FILES = [
    "selfhost/Lex.wiz", "selfhost/Parse.wiz", "selfhost/Kernel.wiz",
    "selfhost/CParse.wiz", "selfhost/CGlue.wiz", "selfhost/Frontend.wiz",
    "selfhost/Tables.wiz", "selfhost/Check.wiz",
]
FRONTEND_FILES = [
    "selfhost/Lex.wiz", "selfhost/Parse.wiz", "selfhost/Kernel.wiz",
    "selfhost/CParse.wiz", "selfhost/CGlue.wiz", "selfhost/Frontend.wiz",
]

# name, argv template, cap in MiB, what it is
#   {wiz}     the compiler under test
#   {out}     bench/.build/mem/program
#   {checker} the self-hosted checker built from this revision
#   {rundir}  a scratch directory for the checker's input.wiz
CORPUS = [
    ("check-prelude", ["{wiz}", "check", "--no-cache", "lib/Prelude.wiz"], 1024,
     "cold check of the standard prelude (the hard-cap example: must fit in 1 GiB)"),
    ("check-std", ["{wiz}", "check", "--no-cache", "lib/Std.wiz"], 1024,
     "cold check of the largest single standard-library module"),
    ("check-text", ["{wiz}", "check", "--no-cache", "lib/Text.wiz"], 1024,
     "cold check of Text (string/list heavy)"),
    ("check-json", ["{wiz}", "check", "--no-cache", "lib/Json.wiz"], 1024,
     "cold check of the JSON parser/serialiser"),
    ("check-example-hdl", ["{wiz}", "check", "--no-cache",
                            "examples/hdl-temporal.wiz"], 2048,
     "cold check of a large example (the temporal-properties UART, 294 lines)"),
    ("build-stdlib-bench", ["{wiz}", "build", "--no-cache",
                            "bench/stdlib-bench.wiz", "-o", "{out}"], 2048,
     "build (elaborate, lower, emit C, cc) of the standard-library benchmark"),
    ("selfhost-checker", None, 1024,
     "the self-hosted checker checking the whole frontend (413 MiB target)"),
]


def git(*args):
    try:
        return subprocess.run(["git", "-C", ROOT, *args], capture_output=True,
                              text=True, check=True).stdout.strip()
    except (OSError, subprocess.CalledProcessError):
        return ""


def wiz_identity(wiz):
    """What compiler the numbers came from: version, size, mtime (not a gate)."""
    try:
        r = subprocess.run([wiz, "--version"], capture_output=True, text=True, timeout=30)
        version = (r.stdout or r.stderr).strip().split("\n")[0]
    except (OSError, subprocess.SubprocessError):
        version = ""
    try:
        st = os.stat(wiz)
        mtime = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime(st.st_mtime))
        size = st.st_size
    except OSError:
        mtime, size = "", 0
    return {"version": version, "size": size, "mtime": mtime,
            "path": os.path.relpath(wiz, ROOT) if os.path.isabs(wiz) and
            os.path.commonpath([os.path.abspath(wiz), ROOT]) == ROOT else wiz}


def default_wiz():
    p = os.path.join(ROOT, ".lake", "build", "bin", "wiz")
    return p if os.path.exists(p) else "wiz"


def work_dir():
    d = os.path.join(ROOT, "bench", ".build", "mem")
    os.makedirs(d, exist_ok=True)
    return d


def machine_info():
    def meminfo(key):
        try:
            with open("/proc/meminfo") as f:
                for line in f:
                    if line.startswith(key + ":"):
                        return int(line.split()[1])
        except OSError:
            pass
        return 0

    model = ""
    try:
        with open("/proc/cpuinfo") as f:
            for line in f:
                if line.startswith("model name"):
                    model = line.split(":", 1)[1].strip()
                    break
    except OSError:
        pass
    return {
        "host": platform.node(),
        "kernel": platform.release(),
        "machine": platform.machine(),
        "cpus": os.cpu_count() or 0,
        "cpu_model": model,
        "mem_total_mib": meminfo("MemTotal") // KIB,
        "python": platform.python_version(),
    }


def strip_imports(text):
    return "\n".join(l for l in text.split("\n") if not l.startswith("import"))


def write_if_different(path, text):
    try:
        with open(path, encoding="utf-8") as f:
            if f.read() == text:
                return False
    except OSError:
        pass
    with open(path, "w", encoding="utf-8") as f:
        f.write(text)
    return True


def build_flags():
    """The C toolchain flags `wiz build` takes (it reads no environment of its own).

    `scripts/stdlib-bench.py` does the same. In a `nix develop` shell these come from
    the environment; in CI the packaged `wiz` wrapper already has them, so they are
    absent here and nothing is appended.
    """
    flags = []
    if os.environ.get("WIZ_CC"):
        flags += ["--cc", os.environ["WIZ_CC"]]
    if os.environ.get("WIZ_CFLAGS"):
        flags += ["--cflags", os.environ["WIZ_CFLAGS"]]
    if os.environ.get("WIZ_LDFLAGS"):
        flags += ["--ldflags", os.environ["WIZ_LDFLAGS"]]
    return flags


def ensure_checker(wiz, quiet=False, force=False, timeout=1800):
    """Build the self-hosted checker from this revision; return (exe, log).

    This is preparation, not a corpus entry: the checker's *run* is what the memory
    gate tracks. The build is kept between runs (the sources are the freshness key).
    """
    d = work_dir()
    src = os.path.join(d, "checker.wiz")
    exe = os.path.join(d, "selfhost-checker")
    text = ("import IO\nimport Std\n" +
            "\n".join(strip_imports(open(os.path.join(ROOT, f), encoding="utf-8").read())
                      for f in CHECKER_FILES))
    changed = write_if_different(src, text)
    fresh = os.path.exists(exe) and not force and not changed and all(
        os.path.getmtime(os.path.join(ROOT, f)) <= os.path.getmtime(exe)
        for f in CHECKER_FILES)
    if fresh:
        return exe, "cached"
    if not quiet:
        print(f"building the self-hosted checker -> {exe}", file=sys.stderr)
    r = subprocess.run([wiz, "build", src, "-o", exe] + build_flags(), cwd=ROOT,
                       capture_output=True, text=True, timeout=timeout)
    if r.returncode != 0:
        sys.stderr.write(r.stdout[-4000:])
        sys.stderr.write(r.stderr[-4000:])
        raise SystemExit("building the self-hosted checker failed")
    return exe, "built"


def checker_input():
    d = work_dir()
    path = os.path.join(d, "input.wiz")
    body = "\n".join(strip_imports(open(os.path.join(ROOT, f), encoding="utf-8").read())
                     for f in FRONTEND_FILES)
    write_if_different(path, "import Prelude\n" + body)
    return path


def proc_snapshot():
    """pid -> (ppid, rss KiB) for every process, or {} when /proc is unavailable."""
    procs = {}
    page_kib = os.sysconf("SC_PAGE_SIZE") // KIB
    try:
        names = os.listdir("/proc")
    except OSError:
        return procs
    for name in names:
        if not name.isdigit():
            continue
        try:
            with open("/proc/%s/stat" % name, "rb") as f:
                data = f.read()
        except OSError:
            continue
        r = data.rfind(b")")
        if r < 0:
            continue
        parts = data[r + 2:].split()
        if len(parts) < 22:
            continue
        try:
            procs[int(name)] = (int(parts[1]), int(parts[21]) * page_kib)
        except ValueError:
            continue
    return procs


def tree_rss_kib(procs, root):
    children = {}
    for pid, (ppid, _rss) in procs.items():
        children.setdefault(ppid, []).append(pid)
    total = 0
    stack = [root]
    seen = set()
    while stack:
        pid = stack.pop()
        if pid in seen:
            continue
        seen.add(pid)
        entry = procs.get(pid)
        if entry is not None:
            total += entry[1]
        stack.extend(children.get(pid, ()))
    return total


def vm_hwm_kib(pid):
    try:
        with open("/proc/%d/status" % pid, encoding="ascii", errors="replace") as f:
            for line in f:
                if line.startswith("VmHWM:"):
                    return int(line.split()[1])
    except (OSError, ValueError):
        pass
    return 0


def run_measured(argv, cwd, env, timeout, interval):
    """Run argv, sampling the tree's RSS; return peak KiB, wall seconds and exit."""
    out_path = os.path.join(work_dir(), "last.stdout")
    err_path = os.path.join(work_dir(), "last.stderr")
    start = time.monotonic()
    peak = 0
    timed_out = False
    with open(out_path, "wb") as out, open(err_path, "wb") as err:
        try:
            p = subprocess.Popen(argv, cwd=cwd, env=env, stdout=out, stderr=err,
                                 start_new_session=True)
        except OSError as e:
            return {"peak_kib": 0, "wall_s": 0.0, "exit": 125, "timed_out": False,
                    "stdout": "", "stderr": str(e)}
        ru_maxrss = 0
        status = None
        while status is None:
            pid, wait_status, ru = os.wait4(p.pid, os.WNOHANG)
            if pid == p.pid:
                status = wait_status
                ru_maxrss = ru.ru_maxrss
                break
            sample = tree_rss_kib(proc_snapshot(), p.pid)
            if sample > peak:
                peak = sample
            hwm = vm_hwm_kib(p.pid)
            if hwm > peak:
                peak = hwm
            if time.monotonic() - start > timeout:
                timed_out = True
                try:
                    os.killpg(p.pid, 9)
                except OSError:
                    pass
                pid, wait_status, ru = os.wait4(p.pid, 0)
                status = wait_status
                ru_maxrss = ru.ru_maxrss
                break
            time.sleep(interval)
        p.returncode = os.waitstatus_to_exitcode(status)
        if ru_maxrss > peak:
            peak = ru_maxrss
    wall = time.monotonic() - start
    try:
        stdout = open(out_path, encoding="utf-8", errors="replace").read()[-4000:]
        stderr = open(err_path, encoding="utf-8", errors="replace").read()[-4000:]
    except OSError:
        stdout = stderr = ""
    return {"peak_kib": peak, "wall_s": wall, "exit": p.returncode,
            "timed_out": timed_out, "stdout": stdout, "stderr": stderr}


def make_corpus(wiz, out_binary, checker, rundir):
    entries = []
    # The large example and the full build are minutes each; the memory peak is stable
    # enough that one run is a sample, and three would triple the nightly.
    max_reps = {"check-example-hdl": 1, "build-stdlib-bench": 2,
                "selfhost-checker": 2}
    for name, argv, cap, note in CORPUS:
        template = argv if argv is not None else ["{checker}"]
        if argv is None:
            argv = [checker]
        else:
            argv = [a.format(wiz=wiz, out=out_binary, checker=checker,
                             rundir=rundir) for a in argv]
        if len(argv) > 1 and argv[1] == "build":
            argv += build_flags()
        cwd = rundir if name == "selfhost-checker" else ROOT
        entries.append({"name": name, "argv": argv, "template": template,
                        "cap_mib": cap, "note": note, "cwd": cwd,
                        "max_reps": max_reps.get(name)})
    return entries


def summarize(samples_kib):
    peak = max(samples_kib)
    return {
        "samples_mib": [round(k / KIB, 1) for k in samples_kib],
        "peak_mib": round(peak / KIB, 1),
        "median_mib": round(statistics.median(samples_kib) / KIB, 1),
    }


def verdict(peak_mib, baseline_mib, tolerance_pct, cap_mib):
    """The two independent limits, in one place so --self-test can exercise them."""
    if cap_mib is not None and peak_mib > cap_mib:
        return "over-cap"
    if baseline_mib is not None and peak_mib > baseline_mib * (1.0 + tolerance_pct / 100.0):
        return "regressed"
    return "ok"


def run_corpus(entries, args, env):
    results = {}
    for i, entry in enumerate(entries, 1):
        name = entry["name"]
        cap = entry["cap_mib"]
        reps = min(args.reps, entry["max_reps"]) if entry.get("max_reps") else args.reps
        argv = list(entry["argv"])
        if args.scope and cap:
            argv = ["systemd-run", "--user", "--scope", "--quiet",
                    "-p", f"MemoryMax={cap}M", "--"] + argv
        samples = []
        exits = []
        walls = []
        out = None
        for r in range(reps):
            if not args.quiet:
                print(f"[{i}/{len(entries)}] {name} "
                      f"({r + 1}/{reps}){f' cap {cap} MiB' if cap else ''}",
                      file=sys.stderr)
            res = run_measured(argv, entry.get("cwd", ROOT), env, args.timeout,
                               args.interval)
            samples.append(res["peak_kib"])
            exits.append(res["exit"])
            walls.append(res["wall_s"])
            out = res
        rec = summarize(samples)
        bad = [e for e in exits if e != 0]
        rec.update({
            "argv": entry["template"],
            "command": entry["argv"],
            "cap_mib": cap,
            "note": entry["note"],
            "reps": reps,
            "exit": bad[0] if bad else 0,
            "timed_out": out["timed_out"],
            "wall_s": round(statistics.median(walls), 3),
        })
        if bad:
            rec["error"] = (out["stderr"] or out["stdout"])[-2000:]
        results[name] = rec
    return results


def checker_phases(env, timeout):
    """Per-phase RSS of *building* the self-hosted checker, from the tests probe.

    This is the only phase profiler that exists today (`tests --probe-checker`, added
    with the memory fixes): it prints its RSS and VmHWM after each compiler phase. The
    corpus entry measures the checker's *run*; this is the optional breakdown that
    says which phase of the in-process build grows. Not part of the gate.
    """
    tests = os.path.join(ROOT, ".lake", "build", "bin", "tests")
    if not os.path.exists(tests):
        return None
    res = run_measured([tests, "--probe-checker"], ROOT, env, timeout, 0.05)
    phases = []
    for line in (res["stdout"] + res["stderr"]).split("\n"):
        m = re.search(r"\[(\d+) ms\] (.*?): rss ([0-9.]+) MiB, peak ([0-9.]+) MiB", line)
        if m:
            phases.append({"at_ms": int(m.group(1)), "phase": m.group(2),
                           "rss_mib": float(m.group(3)),
                           "peak_mib": float(m.group(4))})
    return {"exit": res["exit"], "phases": phases}


def load_json(path):
    with open(path, encoding="utf-8") as f:
        return json.load(f)


def compare(results, baseline, tolerance):
    """Compare a run with the baseline; return (rows, failed)."""
    rows = []
    failed = False
    base = baseline.get("invocations", {})
    tol = tolerance if tolerance is not None else baseline.get("tolerance_pct", 25)

    missing = [n for n in results if n not in base]
    extra = [n for n in base if n not in results]
    changed = [n for n in results if n in base and
               (results[n].get("cap_mib") != base[n].get("cap_mib") or
                results[n].get("argv") != base[n].get("argv"))]
    for name in sorted(set(results) | set(base)):
        rec = results.get(name) or {}
        brec = base.get(name) or {}
        peak = rec.get("peak_mib")
        bpeak = brec.get("peak_mib")
        cap = rec.get("cap_mib", brec.get("cap_mib"))
        if name in missing:
            status, detail = "baseline-missing", "no baseline entry (run --update)"
        elif name in extra:
            status, detail = "baseline-extra", "the baseline has an entry this corpus does not"
        elif name in changed:
            status, detail = "corpus-changed", "argv or cap differs from the baseline"
        elif rec.get("timed_out"):
            status, detail = "timed-out", f"over {rec.get('wall_s')}s"
        elif rec.get("exit"):
            if rec.get("exit") in (137, -9) and cap:
                status, detail = "over-cap", f"killed (exit {rec.get('exit')})"
            else:
                status, detail = "failed", f"exit {rec.get('exit')}"
        else:
            status = verdict(peak, bpeak, tol, cap)
            detail = ""
        if status != "ok":
            failed = True
        delta = None if (peak is None or not bpeak) else 100.0 * (peak - bpeak) / bpeak
        rows.append({"name": name, "peak_mib": peak, "baseline_mib": bpeak,
                     "delta_pct": delta, "cap_mib": cap, "status": status,
                     "detail": detail, "note": rec.get("note") or brec.get("note", "")})
    return rows, failed, tol


def print_table(rows, tol):
    print(f"{'invocation':28s} {'peak':>9s} {'baseline':>9s} {'delta':>8s} "
          f"{'cap':>7s}  status")
    for r in rows:
        peak = f"{r['peak_mib']:9.1f}" if r["peak_mib"] is not None else f"{'-':>9s}"
        base = f"{r['baseline_mib']:9.1f}" if r["baseline_mib"] else f"{'-':>9s}"
        delta = f"{r['delta_pct']:+7.1f}%" if r["delta_pct"] is not None else f"{'-':>8s}"
        cap = f"{r['cap_mib']:7d}" if r["cap_mib"] else f"{'-':>7s}"
        note = f"  {r['detail']}" if r["detail"] else ""
        print(f"{r['name']:28s} {peak} {base} {delta} {cap}  {r['status']}{note}")
    print(f"\nrelative limit: +{tol:g}% against the baseline's peak "
          f"(max of its samples); hard caps are per invocation")


def markdown_table(rows, tol):
    out = [f"### Peak RSS (relative limit +{tol:g} %, per-invocation caps)", ""]
    out.append("| invocation | peak MiB | baseline MiB | delta | cap MiB | status |")
    out.append("|---|---:|---:|---:|---:|---|")
    for r in rows:
        peak = "-" if r["peak_mib"] is None else f"{r['peak_mib']:.1f}"
        base = "-" if not r["baseline_mib"] else f"{r['baseline_mib']:.1f}"
        delta = "-" if r["delta_pct"] is None else f"{r['delta_pct']:+.1f}%"
        cap = "-" if not r["cap_mib"] else str(r["cap_mib"])
        status = r["status"] + (f" ({r['detail']})" if r["detail"] else "")
        out.append(f"| `{r['name']}` | {peak} | {base} | {delta} | {cap} | {status} |")
    out.append("")
    out.append("Peak RSS is the process tree sampled every 20 ms plus `VmHWM`; "
               "treat a number as ±5 %. Absolute values depend on the machine.")
    return "\n".join(out) + "\n"


def self_test():
    failures = []

    def check(label, got, want):
        if got != want:
            failures.append(f"{label}: got {got!r}, want {want!r}")

    # The comparison is a pure function of (peak, baseline, tolerance, cap), so the
    # synthetic series pin every branch without touching the machine.
    check("within tolerance", verdict(450, 400, 25, 1024), "ok")
    check("exactly at tolerance", verdict(500, 400, 25, 1024), "ok")
    check("one MiB over tolerance", verdict(501, 400, 25, 1024), "regressed")
    check("regressed", verdict(520, 400, 25, 1024), "regressed")
    check("over cap", verdict(1050, 900, 25, 1024), "over-cap")
    check("cap wins over regression", verdict(1100, 800, 25, 1024), "over-cap")
    check("no cap", verdict(9999, 1000, 25, None), "regressed")
    check("no baseline", verdict(1000, None, 25, 2048), "ok")

    # A series is judged by its maximum, not its last or its median.
    series = [410, 440, 530]
    s = summarize([x * KIB for x in series])
    check("series max", s["peak_mib"], 530.0)
    check("series median", s["median_mib"], 440.0)
    check("median is not the gate", verdict(s["median_mib"], 400, 25, 1024), "ok")
    check("series regression", verdict(s["peak_mib"], 400, 25, 1024), "regressed")

    # One real sample: a child that allocates and touches 48 MiB must be seen. The
    # bounds are wide (RSS includes the interpreter), but a sampler that reports 0 or
    # 1 GiB is broken.
    code = ("b = bytearray(48 * 1024 * 1024)\n"
            "for i in range(0, len(b), 4096): b[i] = 1\n"
            "import time; time.sleep(0.3)\n")
    env = dict(os.environ)
    res = run_measured([sys.executable, "-c", code], ROOT, env, 60, 0.02)
    peak = res["peak_kib"] / KIB
    if res["exit"] != 0:
        failures.append(f"sampler child exited {res['exit']}")
    if not (24 <= peak <= 320):
        failures.append(f"sampler peak {peak:.1f} MiB outside 24..320 MiB")

    # A failing corpus entry and a changed corpus are failures, not silent passes.
    results = {"x": {"peak_mib": 100.0, "cap_mib": 1000, "argv": ["wiz"], "exit": 0}}
    good = {"invocations": {"x": {"peak_mib": 80.0, "cap_mib": 1000, "argv": ["wiz"]}},
            "tolerance_pct": 25}
    rows, failed, _ = compare(results, good, None)
    check("ok run passes", failed, False)
    rows, failed, _ = compare(results, {"invocations": {}}, None)
    check("missing baseline fails", failed, True)
    check("missing baseline status", rows[0]["status"], "baseline-missing")
    bad_cap = {"invocations": {"x": {"peak_mib": 80.0, "cap_mib": 90, "argv": ["wiz"]}},
               "tolerance_pct": 25}
    rows, failed, _ = compare({"x": {"peak_mib": 100.0, "cap_mib": 90, "argv": ["wiz"],
                                     "exit": 0}}, bad_cap, None)
    check("over cap fails", rows[0]["status"], "over-cap")

    if failures:
        for f in failures:
            print("self-test FAIL: " + f, file=sys.stderr)
        print(f"self-test: {len(failures)} failure(s)", file=sys.stderr)
        return 1
    print("self-test: 16 checks passed (synthetic series + one real sample)")
    return 0


def main(argv=None):
    ap = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--wiz", default=default_wiz(),
                    help="the compiler under test (default .lake/build/bin/wiz)")
    ap.add_argument("--reps", type=int, default=3, help="runs per invocation (default 3)")
    ap.add_argument("--timeout", type=float, default=900.0,
                    help="seconds before an invocation is killed (default 900)")
    ap.add_argument("--interval", type=float, default=0.02,
                    help="RSS sampling interval in seconds (default 0.02)")
    ap.add_argument("--only", action="append", default=[], metavar="NAME",
                    help="run only this invocation (repeatable)")
    ap.add_argument("--json", default=None,
                    help="the run record (default bench/mem-bench.json)")
    ap.add_argument("--baseline", default=os.path.join(ROOT, "bench", "mem-baseline.json"),
                    help="the reference (default bench/mem-baseline.json)")
    ap.add_argument("--check", action="store_true",
                    help="compare with --baseline; exit 1 on a regression or a cap")
    ap.add_argument("--update", action="store_true",
                    help="write --baseline from this run (all invocations must pass)")
    ap.add_argument("--tolerance", type=float, default=None,
                    help="relative limit in percent (default: the baseline's, else 25)")
    ap.add_argument("--scope", action="store_true",
                    help="run under systemd-run --scope -p MemoryMax=cap (enforced live)")
    ap.add_argument("--from-json", metavar="FILE",
                    help="check a previous run record instead of running the corpus")
    ap.add_argument("--markdown", metavar="FILE",
                    help="append a Markdown table to FILE (a CI step summary)")
    ap.add_argument("--rebuild-checker", action="store_true",
                    help="rebuild the self-hosted checker even when it looks fresh")
    ap.add_argument("--phases", action="store_true",
                    help="also record the checker build's per-phase RSS (tests --probe-checker)")
    ap.add_argument("--quiet", action="store_true")
    ap.add_argument("--self-test", action="store_true",
                    help="test the thresholds on synthetic series and exit")
    args = ap.parse_args(argv)

    if args.self_test:
        return self_test()
    if args.reps < 1:
        ap.error("--reps must be at least 1")
    if args.interval <= 0:
        ap.error("--interval must be positive")
    if args.only and (args.check or args.update):
        ap.error("--only is for an experiment; --check and --update need the full corpus")
    if args.scope and not shutil.which("systemd-run"):
        ap.error("--scope needs systemd-run")
    if args.from_json and args.update:
        ap.error("--from-json cannot record a baseline; run the corpus to --update")
    if args.json is None:
        args.json = (None if args.from_json
                     else os.path.join(ROOT, "bench", "mem-bench.json"))

    d = work_dir()
    out_binary = os.path.join(d, "program")
    rundir = d
    selected = args.only or [e[0] for e in CORPUS]
    unknown = [n for n in selected if n not in [e[0] for e in CORPUS]]
    if unknown:
        ap.error(f"unknown invocation(s): {', '.join(unknown)}; choose from "
                 f"{', '.join(e[0] for e in CORPUS)}")
    env = dict(os.environ)
    phases = None
    if args.from_json:
        previous = load_json(args.from_json)
        results = previous.get("invocations", {})
        how = "previous run"
        phases = previous.get("phases")
        names = sorted(results)
    else:
        checker = ""
        how = "not needed"
        if "selfhost-checker" in selected:
            checker, how = ensure_checker(args.wiz, args.quiet, args.rebuild_checker,
                                          timeout=max(args.timeout, 1800))
            checker_input()
        entries = make_corpus(args.wiz, out_binary, checker, rundir)
        entries = [e for e in entries if e["name"] in selected]
        results = run_corpus(entries, args, env)
        names = [e["name"] for e in entries]
        if args.phases:
            if "selfhost-checker" in results:
                phases = checker_phases(env, max(args.timeout, 1800))
                if phases is None:
                    print("phases: no .lake/build/bin/tests; build the test driver "
                          "(lake build tests) to get the checker build's phases",
                          file=sys.stderr)
                elif not phases.get("phases"):
                    print("phases: tests --probe-checker produced no parseable phases",
                          file=sys.stderr)
                elif not args.quiet:
                    print()
                    print(f"{'phase':40s} {'at':>8s} {'rss':>9s} {'peak':>9s}")
                    for p in phases["phases"]:
                        print(f"{p['phase'][:40]:40s} {p['at_ms']:7d}ms "
                              f"{p['rss_mib']:8.1f}M {p['peak_mib']:8.1f}M")
            else:
                print("phases: only the selfhost-checker entry has a phase probe",
                      file=sys.stderr)

    record = {
        "schema": 1,
        "corpus_version": 1,
        "created": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "generator": "scripts/mem-bench.py",
        "commit": git("rev-parse", "HEAD"),
        "branch": git("rev-parse", "--abbrev-ref", "HEAD"),
        "wiz": args.wiz,
        "wiz_info": wiz_identity(args.wiz),
        "checker": how,
        "reps": args.reps,
        "interval_s": args.interval,
        "tolerance_pct": args.tolerance if args.tolerance is not None else 25,
        "machine": machine_info(),
        "invocations": results,
    }
    if phases is not None:
        record["phases"] = phases

    failed = False
    rows = None
    if args.check:
        if not os.path.exists(args.baseline):
            raise SystemExit(f"--check: no baseline at {args.baseline} (run --update)")
        baseline = load_json(args.baseline)
        rows, failed, tol = compare(results, baseline, args.tolerance)
        record["tolerance_pct"] = tol
        record["baseline"] = os.path.abspath(args.baseline)
        record["comparison"] = rows
        if not args.quiet:
            print()
            print_table(rows, tol)
        if args.markdown:
            with open(args.markdown, "a", encoding="utf-8") as f:
                f.write(markdown_table(rows, tol))

    if not args.quiet:
        if not args.check:
            print()
            print(f"{'invocation':28s} {'peak':>9s} {'median':>9s} {'wall':>8s} "
                  f"{'cap':>7s}  exit")
            for name in names:
                r = results[name]
                print(f"{name:28s} {r['peak_mib']:9.1f} {r['median_mib']:9.1f} "
                      f"{r['wall_s']:7.1f}s {r['cap_mib']:7d}  {r['exit']}")
        print()

    if args.json:
        os.makedirs(os.path.dirname(os.path.abspath(args.json)), exist_ok=True)
        with open(args.json, "w", encoding="utf-8") as f:
            json.dump(record, f, indent=2, sort_keys=False)
            f.write("\n")
        if not args.quiet:
            print(f"wrote {os.path.relpath(args.json, ROOT)}")
            if args.baseline and os.path.exists(args.baseline) and not args.check:
                print(f"baseline: {os.path.relpath(args.baseline, ROOT)} "
                      f"(use --check to compare, --update to re-record)")

    if args.update:
        bad = [n for n in names if results[n]["exit"] != 0]
        if bad:
            raise SystemExit("--update: refusing to record a baseline from failed runs: "
                             + ", ".join(bad))
        os.makedirs(os.path.dirname(os.path.abspath(args.baseline)), exist_ok=True)
        with open(args.baseline, "w", encoding="utf-8") as f:
            json.dump(record, f, indent=2, sort_keys=False)
            f.write("\n")
        if not args.quiet:
            print(f"recorded {os.path.relpath(args.baseline, ROOT)}")

    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
