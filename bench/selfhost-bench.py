#!/usr/bin/env python3
"""Compare the self-hosted checker/compiler with the Lean host on the same corpus.

The replacement-parity question is not only "does it accept the same programs" but
"at what cost".  This harness runs the Lean ``wiz`` and the self-hosted compiler
(the one built from ``scripts/GenSelfhost.lean`` with its driver and cache) over a
fixed corpus, one process per file, and records wall time and peak RSS for both.

    $ scripts/fixpoint.sh --help          # how the self-hosted compiler is generated
    $ bench/selfhost-build.sh             # build the host and the self-hosted compiler
    $ bench/selfhost-bench.py             # measure, print the table, update the JSON
    $ bench/selfhost-bench.py --check     # fail if self/host is >TOL% above the record

Two cache states are measured, as the brief asks, in this order:

* ``cold``: ``--no-cache`` for both, so every sample elaborates everything;
* ``warm``: ``--cache DIR`` for both, with a fresh DIR per tool, warmed once before the
  samples.  The host's cache is not the user's ``~/.cache/wiz``; the self-hosted
  driver's cache is not the default ``.wiz-cache``.

Like for like means the same file, the same flags and the same working directory.  The
corpus is existing repository files, all checked successfully by both tools when the
tracking record was written; a file one side rejects is reported as *unsupported* and
left out of the ratio (a rejection is not a check).  ``lib/Prelude.wiz`` is the host's
prelude; the self-hosted frontend embeds its own equivalent (stage 21), so a file that
imports ``Prelude`` uses different bytes on the two sides.  That is a parity property,
not a timing flag: it is recorded, not hidden.

The gate is a **ratio**: ``selfhost / host`` per file and for the corpus total (sum of
per-file medians).  Absolute seconds differ between machines, the ratio does not, so
``--check`` compares this run's ratio with the recorded ``baseline_ratios`` and fails
when it is more than ``--tolerance`` percent worse.  The recorded baseline is the
first measured run's ratio, not a promise about the host's speed.

Peak RSS is read with ``/usr/bin/time -f %M`` (the child's ``wait4`` rusage), so a
short check does not lose its peak to sampling.  Wall time is Python's monotonic clock
around that process (spawn included on both sides).
"""
import argparse
import json
import os
import platform
import shutil
import statistics
import subprocess
import sys
import tempfile
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

# NixOS has no /usr/bin/time; the dev shell and the system profile both provide GNU time.
TIME = shutil.which("time") or "/run/current-system/sw/bin/time"

# The fixed corpus.  Kinds are documentation only.  Keep the list stable: a different
# input is a different benchmark (the same rule as bench/stdlib-bench.py).
#
# These are the files the self-hosted frontend *accepts* today (see "Rejected corpus"
# below).  The lib/ and examples/ files the brief names are not in it: the selfhost
# rejects them at `builtin`, `class`, coinduction, Size, tactics or the embedded
# prelude, which is a parity failure before it is a performance question.  Measuring
# the time to a rejection would not be a check.
CORPUS = [
    ("selfhost/Lex.wiz", "small"),
    ("selfhost/Kernel.wiz", "medium"),
    ("bench/.build/selfhost-all.wiz", "large (Lex+Parse+Kernel+CParse+CGlue+Frontend)"),
    ("bench/.build/compiler.wiz", "xlarge (the whole toolchain)"),
]

# The first `selfhost-bench-before.json` run (2026-11-15, 627b48f6) recorded why each
# requested lib/example file cannot be measured yet; the harness prints this list so a
# later run does not silently look like a comparison of the whole tree.
REJECTED = [
    ("lib/Prelude.wiz", "unsupported command command.builtin"),
    ("lib/Std.wiz", "'Array' has already been declared (the embedded prelude)"),
    ("lib/Vec.wiz", "imports Logic: unsupported term.absurd / notation"),
    ("lib/Json.wiz", "imports Text: 'List.map' has already been declared"),
    ("examples/run.wiz", "unknown identifier Size (sized types)"),
    ("examples/streams.wiz", "unsupported command command.coinductive"),
    ("examples/tactics.wiz", "parse error in a tactic quotation"),
    ("examples/std.wiz", "unknown identifier Str.append"),
]

# `Selfhost.checkerSource` in Wiz/Selfhost.lean: the files it concatenates, in order.
SELFHOST_ALL_FILES = [
    "selfhost/Lex.wiz", "selfhost/Parse.wiz", "selfhost/Kernel.wiz",
    "selfhost/CParse.wiz", "selfhost/CGlue.wiz", "selfhost/Frontend.wiz",
    "selfhost/Tables.wiz", "selfhost/Check.wiz",
]
SELFHOST_ALL = os.path.join("bench", ".build", "selfhost-all.wiz")

MODES = ("cold", "warm")


def git(*args):
    try:
        return subprocess.run(["git", "-C", ROOT, *args], capture_output=True,
                              text=True, check=True).stdout.strip()
    except (OSError, subprocess.CalledProcessError):
        return ""


def lines_of(path):
    try:
        with open(os.path.join(ROOT, path), "rb") as f:
            data = f.read()
        return len(data.splitlines()), len(data)
    except OSError:
        return 0, 0


def ensure_selfhost_all():
    """Write the checker's concatenated source, exactly as `Selfhost.checkerSource` does.

    It is generated from checked-in sources, so the corpus entry is reproducible; a
    stale copy is rewritten before the run.
    """
    parts = []
    for path in SELFHOST_ALL_FILES:
        with open(os.path.join(ROOT, path)) as f:
            parts.append("\n".join(l for l in f.read().split("\n")
                                   if not l.startswith("import")))
    text = "import IO\nimport Std\n" + "\n".join(parts)
    out = os.path.join(ROOT, SELFHOST_ALL)
    os.makedirs(os.path.dirname(out), exist_ok=True)
    try:
        with open(out) as f:
            old = f.read()
    except OSError:
        old = None
    if old != text:
        with open(out, "w") as f:
            f.write(text)
    return out


class Run:
    """One measured process: wall seconds and peak RSS (MB) of the child."""
    __slots__ = ("seconds", "rss_mb", "code")

    def __init__(self, seconds, rss_mb, code):
        self.seconds = seconds
        self.rss_mb = rss_mb
        self.code = code


def one_run(cmd, cwd):
    """Run ``cmd`` once; wall from perf_counter, peak RSS from wait4 via /usr/bin/time."""
    with tempfile.NamedTemporaryFile(prefix="selfhost-bench-", delete=False) as tf:
        stamp = tf.name
    try:
        t0 = time.perf_counter()
        r = subprocess.run([TIME, "-f", "%M", "-o", stamp, "--", *cmd],
                           cwd=cwd, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE)
        t1 = time.perf_counter()
        seconds = t1 - t0
        try:
            with open(stamp) as f:
                rss_kb = int((f.read().strip().splitlines() or ["0"])[-1])
        except (OSError, ValueError):
            rss_kb = 0
        return Run(seconds, rss_kb / 1024.0, r.returncode)
    finally:
        try:
            os.unlink(stamp)
        except OSError:
            pass


def check_cmd(tool, path, mode, cache=None):
    """The like-for-like ``check`` command for one side.

    ``tool`` is ``host`` or ``self``.  The self-hosted driver needs ``-I lib`` because
    its module roots are the ``-I`` directories and the working directory only; the
    Lean host already has the toolchain's ``lib/`` first.  Both run from the repo root.
    """
    flags = ["--no-cache"] if mode == "cold" else ["--cache", cache]
    if tool == "host":
        return [HOST, "check", *flags, path]
    return [SELF, "check", *flags, "-I", "lib", path]


def run_pair(path, mode, caches, order):
    """One host/self pair in the requested order: two Run objects."""
    out = {}
    for tool in order:
        cmd = check_cmd(tool, path, mode, caches[tool])
        out[tool] = one_run(cmd, ROOT)
    return out["host"], out["self"]


def summarize(runs):
    times = [r.seconds for r in runs]
    rss = [r.rss_mb for r in runs]
    med = statistics.median(times)
    vals = sorted(times)
    return {
        "median_s": round(med, 6),
        "min_s": round(vals[0], 6),
        "max_s": round(vals[-1], 6),
        "samples_s": [round(x, 6) for x in times],
        "rss_mb": round(statistics.median(rss), 1),
        "samples_rss_mb": [round(x, 1) for x in rss],
    }


def warm_up(paths, mode, caches):
    """Fill both caches before the warm samples.

    Returns {path: (host exit, self exit)}; a non-zero exit marks the file unsupported
    in the warm mode instead of aborting the run (the cold mode finds out on its own).
    """
    status = {}
    for path in paths:
        codes = []
        for tool in ("host", "self"):
            r = one_run(check_cmd(tool, path, mode, caches[tool]), ROOT)
            codes.append(r.code)
        status[path] = tuple(codes)
    return status


def measure(reps, only=None):
    paths = [p for p, _ in CORPUS if only is None or p in only]
    results = {}
    with tempfile.TemporaryDirectory(prefix="selfhost-bench-cache-") as tmp:
        caches = {"host": os.path.join(tmp, "host"), "self": os.path.join(tmp, "self")}
        for d in caches.values():
            os.makedirs(d, exist_ok=True)
        for mode in MODES:
            warmed = warm_up(paths, mode, caches) if mode == "warm" else {}
            files = {}
            for path in paths:
                if mode == "warm" and warmed[path] != (0, 0):
                    files[path] = {
                        "status": "unsupported",
                        "host_exit": warmed[path][0],
                        "selfhost_exit": warmed[path][1],
                    }
                    continue
                host_runs, self_runs = [], []
                for i in range(reps):
                    # Alternate which side goes first: a load that arrives mid-pair, or a
                    # page-cache warm-up, cancels between the two.
                    order = ("host", "self") if i % 2 == 0 else ("self", "host")
                    h, s = run_pair(path, mode, caches, order)
                    if h.code != 0 or s.code != 0:
                        files[path] = {
                            "status": "unsupported",
                            "host_exit": h.code,
                            "selfhost_exit": s.code,
                        }
                        break
                    host_runs.append(h)
                    self_runs.append(s)
                else:
                    hs = summarize(host_runs)
                    ss = summarize(self_runs)
                    files[path] = {
                        "status": "ok",
                        "host": hs,
                        "selfhost": ss,
                        "ratio": round(ss["median_s"] / hs["median_s"], 4),
                        "rss_ratio": round(ss["rss_mb"] / hs["rss_mb"], 4)
                        if hs["rss_mb"] else None,
                    }
            ok = {p: v for p, v in files.items() if v["status"] == "ok"}
            total = {
                "host_s": round(sum(v["host"]["median_s"] for v in ok.values()), 6),
                "selfhost_s": round(sum(v["selfhost"]["median_s"] for v in ok.values()), 6),
                "host_rss_mb": round(max((v["host"]["rss_mb"] for v in ok.values()), default=0), 1),
                "selfhost_rss_mb": round(max((v["selfhost"]["rss_mb"] for v in ok.values()), default=0), 1),
            }
            total["ratio"] = round(total["selfhost_s"] / total["host_s"], 4) if total["host_s"] else None
            total["rss_ratio"] = round(total["selfhost_rss_mb"] / total["host_rss_mb"], 4) \
                if total["host_rss_mb"] else None
            results[mode] = {"files": files, "total": total}
    return results


def print_table(results):
    for mode in MODES:
        r = results[mode]
        print(f"\n{mode} (--no-cache)" if mode == "cold" else f"\n{mode} (--cache DIR)")
        print(f"{'file':28s} {'host s':>9s} {'self s':>9s} {'ratio':>7s} "
              f"{'host MB':>8s} {'self MB':>8s} {'RSS×':>6s}")
        for path, _ in CORPUS:
            v = r["files"].get(path)
            if not v:
                continue
            if v["status"] != "ok":
                print(f"{path:28s} {'—':>9s} {'—':>9s} {'unsupported':>7s} "
                      f"(host exit {v['host_exit']}, self exit {v['selfhost_exit']})")
                continue
            print(f"{path:28s} {v['host']['median_s']:9.3f} {v['selfhost']['median_s']:9.3f} "
                  f"{v['ratio']:7.2f} {v['host']['rss_mb']:8.1f} {v['selfhost']['rss_mb']:8.1f} "
                  f"{v['rss_ratio']:6.2f}")
        t = r["total"]
        print(f"{'TOTAL (sum / max RSS)':28s} {t['host_s']:9.3f} {t['selfhost_s']:9.3f} "
              f"{t['ratio']:7.2f} {t['host_rss_mb']:8.1f} {t['selfhost_rss_mb']:8.1f} "
              f"{t['rss_ratio']:6.2f}")
    if REJECTED:
        print("\nRejected corpus (the selfhost stops before a check; not timed):")
        for path, why in REJECTED:
            print(f"  {path:28s} {why}")


def baseline_of(doc):
    """The ratio record a --check compares with (new schema, or the first run's results)."""
    if doc and "baseline_ratios" in doc:
        return doc["baseline_ratios"]
    if not doc:
        return {}
    return {mode: {"files": {p: v.get("ratio") for p, v in doc.get("results", {})
                             .get(mode, {}).get("files", {}).items()
                             if v.get("status") == "ok"},
                   "total": doc.get("results", {}).get(mode, {}).get("total", {}).get("ratio")}
            for mode in MODES}


def check(results, baseline, tolerance, quiet=False):
    bad = []
    print(f"\nratio check (baseline × (1 + {tolerance:.0f}%))")
    print(f"{'mode':6s} {'file':28s} {'baseline':>9s} {'now':>9s} {'change':>9s}")
    for mode in MODES:
        base = baseline.get(mode, {})
        base_files = base.get("files", {})
        for path, v in results[mode]["files"].items():
            if v["status"] != "ok":
                if path in base_files:
                    bad.append(f"{mode} {path}: unsupported now, supported in the baseline")
                continue
            before = base_files.get(path)
            if before is None:
                continue
            now = v["ratio"]
            change = (now - before) / before if before else 0.0
            mark = "  FAIL" if change * 100 > tolerance else ""
            if not quiet:
                print(f"{mode:6s} {path:28s} {before:9.2f} {now:9.2f} "
                      f"{100 * change:+8.1f}%{mark}")
            if change * 100 > tolerance:
                bad.append(f"{mode} {path}: ratio {now:.2f} vs {before:.2f} "
                           f"({100 * change:+.1f}%)")
        before = base.get("total")
        if before is not None:
            now = results[mode]["total"]["ratio"]
            change = (now - before) / before if before else 0.0
            mark = "  FAIL" if change * 100 > tolerance else ""
            if not quiet:
                print(f"{mode:6s} {'TOTAL':28s} {before:9.2f} {now:9.2f} "
                      f"{100 * change:+8.1f}%{mark}")
            if change * 100 > tolerance:
                bad.append(f"{mode} total: ratio {now:.2f} vs {before:.2f} "
                           f"({100 * change:+.1f}%)")
    if bad:
        print("\nSELFHOST REGRESSION (relative to the host):", file=sys.stderr)
        for b in bad:
            print(f"  {b}", file=sys.stderr)
        return 1
    print("\nSELFHOST RATIO OK")
    return 0


def main(argv=None):
    global HOST, SELF
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--host", default=os.environ.get("WIZ", os.path.join(ROOT, ".lake", "build", "bin", "wiz")),
                    help="the Lean-hosted wiz (default .lake/build/bin/wiz)")
    ap.add_argument("--self", dest="selfhost",
                    default=os.environ.get("WIZ_SELFHOST", os.path.join(ROOT, "bench", ".build", "selfhost")),
                    help="the self-hosted compiler (default bench/.build/selfhost)")
    ap.add_argument("--reps", type=int, default=3, help="samples per side per file (default 3)")
    ap.add_argument("--json", default=os.path.join(ROOT, "bench", "selfhost-bench.json"),
                    help="the tracking file (default bench/selfhost-bench.json)")
    ap.add_argument("--check", action="store_true",
                    help="compare the measured ratios with the tracking file and fail on a regression")
    ap.add_argument("--tolerance", type=float, default=20.0, metavar="PCT",
                    help="--check fails when a ratio is more than PCT%% worse (default 20)")
    ap.add_argument("--baseline", help="another tracking file for --check (default --json)")
    ap.add_argument("--update-baseline", action="store_true",
                    help="record this run's ratios as the baseline in --json")
    ap.add_argument("--write", action="store_true",
                    help="write --json even with --check")
    ap.add_argument("--only", action="append", default=[], metavar="FILE",
                    help="measure only FILE (repeatable)")
    args = ap.parse_args(argv)

    HOST = os.path.abspath(args.host)
    SELF = os.path.abspath(args.selfhost)
    for name, exe in (("host", HOST), ("selfhost", SELF)):
        if not os.path.exists(exe):
            raise SystemExit(f"{name} binary not found: {exe}\n"
                             "build it with bench/selfhost-build.sh (under heavy)")
    ensure_selfhost_all()
    missing = [p for p, _ in CORPUS if not os.path.exists(os.path.join(ROOT, p))]
    if missing:
        raise SystemExit("corpus file(s) missing: " + ", ".join(missing) +
                         "\nbuild the self-hosted compiler with bench/selfhost-build.sh "
                         "(it generates bench/.build/compiler.wiz)")

    doc = None
    if os.path.exists(args.json):
        try:
            with open(args.json) as f:
                doc = json.load(f)
        except (OSError, ValueError):
            doc = None
    baseline = baseline_of(doc) if args.check else None
    if args.check and not baseline:
        raise SystemExit(f"--check: no baseline_ratios in {args.baseline or args.json}; "
                         "run once with --update-baseline first")

    results = measure(args.reps, set(args.only) or None)
    print_table(results)

    if args.check:
        code = check(results, baseline, args.tolerance)
        if code:
            return code

    if args.write or not args.check:
        out = {
            "schema": 1,
            "created": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
            "generator": "bench/selfhost-bench.py",
            "commit": git("rev-parse", "HEAD"),
            "branch": git("rev-parse", "--abbrev-ref", "HEAD"),
            "host": platform.node(),
            "host_binary": HOST,
            "selfhost_binary": SELF,
            "reps": args.reps,
            "corpus": [{"path": p, "kind": k, "lines": lines_of(p)[0], "bytes": lines_of(p)[1]}
                       for p, k in CORPUS],
            "rejected": [{"path": p, "why": w} for p, w in REJECTED],
            "modes": list(MODES),
            "results": results,
        }
        old = doc.get("baseline_ratios") if doc else None
        if args.update_baseline or not old:
            old = {mode: {"files": {p: v.get("ratio") for p, v in results[mode]["files"].items()
                                    if v["status"] == "ok"},
                          "total": results[mode]["total"]["ratio"]}
                   for mode in MODES}
        out["baseline_ratios"] = old
        os.makedirs(os.path.dirname(os.path.abspath(args.json)), exist_ok=True)
        with open(args.json, "w") as f:
            json.dump(out, f, indent=2, sort_keys=True)
            f.write("\n")
        print(f"\nwrote {args.json}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
