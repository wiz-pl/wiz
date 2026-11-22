#!/usr/bin/env python3
"""Measure the e-graph engine change on two revisions, with one harness and compiler.

The comparison is A/B on two revisions of the same tree, built with the same
`wiz` compiler and the same harness (`examples/scry-egraph-bench.wiz`):

  old  9de503419^  `Scry.Egraph` the reference engine: the hash cons is a flat
                   association list and `rebuildNodes` appends one node at a time
  new  HEAD        `Scry.Egraph` the one engine: `etable` is a `U64Map` bucket and
                   `rebuildNodes` conses onto a fresh list

The shapes are `add` (hash-cons path), `rebuild` (congruence closure and the node
table rewrite) and `merge` (the Datalog stratum's `mergeFacts`: all unions, one
rebuild). See README.md.

Usage:
  python3 scry/bench/egraph/run.py                 # 3 rounds, rewrite results.json/tsv
  python3 scry/bench/egraph/run.py --rounds 5
  python3 scry/bench/egraph/run.py --sizes 200,1600,12800
  python3 scry/bench/egraph/run.py --check         # build the harness, verify counts only

The driver builds each revision in a throwaway `git worktree` under /tmp and
removes it afterwards; it never touches the working tree. `wiz build` is a
compile, so run this under `heavy` (AGENTS.md). The reported times are
informational and are not a `perf-run` claim; the derived counts are checked.
"""

import json
import os
import platform
import shutil
import statistics
import subprocess
import sys
import tempfile
import time

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = subprocess.check_output(
    ["git", "-C", HERE, "rev-parse", "--show-toplevel"], text=True).strip()
HARNESS = os.path.join(REPO, "examples", "scry-egraph-bench.wiz")
DEFAULT_OLD_REV = "9de503419^"
DEFAULT_NEW_REV = "HEAD"
DEFAULT_SIZES = [200, 400, 800, 1600, 3200, 6400, 12800, 25600]
MODES = ["add", "rebuild", "merge"]


def log(msg):
    print(msg, file=sys.stderr, flush=True)


def shown(path):
    """A path for output: relative to the invocation directory when it is below it."""
    try:
        rel = os.path.relpath(path)
    except ValueError:
        return path
    return rel if not rel.startswith("..") else path


def run_capture(cmd, cwd=None):
    p = subprocess.run(cmd, cwd=cwd, text=True, capture_output=True)
    if p.returncode != 0:
        raise RuntimeError("%s failed (%d):\n%s\n%s" %
                           (" ".join(cmd), p.returncode, p.stdout, p.stderr))
    return p.stdout


def measure(cmd, out_path):
    """Run cmd, returning (wall_ms, peak_rss_kib, parsed fields)."""
    start = time.monotonic()
    pid = os.fork()
    if pid == 0:
        fd = os.open(out_path, os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o644)
        os.dup2(fd, 1)
        os.dup2(fd, 2)
        try:
            os.execvpe(cmd[0], cmd, os.environ)
        except BaseException:
            os._exit(127)
    _, status, ru = os.wait4(pid, 0)
    wall_ms = (time.monotonic() - start) * 1000.0
    if os.WIFSIGNALED(status):
        raise RuntimeError("%s killed by signal %d (see %s)" %
                           (" ".join(cmd), os.WTERMSIG(status), out_path))
    if os.WEXITSTATUS(status) != 0:
        raise RuntimeError("%s exited %d (see %s)" %
                           (" ".join(cmd), os.WEXITSTATUS(status), out_path))
    return wall_ms, ru.ru_maxrss, parse_output(out_path)


def parse_output(path):
    fields = {}
    with open(path, "r", errors="replace") as f:
        for line in f:
            line = line.rstrip("\n")
            if "=" in line:
                k, _, v = line.partition("=")
                fields[k] = int(v) if v.isdigit() else v
    return fields


def expected(case):
    mode, n = case["mode"], case["size"]
    if mode == "add":
        return {"nodes": n, "classes": n}
    # every leaf collapses to one class, so congruence leaves one leaf and one f node
    return {"nodes": 2, "classes": 1}


def include_args(tree):
    """The library paths that tree imports `Scry.Egraph` from."""
    args = ["-I", os.path.join(tree, "lib")]
    if not os.path.exists(os.path.join(tree, "lib", "Scry", "Egraph.wiz")):
        args += ["-I", os.path.join(tree, "scry", "src")]
    return args


def build(tree, out, wiz):
    t0 = time.monotonic()
    run_capture([wiz, "build"] + include_args(tree) +
                [os.path.join(tree, "egraph-bench.wiz"), "-o", out], cwd=tree)
    return time.monotonic() - t0


def checkout(rev, dest):
    run_capture(["git", "-C", REPO, "worktree", "add", "--detach", dest, rev])
    shutil.copy2(HARNESS, os.path.join(dest, "egraph-bench.wiz"))
    return dest


def loadavg():
    with open("/proc/loadavg") as f:
        return [float(x) for x in f.read().split()[:3]]


def cpu_model():
    try:
        with open("/proc/cpuinfo") as f:
            for line in f:
                if line.startswith("model name"):
                    return line.split(":", 1)[1].strip()
    except OSError:
        pass
    return platform.processor() or "unknown"


def wiz_version(wiz):
    try:
        return run_capture([wiz, "--version"]).strip()
    except Exception as e:  # pragma: no cover - only on a broken toolchain
        return "unknown (%s)" % e


def main():
    import argparse
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--rounds", type=int, default=3)
    ap.add_argument("--old-rev", default=DEFAULT_OLD_REV)
    ap.add_argument("--new-rev", default=DEFAULT_NEW_REV)
    ap.add_argument("--sizes", default=",".join(str(s) for s in DEFAULT_SIZES))
    ap.add_argument("--wiz", default=os.environ.get("WIZ", "wiz"),
                    help="the wiz compiler (default: $WIZ or wiz on PATH)")
    ap.add_argument("--out-dir", default=HERE)
    ap.add_argument("--check", action="store_true",
                    help="build the new revision, verify the derived counts, exit")
    args = ap.parse_args()
    if args.rounds < 1:
        ap.error("--rounds must be positive")
    sizes = [int(s) for s in args.sizes.split(",") if s]
    if not sizes or any(s < 2 for s in sizes):
        ap.error("--sizes needs integers >= 2")
    cases = [{"mode": m, "size": s} for s in sizes for m in MODES]

    tmp = tempfile.mkdtemp(prefix="egraph-bench-")
    old_tree = os.path.join(tmp, "old")
    new_tree = os.path.join(tmp, "new")
    old_bin = os.path.join(tmp, "bench-old")
    new_bin = os.path.join(tmp, "bench-new")
    results_path = os.path.join(args.out_dir, "results.json")
    try:
        log("worktrees: %s" % tmp)
        checkout(args.new_rev, new_tree)
        log("building new %s ..." % args.new_rev)
        new_build_s = build(new_tree, new_bin, args.wiz)

        if args.check:
            bad = []
            for c in cases:
                _, _, got = measure([new_bin, c["mode"], str(c["size"])],
                                    os.path.join(tmp, "check.out"))
                want = expected(c)
                if any(got.get(k) != v for k, v in want.items()):
                    bad.append("%s %d: %s, expected %s" %
                               (c["mode"], c["size"], got, want))
            if bad:
                for b in bad:
                    print("STALE: " + b)
                return 1
            print("ok: %d derived counts match" % len(cases))
            return 0

        checkout(args.old_rev, old_tree)
        log("building old %s ..." % args.old_rev)
        old_build_s = build(old_tree, old_bin, args.wiz)

        # Warm every (engine, case) once and check the derived counts before any
        # timed round; round 1 is otherwise a page-cache/allocator outlier.
        for c in cases:
            for engine, binary in (("old", old_bin), ("new", new_bin)):
                out = os.path.join(tmp, "warmup-%s-%d-%s.out" %
                                   (c["mode"], c["size"], engine))
                _, _, got = measure([binary, c["mode"], str(c["size"])], out)
                want = expected(c)
                if any(got.get(k) != v for k, v in want.items()):
                    raise RuntimeError("%s %s %d: counts %s, expected %s" %
                                       (engine, c["mode"], c["size"], got, want))

        records = []
        loads = []
        measured_utc = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
        for r in range(1, args.rounds + 1):
            loads.append(loadavg())
            log("round %d/%d (load %s)" % (r, args.rounds,
                                           " ".join("%.2f" % x for x in loads[-1])))
            order = [("old", old_bin), ("new", new_bin)]
            if r % 2 == 0:
                order.reverse()  # interleave the order, not just the runs
            for c in cases:
                for engine, binary in order:
                    out = os.path.join(tmp, "r%d-%s-%d-%s.out" %
                                       (r, c["mode"], c["size"], engine))
                    wall, rss, got = measure(
                        [binary, c["mode"], str(c["size"])], out)
                    want = expected(c)
                    if any(got.get(k) != v for k, v in want.items()):
                        raise RuntimeError("%s %s %d: counts %s, expected %s" %
                                           (engine, c["mode"], c["size"], got, want))
                    key = c["mode"] + "_ms"
                    records.append({
                        "case": "%s %d" % (c["mode"], c["size"]),
                        "mode": c["mode"],
                        "size": c["size"],
                        "engine": engine,
                        "round": r,
                        "engine_ms": got.get(key),
                        "wall_ms": round(wall, 1),
                        "peak_rss_kib": rss,
                        "derived": {k: got.get(k) for k in want},
                    })

        summary = {}
        for c in cases:
            name = "%s %d" % (c["mode"], c["size"])
            summary[name] = {}
            for engine in ("old", "new"):
                xs = [x["engine_ms"] for x in records
                      if x["case"] == name and x["engine"] == engine
                      and x["engine_ms"] is not None]
                summary[name][engine] = {
                    "median_ms": statistics.median(xs) if xs else None,
                    "runs_ms": xs,
                }

        results = {
            "schema": 1,
            "measured_utc": measured_utc,
            "host": {
                "uname": platform.uname().release + "-" + platform.machine(),
                "cpu": cpu_model(),
                "nproc": os.cpu_count(),
                "load_average_1_5_15_start": loads[0] if loads else None,
                "load_average_per_round": loads,
            },
            "revisions": {
                "old": run_capture(["git", "-C", REPO, "rev-parse",
                                    args.old_rev + "^{commit}"]).strip(),
                "new": run_capture(["git", "-C", REPO, "rev-parse",
                                    args.new_rev + "^{commit}"]).strip(),
                "new_is_head": args.new_rev == "HEAD",
            },
            "toolchain": {
                "wiz": wiz_version(args.wiz),
                "build_command": "wiz build -I lib [-I scry/src] egraph-bench.wiz -o bench",
                "old_build_s": round(old_build_s, 2),
                "new_build_s": round(new_build_s, 2),
            },
            "summary": summary,
            "rounds": records,
        }
        with open(results_path, "w") as f:
            json.dump(results, f, indent=2)
            f.write("\n")
        tsv_path = os.path.join(args.out_dir, "results.tsv")
        with open(tsv_path, "w") as f:
            f.write("case\tengine\tmedian_ms\truns_ms\n")
            for name in summary:
                for engine in ("old", "new"):
                    s = summary[name][engine]
                    runs = ",".join(str(x) for x in s["runs_ms"])
                    f.write("%s\t%s\t%s\t%s\n" %
                            (name, engine, s["median_ms"], runs))
        print("wrote %s and %s" % (shown(results_path), shown(tsv_path)))
        for name in summary:
            o = summary[name]["old"]["median_ms"]
            n = summary[name]["new"]["median_ms"]
            print("%-12s old %8s ms   new %8s ms" % (name, o, n))
        return 0
    finally:
        for tree in (old_tree, new_tree):
            if os.path.isdir(tree):
                subprocess.run(["git", "-C", REPO, "worktree", "remove", "--force",
                                tree], capture_output=True, text=True)
        subprocess.run(["git", "-C", REPO, "worktree", "prune"], capture_output=True)
        shutil.rmtree(tmp, ignore_errors=True)


if __name__ == "__main__":
    sys.exit(main())
