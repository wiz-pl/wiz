#!/usr/bin/env python3
"""Measure the Datalog store/index change and the naive baseline.

The comparison is A/B on two revisions of the same tree, built with the same
`wiz` compiler and the same harness:

  old  bb1a6294  `Scry.Store`/`Scry.Eval` with no dedup or join index
  new  1fde883a  the hashed dedup + (column, value) join indexes + indexed
                provenance, all in the same semi-naive delta loop

Both evaluators are semi-naive.  The optional `naive` rows are a third program:
one round of every rule against the whole store, repeated to the fixpoint, to
separate the delta loop from the store.  See README.md.

Usage:
  python3 scry/bench/datalog/run.py                 # 3 rounds, rewrite results.json/tsv
  python3 scry/bench/datalog/run.py --rounds 5
  python3 scry/bench/datalog/run.py --check         # rebuild + verify input hashes only

The driver builds each revision in a throwaway `git worktree` under /tmp and
removes it afterwards; it never touches the working tree.
"""

import hashlib
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
HARNESS = os.path.join(REPO, "examples", "scry-datalog-bench.wiz")
QUERIES = os.path.join(HERE, "queries.json")
DEFAULT_OLD_REV = "bb1a6294"
DEFAULT_NEW_REV = "1fde883a"


def log(msg):
    print(msg, file=sys.stderr, flush=True)


def shown(path):
    """A path for output: relative to the invocation directory when it is below it."""
    try:
        rel = os.path.relpath(path)
    except ValueError:
        return path
    return rel if not rel.startswith("..") else path


def sha256_file(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def run_capture(cmd, cwd=None):
    p = subprocess.run(cmd, cwd=cwd, text=True, capture_output=True)
    if p.returncode != 0:
        raise RuntimeError("%s failed (%d):\n%s\n%s" %
                           (" ".join(cmd), p.returncode, p.stdout, p.stderr))
    return p.stdout


def measure(cmd, out_path, timeout=None):
    """Run cmd, returning (wall_ms, peak_rss_kib, parsed output).

    os.wait4 gives the peak RSS of this child alone; /usr/bin/time is not
    present on every machine.  The child's stdout and stderr go to out_path.
    """
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
                if v.isdigit():
                    fields[k] = int(v)
                else:
                    fields[k] = v
    return fields


def derived_ok(fields, expect):
    return all(fields.get(k) == v for k, v in expect.items())


def checkout(rev, dest):
    run_capture(["git", "-C", REPO, "worktree", "add", "--detach", dest, rev])
    shutil.copy2(HARNESS, os.path.join(dest, "scry-bench.wiz"))
    return dest


def build(tree, out):
    t0 = time.monotonic()
    run_capture(["wiz", "build", "-I", os.path.join(tree, "lib"),
                 os.path.join(tree, "scry-bench.wiz"), "-o", out], cwd=tree)
    return time.monotonic() - t0


def dump_hash(binary, kind, n, path):
    out = run_capture([binary, "dump", kind, str(n)])
    with open(path, "w") as f:
        f.write(out)
    rows = sum(1 for line in out.splitlines() if line)
    return hashlib.sha256(out.encode()).hexdigest(), rows


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


def wiz_version():
    try:
        return run_capture(["wiz", "--version"]).strip()
    except Exception as e:  # pragma: no cover - only on a broken toolchain
        return "unknown (%s)" % e


def median(xs):
    return statistics.median(xs)


def main():
    import argparse
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--rounds", type=int, default=3)
    ap.add_argument("--old-rev", default=DEFAULT_OLD_REV)
    ap.add_argument("--new-rev", default=DEFAULT_NEW_REV)
    ap.add_argument("--out-dir", default=HERE)
    ap.add_argument("--check", action="store_true",
                    help="rebuild the new revision, verify the pinned input hashes, exit")
    args = ap.parse_args()
    if args.rounds < 1:
        ap.error("--rounds must be positive")

    with open(QUERIES) as f:
        spec = json.load(f)
    cases = spec["cases"]
    naive_cases = spec.get("naive_cases", [])

    tmp = tempfile.mkdtemp(prefix="datalog-bench-")
    old_tree = os.path.join(tmp, "old")
    new_tree = os.path.join(tmp, "new")
    old_bin = os.path.join(tmp, "bench-old")
    new_bin = os.path.join(tmp, "bench-new")
    results_path = os.path.join(args.out_dir, "results.json")
    try:
        log("worktrees: %s" % tmp)
        checkout(args.new_rev, new_tree)
        log("building new %s ..." % args.new_rev)
        new_build_s = build(new_tree, new_bin)

        harness_sha = sha256_file(HARNESS)
        if args.check:
            with open(results_path) as f:
                pinned = json.load(f)
            bad = []
            harness_pin = pinned.get("toolchain", {}).get("harness_sha256")
            if harness_pin != harness_sha:
                bad.append("harness sha256: pinned %s, now %s" %
                           (harness_pin, harness_sha))
            for c in cases:
                kind, n = c["input"]
                got, rows = dump_hash(new_bin, kind, n,
                                      os.path.join(tmp, "dump-%s.tsv" % kind))
                want = pinned.get("inputs", {}).get(c["name"], {})
                if want.get("sha256") != got:
                    bad.append("%s input sha256: pinned %s, now %s" %
                               (c["name"], want.get("sha256"), got))
                elif want.get("edb_rows") != rows:
                    bad.append("%s edb rows: pinned %s, now %d" %
                               (c["name"], want.get("edb_rows"), rows))
            if bad:
                for b in bad:
                    print("STALE: " + b)
                return 1
            print("ok: harness and %d input hashes match %s" %
                  (len(cases), shown(results_path)))
            return 0

        checkout(args.old_rev, old_tree)
        log("building old %s ..." % args.old_rev)
        old_build_s = build(old_tree, old_bin)

        # Pin what the inputs were before timing anything.  The old binary must
        # produce the same EDB, otherwise the A/B is not one input.
        inputs = {}
        for c in cases:
            kind, n = c["input"]
            new_sha, rows = dump_hash(new_bin, kind, n,
                                      os.path.join(tmp, "new-%s.tsv" % kind))
            old_sha, old_rows = dump_hash(old_bin, kind, n,
                                          os.path.join(tmp, "old-%s.tsv" % kind))
            if (new_sha, rows) != (old_sha, old_rows):
                raise RuntimeError("%s: old and new EDB differ" % c["name"])
            inputs[c["name"]] = {"sha256": new_sha, "edb_rows": rows}
            log("input %-12s %d EDB rows sha256=%s" % (c["name"], rows, new_sha[:16]))

        # Warm every (engine, case) once and check the pinned counts before any
        # timed round; round 1 is otherwise a page-cache/allocator outlier.
        for c in cases:
            for engine, binary in (("old", old_bin), ("new", new_bin)):
                out = os.path.join(
                    tmp, "warmup-%s-%s.out" %
                    (c["name"].replace(" ", "-"), engine))
                _, _, fields = measure([binary] + c["args"], out)
                if not derived_ok(fields, c["expect"]):
                    raise RuntimeError("%s %s: counts %s, expected %s" %
                                       (engine, c["name"], fields, c["expect"]))
        for c in naive_cases:
            out = os.path.join(tmp, "warmup-%s.out" %
                               c["name"].replace(" ", "-"))
            _, _, fields = measure([new_bin] + c["args"], out)
            if not derived_ok(fields, c["expect"]):
                raise RuntimeError("new %s: counts %s, expected %s" %
                                   (c["name"], fields, c["expect"]))

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
                    out = os.path.join(
                        tmp, "r%d-%s-%s.out" %
                        (r, c["name"].replace(" ", "-"), engine))
                    wall, rss, fields = measure([binary] + c["args"], out)
                    if not derived_ok(fields, c["expect"]):
                        raise RuntimeError("%s %s: counts %s, expected %s" %
                                           (engine, c["name"], fields, c["expect"]))
                    records.append({
                        "case": c["name"],
                        "engine": engine,
                        "round": r,
                        "eval_ms": fields["eval_ms"],
                        "build_ms": fields.get("build_ms"),
                        "wall_ms": round(wall, 1),
                        "peak_rss_kib": rss,
                        "derived": {k: fields[k] for k in c["expect"]},
                    })
            # Naive is measured on the new binary only, after the A/B pair.
            for c in naive_cases:
                out = os.path.join(tmp, "r%d-%s.out" %
                                   (r, c["name"].replace(" ", "-")))
                wall, rss, fields = measure([new_bin] + c["args"], out)
                if not derived_ok(fields, c["expect"]):
                    raise RuntimeError("%s: counts %s, expected %s" %
                                       (c["name"], fields, c["expect"]))
                records.append({
                    "case": c["name"],
                    "engine": "naive",
                    "round": r,
                    "eval_ms": fields["eval_ms"],
                    "build_ms": fields.get("build_ms"),
                    "wall_ms": round(wall, 1),
                    "peak_rss_kib": rss,
                    "derived": {k: fields[k] for k in c["expect"]},
                })
        end_load = loadavg()

        def series(case, engine, key):
            return [x[key] for x in records
                    if x["case"] == case and x["engine"] == engine]

        summary = []
        for c in cases:
            old = series(c["name"], "old", "eval_ms")
            new = series(c["name"], "new", "eval_ms")
            oldw = series(c["name"], "old", "wall_ms")
            neww = series(c["name"], "new", "wall_ms")
            oldr = series(c["name"], "old", "peak_rss_kib")
            newr = series(c["name"], "new", "peak_rss_kib")
            ratio = median(old) / median(new)
            row = {
                "case": c["name"],
                "input_sha256": inputs[c["name"]]["sha256"],
                "edb_rows": inputs[c["name"]]["edb_rows"],
                "expect": c["expect"],
                "old": {
                    "eval_ms": old,
                    "eval_ms_median": median(old),
                    "wall_ms": oldw,
                    "wall_ms_median": median(oldw),
                    "peak_rss_mib_median": round(median(oldr) / 1024.0, 1),
                },
                "new": {
                    "eval_ms": new,
                    "eval_ms_median": median(new),
                    "wall_ms": neww,
                    "wall_ms_median": median(neww),
                    "peak_rss_mib_median": round(median(newr) / 1024.0, 1),
                },
                "speedup_median": round(ratio, 2),
                "speedup_per_round": [round(a / b, 2) for a, b in zip(old, new)],
            }
            summary.append(row)
            log("%-12s old %8.1f ms  new %7.1f ms  %6.2fx" %
                (c["name"], median(old), median(new), ratio))

        naive_summary = []
        by_case = {r["case"]: r for r in summary}
        for c in naive_cases:
            mine = series(c["name"], "naive", "eval_ms")
            ref = by_case[c["against"]]
            row = {
                "case": c["name"],
                "against": c["against"],
                "eval_ms": mine,
                "eval_ms_median": median(mine),
                "wall_ms": series(c["name"], "naive", "wall_ms"),
                "peak_rss_mib_median": round(
                    median(series(c["name"], "naive", "peak_rss_kib")) / 1024.0, 1),
                "slowdown_vs_seminaive": round(
                    median(mine) / ref["new"]["eval_ms_median"], 2),
            }
            naive_summary.append(row)
            log("%-16s %8.1f ms vs semi-naive %7.1f ms  %.2fx slower" %
                (c["name"], median(mine), ref["new"]["eval_ms_median"],
                 row["slowdown_vs_seminaive"]))

        result = {
            "schema": 1,
            "measured_utc": measured_utc,
            "host": {
                "uname": platform.platform(),
                "cpu": cpu_model(),
                "nproc": os.cpu_count(),
                "load_average_1_5_15_start": loads[0] if loads else None,
                "load_average_1_5_15_end": end_load,
                "load_average_per_round": loads,
            },
            "toolchain": {
                "wiz": wiz_version(),
                "build_command": "wiz build -I lib examples/scry-datalog-bench.wiz -o bench",
                "harness_sha256": harness_sha,
            },
            "revisions": {
                "old": run_capture(["git", "-C", REPO, "rev-parse", args.old_rev]).strip(),
                "new": run_capture(["git", "-C", REPO, "rev-parse", args.new_rev]).strip(),
                "old_label": args.old_rev,
                "new_label": args.new_rev,
            },
            "rounds": args.rounds,
            "inputs": inputs,
            "cases": summary,
            "naive_cases": naive_summary,
            "records": records,
            "cold_build_seconds": {"old": round(old_build_s, 1),
                                   "new": round(new_build_s, 1)},
        }
        os.makedirs(args.out_dir, exist_ok=True)
        with open(results_path, "w") as f:
            json.dump(result, f, indent=2)
            f.write("\n")
        tsv_path = os.path.join(args.out_dir, "results.tsv")
        with open(tsv_path, "w") as f:
            f.write("case\tengine\tround\teval_ms\tbuild_ms\twall_ms\tpeak_rss_mib\tderived\n")
            for x in records:
                f.write("%s\t%s\t%d\t%d\t%s\t%.1f\t%.1f\t%s\n" % (
                    x["case"], x["engine"], x["round"], x["eval_ms"],
                    x["build_ms"] if x["build_ms"] is not None else "",
                    x["wall_ms"], x["peak_rss_kib"] / 1024.0,
                    json.dumps(x["derived"], sort_keys=True)))
        log("wrote %s and %s" % (shown(results_path), shown(tsv_path)))
        return 0
    finally:
        for wt in (old_tree, new_tree):
            if os.path.isdir(wt):
                subprocess.run(["git", "-C", REPO, "worktree", "remove", "--force", wt],
                               stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        shutil.rmtree(tmp, ignore_errors=True)


if __name__ == "__main__":
    sys.exit(main())
