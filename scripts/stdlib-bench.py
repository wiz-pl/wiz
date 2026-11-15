#!/usr/bin/env python3
"""Measure the standard library's hot data structures.

Builds ``bench/stdlib-bench.wiz`` and runs each mode several times in its own process
(the wall time includes the same constant program start-up in every sample).  Prints a
table and writes a JSON record with every sample, the median, the variance and the
coefficient of variation, so a later run can be compared with an earlier one:

    scripts/stdlib-bench.py                          # 5 samples per mode
    scripts/stdlib-bench.py --reps 7 --json /tmp/out.json
    scripts/stdlib-bench.py --baseline bench/stdlib-baseline.json
    scripts/stdlib-bench.py --baseline-bin bin/old                  # interleaved A/B
    scripts/stdlib-bench.py --baseline bench/stdlib-baseline.json --fail-regression 5

Two kinds of comparison are supported.  `--baseline JSON` compares this run's medians
with a previous JSON (cheap, but the machine may have changed between the runs).
`--baseline-bin EXE` alternates one run of the old executable with one run of the new
for every sample, and reports the median of the per-pair ratios: drift in machine load
cancels out, which is what to use when deciding whether a change is a regression.

The sizes are fixed in the benchmark program (``defaultN``); ``--size MODE=N`` overrides
one for an experiment.  Sizes are passed to the program, so a sample does exactly the
work its JSON says, and the program prints a checksum: a mode whose checksum changes
between runs (or between the two builds of a comparison) is a failure, not a timing.

The machine-readable output is written to ``--json`` (default
``bench/stdlib-bench.json``); ``--quiet`` prints nothing but that file.  Nothing here
touches the network or the source tree except the build output under
``bench/.build`` (override with ``--bin``).
"""
import argparse
import json
import os
import platform
import statistics
import subprocess
import sys
import tempfile
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

MODES = [
    "strmap-insert", "strmap-find", "strmap-miss", "strmap-iterate",
    "array-push", "array-index", "array-map", "array-fold",
    "bytes-append", "bytes-slice", "bytes-compare",
    "text-split", "text-replace", "text-trim", "text-eq", "text-suffix",
    "sort", "hash",
]


def git(*args):
    try:
        return subprocess.run(["git", "-C", ROOT, *args], capture_output=True,
                              text=True, check=True).stdout.strip()
    except (OSError, subprocess.CalledProcessError):
        return ""


def default_bin():
    return os.path.join(ROOT, "bench", ".build", "stdlib-bench")


def build(binary, cc=None, quiet=False):
    src = os.path.join(ROOT, "bench", "stdlib-bench.wiz")
    if os.path.exists(binary) and os.path.getmtime(binary) >= os.path.getmtime(src):
        return binary
    os.makedirs(os.path.dirname(binary), exist_ok=True)
    wiz = os.environ.get("WIZ", os.path.join(ROOT, ".lake", "build", "bin", "wiz"))
    if not os.path.exists(wiz):
        wiz = "wiz"
    cmd = [wiz, "build", src, "-o", binary]
    if cc:
        cmd += ["--cc", cc]
    if os.environ.get("WIZ_CFLAGS"):
        cmd += ["--cflags", os.environ["WIZ_CFLAGS"]]
    if os.environ.get("WIZ_LDFLAGS"):
        cmd += ["--ldflags", os.environ["WIZ_LDFLAGS"]]
    if not quiet:
        print("building", binary, file=sys.stderr)
    r = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True)
    if r.returncode != 0:
        sys.stderr.write(r.stdout)
        sys.stderr.write(r.stderr)
        raise SystemExit("build failed")
    return binary


def one_run(binary, mode, n):
    """One sample: (nanoseconds, checksum)."""
    t0 = time.perf_counter_ns()
    r = subprocess.run([binary, mode, str(n)], cwd=ROOT, capture_output=True, text=True)
    t1 = time.perf_counter_ns()
    if r.returncode != 0:
        raise SystemExit(f"{mode}: exited {r.returncode}: {r.stderr[-2000:]}")
    parts = r.stdout.split()
    if len(parts) != 2:
        raise SystemExit(f"{mode}: expected 'MODE CHECKSUM', got {r.stdout!r}")
    return t1 - t0, parts[1]


def summarize(samples):
    med = int(statistics.median(samples))
    mean = statistics.fmean(samples)
    var = statistics.pvariance(samples) if len(samples) > 1 else 0.0
    sd = var ** 0.5
    return {
        "samples_ns": samples,
        "median_ns": med,
        "mean_ns": int(mean),
        "min_ns": min(samples),
        "max_ns": max(samples),
        "variance_ns2": var,
        "stdev_ns": sd,
        "cv": (sd / mean) if mean else 0.0,
        "spread": ((max(samples) - min(samples)) / med) if med else 0.0,
    }


def fmt_ms(ns):
    return f"{ns / 1e6:.1f}"


def fmt_pct(x):
    return f"{100.0 * x:+.1f}%"


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--reps", type=int, default=5, help="samples per mode (default 5)")
    ap.add_argument("--warmup", type=int, default=1, help="unrecorded runs before samples")
    ap.add_argument("--json", default=os.path.join(ROOT, "bench", "stdlib-bench.json"),
                    help="machine-readable output")
    ap.add_argument("--baseline", help="an earlier JSON to compare with")
    ap.add_argument("--baseline-bin", metavar="EXECUTABLE",
                    help="an older benchmark executable to interleave with this one")
    ap.add_argument("--allow-checksum", action="append", default=[], metavar="MODE",
                    help="do not fail when MODE's checksum differs (a deliberate change)")
    ap.add_argument("--fail-regression", type=float, metavar="PCT",
                    help="exit 1 if a mode is slower than the baseline by more than PCT%%")
    ap.add_argument("--size", action="append", default=[], metavar="MODE=N",
                    help="override a mode's size (repeatable)")
    ap.add_argument("--bin", default=None, help="benchmark executable")
    ap.add_argument("--cc", default=os.environ.get("WIZ_CC"), help="C compiler")
    ap.add_argument("--quiet", action="store_true")
    args = ap.parse_args(argv)

    sizes = {}
    for spec in args.size:
        if "=" not in spec:
            ap.error(f"--size wants MODE=N, got {spec!r}")
        m, n = spec.split("=", 1)
        if m not in MODES:
            ap.error(f"unknown mode {m!r}")
        sizes[m] = int(n)

    if args.bin:
        # An explicit executable is used as it is: it may be an older build (the
        # A-side of a comparison) that must not be rebuilt from the current sources.
        binary = args.bin
        if not os.path.exists(binary):
            raise SystemExit(f"--bin: no such file: {binary}")
    else:
        binary = build(default_bin(), args.cc, args.quiet)
    results = {}
    checksums = {}
    for mode in MODES:
        n = sizes.get(mode, DEFAULT_SIZES[mode])
        ck = None
        for _ in range(args.warmup):
            one_run(binary, mode, n)
        samples = []
        for _ in range(args.reps):
            ns, c = one_run(binary, mode, n)
            samples.append(ns)
            if ck is None:
                ck = c
            elif c != ck:
                raise SystemExit(f"{mode}: non-deterministic checksum ({ck} then {c})")
        checksums[mode] = ck
        s = summarize(samples)
        s.update({"mode": mode, "n": n, "checksum": ck})
        results[mode] = s
        if not args.quiet:
            print(f"{mode:14s} n={n:<8d} median {fmt_ms(s['median_ns']):>8s} ms  "
                  f"sd {fmt_ms(s['stdev_ns']):>6s} ms  cv {100*s['cv']:5.1f}%  "
                  f"checksum {ck}")

    ab = {}
    if args.baseline_bin:
        old = os.path.abspath(args.baseline_bin)
        if not os.path.exists(old):
            raise SystemExit(f"--baseline-bin: no such file: {old}")
        if not args.quiet:
            print()
        for mode in MODES:
            n = sizes.get(mode, DEFAULT_SIZES[mode])
            ratios, olds, news = [], [], []
            for i in range(args.reps):
                # Alternate which build runs first: a systematic first/second effect
                # (cache warmth, a load that arrives mid-pair) then cancels too.
                if i % 2 == 0:
                    a, ca = one_run(old, mode, n)
                    b, cb = one_run(binary, mode, n)
                else:
                    b, cb = one_run(binary, mode, n)
                    a, ca = one_run(old, mode, n)
                if ca != cb and mode not in args.allow_checksum:
                    raise SystemExit(f"{mode}: baseline checksum {ca}, this build {cb}")
                ratios.append(b / a)
                olds.append(a)
                news.append(b)
            ratios.sort()
            rec = {
                "baseline_median_ns": int(statistics.median(olds)),
                "median_ns": int(statistics.median(news)),
                "median_ratio": statistics.median(ratios),
                "min_ratio": ratios[0],
                "max_ratio": ratios[-1],
                "samples_ratio": ratios,
                "checksums_equal": ca == cb,
            }
            ab[mode] = rec
            if not args.quiet:
                print(f"{mode:14s} A {fmt_ms(rec['baseline_median_ns']):>8s}ms  "
                      f"B {fmt_ms(rec['median_ns']):>8s}ms  "
                      f"ratio {rec['median_ratio']:6.3f}")

    out = {
        "schema": 1,
        "created": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "generator": "scripts/stdlib-bench.py",
        "commit": git("rev-parse", "HEAD"),
        "branch": git("rev-parse", "--abbrev-ref", "HEAD"),
        "host": platform.node(),
        "binary": binary,
        "reps": args.reps,
        "warmup": args.warmup,
        "results": results,
    }
    if ab:
        out["ab"] = {"baseline_bin": args.baseline_bin, "results": ab}
    os.makedirs(os.path.dirname(os.path.abspath(args.json)), exist_ok=True)
    with open(args.json, "w") as f:
        json.dump(out, f, indent=2, sort_keys=True)
        f.write("\n")

    if args.baseline:
        with open(args.baseline) as f:
            base = json.load(f)
        print(f"\n{'mode':14s} {'before':>10s} {'after':>10s} {'change':>9s}  checksum")
        bad = []
        for mode in MODES:
            if mode not in base.get("results", {}):
                continue
            b = base["results"][mode]["median_ns"]
            a = results[mode]["median_ns"]
            change = (a - b) / b if b else 0.0
            same = (base["results"][mode].get("checksum") == results[mode]["checksum"]
                    or mode in args.allow_checksum)
            mark = "" if same else "  (CHECKSUM CHANGED)"
            print(f"{mode:14s} {fmt_ms(b):>8s}ms {fmt_ms(a):>8s}ms {fmt_pct(change):>9s}{mark}")
            if not same:
                bad.append(mode)
            elif args.fail_regression is not None and change * 100 > args.fail_regression:
                bad.append(mode)
        if bad:
            raise SystemExit(f"regressions or changed checksums: {', '.join(bad)}")

    if not args.quiet:
        print(f"\nwrote {args.json}")
    return 0


# The benchmark program's sizes, kept in sync with `defaultN` in the .wiz file.
DEFAULT_SIZES = {
    "strmap-insert": 200000, "strmap-find": 200000, "strmap-miss": 200000,
    "strmap-iterate": 200000,
    "array-push": 2000000, "array-index": 500000, "array-map": 1000000,
    "array-fold": 1000000,
    "bytes-append": 2000000, "bytes-slice": 2000000, "bytes-compare": 2000000,
    "text-split": 40000, "text-replace": 40000, "text-trim": 40000, "text-eq": 40000,
    "text-suffix": 40000,
    "sort": 100000, "hash": 300000,
}

if __name__ == "__main__":
    sys.exit(main())
