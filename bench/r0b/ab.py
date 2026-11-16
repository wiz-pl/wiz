#!/usr/bin/env python3
"""Interleaved A/B timing of two builds of one program (R0(b)).

    ab.py --reps N --json OUT [--tsv FILE --tag TARGET VARIANT] NAME BASE_EXE VARIANT_EXE [ARGS...]

Runs BASE and VARIANT alternately N times (after one unrecorded warm-up of each), checks
that both print the same output every time (a different output is a failure, exit 1),
and writes the samples, the medians and the median of the per-pair ratios VARIANT/BASE
to OUT. The paired ratio cancels drift in machine load, as scripts/stdlib-bench.py's
--baseline-bin does.
"""
import argparse
import json
import statistics
import subprocess
import sys
import time


def run(exe, args):
    t = time.perf_counter_ns()
    p = subprocess.run([exe, *args], capture_output=True)
    dt = time.perf_counter_ns() - t
    if p.returncode != 0:
        sys.exit(f"ab: {exe} exited {p.returncode}: {p.stderr.decode()[:500]}")
    return dt, p.stdout


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--reps", type=int, default=11)
    ap.add_argument("--json", required=True)
    ap.add_argument("--tsv", help="append TARGET NAME VARIANT ratio_median min max to this file")
    ap.add_argument("--tag", nargs=2, metavar=("TARGET", "VARIANT"), default=["-", "-"])
    ap.add_argument("name")
    ap.add_argument("base")
    ap.add_argument("variant")
    ap.add_argument("args", nargs="*")
    a = ap.parse_args()
    _, ref = run(a.base, a.args)
    _, out = run(a.variant, a.args)
    if out != ref:
        sys.exit(f"ab: {a.name}: the outputs differ ({ref[:80]!r} vs {out[:80]!r})")
    bs, vs = [], []
    for _ in range(a.reps):
        b, o1 = run(a.base, a.args)
        v, o2 = run(a.variant, a.args)
        if o1 != ref or o2 != ref:
            sys.exit(f"ab: {a.name}: an output changed between runs")
        bs.append(b)
        vs.append(v)
    ratios = [v / b for b, v in zip(bs, vs)]
    rec = {"name": a.name, "args": a.args, "reps": a.reps, "base_ns": bs, "variant_ns": vs,
           "base_median_ns": statistics.median(bs), "variant_median_ns": statistics.median(vs),
           "ratio_median": statistics.median(ratios),
           "ratio_min": min(ratios), "ratio_max": max(ratios)}
    with open(a.json, "w") as f:
        json.dump(rec, f, indent=1)
    if a.tsv:
        with open(a.tsv, "a") as f:
            f.write(f"{a.tag[0]}\t{a.name}\t{a.tag[1]}\t{rec['ratio_median']:.4f}\t"
                    f"{rec['ratio_min']:.4f}\t{rec['ratio_max']:.4f}\n")
    print(f"  {a.name:<28} base {rec['base_median_ns'] / 1e6:9.1f} ms  variant "
          f"{rec['variant_median_ns'] / 1e6:9.1f} ms  ratio {rec['ratio_median']:.4f} "
          f"[{rec['ratio_min']:.3f}, {rec['ratio_max']:.3f}]")


main()
