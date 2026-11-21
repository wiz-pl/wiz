#!/usr/bin/env bash
# The single-thread cost of thread-safe reference counting in runtime/ (concurrency plan
# R1, item R-d; perf-queue.md "single-thread cost of thread-safe reference counts").
#
# runtime/ counts with a sign bit (stage 25a): rc > 0 is owned by one thread and changed
# with plain arithmetic, rc < 0 is shared and changed atomically, so a program that never
# forks pays a relaxed atomic load and a sign test per inc/dec, a CAS per closed constant,
# and `__thread` for the live counter. Three builds of the same generated C, differing
# only in a define:
#
#   mt      the default: sign-bit counts (what every native program runs today)
#   st      -DWIZ_NO_THREADS: one thread, every count operation plain, constants
#           published without CAS, main on the calling thread (the baseline: what a
#           runtime that knows nothing of threads would cost). `__thread` stays.
#   atomic  -DWIZ_RC_ATOMIC: thread-owned counts atomic too (lock-prefixed inc/dec on
#           every count): the cost of "make every count atomic", the upper bound
#
# The result that matters is mt/st. The plan keeps the sign bit unless it costs more
# than 3% (R-b), and T1 (Task) is gated on "no >5% regression".
#
# Workloads (all built by the Lean `wiz build`, so all run runtime/):
#   stage1   the self-hosted compiler (scripts/GenSelfhost.lean's compiler.wiz) compiling
#            the whole toolchain (self.wiz) to C: ~22 s, ~380 MB each on the perf cores
#            (perf-history.tsv, stage1-selfcompile). Its C output must be byte-identical
#            across the three builds (checked).
#   stdlib   bench/stdlib-bench.wiz, all 20 modes, through scripts/stdlib-bench.py with
#            --baseline-bin mt (interleaved A/B pairs; checksums must agree).
#
# Usage (from the repository root, with the toolchain environment: . /workspace/wiz-env.sh
# or `nix develop`):
#   scripts/rc-cost-bench.sh [--reps N] [--build-only | --measure-only] [OUTDIR]
#     --reps N        stage-1 rounds (each runs the three builds, order rotated; default 3)
#                     and stdlib-bench samples per mode (default 5)
#     --build-only    build and check only (run this under `heavy` before a perf window)
#     --measure-only  only measure builds already in OUTDIR
#     OUTDIR          default .lake/rc-cost
#   PERFRUN=/workspace/wiz-tools/perf-run  wrap every timed command in `perf-run LABEL`
#                   (inside `perf-run --batch` it only measures)
#
# The one heavy command (about 20-25 min: lake build if stale, generation, 6 `wiz build`s
# of which the 3 compiler builds take ~2 min each, 9 stage-1 runs, 2 x 18 x 12 stdlib runs):
#   /workspace/wiz-tools/heavy --mem 6G timeout 1800 scripts/rc-cost-bench.sh
# Peak memory is the Lean `wiz build` of compiler.wiz (~1.3 GB) or the lake build; the
# measured programs stay under 0.5 GB. Numbers from a shared machine are approximate: the
# variants are interleaved, so the ratios are the robust part. For clean numbers, run
# --build-only under heavy, then in a window:
#   PERFRUN=/workspace/wiz-tools/perf-run scripts/rc-cost-bench.sh --measure-only
# Results: OUTDIR/summary.txt (and stage1.tsv, stdlib-st.json, stdlib-atomic.json).
set -euo pipefail

die() { echo "rc-cost-bench: $*" >&2; exit 2; }
reps=3; sreps=5; build=1; measure=1; out=
while [ $# -gt 0 ]; do
  case "$1" in
    --reps) [ $# -ge 2 ] || die "--reps needs a number"; reps=$2; sreps=$2; shift 2 ;;
    --build-only) measure=0; shift ;;
    --measure-only) build=0; shift ;;
    -h|--help) awk 'NR > 1 && /^#/ { sub(/^# ?/, ""); print; next } NR > 1 { exit }' "$0"; exit 0 ;;
    -*) die "unknown option: $1" ;;
    *) [ -z "$out" ] || die "unexpected argument: $1"; out=$1; shift ;;
  esac
done
: "${WIZ_CFLAGS?needs the toolchain environment (. /workspace/wiz-env.sh or nix develop)}"
root=$(cd "$(dirname "$0")/.." && pwd)
cd "$root"
out=${out:-.lake/rc-cost}
mkdir -p "$out/run"
out=$(cd "$out" && pwd)
wiz=$root/.lake/build/bin/wiz
variants="mt st atomic"
vflag() { case $1 in mt) echo "" ;; st) echo "-DWIZ_NO_THREADS" ;; atomic) echo "-DWIZ_RC_ATOMIC" ;; esac; }

# `st` runs main on the calling thread (no 1 GiB thread of its own): give every variant
# the biggest stack the limits allow, so deep recursion behaves the same in all three.
ulimit -s unlimited 2>/dev/null || ulimit -s "$(ulimit -H -s)"

timed() { # timed LABEL CMD… : run, print "wall_s maxrss_kib" (wrapped in perf-run if set)
  local label=$1; shift
  local pre=(); [ -n "${PERFRUN:-}" ] && pre=("$PERFRUN" "$label")
  python3 -c '
import resource, subprocess, sys, time
t = time.monotonic(); rc = subprocess.call(sys.argv[1:]); w = time.monotonic() - t
if rc: sys.exit("rc-cost-bench: %r exited %d" % (sys.argv[1:], rc))
print("%.3f %d" % (w, resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss))' "${pre[@]}" "$@"
}

if [ "$build" = 1 ]; then
  echo "== build ($(date +%T))"
  lake build wiz Tests.Elab 2>&1 | tail -1
  OUT="$out" lake lean scripts/GenSelfhost.lean
  cp "$out/self.wiz" "$out/run/input.wiz"
  for v in $variants; do
    for p in compiler stdlib-bench; do
      src=$out/compiler.wiz; [ "$p" = stdlib-bench ] && src=$root/bench/stdlib-bench.wiz
      echo "wiz build $p-$v $(vflag "$v")"
      "$wiz" build "$src" -o "$out/$p-$v" --cflags "$WIZ_CFLAGS $(vflag "$v")" --ldflags "${WIZ_LDFLAGS:-}"
    done
  done
  # check: the builds really differ (no cached build ignored the define) ...
  for p in compiler stdlib-bench; do
    [ "$(md5sum "$out/$p"-{mt,st,atomic} | cut -d' ' -f1 | sort -u | wc -l)" = 3 ] \
      || die "two builds of $p are identical: was a define ignored?"
  done
  # ... and the three stage-1 compilers emit the same C
  for v in $variants; do (cd "$out/run" && "$out/compiler-$v" > "$out/self1-$v.c"); done
  for v in st atomic; do
    cmp -s "$out/self1-mt.c" "$out/self1-$v.c" || die "stage 1 ($v) emits different C from mt"
  done
  echo "check ok: the three stage-1 builds emit identical C ($(stat -c %s "$out/self1-mt.c") bytes)"
fi

if [ "$measure" = 1 ]; then
  echo "== measure ($(date +%T))"
  for v in $variants; do [ -x "$out/compiler-$v" ] && [ -x "$out/stdlib-bench-$v" ] || die "missing builds in $out (run without --measure-only)"; done
  printf 'round\tvariant\twall_s\tmaxrss_kib\n' > "$out/stage1.tsv"
  set -- $variants
  for r in $(seq "$reps"); do
    for v in "$@"; do
      m=$(cd "$out/run" && timed "rc-cost-stage1-$v" sh -c "exec '$out/compiler-$v' > '$out/self1-$v.out'")
      printf '%s\t%s\t%s\n' "$r" "$v" "${m// /$'\t'}" >> "$out/stage1.tsv"
      echo "stage1 round $r $v: $m"
    done
    set -- "${@:2}" "$1" # rotate the order
  done
  for v in st atomic; do
    sp=(); [ -n "${PERFRUN:-}" ] && sp=("$PERFRUN" "rc-cost-stdlib-$v")
    "${sp[@]}" python3 scripts/stdlib-bench.py --reps "$sreps" --bin "$out/stdlib-bench-$v" \
      --baseline-bin "$out/stdlib-bench-mt" --json "$out/stdlib-$v.json" --quiet
  done
  python3 - "$out" > "$out/summary.txt" <<'PY'
import csv, json, statistics, sys
out = sys.argv[1]
rows = list(csv.DictReader(open(f"{out}/stage1.tsv"), delimiter="\t"))
med = {v: statistics.median(float(r["wall_s"]) for r in rows if r["variant"] == v) for v in ("mt", "st", "atomic")}
print("stage 1 self-compile, median wall (s):", ", ".join(f"{v} {t:.2f}" for v, t in med.items()))
print(f"  mt/st {med['mt'] / med['st']:.4f}  (the sign-bit cost)   atomic/st {med['atomic'] / med['st']:.4f}")
print("  (caveat: st keeps __thread for the live counter, so mt/st measures counts, CAF CAS and")
print("   mark_mt, not the cost of thread-local storage)")
for v in ("st", "atomic"):
    j = json.load(open(f"{out}/stdlib-{v}.json"))
    ab = j["ab"]["results"]
    print(f"stdlib-bench, {v} (B) vs mt (A), median per-pair ratio B/A per mode:")
    for mode, rec in sorted(ab.items()):
        print(f"  {mode:16s} {rec['median_ratio']:.4f}  (min {rec['min_ratio']:.4f}, max {rec['max_ratio']:.4f})")
PY
  cat "$out/summary.txt"
fi
