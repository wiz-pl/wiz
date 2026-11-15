#!/bin/sh
# bench-parse.sh — measure the S1 C parser end to end (`scry parse --stats`).
#
# One run = the `scry` binary reading a file, tree-sitter parsing it through
# native/ts_shim.c, copying the columns into the Wiz model (Scry.CstStore) and
# printing the stats block. That is the whole current path: tree-sitter + shim
# walk + column copy + stats render. It is not a pure tree-sitter benchmark.
#
#   scry/tools/bench-parse.sh [-n RUNS] [-b BIN] [FILE…]
#
# Build first (from scry/, with cc and the worktree's wiz on PATH):
#   ../../.lake/build/bin/grail build scry
#
# No file arguments: the repo's two small C files, plus $SCRY_BENCH_EXTRA (a
# space-separated list, e.g. a big generated file or a SQLite amalgamation).
# External corpora are never hardcoded here; pass them as arguments.
#
# Output: a TSV table on stdout, one row per file:
#   file bytes nodes edges depth errors runs wall_ms rss_kb MB_s knodes_s err_per_knodes
# plus a `__startup__` row (`scry --version`: binary + runtime start, no parse)
# and a `__tiny__` row (a 95-byte C file: the per-invocation floor). Wall time is
# the median of RUNS; peak RSS is the median of the same runs (wait4 ru_maxrss).
# Throughput uses decimal MB (10^6 bytes) and 10^3 nodes.
#
# Deliberately no timing policy: run it under `heavy` for a rough number, or as
# `perf-run` inside an exclusive measurement window for a real one. Do not quote
# its output as a perf claim from a loaded machine (AGENTS.md).
set -eu

runs=3
bin=${SCRY_BENCH_BIN:-}
while [ $# -gt 0 ]; do
  case "$1" in
    -n) runs=$2; shift 2 ;;
    -b) bin=$2; shift 2 ;;
    -h|--help) sed -n '2,26p' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
    --) shift; break ;;
    -*) echo "bench-parse: unknown option $1" >&2; exit 2 ;;
    *) break ;;
  esac
done

root=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)

if [ -z "$bin" ]; then
  bin=$root/scry/.grail/bin/scry
fi
if [ ! -x "$bin" ]; then
  echo "bench-parse: no scry binary at $bin" >&2
  echo "  build it: (cd $root/scry && $root/.lake/build/bin/grail build scry)" >&2
  exit 2
fi
# os.execv needs an absolute path; resolve relative -b values.
case "$bin" in
  /*) ;;
  *) bin=$(CDPATH= cd -- "$(dirname -- "$bin")" && pwd)/$(basename -- "$bin") ;;
esac

# Default corpus: the two tracked C files, then any extra files named by the caller.
files=""
if [ $# -gt 0 ]; then
  for f in "$@"; do files="$files $f"; done
else
  files="$root/c/sockets.c $root/c/proc.c"
  if [ -n "${SCRY_BENCH_EXTRA:-}" ]; then
    for f in $SCRY_BENCH_EXTRA; do files="$files $f"; done
  fi
fi
tiny=$root/scry/fixtures/hello.c   # 95 bytes, a real (valid) C file

tmp=${TMPDIR:-/tmp}/scry-bench.$$
mkdir -p "$tmp"
trap 'rm -rf "$tmp"' EXIT INT TERM

# Run one command; write its stdout to "$tmp/out", its stderr and one metrics
# line (`M <wall_ms> <rss_kb> <exit>`) to "$tmp/met". timing and rusage come from
# os.wait4 on exactly this child (no polling, no /usr/bin/time dependency).
run_once() {
  : > "$tmp/out"
  : > "$tmp/met"
  python3 - "$@" <<'PY' >"$tmp/out" 2>"$tmp/met"
import os, sys, time
cmd = sys.argv[1:]
t0 = time.monotonic()
pid = os.fork()
if pid == 0:
    try:
        os.execv(cmd[0], cmd)
    except OSError:
        os._exit(127)
_, status, ru = os.wait4(pid, 0)
wall_ms = (time.monotonic() - t0) * 1000.0
code = os.waitstatus_to_exitcode(status)
sys.stderr.write("M %.3f %d %d\n" % (wall_ms, ru.ru_maxrss, code))
PY
}

median() { # median of the numbers on stdin
  sort -n | awk '{ a[NR] = $1 } END { if (NR == 0) print ""; else print a[int((NR + 1) / 2)] }'
}

# Measure one command `runs` times; sets med_ms, med_rss, last exit code.
measure() {
  i=0
  : > "$tmp/ms"
  : > "$tmp/rss"
  while [ "$i" -lt "$runs" ]; do
    run_once "$@"
    line=$(grep '^M ' "$tmp/met" | tail -1)
    if [ -z "$line" ]; then
      echo "bench-parse: measurement failed for $*" >&2
      cat "$tmp/met" >&2
      exit 1
    fi
    code=$(printf '%s\n' "$line" | awk '{ print $4 }')
    if [ "$code" -ne 0 ]; then
      echo "bench-parse: $* exited $code" >&2
      cat "$tmp/out" >&2
      exit 1
    fi
    printf '%s\n' "$line" | awk '{ print $2 }' >> "$tmp/ms"
    printf '%s\n' "$line" | awk '{ print $3 }' >> "$tmp/rss"
    i=$((i + 1))
  done
  med_ms=$(median < "$tmp/ms")
  med_rss=$(median < "$tmp/rss")
}

printf 'file\tbytes\tnodes\tedges\tdepth\terrors\truns\twall_ms\trss_kb\tMB_s\tknodes_s\terr_per_knodes\n'

# Fixed overhead: startup only (no file, no parse).
measure "$bin" --version
awk -v f='__startup__' -v ms="$med_ms" -v rss="$med_rss" -v n="$runs" \
  'BEGIN { printf "%s\t0\t0\t0\t0\t0\t%d\t%s\t%s\t-\t-\t-\n", f, n, ms, rss }'

for f in $files; do
  if [ ! -f "$f" ]; then
    echo "bench-parse: no such file: $f" >&2
    exit 2
  fi
  measure "$bin" parse --stats "$f"
  # The stats block is stable; the three runs must agree, else say so.
  bytes=$(awk -F': ' '$1 == "bytes" { print $2 }' "$tmp/out")
  nodes=$(awk -F': ' '$1 == "nodes" { print $2 }' "$tmp/out")
  edges=$(awk -F': ' '$1 == "edges" { print $2 }' "$tmp/out")
  depth=$(awk -F': ' '$1 == "max depth" { print $2 }' "$tmp/out")
  errors=$(awk -F': ' '$1 == "errors" { print $2 }' "$tmp/out")
  awk -v f="$f" -v b="$bytes" -v n="$nodes" -v e="$edges" -v d="$depth" \
      -v r="$errors" -v runs="$runs" -v ms="$med_ms" -v rss="$med_rss" \
      'BEGIN {
         mb = (ms > 0) ? (b / 1e6) / (ms / 1000.0) : 0
         kn = (ms > 0) ? (n / 1e3) / (ms / 1000.0) : 0
         er = (n > 0) ? r * 1000.0 / n : 0
         printf "%s\t%d\t%d\t%d\t%d\t%d\t%d\t%s\t%s\t%.2f\t%.1f\t%.2f\n",
                f, b, n, e, d, r, runs, ms, rss, mb, kn, er
       }'
done

# Per-invocation floor: the smallest real file, so the fixed cost is visible
# next to the big files (a 1 KB file is nearly all startup).
if [ -f "$tiny" ]; then
  measure "$bin" parse --stats "$tiny"
  bytes=$(awk -F': ' '$1 == "bytes" { print $2 }' "$tmp/out")
  nodes=$(awk -F': ' '$1 == "nodes" { print $2 }' "$tmp/out")
  edges=$(awk -F': ' '$1 == "edges" { print $2 }' "$tmp/out")
  depth=$(awk -F': ' '$1 == "max depth" { print $2 }' "$tmp/out")
  errors=$(awk -F': ' '$1 == "errors" { print $2 }' "$tmp/out")
  awk -v f='__tiny__' -v b="$bytes" -v n="$nodes" -v e="$edges" -v d="$depth" \
      -v r="$errors" -v runs="$runs" -v ms="$med_ms" -v rss="$med_rss" \
      'BEGIN {
         mb = (ms > 0) ? (b / 1e6) / (ms / 1000.0) : 0
         kn = (ms > 0) ? (n / 1e3) / (ms / 1000.0) : 0
         er = (n > 0) ? r * 1000.0 / n : 0
         printf "%s\t%d\t%d\t%d\t%d\t%d\t%d\t%s\t%s\t%.2f\t%.1f\t%.2f\n",
                f, b, n, e, d, r, runs, ms, rss, mb, kn, er
       }'
fi
