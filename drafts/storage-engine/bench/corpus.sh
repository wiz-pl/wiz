#!/bin/sh
# The project findings index on the real corpus: JSON against Quire, one operation per
# process (cold write, warm read, index hit). The rows come from an actual
# `scry/corpus/project/taint` analysis; only the cache operation is timed.
#
#   heavy sh drafts/storage-engine/bench/corpus.sh
#
# Timing is the program's own `Clock.monotonic` around the operation (`inner_ns`), plus
# the harness's wall clock (which includes start-up and the project analysis) and VmHWM
# from /proc/self/status. (/usr/bin/time is not installed on the nodes.) The analysis is
# repeated in each process so the rows are real; it is outside the timed region.
set -eu
root=$(CDPATH= cd -- "$(dirname "$0")/../../.." && pwd)
wiz=${WIZ:-$root/.lake/build/bin/wiz}
out=${BENCH_DIR:-/tmp/quire-corpus-bench}
cc=${WIZ_CC:-cc}
mkdir -p "$out"

. /workspace/wiz-env.sh 2>/dev/null || true
CF="${WIZ_CFLAGS:-}"
LF=${WIZ_LDFLAGS:-}
cd "$root"

bin=$out/corpus-bench
if [ -z "${BENCH_SKIP_BUILD:-}" ]; then
  echo "bench: building the corpus bench" >&2
  "$wiz" build -I scry/src -I scry/gen --cflags "$CF" --ldflags "$LF" \
    drafts/storage-engine/bench/CorpusBench.wiz -o "$bin"
fi

tsv="$out/results.tsv"
: > "$tsv"

for backend in json quire; do
  dir="$out/$backend"
  rm -rf "$dir"
  mkdir -p "$dir"
  for op in write read query; do
    t0=$(date +%s%N)
    if ! "$bin" "$backend" "$op" "$cc" "$dir" > "$out/out.txt" 2> "$out/err.txt"; then
      echo "bench: $backend $op failed:" >&2
      cat "$out/err.txt" >&2
      exit 1
    fi
    t1=$(date +%s%N)
    wall_us=$(( (t1 - t0) / 1000 ))
    inner=$(awk '$1 == "time_ns" { print $2 }' "$out/out.txt" | head -1)
    rss=$(awk '$1 == "rss_kb" { print $2 }' "$out/out.txt" | head -1)
    rows=$(awk '$1 == "rows" { print $2 }' "$out/out.txt" | head -1)
    size=$(find "$dir" -type f -printf '%s\n' 2>/dev/null | awk '{s+=$1} END {print s+0}')
    printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
      "$backend" "$op" "$wall_us" "${inner:-0}" "${rss:-0}" "${rows:-0}" "${size:-0}" >> "$tsv"
    echo "bench: $backend $op wall=${wall_us}us inner_ns=${inner:-0} rss=${rss:-0}kB rows=${rows:-0} size=${size:-0}B" >&2
  done
done

echo
echo "=== project findings index (scry/corpus/project/taint; inner = Clock.monotonic) ==="
awk -F '\t' '
BEGIN {
  printf "%-6s %-6s | %10s %9s %7s %9s | %8s\n", "backend", "op", "inner_ns", "wall_us", "rss_kB", "bytes", "vs json"
  printf "%s\n", "------------------------------------------------------------------------------"
}
{
  key = $2
  if ($1 == "json") { jt[key] = $4; jw[key] = $3; jr[key] = $5; js[key] = $7; seen[key] = 1 }
  else { qt[key] = $4; qw[key] = $3; qr[key] = $5; qs[key] = $7; order[++m] = key }
}
END {
  for (i = 1; i <= m; i++) {
    k = order[i]
    printf "%-6s %-6s | %10d %9d %7d %9d | %7s\n", "json", k, jt[k], jw[k], jr[k], js[k], "-"
    sp = (qt[k] > 0 && jt[k] > 0) ? jt[k] / qt[k] : 0
    printf "%-6s %-6s | %10d %9d %7d %9d | %6.2fx\n", "quire", k, qt[k], qw[k], qr[k], qs[k], sp
  }
}' "$tsv"
