#!/bin/sh
# The adopted consumer's cache operations: Scry.findingsSave (cold write),
# Scry.findingsProbe (warm read) and Scry.findingsQuery (severity hit) on synthetic
# findings with the project corpus's schema, JSON against Quire. One operation per
# process; the rows are built before the timer, and the program times only the cache
# call.
#
#   heavy sh drafts/storage-engine/bench/cache.sh
#
# The live scry/corpus/project measurement is corpus.sh; it needs the vendored C#
# grammar (Scry.NativeLink), which a worktree does not have.
set -eu
root=$(CDPATH= cd -- "$(dirname "$0")/../../.." && pwd)
wiz=${WIZ:-$root/.lake/build/bin/wiz}
out=${BENCH_DIR:-/tmp/quire-cache-bench}
mkdir -p "$out"

. /workspace/wiz-env.sh 2>/dev/null || true
CF="${WIZ_CFLAGS:-}"
LF=${WIZ_LDFLAGS:-}
cd "$root"

bin=$out/cache-bench
if [ -z "${BENCH_SKIP_BUILD:-}" ]; then
  echo "bench: building the cache bench" >&2
  "$wiz" build -I scry/src -I scry/gen --cflags "$CF" --ldflags "$LF" \
    drafts/storage-engine/bench/CacheBench.wiz -o "$bin"
fi

tsv="$out/results.tsv"
: > "$tsv"

run_one() {
  impl=$1; op=$2; n=$3; dir=$4
  t0=$(date +%s%N)
  if ! "$bin" "$impl" "$op" "$n" "$dir" > "$out/out.txt" 2> "$out/err.txt"; then
    echo "bench: $impl $op n=$n failed:" >&2
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
    "$impl" "$op" "$n" "$wall_us" "${inner:-0}" "${rss:-0}" "$rows" >> "$tsv"
  echo "bench: $impl $op n=$n wall=${wall_us}us inner_ns=${inner:-0} rss=${rss:-0}kB rows=${rows:-0} bytes=$size" >&2
}

for backend in json quire; do
  dir="$out/$backend"
  rm -rf "$dir"
  mkdir -p "$dir"
  if [ "$backend" = "quire" ]; then ns="1000 10000 100000"; else ns="1000 10000"; fi
  for n in $ns; do
    for op in write read query; do
      run_one "$backend" "$op" "$n" "$dir"
    done
  done
done

echo
echo "=== project findings index (synthetic corpus schema; inner = Clock.monotonic) ==="
awk -F '\t' '
BEGIN {
  printf "%-6s %-6s %7s | %10s %9s %7s | %8s\n", "backend", "op", "N", "inner_ns", "wall_us", "rss_kB", "vs json"
  printf "%s\n", "-------------------------------------------------------------------------------"
}
{
  key = $3 SUBSEP $2
  if ($1 == "json") { jt[key] = $5; jw[key] = $4; jr[key] = $6 }
  else { qt[key] = $5; qw[key] = $4; qr[key] = $6; order[++m] = key }
}
END {
  for (i = 1; i <= m; i++) {
    k = order[i]; split(k, p, SUBSEP); n = p[1]; op = p[2]
    printf "%-6s %-6s %7d | %10d %9d %7d | %7s\n", "json", op, n, jt[k], jw[k], jr[k], "-"
    sp = (qt[k] > 0 && jt[k] > 0) ? jt[k] / qt[k] : 0
    printf "%-6s %-6s %7d | %10d %9d %7d | %6.2fx\n", "quire", op, n, qt[k], qw[k], qr[k], sp
  }
}' "$tsv"
