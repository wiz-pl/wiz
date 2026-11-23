#!/bin/sh
# The findings-store benchmark: JSON (lib/Json + whole-file write/read) against Quire
# (the page-backed store). One run per (side, operation, N); the table is printed at the
# end.
#
# Run it as one heavy job (all measurements on one node, sequentially):
#   heavy sh drafts/storage-engine/bench/run.sh
#
# Timing is the harness's own: the shell brackets each process with `date +%s%N` (wall,
# including start-up) and the program prints its own `Clock.monotonic` time around the
# operation. Peak RSS is the process's `VmHWM` from /proc/self/status; file size is
# `stat -c %s`. (/usr/bin/time is not installed on the nodes.)
set -eu
root=$(CDPATH= cd -- "$(dirname "$0")/../../.." && pwd)
wiz=${WIZ:-$root/.lake/build/bin/wiz}
out=${BENCH_DIR:-/tmp/quire-perf-bench}
ns=${BENCH_NS:-"1000 10000 100000"}
mkdir -p "$out"

. /workspace/wiz-env.sh 2>/dev/null || true
CF="${WIZ_CFLAGS:-} -Idrafts/storage-engine"
LF=${WIZ_LDFLAGS:-}
cd "$root"

bidir=${BENCH_BIN_DIR:-$out}
if [ -z "${BENCH_SKIP_BUILD:-}" ]; then
  bidir=$out
  echo "bench: building the three programs" >&2
  "$wiz" build -I drafts/storage-engine --cflags "$CF" --ldflags "$LF" \
    drafts/storage-engine/bench/QuireBench.wiz -o "$bidir/quire-bench"
  "$wiz" build -I drafts/storage-engine --cflags "$CF" --ldflags "$LF" \
    drafts/storage-engine/bench/JsonBench.wiz -o "$bidir/json-bench"
  "$wiz" build -I drafts/storage-engine --cflags "$CF" --ldflags "$LF" \
    drafts/storage-engine/bench/BeforeBench.wiz -o "$bidir/before-bench"
fi

tsv="$out/results.tsv"
: > "$tsv"

# run_one IMPL OP N BIN PATH [COPY]
run_one() {
  impl=$1; op=$2; n=$3; prog=$4; path=$5; copy=${6:-}
  if [ "$copy" = "keep" ]; then
    :
  elif [ -n "$copy" ]; then
    cp "$copy" "$path"
  else
    rm -f "$path"
  fi
  t0=$(date +%s%N)
  if ! "$prog" "$op" "$n" "$path" > "$out/out.txt" 2> "$out/err.txt"; then
    echo "bench: $impl $op $n failed:" >&2
    cat "$out/err.txt" >&2
    exit 1
  fi
  t1=$(date +%s%N)
  wall_us=$(( (t1 - t0) / 1000 ))
  inner=$(awk '$1 == "time_ns" { print $2 }' "$out/out.txt" | head -1)
  rss=$(awk '$1 == "rss_kb" { print $2 }' "$out/out.txt" | head -1)
  cost=$(awk '$1 == "cost" { $1 = ""; print }' "$out/out.txt" | head -1)
  size=$(stat -c %s "$path" 2>/dev/null || echo 0)
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$impl" "$op" "$n" "$wall_us" "${inner:-0}" "${rss:-0}" "$size" "${cost:-}" >> "$tsv"
  echo "bench: $impl $op n=$n wall=${wall_us}us inner_ns=${inner:-0} rss=${rss:-0}kB size=${size}B$cost" >&2
}

for n in $ns; do
  J="$out/json-$n.json"
  QB="$out/quire-batch-$n.db"
  QA="$out/quire-append-$n.db"
  JU="$out/json-$n-update.json"
  QU="$out/quire-$n-update.db"

  # build / append
  run_one json  batch  "$n" "$bidir/json-bench"  "$J"
  run_one quire batch  "$n" "$bidir/quire-bench" "$QB"
  run_one quire append "$n" "$bidir/quire-bench" "$QA"

  # reopen (parse the whole file vs open the snapshot)
  run_one json  reopen "$n" "$bidir/json-bench"  "$J" keep
  run_one quire reopen "$n" "$bidir/quire-bench" "$QB" keep
  run_one quire reopen-fast "$n" "$bidir/quire-bench" "$QB" keep

  # query by state (parse+filter vs indexCursor + filterKey)
  run_one json  query  "$n" "$bidir/json-bench"  "$J" keep
  run_one quire query  "$n" "$bidir/quire-bench" "$QB" keep

  # update one record's state (parse/mutate/rewrite vs lens over + commit)
  run_one json  update "$n" "$bidir/json-bench"  "$JU" "$J"
  run_one quire update "$n" "$bidir/quire-bench" "$QU" "$QB"

  # compact the never-reuse append file: the reclamation the design note promises
  run_one quire compact "$n" "$bidir/quire-bench" "$QA" keep
  rm -f "$QA"
done

# The engine Quire replaces: train7's Durable (whole-chain rewrite on every commit).
# Its append is O(n^2) pages, so only the small Ns are feasible.
bns=${BENCH_BEFORE_NS:-1000 10000}
for n in $bns; do
  B="$out/before-$n.db"
  BU="$out/before-$n-update.db"
  run_one before append "$n" "$bidir/before-bench" "$B"
  run_one before reopen "$n" "$bidir/before-bench" "$B" keep
  run_one before query  "$n" "$bidir/before-bench" "$B" keep
  if [ "$n" = "1000" ]; then
    run_one before update "$n" "$bidir/before-bench" "$BU" "$B"
    rm -f "$BU"
  fi
  rm -f "$B"
done

echo
echo "=== results (one heavy job; harness wall time, VmHWM, stat size) ==="
awk -F '\t' '
BEGIN {
  printf "%-6s %-7s | %10s %9s %10s | %10s %9s %10s | %8s\n",
    "N", "op", "json_us", "json_kB", "json_B", "quire_us", "quire_kB", "quire_B", "speedup"
  printf "%s\n", "-----------------------------------------------------------------------------------------------"
}
{
  if ($1 == "before") { key = $3 SUBSEP $2; bt[key]=$4; br[key]=$6; bs[key]=$7; border[++bm]=key; next }
  key = $3 SUBSEP $2
  if ($1 == "json") { jt[key]=$4; jr[key]=$6; js[key]=$7 }
  else { qt[key]=$4; qr[key]=$6; qs[key]=$7; order[++m]=key }
}
END {
  # keep input order of the quire rows (json is run first for each pair)
  for (i = 1; i <= m; i++) {
    k = order[i]; split(k, p, SUBSEP); n = p[1]; op = p[2]
    sp = (qt[k] > 0 && jt[k] > 0) ? jt[k] / qt[k] : 0
    printf "%-6s %-7s | %10d %9d %10d | %10d %9d %10d | %7.2fx\n",
      n, op, jt[k], jr[k], js[k], qt[k], qr[k], qs[k], sp
  }
}' "$tsv"

echo
echo "=== before (train7 Durable: whole-chain commits; small N only) ==="
awk -F '\t' '
BEGIN {
  printf "%-6s %-7s | %10s %9s %10s\n", "N", "op", "before_us", "before_kB", "before_B"
}
$1 == "before" {
  printf "%-6s %-7s | %10d %9d %10d\n", $3, $2, $4, $6, $7
}' "$tsv"

echo
echo "=== operation time (the program's own Clock.monotonic; process start-up excluded) ==="
awk -F '\t' '
BEGIN {
  printf "%-6s %-12s | %11s %9s %10s | %11s %9s %10s | %8s\n",
    "N", "op", "json_ns", "json_kB", "json_B", "quire_ns", "quire_kB", "quire_B", "speedup"
  printf "%s\n", "-----------------------------------------------------------------------------------------------"
}
{
  if ($1 == "before") next
  key = $3 SUBSEP $2
  if ($1 == "json") { jt[key]=$5; jr[key]=$6; js[key]=$7 }
  else { qt[key]=$5; qr[key]=$6; qs[key]=$7; order[++m]=key }
}
END {
  for (i = 1; i <= m; i++) {
    k = order[i]; split(k, p, SUBSEP); n = p[1]; op = p[2]
    sp = (qt[k] > 0 && jt[k] > 0) ? jt[k] / qt[k] : 0
    printf "%-6s %-12s | %11d %9d %10d | %11d %9d %10d | %7.2fx\n",
      n, op, jt[k], jr[k], js[k], qt[k], qr[k], qs[k], sp
  }
}' "$tsv"

echo
echo "=== markdown ==="
awk -F '\t' '
BEGIN {
  print "| N | operation | JSON wall (ms) | JSON peak RSS (MB) | JSON file (KB) | Quire wall (ms) | Quire peak RSS (MB) | Quire file (KB) | speed-up |"
  print "|---:|---|---:|---:|---:|---:|---:|---:|---:|"
}
{
  if ($1 == "before") next
  key = $3 SUBSEP $2
  if ($1 == "json") { jt[key]=$4; jr[key]=$6; js[key]=$7 }
  else { qt[key]=$4; qr[key]=$6; qs[key]=$7; order[++m]=key }
}
END {
  for (i = 1; i <= m; i++) {
    k = order[i]; split(k, p, SUBSEP); n = p[1]; op = p[2]
    sp = (qt[k] > 0 && jt[k] > 0) ? jt[k] / qt[k] : 0
    printf "| %s | %s | %.1f | %.1f | %.1f | %.1f | %.1f | %.1f | %.2fx |\n",
      n, op, jt[k]/1000, jr[k]/1024, js[k]/1024, qt[k]/1000, qr[k]/1024, qs[k]/1024, sp
  }
}' "$tsv"

echo
echo "raw: $tsv"
