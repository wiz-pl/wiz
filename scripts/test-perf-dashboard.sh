#!/bin/sh
# A small end-to-end check of scripts/perf-dashboard.py: the perf-history format, CI
# test-timings.jsonl ingestion (group medians, trends, slowest cases) and the
# self-contained --html output. No network, no toolchain, under a second.
#
#   scripts/test-perf-dashboard.sh
#
# The fixtures are in scripts/fixtures/perf/ (two CI runs with a trend and one failing
# case; a small perf-history.tsv with two measurement windows).
set -eu
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo=$(CDPATH= cd -- "$here/.." && pwd)
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

dash=$here/perf-dashboard.py
fx=$here/fixtures/perf

# --- everything: history + both CI runs (a directory is searched for *.jsonl)
python3 "$dash" --history "$fx/history.tsv" --timings "$fx" --repo "$repo" --html "$tmp/all.html"
test -s "$tmp/all.html"

for needle in \
  'CI test timings' \
  'median (runs)' \
  'The 6 slowest cases' \
  'grail-commands' \
  'examples/tour/00-hello.wiz' \
  'class="spark"' \
  'Latest window' \
  'Benchmarks across commits'
do
  grep -q -- "$needle" "$tmp/all.html" || { echo "missing from the page: $needle" >&2; exit 1; }
done
# a failed case is counted, not timed: grail-commands' "an edit reruns" failed in run 2
grep -q '1 failed' "$tmp/all.html" || { echo "the failed case is not reported" >&2; exit 1; }
# the page is self-contained: no external script, stylesheet, image or font
if grep -Eq '(src|href)="?(https?:)?//' "$tmp/all.html"; then
  echo "the page loads something from the network" >&2
  exit 1
fi

# --- --out still works, and without --timings the CI section is absent
python3 "$dash" --history "$fx/history.tsv" --repo "$repo" --out "$tmp/plain.html"
test -s "$tmp/plain.html"
grep -q 'Benchmarks across commits' "$tmp/plain.html"
if grep -q 'CI test timings' "$tmp/plain.html"; then
  echo "the CI section is rendered without --timings" >&2
  exit 1
fi

# --- one timing file with --commit/--at overrides (a run whose file says nothing)
python3 "$dash" --history "$fx/history.tsv" \
  --timings "$fx/ci-2026-11-12.jsonl" --commit deadbeef --at 2026-11-12T10:00:00Z \
  --repo "$repo" --html "$tmp/one.html"
grep -q 'deadbeef' "$tmp/one.html"

echo "perf-dashboard: ok ($(wc -c < "$tmp/all.html") bytes with --timings, $(wc -c < "$tmp/plain.html") without)"
