#!/bin/sh
# Count the declarations whose guessed hole solutions reach the whole-declaration recheck
# (`checkGuessedDecl`, docs/stages/13-language.md, 13b), and why. The goal is zero.
#
#   scripts/guess-fallback-stats.sh WIZ [DIR|FILE ...]          (default: lib examples tests)
#   scripts/guess-fallback-stats.sh --tests TESTS [SELECTOR ...] (default: every group)
#
# The first form checks each .wiz file with `WIZ check --trace-guess-fallback` (which turns
# the cache off). The second runs the test suite, `TESTS --trace-guess-fallback`, which covers
# the programs written inline in the Lean test groups: each case's process reports, and the
# driver forwards the lines with the case's own file named GROUP#INDEX. (A traced run reads no
# cache, so every case elaborates its imports again: it is slower than a normal run.)
#
# A module seen several times (a library module imported by many files or cases) is counted
# once: lines are deduplicated by module and declaration. Prints the per-declaration lines,
# then counts by reason and in total. Exit status: 0 when no declaration reached the recheck,
# 1 otherwise, 2 on a usage error.
set -u
usage="usage: $0 WIZ [DIR|FILE ...] | $0 --tests TESTS [SELECTOR ...]"
[ $# -ge 1 ] || { echo "$usage" >&2; exit 2; }
tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
touch "$tmp/lines"
if [ "$1" = --tests ]; then
  [ $# -ge 2 ] || { echo "$usage" >&2; exit 2; }
  TESTS=$2; shift 2
  [ -x "$TESTS" ] || { echo "$0: $TESTS is not executable" >&2; exit 2; }
  "$TESTS" --trace-guess-fallback "$@" >"$tmp/out" 2>"$tmp/err"
  status=$?
  grep '^guess-fallback: ' "$tmp/err" >>"$tmp/lines"
  what="test suite run (exit $status; $(tail -n 1 "$tmp/out"))"
else
  WIZ=$1; shift
  [ -x "$WIZ" ] || { echo "$0: $WIZ is not executable" >&2; exit 2; }
  [ $# -ge 1 ] || set -- lib examples tests
  files=0; failed=0
  for f in $(find "$@" -name '*.wiz' -type f | sort); do
    files=$((files + 1))
    "$WIZ" check --trace-guess-fallback "$f" >/dev/null 2>"$tmp/err" || failed=$((failed + 1))
    grep '^guess-fallback: ' "$tmp/err" >>"$tmp/lines"
  done
  what="$files files checked ($failed with errors)"
fi
# one line per module and declaration (the first seen)
awk '!seen[$2" "$3]++' "$tmp/lines" >"$tmp/uniq"
cat "$tmp/uniq"
echo "== by reason (a declaration may have several)"
sed -n 's/.* reasons=//p' "$tmp/uniq" | tr ';' '\n' | sed 's/^ *//; s/ (.*)$//' | grep -v '^$' |
  sort | uniq -c | sort -rn
ran=$(grep -c ' recheck=ran ' "$tmp/uniq")
skipped=$(grep -c ' recheck=skipped ' "$tmp/uniq")
echo "== $what; declarations reaching the fallback: $((ran + skipped)) (recheck ran: $ran, skipped: $skipped)"
[ $((ran + skipped)) -eq 0 ]
