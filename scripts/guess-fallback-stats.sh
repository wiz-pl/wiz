#!/bin/sh
# Count the declarations whose guessed hole solutions reach the whole-declaration recheck
# (`checkGuessedDecl`, docs/stages/13-language.md, 13b), and why. The goal is zero.
#
#   scripts/guess-fallback-stats.sh WIZ [DIR|FILE ...]     (default: lib examples tests)
#
# WIZ is the `wiz` binary to measure (a worktree's .lake/build/bin/wiz). Each file is
# checked with `--trace-guess-fallback` (which turns the cache off); a module imported by
# several files is counted once (lines are deduplicated by module and declaration).
# Prints the per-declaration lines, then counts by reason and in total.
# Exit status: 0 when no declaration reached the recheck, 1 otherwise, 2 on a usage error.
set -u
[ $# -ge 1 ] || { echo "usage: $0 WIZ [DIR|FILE ...]" >&2; exit 2; }
WIZ=$1; shift
[ -x "$WIZ" ] || { echo "$0: $WIZ is not executable" >&2; exit 2; }
[ $# -ge 1 ] || set -- lib examples tests
tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
files=0; failed=0
for f in $(find "$@" -name '*.wiz' -type f | sort); do
  files=$((files + 1))
  "$WIZ" check --trace-guess-fallback "$f" >/dev/null 2>"$tmp/err" || failed=$((failed + 1))
  grep '^guess-fallback: ' "$tmp/err" >>"$tmp/lines"
done
touch "$tmp/lines"
# one line per module and declaration (the first seen)
awk '!seen[$2" "$3]++' "$tmp/lines" >"$tmp/uniq"
cat "$tmp/uniq"
echo "== by reason (a declaration may have several)"
sed -n 's/.* reasons=//p' "$tmp/uniq" | tr ';' '\n' | sed 's/^ *//; s/ (.*)$//' | grep -v '^$' |
  sort | uniq -c | sort -rn
ran=$(grep -c ' recheck=ran ' "$tmp/uniq")
skipped=$(grep -c ' recheck=skipped ' "$tmp/uniq")
echo "== $files files checked ($failed with errors); declarations reaching the fallback: $((ran + skipped)) (recheck ran: $ran, skipped: $skipped)"
[ $((ran + skipped)) -eq 0 ]
