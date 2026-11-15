#!/bin/sh
# A git merge driver for the trust ledger (.github/trust-baseline.tsv).
#
# The ledger is a set of rows keyed by `module<TAB>declaration<TAB>item`, so two
# branches that review different declarations have no textual conflict even when
# their rows are adjacent. This driver merges by that key:
#
#   * the result is the union of the rows of ours and theirs; a row deleted on one
#     side stays unless both sides deleted it;
#   * header/comment lines are kept once, in base order followed by any new comments;
#   * rows are sorted by key (byte order, the order `--update` writes);
#   * when both sides have a key with different contents, the row whose reason is
#     not the migration marker (`legacy:`) wins;
#   * if both rows are reasoned and differ, or both are still legacy and differ, the
#     merge is ambiguous: exit 1, list the keys, and leave ours untouched for a human
#     to resolve.
#
# Git invokes a merge driver as `DRIVER %O %A %B`: base, ours, theirs. `%A` is the
# working-tree copy and receives the result. Install the driver in a checkout with
# `scripts/setup-trust-merge.sh`; `.gitattributes` names it `trust-ledger`.
#
# The driver must still be followed by `scripts/trust-ledger.sh --check`: CI cannot
# install a local git driver, so a merge made without this one can leave a ledger
# that is textually merged but stale or duplicate.
#
# Test it with `scripts/trust-ledger-merge_test.sh`.
set -eu

if [ "$#" -ne 3 ]; then
  echo "usage: $0 BASE OURS THEIRS  (git merge driver: %O %A %B)" >&2
  exit 2
fi

base=$1
ours=$2
theirs=$3

for f in "$base" "$ours" "$theirs"; do
  if [ ! -r "$f" ]; then
    echo "trust-ledger-merge: cannot read $f" >&2
    exit 2
  fi
done

tmp=$(mktemp -d "${TMPDIR:-/tmp}/trust-ledger-merge.XXXXXX") || exit 2
trap 'rm -rf "$tmp"' EXIT HUP INT TERM

# Work from private copies: git gives three distinct temporary paths, and this
# keeps a direct invocation with two equal paths from confusing the three roles.
cp "$base" "$tmp/base"
cp "$ours" "$tmp/ours"
cp "$theirs" "$tmp/theirs"
: > "$tmp/comments"
: > "$tmp/rows"

# Every row of ours and theirs is kept once, under its key. The base contributes
# its header comments; a row is taken from ours or theirs, never from the base.
LC_ALL=C awk \
  -v ofile="$tmp/base" -v afile="$tmp/ours" -v bfile="$tmp/theirs" \
  -v rowfile="$tmp/rows" -v cmtfile="$tmp/comments" \
  -v conffile="$tmp/conflicts" -v errfile="$tmp/errors" '
function fmtkey(k, f) {
  split(k, f, "\t")
  return f[1] " | " f[2] " | " f[3]
}
function reasoned(s, f, n) {
  n = split(s, f, "\t")
  return n >= 4 && f[4] != "" && f[4] !~ /^legacy:/
}
function duplicate(which, key, line) {
  print "trust-ledger-merge: duplicate key in " which ": " fmtkey(key) > errfile
  bad = 1
}
FNR == 1 {
  if (FILENAME == ofile) side = "O"
  else if (FILENAME == afile) side = "A"
  else if (FILENAME == bfile) side = "B"
  else {
    print "trust-ledger-merge: unexpected input file: " FILENAME > errfile
    bad = 1
  }
}
{
  line = $0
  sub(/\r$/, "", line)          # a CRLF checkout merges to LF
  if (line == "") next
  if (substr(line, 1, 1) == "#") {
    if (!(line in seen_comment)) {
      seen_comment[line] = 1
      print line > cmtfile
    }
    next
  }
  n = split(line, f, "\t")
  if (n < 3) {
    print "trust-ledger-merge: " FILENAME ":" FNR ": not a ledger row (need module, declaration, item): " line > errfile
    bad = 1
    next
  }
  key = f[1] "\t" f[2] "\t" f[3]
  if (side == "A") {
    if (key in aline) {
      if (aline[key] != line) duplicate("ours", key, line)
    } else aline[key] = line
    akeys[key] = 1
  } else if (side == "B") {
    if (key in bline) {
      if (bline[key] != line) duplicate("theirs", key, line)
    } else bline[key] = line
    bkeys[key] = 1
  }
}
END {
  if (bad) exit 1
  for (k in akeys) allkeys[k] = 1
  for (k in bkeys) allkeys[k] = 1
  conflicts = 0
  for (k in allkeys) {
    ina = (k in aline)
    inb = (k in bline)
    if (ina && inb) {
      if (aline[k] == bline[k]) {
        result[k] = aline[k]
      } else if (reasoned(aline[k]) && !reasoned(bline[k])) {
        result[k] = aline[k]
      } else if (reasoned(bline[k]) && !reasoned(aline[k])) {
        result[k] = bline[k]
      } else {
        print k > conffile
        conflicts++
      }
    } else if (ina) {
      result[k] = aline[k]
    } else if (inb) {
      result[k] = bline[k]
    }
  }
  if (conflicts) exit 1
  for (k in result) print result[k] > rowfile
}
' "$tmp/base" "$tmp/ours" "$tmp/theirs" || status=$?

if [ -s "$tmp/errors" ]; then
  cat "$tmp/errors" >&2
  exit 1
fi

if [ -s "$tmp/conflicts" ]; then
  echo "trust-ledger-merge: conflicting ledger rows; refusing to choose one." >&2
  echo "  A human must pick a row for each key (module | declaration | item):" >&2
  LC_ALL=C sort "$tmp/conflicts" |
    awk -F'\t' '{ printf "  %s | %s | %s\n", $1, $2, $3 }' >&2
  echo "" >&2
  echo "  Fix .github/trust-baseline.tsv by hand, then run:" >&2
  echo "    scripts/trust-ledger.sh --check" >&2
  exit 1
fi

if [ "${status:-0}" -ne 0 ]; then
  echo "trust-ledger-merge: the merge failed (awk exit $status)" >&2
  exit 1
fi

{
  cat "$tmp/comments"
  LC_ALL=C sort "$tmp/rows"
} > "$tmp/result"

# Only now, with a complete result, replace ours. A conflict leaves %A untouched.
cat "$tmp/result" > "$ours"
