#!/usr/bin/env bash
# Check that .github/libdiff-corpus.txt is exactly the list `=selfhost-libdiff` sweeps:
# every *.wiz under lib/ and scry/, recursively, in `LC_ALL=C` order.
#
# The group does not read this file. It walks the two trees itself
# (Tests/Groups/SelfhostLibDiff.lean, `libDiffFiles`) and splits the result into four
# contiguous parts by index, so what makes the corpus meaningful is that it is total:
# if the list and the walk agree, every file is compared exactly once, and a CI part
# that uploads no record for a file is a missing run, not a shrinking total.
#
# The check fails when
#   * a line in the corpus is not a file on disk (a covered file is absent),
#   * a *.wiz under lib/ or scry/ is not in the corpus (a corpus entry is missing),
#   * a line occurs twice, is not under lib/ or scry/, or the list is out of order.
# Blank lines and lines starting with `#` are the file's own comment and are ignored.
#
# Rule for exclusions: there are none. The sweep compares acceptance, the first error's
# code, span and message, and the declaration count; a file the self-hosted frontend
# cannot parse is a divergence to report, not a reason to drop it. A module that genuinely
# cannot be compared needs a reason next to its removal from this list, not silence.
#
# Usage:
#   scripts/check-libdiff-corpus.sh              check the checkout
#   scripts/check-libdiff-corpus.sh --quiet      print nothing on success
#   scripts/check-libdiff-corpus.sh --self-test  exercise the failure modes on fixtures
#   scripts/check-libdiff-corpus.sh --root DIR --corpus FILE
#                                                 check another tree (used by --self-test)
#
# No compiler, no build, no network: `find`, `sort`, `comm` and `cmp`.
set -uo pipefail

here=$(cd "$(dirname "$0")" && pwd)
self=$here/$(basename "$0")
root=$(cd "$here/.." && pwd)
corpus=$root/.github/libdiff-corpus.txt
quiet=0
self_test=0

usage() {
  awk 'NR > 1 && /^#/ { sub(/^# ?/, ""); print; next } NR > 1 { exit }' "$0"
  cat <<'EOF'

Options:
  --root DIR      the checkout to scan (default: the script's parent)
  --corpus FILE   the list to check (default: DIR/.github/libdiff-corpus.txt)
  --quiet         print nothing when the list is total
  --self-test     run the checker on deliberate fixtures (fast; no checkout needed)
  -h, --help      this text
EOF
}

# check ROOT CORPUS QUIET: print the problems and return 1, or the counts and return 0.
check() {
  local root=$1 corpus=$2 quiet=$3
  local tmp rc=0
  tmp=$(mktemp -d "${TMPDIR:-/tmp}/libdiff-corpus.XXXXXX") || return 2
  # shellcheck disable=SC2064
  trap "rm -rf '$tmp'" RETURN

  if [ ! -f "$corpus" ]; then
    echo "libdiff corpus: no such file: $corpus" >&2
    return 1
  fi
  if [ ! -d "$root/lib" ] || [ ! -d "$root/scry" ]; then
    echo "libdiff corpus: $root has no lib/ and scry/ to scan" >&2
    return 1
  fi

  # The list as written (blank lines and comments removed), and its canonical form.
  awk 'NF && $1 !~ /^#/' "$corpus" > "$tmp/list"
  LC_ALL=C sort "$tmp/list" > "$tmp/list.sorted"
  # The tree the group actually walks.
  ( cd "$root" && find lib scry -name '*.wiz' ) | LC_ALL=C sort > "$tmp/disk"

  if ! cmp -s "$tmp/list" "$tmp/list.sorted"; then
    echo "libdiff corpus: entries are not in LC_ALL=C order; first out-of-order line:" >&2
    LC_ALL=C awk 'NR > 1 && $0 < prev { printf "  %s:%d: %s\n    sorts before the previous line: %s\n", FILENAME, NR, $0, prev; exit } { prev = $0 }' \
      "$tmp/list" >&2
    rc=1
  fi

  LC_ALL=C uniq -d "$tmp/list.sorted" > "$tmp/dupes"
  if [ -s "$tmp/dupes" ]; then
    echo "libdiff corpus: entries listed more than once:" >&2
    sed 's/^/  /' "$tmp/dupes" >&2
    rc=1
  fi

  awk '$0 !~ /^(lib|scry)\//' "$tmp/list" > "$tmp/outside"
  if [ -s "$tmp/outside" ]; then
    echo "libdiff corpus: entries outside lib/ and scry/:" >&2
    sed 's/^/  /' "$tmp/outside" >&2
    rc=1
  fi

  # A covered file that is absent (listed, not on disk) and a file the list misses.
  LC_ALL=C comm -23 "$tmp/list.sorted" "$tmp/disk" > "$tmp/absent"
  LC_ALL=C comm -13 "$tmp/list.sorted" "$tmp/disk" > "$tmp/unlisted"
  local absent unlisted
  absent=$(wc -l < "$tmp/absent")
  unlisted=$(wc -l < "$tmp/unlisted")
  if [ "$absent" -gt 0 ]; then
    echo "libdiff corpus: $absent listed file(s) are not on disk (covered file absent):" >&2
    head -n 50 "$tmp/absent" | sed 's/^/  /' >&2
    [ "$absent" -le 50 ] || echo "  … and $((absent - 50)) more" >&2
    rc=1
  fi
  if [ "$unlisted" -gt 0 ]; then
    echo "libdiff corpus: $unlisted file(s) under lib/ and scry/ are not listed (corpus entry missing):" >&2
    head -n 50 "$tmp/unlisted" | sed 's/^/  /' >&2
    [ "$unlisted" -le 50 ] || echo "  … and $((unlisted - 50)) more" >&2
    rc=1
  fi
  if [ "$rc" -ne 0 ]; then
    echo "libdiff corpus: regenerate with: find lib scry -name '*.wiz' | LC_ALL=C sort" >&2
    return 1
  fi

  [ "$quiet" -eq 1 ] || \
    echo "libdiff corpus: $(wc -l < "$tmp/disk") files, every *.wiz under lib/ and scry/ listed once, in LC_ALL=C order"
  return 0
}

# self_test: fixture trees for every rule, each checked by running this script again.
self_test_run() {
  local name=$1 want=$2 got out
  shift 2
  out=$("$self" --quiet "$@" 2>&1)
  got=$?
  if [ "$got" -eq "$want" ]; then
    printf '  ok    %s (exit %d)\n' "$name" "$got"
    return 0
  fi
  printf '  FAIL  %s: wanted exit %d, got %d\n%s\n' "$name" "$want" "$got" "$out"
  return 1
}

self_test() {
  local d rc=0
  d=$(mktemp -d "${TMPDIR:-/tmp}/libdiff-corpus-test.XXXXXX") || return 2
  # shellcheck disable=SC2064
  trap "rm -rf '$d'" RETURN
  mkdir -p "$d/tree/lib/Sub" "$d/tree/scry/tests"
  : > "$d/tree/lib/A.wiz"
  : > "$d/tree/lib/Sub/B.wiz"
  : > "$d/tree/scry/C.wiz"
  : > "$d/tree/scry/tests/D.wiz"
  printf '# a comment\n\nlib/A.wiz\nlib/Sub/B.wiz\nscry/C.wiz\nscry/tests/D.wiz\n' > "$d/good"

  printf '\n%s\n' "self-test (fixtures under $d/tree):"
  self_test_run "a total list passes" 0 --root "$d/tree" --corpus "$d/good" || rc=1

  # one file the list forgets
  printf '# a comment\nlib/A.wiz\nlib/Sub/B.wiz\nscry/C.wiz\n' > "$d/missing"
  self_test_run "an unlisted file fails" 1 --root "$d/tree" --corpus "$d/missing" || rc=1

  # one entry that names no file
  printf 'lib/A.wiz\nlib/Sub/B.wiz\nscry/C.wiz\nscry/tests/D.wiz\nscry/tests/Gone.wiz\n' > "$d/absent"
  self_test_run "a listed file that is absent fails" 1 --root "$d/tree" --corpus "$d/absent" || rc=1

  # the same file twice
  printf 'lib/A.wiz\nlib/A.wiz\nlib/Sub/B.wiz\nscry/C.wiz\nscry/tests/D.wiz\n' > "$d/dupe"
  self_test_run "a duplicate entry fails" 1 --root "$d/tree" --corpus "$d/dupe" || rc=1

  # order
  printf 'lib/Sub/B.wiz\nlib/A.wiz\nscry/C.wiz\nscry/tests/D.wiz\n' > "$d/unsorted"
  self_test_run "an unsorted list fails" 1 --root "$d/tree" --corpus "$d/unsorted" || rc=1

  # outside the two roots
  printf 'lib/A.wiz\nlib/Sub/B.wiz\nscry/C.wiz\nscry/tests/D.wiz\ndocs/E.wiz\n' > "$d/outside"
  mkdir -p "$d/tree/docs"; : > "$d/tree/docs/E.wiz"
  self_test_run "an entry outside lib/ and scry/ fails" 1 --root "$d/tree" --corpus "$d/outside" || rc=1

  # no corpus at all
  self_test_run "a missing corpus fails" 1 --root "$d/tree" --corpus "$d/nope" || rc=1

  if [ "$rc" -eq 0 ]; then
    echo "self-test: ok"
  else
    echo "self-test: FAILED" >&2
  fi
  return "$rc"
}

while [ $# -gt 0 ]; do
  case $1 in
    --root) [ $# -ge 2 ] || { usage; exit 2; }; root=$2; shift 2 ;;
    --root=*) root=${1#*=}; shift ;;
    --corpus) [ $# -ge 2 ] || { usage; exit 2; }; corpus=$2; shift 2 ;;
    --corpus=*) corpus=${1#*=}; shift ;;
    --quiet) quiet=1; shift ;;
    --self-test) self_test=1; shift ;;
    -h|--help) usage; exit 0 ;;
    *) echo "check-libdiff-corpus: unknown argument $1" >&2; usage >&2; exit 2 ;;
  esac
done

if [ "$self_test" -eq 1 ]; then
  self_test
  exit $?
fi

check "$root" "$corpus" "$quiet"
exit $?
