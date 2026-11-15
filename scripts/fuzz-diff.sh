#!/usr/bin/env sh
# Run the deterministic differential fuzzer (Tests/FuzzDiff.lean).
#
#   scripts/fuzz-diff.sh --fast          # the fast PR subset (fixed seed, no Wiz→C)
#   scripts/fuzz-diff.sh --nightly       # today's date as the seed, full pipelines
#   scripts/fuzz-diff.sh --seed N [--terms N] [--programs N] [--no-wiz] [--shrink]
#
# `--nightly` prints the seed it used; replay a finding with
#   .lake/build/bin/tests --fuzz-diff --replay KIND SEED INDEX CHOICE...
# A skipped pipeline (no C toolchain, no Boehm GC) is not a pass.
set -eu

root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$root"

bin=${TESTS_BIN:-.lake/build/bin/tests}
mode=full
seed=
terms=
programs=
wiz=
shrink=
report=
findings=

usage() {
  echo "usage: scripts/fuzz-diff.sh (--fast | --nightly | --seed N) [--terms N] [--programs N] [--no-wiz] [--shrink] [--report FILE] [--findings FILE]" >&2
  exit 2
}

while [ $# -gt 0 ]; do
  case "$1" in
    --fast) mode=fast ;;
    --nightly) mode=nightly ;;
    --seed) shift; seed=${1:?--seed needs a number} ;;
    --terms) shift; terms=${1:?--terms needs a number} ;;
    --programs) shift; programs=${1:?--programs needs a number} ;;
    --no-wiz) wiz=--no-wiz ;;
    --wiz) wiz=--wiz ;;
    --shrink) shrink=--shrink ;;
    --no-shrink) shrink=--no-shrink ;;
    --report) shift; report=${1:?--report needs a path} ;;
    --findings) shift; findings=${1:?--findings needs a path} ;;
    --help|-h) usage ;;
    *) echo "unknown argument: $1" >&2; usage ;;
  esac
  shift
done

case "$mode" in
  fast)
    [ -n "$seed" ] || seed=20261115
    set -- --seed "$seed" --fast
    ;;
  nightly)
    [ -n "$seed" ] || seed=$(date +%Y%m%d)
    set -- --seed "$seed" --terms "${terms:-16}" --programs "${programs:-32}" --wiz --shrink
    ;;
  full)
    [ -n "$seed" ] || usage
    set -- --seed "$seed" --terms "${terms:-8}" --programs "${programs:-16}"
    [ -n "$wiz" ] || wiz=--wiz
    [ -n "$shrink" ] || shrink=--shrink
    ;;
esac

# The explicit options above win; the mode's defaults fill the rest.
if [ -n "$terms" ]; then set -- "$@" --terms "$terms"; fi
if [ -n "$programs" ]; then set -- "$@" --programs "$programs"; fi
if [ -n "$wiz" ]; then set -- "$@" "$wiz"; fi
if [ -n "$shrink" ]; then set -- "$@" "$shrink"; fi
if [ -n "$report" ]; then set -- "$@" --report "$report"; fi
if [ -n "$findings" ]; then set -- "$@" --findings "$findings"; fi

# The binary is the driver's, not `lake test`: the campaign prints its seed and counts
# and returns 1 on a finding, which is what CI should see.
echo "$bin --fuzz-diff $*"
exec "$bin" --fuzz-diff "$@"
