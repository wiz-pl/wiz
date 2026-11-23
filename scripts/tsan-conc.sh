#!/usr/bin/env bash
# ThreadSanitizer over the concurrency programs (docs/stages/25-concurrency.md, 25a).
#
#   scripts/tsan-conc.sh
#
# Builds each `Tests/tsan/*.wiz` program with the C backend and
# `--cflags "-O1 -g -fsanitize=thread"`, runs it, and checks its output.  A data race
# makes ThreadSanitizer exit 66 and print a report, so a program that prints its
# expected output and exits 0 is evidence that what it exercises (the lock, the MVar
# and channel handshakes, concurrent process spawns) is free of data races.
#
# The compiler is `.lake/build/bin/wiz` (build it with `lake build wiz tests` first),
# or `$WIZ_BIN`.  `$TSAN_CFLAGS` overrides the sanitiser flags.  Run it through `heavy`:
#   heavy --mem 4G scripts/tsan-conc.sh
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
wiz=${WIZ_BIN:-$root/.lake/build/bin/wiz}
cflags=${TSAN_CFLAGS:-"-O1 -g -fsanitize=thread"}

if [ ! -x "$wiz" ]; then
  echo "tsan-conc: no compiler at $wiz (build it with 'lake build wiz tests', or set WIZ_BIN)" >&2
  exit 2
fi

tmp=$(mktemp -d "${TMPDIR:-/tmp}/wiz-tsan-conc.XXXXXX")
trap 'rm -rf "$tmp"' EXIT

# ThreadSanitizer's shadow memory for the runtime's 1 GiB main stack and 256 MB thread
# stacks is unmapped until used, but keep the run small: the concurrency under test is
# the lock, not the stack.
export WIZ_STACK_MB=${WIZ_STACK_MB:-64}
export WIZ_THREAD_STACK_MB=${WIZ_THREAD_STACK_MB:-16}
export TSAN_OPTIONS=${TSAN_OPTIONS:-halt_on_error=1:exitcode=66:second_deadlock_stack=1}

fail=0
run() { # run NAME WIZ-FILE EXPECTED-OUTPUT
  local name=$1 src=$2 want=$3
  local exe=$tmp/$name
  if ! "$wiz" build "$root/Tests/tsan/$src" -o "$exe" --cflags "$cflags" > "$tmp/$name.build" 2>&1; then
    echo "tsan-conc: FAIL: $name does not build" >&2
    sed 's/^/    /' "$tmp/$name.build" >&2
    fail=1
    return
  fi
  local rc=0
  timeout 180 "$exe" > "$tmp/$name.out" 2> "$tmp/$name.err" || rc=$?
  if [ "$rc" -eq 124 ]; then
    echo "tsan-conc: FAIL: $name did not finish in 180 s" >&2
    fail=1
    return
  fi
  if [ "$rc" -eq 66 ] || grep -q "WARNING: ThreadSanitizer" "$tmp/$name.err"; then
    echo "tsan-conc: FAIL: $name: ThreadSanitizer reported a data race" >&2
    sed -n '1,40p' "$tmp/$name.err" | sed 's/^/    /' >&2
    fail=1
    return
  fi
  if [ "$rc" -ne 0 ]; then
    echo "tsan-conc: FAIL: $name exited $rc" >&2
    sed -n '1,20p' "$tmp/$name.err" | sed 's/^/    /' >&2
    fail=1
    return
  fi
  if [ "$(cat "$tmp/$name.out")" != "$(printf '%s' "$want")" ]; then
    echo "tsan-conc: FAIL: $name printed the wrong output" >&2
    echo "  expected: $(printf '%s' "$want" | tr '\n' '|')" >&2
    echo "  got:      $(tr '\n' '|' < "$tmp/$name.out")" >&2
    fail=1
    return
  fi
  echo "ok: $name (ThreadSanitizer)"
}

# A lock around a plain, non-atomic C counter: 8 threads x 1000 increments.
run lock-sum lock-sum.wiz "counter 8000
overlap 0"
# A second thread must wait for the holder to release (ordering, not elapsed time).
run lock-order lock-order.wiz "holder in
second wants
holder checks
holder out
second in
overlap 0
second got it"
# Four threads spawn processes at once: the one-shot SIGPIPE-ignore is done once.
run spawn spawn.wiz "spawned 20"

if [ "$fail" -ne 0 ]; then
  echo "tsan-conc: FAILED" >&2
  exit 1
fi
echo "tsan-conc: all checks passed"
