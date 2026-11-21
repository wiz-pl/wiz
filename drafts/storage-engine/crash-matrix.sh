#!/bin/sh
# Quire's crash matrix: kill -9 at each commit point and at the compaction swap.
#
#   drafts/storage-engine/crash-matrix.sh
#
# The writer is the same `Durable.wiz`/`Compact.wiz` code, built once with the
# train7 compiler.  `crash_shim.so` (LD_PRELOAD) kills it with SIGKILL at the
# checkpoint named by `QUIRE_CRASH`; the checker is then a fresh process.  Every
# row checks the same contract:
#
#   * the last committed generation is readable and its content is intact;
#   * a torn generation is never served as a mixed state (count = gen - 1);
#   * every retained root still loads through the durable loader;
#   * the next commit succeeds, is at the expected generation (the genFloor case
#     skips the torn one), and survives a reopen;
#   * a compaction temp file is ignored (and removed) rather than read.
#
# The matrix is one heavy job; it also runs DurableTest, CompactTest and
# RegistryTest.  Exit status is nonzero if any row or existing test fails.
set -u

root=$(CDPATH= cd -- "$(dirname "$0")/../.." && pwd)
wiz=${WIZ:-/workspace/wt/train7/.lake/build/bin/wiz}

# The wiz build needs a C compiler and GMP; the stock PATH has neither.  These
# are the train7 host's store paths (override with GMP_DEV/GMP_LIB).
gmp_dev=${GMP_DEV:-/nix/store/58cds16cp7zyiywadnfih6x99vd7f9fq-gmp-with-cxx-6.3.0-dev}
gmp_lib=${GMP_LIB:-/nix/store/3z4n8rmy4cfp0km5jaczz7f404j9sa64-gmp-with-cxx-6.3.0}
# Prefer the host x86-64 wrapper the train7 binary was built with, even when a
# `cc` is already on PATH: the /nix/store also contains cross wrappers whose
# `cc` hangs on this host.  Override with CC_DIR.
good_cc=${CC_DIR:-/nix/store/r5ri78axx1qggkjq3vawywlzglg70b5w-gcc-wrapper-16.2.0/bin}
if [ -x "$good_cc/cc" ]; then
  PATH=$good_cc:$PATH
else
  for d in \
    /nix/store/kbw2j1vag664b3sj3rjwz9v53cqx87sb-gcc-wrapper-15.2.0/bin \
    /nix/store/*-gcc-wrapper-16.2.0/bin \
    /nix/store/*-gcc-wrapper-15.2.0/bin; do
    if [ -x "$d/cc" ]; then PATH=$d:$PATH; break; fi
  done
fi
if ! command -v cc >/dev/null 2>&1; then
  echo "crash-matrix: no C compiler on PATH" >&2; exit 2
fi
if [ ! -f "$gmp_dev/include/gmp.h" ] || [ ! -f "$gmp_lib/lib/libgmp.so.10" ]; then
  echo "crash-matrix: GMP dev/lib not found (set GMP_DEV and GMP_LIB)" >&2
  exit 2
fi
export CPATH="$gmp_dev/include${CPATH:+:$CPATH}"
export LIBRARY_PATH="$gmp_lib/lib${LIBRARY_PATH:+:$LIBRARY_PATH}"
export LD_LIBRARY_PATH="$gmp_lib/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"

tmp=$(mktemp -d "${TMPDIR:-/tmp}/quire-crash.XXXXXX")
cleanup() { rm -rf "$tmp"; }
trap cleanup EXIT HUP INT TERM

shim="$tmp/crash_shim.so"
bin="$tmp/crash-harness"
rows="$tmp/rows"
: >"$rows"
fail=0

cc -shared -fPIC -O2 -o "$shim" "$root/drafts/storage-engine/crash_shim.c" -ldl || {
  echo "crash-matrix: the crash shim did not compile" >&2; exit 2; }

cd "$root"
"$wiz" check -I drafts/storage-engine drafts/storage-engine/CrashHarness.wiz || exit 2
"$wiz" build -I drafts/storage-engine drafts/storage-engine/CrashHarness.wiz -o "$bin" || exit 2
echo "crash-matrix: harness $bin"

row() {
  # point | writer | open | next | roots/temp | note
  printf '%-30s | %-8s | %-10s | %-4s | %-14s | %s\n' "$1" "$2" "$3" "$4" "$5" "$6" >>"$rows"
}

field() {
  # field NAME "$line"
  printf '%s\n' "$2" | sed -n "s/.*$1=\([^ ]*\).*/\1/p" | tail -1
}

run_commit_case() {
  cp=$1; eo=$2; en=$3
  d="$tmp/$cp"; mkdir -p "$d"; db="$d/db"
  if ! QUIRE_ROLE=setup-commit QUIRE_DB="$db" "$bin" >"$d/setup.log" 2>&1; then
    row "$cp" "setup" "-" "-" "-" "setup failed (see $d/setup.log)"; fail=$((fail+1)); return
  fi
  QUIRE_ROLE=commit QUIRE_DB="$db" QUIRE_CRASH="$cp" LD_PRELOAD="$shim" \
    "$bin" >"$d/crash.log" 2>&1
  wst=$?
  if [ "$wst" -eq 137 ]; then died="SIGKILL"; else died="exit $wst"; fail=$((fail+1)); fi
  if res=$(QUIRE_ROLE=check-commit QUIRE_DB="$db" \
      QUIRE_EXPECT_OPEN="$eo" QUIRE_EXPECT_NEXT="$en" "$bin" 2>"$d/check.err"); then
    line=$(printf '%s\n' "$res" | grep '^RESULT ' | tail -1)
    og=$(field open_gen "$line"); oc=$(field open_count "$line")
    ng=$(field next_gen "$line"); rt=$(field roots "$line")
    note="ok"
    if [ "$og" != "$eo" ] || [ "$ng" != "$en" ]; then
      note="MISMATCH expected open=$eo next=$en"; fail=$((fail+1))
    fi
    row "$cp" "$died" "$og/$oc" "$ng" "roots=$rt" "$note"
  else
    row "$cp" "$died" "-" "-" "-" "CHECK FAILED (see $d/check.err)"
    fail=$((fail+1))
  fi
}

run_compact_case() {
  cp=$1; eo=$2; en=$3
  d="$tmp/$cp"; mkdir -p "$d"; db="$d/db"
  if ! QUIRE_ROLE=setup-compact QUIRE_DB="$db" "$bin" >"$d/setup.log" 2>&1; then
    row "$cp" "setup" "-" "-" "-" "setup failed (see $d/setup.log)"; fail=$((fail+1)); return
  fi
  QUIRE_ROLE=compact QUIRE_DB="$db" QUIRE_CRASH="$cp" LD_PRELOAD="$shim" \
    "$bin" >"$d/crash.log" 2>&1
  wst=$?
  if [ "$wst" -eq 137 ]; then died="SIGKILL"; else died="exit $wst"; fail=$((fail+1)); fi
  if res=$(QUIRE_ROLE=check-compact QUIRE_DB="$db" \
      QUIRE_EXPECT_OPEN="$eo" QUIRE_EXPECT_NEXT="$en" "$bin" 2>"$d/check.err"); then
    line=$(printf '%s\n' "$res" | grep '^RESULT ' | tail -1)
    og=$(field open_gen "$line"); oc=$(field open_count "$line")
    ng=$(field next_gen "$line"); rt=$(field roots "$line"); tp=$(field temp "$line")
    note="ok"
    if [ "$og" != "$eo" ] || [ "$ng" != "$en" ]; then
      note="MISMATCH expected open=$eo next=$en"; fail=$((fail+1))
    fi
    row "$cp" "$died" "$og/$oc" "$ng" "roots=$rt temp=$tp" "$note"
  else
    row "$cp" "$died" "-" "-" "-" "CHECK FAILED (see $d/check.err)"
    fail=$((fail+1))
  fi
}

# -- Control: no crash (the same code, no shim) --------------------------------
d="$tmp/control-commit"; mkdir -p "$d"; db="$d/db"
QUIRE_ROLE=setup-commit QUIRE_DB="$db" "$bin" >"$d/setup.log" 2>&1
QUIRE_ROLE=commit QUIRE_DB="$db" "$bin" >"$d/commit.log" 2>&1
if res=$(QUIRE_ROLE=check-commit QUIRE_DB="$db" QUIRE_EXPECT_OPEN=3 \
    QUIRE_EXPECT_NEXT=4 "$bin" 2>"$d/check.err"); then
  line=$(printf '%s\n' "$res" | grep '^RESULT ' | tail -1)
  row "control-commit" "none" "$(field open_gen "$line")/$(field open_count "$line")" \
    "$(field next_gen "$line")" "roots=$(field roots "$line")" "ok"
else
  row "control-commit" "none" "-" "-" "-" "CHECK FAILED"; fail=$((fail+1))
fi

d="$tmp/control-compact"; mkdir -p "$d"; db="$d/db"
QUIRE_ROLE=setup-compact QUIRE_DB="$db" "$bin" >"$d/setup.log" 2>&1
QUIRE_ROLE=compact QUIRE_DB="$db" "$bin" >"$d/compact.log" 2>&1
if res=$(QUIRE_ROLE=check-compact QUIRE_DB="$db" QUIRE_EXPECT_OPEN=8 \
    QUIRE_EXPECT_NEXT=9 "$bin" 2>"$d/check.err"); then
  line=$(printf '%s\n' "$res" | grep '^RESULT ' | tail -1)
  row "control-compact" "none" "$(field open_gen "$line")/$(field open_count "$line")" \
    "$(field next_gen "$line")" "roots=$(field roots "$line") temp=$(field temp "$line")" "ok"
else
  row "control-compact" "none" "-" "-" "-" "CHECK FAILED"; fail=$((fail+1))
fi

# A stale temp image beside the old store: open ignores it.
d="$tmp/garbage-temp"; mkdir -p "$d"; db="$d/db"
QUIRE_ROLE=setup-compact QUIRE_DB="$db" "$bin" >"$d/setup.log" 2>&1
printf 'not a store' >"$db.compact"
if res=$(QUIRE_ROLE=check-compact QUIRE_DB="$db" QUIRE_EXPECT_OPEN=8 \
    QUIRE_EXPECT_NEXT=9 "$bin" 2>"$d/check.err"); then
  line=$(printf '%s\n' "$res" | grep '^RESULT ' | tail -1)
  row "garbage-temp" "none" "$(field open_gen "$line")/$(field open_count "$line")" \
    "$(field next_gen "$line")" "roots=$(field roots "$line") temp=$(field temp "$line")" \
    "old file, temp ignored"
else
  row "garbage-temp" "none" "-" "-" "-" "CHECK FAILED"; fail=$((fail+1))
fi

# -- Commit matrix -------------------------------------------------------------
# The baseline is generation 2 (seed + one +1); the victim is generation 3.
# open=2 means the commit point was not reached; open=3 means it was.
run_commit_case before-pages       2 3
run_commit_case during-page        2 3
run_commit_case after-pages        2 3
run_commit_case after-fdatasync    2 3
run_commit_case torn-meta          2 3
run_commit_case after-meta-write   3 4
run_commit_case after-fsync        3 4
# A published meta over a page whose write was short: the chain must fail and
# recovery must fall back, but the genFloor/page_count must not reuse generation 3.
run_commit_case torn-page-published 2 4

# -- Compaction matrix ---------------------------------------------------------
# The baseline is generation 8; a completed compaction keeps it, so open is 8
# whether the path still names the old file or the renamed new one.
run_compact_case compact-during-temp       8 9
run_compact_case compact-torn-temp         8 9
run_compact_case compact-before-temp-fsync 8 9
run_compact_case compact-after-temp-fsync  8 9
run_compact_case compact-before-rename     8 9
run_compact_case compact-after-rename      8 9
run_compact_case compact-after-dir-fsync   8 9

echo
echo "Crash matrix (train7 runtime; writer is SIGKILLed, checker is a fresh process)"
echo "point                          | writer   | open       | next | roots/temp     | note"
echo "-------------------------------+----------+------------+------+----------------+-----"
cat "$rows"

# -- Existing tests ------------------------------------------------------------
echo
if [ "${QUIRE_SKIP_EXISTING:-0}" = 1 ]; then
  echo "existing: skipped (QUIRE_SKIP_EXISTING=1)"
else
for t in DurableTest CompactTest RegistryTest; do
  case "$t" in
    DurableTest) s=test-durable.sh ;;
    CompactTest) s=test-compact.sh ;;
    RegistryTest) s=test-registry.sh ;;
  esac
  if sh "drafts/storage-engine/$s" "$wiz" >"$tmp/$t.log" 2>&1; then
    echo "existing: $t ok"
  else
    echo "existing: $t FAILED (see $tmp/$t.log)"
    tail -20 "$tmp/$t.log"
    fail=$((fail+1))
  fi
done
fi

echo
if [ "$fail" -ne 0 ]; then
  echo "crash-matrix: $fail failure(s)"
  exit 1
fi
echo "crash-matrix: all rows and existing tests passed"
