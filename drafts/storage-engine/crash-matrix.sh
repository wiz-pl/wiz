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
# The runtime under test is the train7 binary, not whatever `WIZ` the job
# environment happens to export.  The binary reads its standard library from
# the worktree it lives in, so use a copy inside this worktree: the train7
# worktree itself may have moved on, and its lib is not the base this branch
# was cut from.  A copy is byte-for-byte the same compiler/runtime.  Override
# deliberately with QUIRE_WIZ.
train7_wiz=/workspace/wt/train7/.lake/build/bin/wiz
wiz=${QUIRE_WIZ:-$root/.lake/build/bin/wiz}
if [ -z "${QUIRE_WIZ:-}" ] && [ ! -x "$wiz" ]; then
  if [ ! -x "$train7_wiz" ]; then
    echo "crash-matrix: $train7_wiz is missing" >&2; exit 2
  fi
  mkdir -p "$root/.lake/build/bin"
  cp "$train7_wiz" "$wiz" || {
    echo "crash-matrix: could not copy the train7 wiz to $wiz" >&2; exit 2; }
fi

# The wiz build needs a C compiler and GMP.  The batch nodes do not share the
# controller's /nix/store paths, so discover both on the node this job got.
# Override with CC_DIR, GMP_DEV, GMP_LIB if needed.
probe_cc() {
  if command -v timeout >/dev/null 2>&1; then
    timeout 15 "$1" --version >/dev/null 2>&1
  else
    "$1" --version >/dev/null 2>&1
  fi
}

if [ -n "${CC_DIR:-}" ] && [ -x "$CC_DIR/cc" ]; then
  PATH=$CC_DIR:$PATH
elif ! command -v cc >/dev/null 2>&1 || ! probe_cc "$(command -v cc)"; then
  # The /nix/store also holds cross wrappers whose cc hangs on some nodes, so
  # probe each candidate instead of taking the first.
  for d in /nix/store/*-gcc-wrapper-*/bin; do
    if [ -x "$d/cc" ] && probe_cc "$d/cc"; then PATH=$d:$PATH; break; fi
  done
fi
if ! command -v cc >/dev/null 2>&1; then
  echo "crash-matrix: no working C compiler (set CC_DIR)" >&2; exit 2
fi

gmp_dev=${GMP_DEV:-}
gmp_lib=${GMP_LIB:-}
if [ -z "$gmp_dev" ]; then
  for d in /nix/store/*gmp*/include; do
    if [ -f "$d/gmp.h" ]; then gmp_dev=${d%/include}; break; fi
  done
fi
libdirs=""
if [ -n "$gmp_lib" ] && [ -f "$gmp_lib/lib/libgmp.so.10" ]; then
  libdirs="$gmp_lib/lib"
else
  for f in /nix/store/*gmp*/lib/libgmp.so.10; do
    if [ -f "$f" ]; then libdirs="$libdirs ${f%/libgmp.so.10}"; fi
  done
fi
if [ -z "$gmp_dev" ] || [ ! -f "$gmp_dev/include/gmp.h" ] || [ -z "$libdirs" ]; then
  echo "crash-matrix: GMP dev/lib not found on $(hostname) (set GMP_DEV and GMP_LIB)" >&2
  exit 2
fi
export CPATH="$gmp_dev/include${CPATH:+:$CPATH}"
for d in $libdirs; do
  LIBRARY_PATH="$d${LIBRARY_PATH:+:$LIBRARY_PATH}"
  LD_LIBRARY_PATH="$d${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
done
export LIBRARY_PATH LD_LIBRARY_PATH

# The train7 binary is the runtime under test.  If this node's store cannot run
# it, say so and fall back to the node's wiz rather than failing at the first
# check with a less obvious error.
if ! "$wiz" --version >/dev/null 2>&1; then
  if command -v wiz >/dev/null 2>&1; then
    echo "crash-matrix: $(hostname) cannot run $wiz; using $(command -v wiz)" >&2
    wiz=$(command -v wiz)
  else
    echo "crash-matrix: the train7 wiz does not run on $(hostname) and no wiz is on PATH" >&2
    exit 2
  fi
fi

echo "crash-matrix: wiz=$wiz"
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
