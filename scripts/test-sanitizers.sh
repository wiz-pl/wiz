#!/usr/bin/env bash
# The C runtime under the sanitizers, with a small compiled corpus.
#
# Three builds of the runtime and of every corpus program (runtime/corpus/*.c):
#   * AddressSanitizer (-fsanitize=address), with LeakSanitizer's leak check;
#   * UndefinedBehaviorSanitizer (-fsanitize=undefined, errors are fatal);
#   * ThreadSanitizer (-fsanitize=thread).
# The runtime is built the two ways generated code uses it: as an object, with
# WIZ_API= (the LLVM backend's ABI), and inline, with WIZ_API=static (what the C
# backend pastes into a program). Every program is run in both, so a failure in
# either build is found. The corpus checks its own values; this script checks the
# exit status and prints a failing program's output.
#
# A sanitizer the compiler or this machine cannot run is skipped, not failed: the
# probe program below is compiled and run first, and an unavailable sanitizer is
# reported in a `skip:` line (ASAN under a kernel whose address space layout it
# cannot map, TSAN on an architecture without it, a compiler built without it).
# The exit status is 0 when everything that ran passed, 1 on a failure, and 3 when
# no sanitizer was available (the plain build still ran).
#
# Usage: scripts/test-sanitizers.sh [options]
#   --sanitizer NAME   asan, ubsan or tsan; repeatable (default: all three)
#   --plain-only       only the uninstrumented build (a baseline, used before each
#                      sanitizer and available on its own)
#   --cc CC            the C compiler (default: $CC, else cc)
#   --list             the corpus programs and the sanitizer names, then exit
#   --keep             keep the temporary build directory
#
# The toolchain flags are the ones the rest of the tests use: WIZ_CFLAGS and
# WIZ_LDFLAGS (the dev shell writes them to grail.local.wiz; this script reads the
# environment, as scripts/test-runtime.sh does). GMP is linked with `-lgmp`.
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
corpus=$root/runtime/corpus

cc=${CC:-cc}
cflags=${WIZ_CFLAGS:-}
ldflags=${WIZ_LDFLAGS:-}
libs=${WIZ_LIBS:--lgmp -lpthread}
keep=0
plain_only=0
sanitizers=()
while (($#)); do
  case $1 in
  --sanitizer)
    (($# >= 2)) || { echo "test-sanitizers: --sanitizer needs a name" >&2; exit 2; }
    case $2 in
    asan|ubsan|tsan) sanitizers+=("$2") ;;
    all) sanitizers=(asan ubsan tsan) ;;
    *) echo "test-sanitizers: unknown sanitizer '$2' (asan, ubsan, tsan, all)" >&2; exit 2 ;;
    esac
    shift 2 ;;
  --plain-only) plain_only=1; shift ;;
  --cc) (($# >= 2)) || { echo "test-sanitizers: --cc needs a compiler" >&2; exit 2; }; cc=$2; shift 2 ;;
  --list)
    echo "programs:"
    for src in "$corpus"/*.c; do echo "  $(basename "$src" .c)"; done
    echo "sanitizers: asan ubsan tsan"
    exit 0 ;;
  --keep) keep=1; shift ;;
  -h|--help) sed -n '2,/^set -euo/p' "$0" | sed '$d' | sed 's/^# \{0,1\}//'; exit 0 ;;
  *) echo "test-sanitizers: unknown argument '$1' (--help)" >&2; exit 2 ;;
  esac
done
if ((plain_only)); then sanitizers=(); fi
if ((${#sanitizers[@]} == 0)) && ((!plain_only)); then sanitizers=(asan ubsan tsan); fi

tmp=$(mktemp -d "${TMPDIR:-/tmp}/wiz-test-sanitizers.XXXXXX")
cleanup() { if ((keep)); then echo "test-sanitizers: build directory $tmp"; else rm -rf "$tmp"; fi; }
trap cleanup EXIT

cat > "$tmp/runtime.c" <<'EOF'
/* The runtime as one translation unit: the ABI header, then the areas in the order of
   the old runtime/wiz.c. */
#include "wiz_rt.h"
#include "rt_core.inc"
#include "rt_num.inc"
#include "rt_words.inc"
#include "rt_data.inc"
#include "rt_sys.inc"
#include "rt_con.inc"
EOF

# the corpus: one program per file, in a stable order
programs=()
for src in "$corpus"/*.c; do programs+=("$src"); done
((${#programs[@]} > 0)) || { echo "test-sanitizers: no corpus programs in $corpus" >&2; exit 2; }

passed=0
failed=0
skipped_san=0

# build MODE SANFLAG SOURCE OUTPUT
# MODE: object (WIZ_API=, the runtime in its own translation unit) or inline
# (WIZ_API=static, the runtime pasted in). SANFLAG may be plain (no instrumentation).
build() {
  local mode=$1 sanflag=$2 src=$3 exe=$4
  local -a extra=()
  if [[ $sanflag == *address* ]]; then
    extra+=(-fsanitize=address)
  elif [[ $sanflag == *undefined* ]]; then
    extra+=(-fsanitize=undefined -fno-sanitize-recover=all)
  elif [[ $sanflag == *thread* ]]; then
    extra+=(-fsanitize=thread)
  fi
  local -a compile=(-O1 -g -Wall -Wextra -Wno-unused-function "${extra[@]}" -I "$root/runtime" -I "$corpus" $cflags)
  if [[ $mode == object ]]; then
    # the runtime's object build is shared by every corpus program of this sanitizer
    local obj=$tmp/runtime-$sanflag.o
    if [[ ! -e $obj ]]; then
      "$cc" -c "${compile[@]}" -DWIZ_API= -I "$root/runtime" "$tmp/runtime.c" -o "$obj"
    fi
    "$cc" "${compile[@]}" -DWIZ_API= "$src" "$obj" $ldflags $libs -o "$exe"
  else
    "$cc" "${compile[@]}" -DWIZ_API=static -DWIZ_CORPUS_INLINE "$src" $ldflags $libs -o "$exe"
  fi
}

# run_program NAME SANFLAG MODE
run_program() {
  local name=$1 sanflag=$2 mode=$3 src=$corpus/$1.c
  local exe=$tmp/$name-$sanflag-$mode
  local out=$tmp/$name-$sanflag-$mode.out err=$tmp/$name-$sanflag-$mode.err
  local -a envs=("WIZ_STACK_MB=${WIZ_STACK_MB:-16}")
  case $sanflag in
  address) envs+=("ASAN_OPTIONS=detect_leaks=1:abort_on_error=1:strict_string_checks=1") ;;
  undefined) envs+=("UBSAN_OPTIONS=halt_on_error=1:print_stacktrace=1") ;;
  thread) envs+=("TSAN_OPTIONS=halt_on_error=1:second_deadlock_stack=1") ;;
  esac
  if ! build "$mode" "$sanflag" "$src" "$exe" >"$tmp/build.log" 2>&1; then
    echo "  ✗ $name ($mode): does not build"
    sed 's/^/      /' "$tmp/build.log" | tail -20
    return 1
  fi
  if ! env "${envs[@]}" "$exe" >"$out" 2>"$err"; then
    echo "  ✗ $name ($mode)"
    if [[ -s $err ]]; then sed 's/^/      /' "$err" | head -40; fi
    if [[ -s $out ]]; then sed 's/^/      /' "$out" | head -20; fi
    return 1
  fi
  echo "  ✓ $name ($mode)"
}

# probe SANFLAG: whether this compiler and machine can build and run it, quietly
probe() {
  local sanflag=$1
  local -a extra=()
  case $sanflag in
  address) extra=(-fsanitize=address) ;;
  undefined) extra=(-fsanitize=undefined -fno-sanitize-recover=all) ;;
  thread) extra=(-fsanitize=thread) ;;
  esac
  printf 'int main(void) { return 0; }\n' > "$tmp/probe.c"
  if ! "$cc" -O1 "${extra[@]}" -I "$root/runtime" "$tmp/probe.c" $cflags $ldflags $libs -o "$tmp/probe-$sanflag" \
      >"$tmp/probe.log" 2>&1; then
    return 1
  fi
  case $sanflag in
  address) ASAN_OPTIONS=detect_leaks=1:abort_on_error=1 "$tmp/probe-$sanflag" >>"$tmp/probe.log" 2>&1 ;;
  undefined) UBSAN_OPTIONS=halt_on_error=1 "$tmp/probe-$sanflag" >>"$tmp/probe.log" 2>&1 ;;
  thread) TSAN_OPTIONS=halt_on_error=1 "$tmp/probe-$sanflag" >>"$tmp/probe.log" 2>&1 ;;
  *) "$tmp/probe-$sanflag" >>"$tmp/probe.log" 2>&1 ;;
  esac
}

# run_sanitizer DESCRIPTION SANFLAG
run_sanitizer() {
  local description=$1 sanflag=$2 n=0
  echo "── $description"
  if ! probe "$sanflag"; then
    echo "skip: $description is not available here"
    if [[ -s $tmp/probe.log ]]; then sed 's/^/      /' "$tmp/probe.log" | tail -3; fi
    skipped_san=$((skipped_san + 1))
    return 0
  fi
  local ok=1
  for src in "${programs[@]}"; do
    local name; name=$(basename "$src" .c)
    run_program "$name" "$sanflag" object || ok=0
    run_program "$name" "$sanflag" inline || ok=0
    n=$((n + 2))
  done
  if ((ok)); then
    echo "ok: $description ($n programs)"
    passed=$((passed + 1))
  else
    echo "FAIL: $description"
    failed=$((failed + 1))
  fi
}

# the baseline: the same programs, built and run as usual (no sanitizer)
if ((!plain_only || ${#sanitizers[@]} == 0)); then
  echo "── plain build (baseline)"
  ok=1
  for src in "${programs[@]}"; do
    name=$(basename "$src" .c)
    run_program "$name" plain object || ok=0
    run_program "$name" plain inline || ok=0
  done
  if ((!ok)); then failed=$((failed + 1)); fi
fi

for san in "${sanitizers[@]}"; do
  case $san in
  asan) run_sanitizer "address sanitizer (asan)" address ;;
  ubsan) run_sanitizer "undefined behavior sanitizer (ubsan)" undefined ;;
  tsan) run_sanitizer "thread sanitizer (tsan)" thread ;;
  esac
done

echo
if ((failed)); then
  echo "test-sanitizers: FAIL ($failed build(s) with failures, $passed passed, $skipped_san skipped)"
  exit 1
fi
if ((${#sanitizers[@]} > 0 && skipped_san == ${#sanitizers[@]})); then
  echo "test-sanitizers: every selected sanitizer is unavailable here ($skipped_san skipped)"
  exit 3
fi
echo "test-sanitizers: all checks passed ($passed sanitizer build(s) passed, $skipped_san skipped)"
