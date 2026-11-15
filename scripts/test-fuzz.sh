#!/usr/bin/env bash
# The C runtime under libFuzzer: constructors and fields, reference counting,
# strings/Bytes/Array/StringMap, words and numbers, and finalizers.
#
# Four harnesses (runtime/fuzz/fuzz_*.c) share the runtime built as an object
# (`-DWIZ_API=`) and are compiled with Clang's libFuzzer together with ASAN and
# UBSAN (every UBSAN error is fatal). Each run starts from a generated seed
# corpus (scripts/gen-fuzz-seeds.py): the existing programs in runtime/corpus/
# plus one short seed per operation. The default is a bounded smoke run
# (`-runs`, a few thousand inputs per harness); `--max-total-time` runs for a
# time budget instead. Every root is dropped by the harness, which also checks
# the runtime's live-object count, so a leak is an input failure rather than
# only a process-exit report.
#
# A crash is deduplicated by content hash and a `crash-*` unit is minimised with
# libFuzzer's `-minimize_crash=1`. The temporary directory (seed corpus, logs,
# deduplicated and minimised units) is kept when a run fails, so the units can
# be reproduced; `--keep` keeps it even on success.
#
# A Clang without libFuzzer, or a machine that cannot run ASAN/UBSAN, is a clean
# skip: the probe fails and the script prints a `skip:` line and exits 3 (the
# CI job reports that as a warning, not a failure). Exit status: 0 pass, 1 a
# failing harness, 2 usage error, 3 no fuzzer/sanitizer available.
#
# Usage: scripts/test-fuzz.sh [options]
#   --runs N             inputs per harness (default 5000; the smoke corpus)
#   --max-total-time S   run each harness for at most S seconds instead
#   --target NAME        values, data, words or finalizers (repeatable)
#   --cc CC              the compiler (default $CC, else clang)
#   --seed N             libFuzzer's random seed
#   --list               the harnesses and their seed programs, then exit
#   --keep               keep the temporary build/crash directory
#
# It reads WIZ_CFLAGS, WIZ_LDFLAGS and WIZ_LIBS like scripts/test-sanitizers.sh.
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
fuzz=$root/runtime/fuzz

cc=${CC:-clang}
cflags=${WIZ_CFLAGS:-}
ldflags=${WIZ_LDFLAGS:-}
libs=${WIZ_LIBS:--lgmp -lpthread}
runs=5000
max_time=
seed=
keep=0
targets=()
all_targets=(values data words finalizers)
while (($#)); do
  case $1 in
  --runs)
    (($# >= 2)) || { echo "test-fuzz: --runs needs a number" >&2; exit 2; }
    runs=$2; shift 2 ;;
  --max-total-time)
    (($# >= 2)) || { echo "test-fuzz: --max-total-time needs seconds" >&2; exit 2; }
    max_time=$2; shift 2 ;;
  --target)
    (($# >= 2)) || { echo "test-fuzz: --target needs a name" >&2; exit 2; }
    case $2 in
    values|data|words|finalizers) targets+=("$2") ;;
    *) echo "test-fuzz: unknown target '$2' (values, data, words, finalizers)" >&2; exit 2 ;;
    esac
    shift 2 ;;
  --cc) (($# >= 2)) || { echo "test-fuzz: --cc needs a compiler" >&2; exit 2; }; cc=$2; shift 2 ;;
  --seed) (($# >= 2)) || { echo "test-fuzz: --seed needs a number" >&2; exit 2; }; seed=$2; shift 2 ;;
  --list)
    echo "harnesses:"
    for t in "${all_targets[@]}"; do echo "  $t"; done
    echo "seed programs: runtime/corpus/{values,numbers,text,threads}.c"
    exit 0 ;;
  --keep) keep=1; shift ;;
  -h|--help) sed -n '2,/^set -euo/p' "$0" | sed '$d' | sed 's/^# \{0,1\}//'; exit 0 ;;
  *) echo "test-fuzz: unknown argument '$1' (--help)" >&2; exit 2 ;;
  esac
done
((${#targets[@]})) || targets=("${all_targets[@]}")

tmp=$(mktemp -d "${TMPDIR:-/tmp}/wiz-test-fuzz.XXXXXX")
failed=0
cleanup() {
  if ((keep || failed)); then
    echo "test-fuzz: build/crash directory $tmp"
  else
    rm -rf "$tmp"
  fi
}
trap cleanup EXIT

# probe: libFuzzer, ASAN and UBSAN can be built and run here
cat >"$tmp/probe.c" <<'EOF'
#include <stddef.h>
#include <stdint.h>
int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) { (void)data; (void)size; return 0; }
EOF
if ! "$cc" -O1 -g -fsanitize=fuzzer,address,undefined -fno-sanitize-recover=all \
    "$tmp/probe.c" -o "$tmp/probe" >"$tmp/probe-build.log" 2>&1; then
  echo "skip: $cc (or libFuzzer) is not available here"
  sed 's/^/      /' "$tmp/probe-build.log" | tail -3
  exit 3
fi
if ! env ASAN_OPTIONS=detect_leaks=1:abort_on_error=1 UBSAN_OPTIONS=halt_on_error=1 \
    "$tmp/probe" -runs=1 >"$tmp/probe-run.log" 2>&1; then
  echo "skip: ASAN/UBSAN cannot run here"
  sed 's/^/      /' "$tmp/probe-run.log" | tail -3
  exit 3
fi

echo "── seeds (runtime/corpus plus one per operation)"
python3 "$root/scripts/gen-fuzz-seeds.py" "$tmp/seeds"

hash_file() {
  if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | cut -d' ' -f1
  elif command -v shasum >/dev/null 2>&1; then shasum -a 256 "$1" | cut -d' ' -f1
  else cksum "$1" | cut -d' ' -f1; fi
}

minimize() { # BIN UNIT OUT
  local bin=$1 unit=$2 out=$3
  local -a t=()
  command -v timeout >/dev/null 2>&1 && t=(timeout 60)
  "${t[@]}" "$bin" -minimize_crash=1 -runs=100000 -max_len=4096 -timeout=15 \
    -rss_limit_mb=2048 -artifact_prefix="$(dirname "$out")/" \
    -exact_artifact_path="$out" "$unit" >/dev/null 2>&1 || true
}

run_target() { # NAME
  local name=$1 src=$fuzz/fuzz_$1.c bin=$tmp/fuzz-$1
  local corpus=$tmp/corpus-$1 artifacts=$tmp/artifacts-$1 log=$tmp/$1.log
  mkdir -p "$corpus" "$artifacts"
  cp "$tmp/seeds/$name"/* "$corpus"/ 2>/dev/null || true
  echo "── $name"
  if ! "$cc" -O1 -g -fno-omit-frame-pointer \
      -fsanitize=fuzzer,address,undefined -fno-sanitize-recover=all \
      -DWIZ_API= -I "$root/runtime" -I "$fuzz" -Wall -Wextra -Wno-unused-function \
      "$fuzz/runtime.c" "$src" -o "$bin" $cflags $ldflags $libs >"$tmp/$name-build.log" 2>&1; then
    echo "  ✗ $name: does not build"
    sed 's/^/      /' "$tmp/$name-build.log" | tail -20
    failed=1
    return
  fi
  local -a args=(-max_len=4096 -timeout=15 -rss_limit_mb=2048 -detect_leaks=1
                 -print_final_stats=1 -artifact_prefix="$artifacts/")
  if [[ -n $max_time ]]; then args+=("-max_total_time=$max_time")
  else args+=("-runs=$runs"); fi
  [[ -n $seed ]] && args+=("-seed=$seed")
  if env ASAN_OPTIONS=detect_leaks=1:abort_on_error=1:strict_string_checks=1 \
      UBSAN_OPTIONS=halt_on_error=1:print_stacktrace=1 \
      "$bin" "${args[@]}" "$corpus" >"$log" 2>&1; then
    echo "  ✓ $name ($(grep -E '^Done [0-9]+ runs' "$log" | tail -1 || echo 'ok'))"
    return
  fi
  failed=1
  echo "  ✗ $name"
  # collect every artifact libFuzzer wrote, deduplicate by content
  local units=("$artifacts"/*)
  if [[ ${#units[@]} -eq 0 || ! -e ${units[0]} ]]; then
    echo "      (no artifact; last lines of the run)"
    sed 's/^/      /' "$log" | tail -25
    return
  fi
  local unique=$tmp/crashes-$name
  mkdir -p "$unique"
  local -A seen=()
  local u
  for u in "${units[@]}"; do
    [[ -e $u ]] || continue
    local h; h=$(hash_file "$u")
    if [[ -z ${seen[$h]:-} ]]; then
      seen[$h]=1
      local base0; base0=$(basename "$u")
      cp "$u" "$unique/${base0%%-*}-$h"
    fi
  done
  for u in "$unique"/*; do
    [[ -e $u ]] || continue
    local base; base=$(basename "$u")
    if [[ $base == crash-* ]]; then
      local out=$unique/min-$base
      minimize "$bin" "$u" "$out"
      if [[ -s $out ]]; then
        echo "      crash $base ($(wc -c <"$u") bytes) -> $(basename "$out") ($(wc -c <"$out") bytes)"
      else
        echo "      crash $base ($(wc -c <"$u") bytes)"
      fi
    else
      echo "      artifact $base ($(wc -c <"$u") bytes)"
    fi
  done
  # the deduplicated units are the ones to reproduce
  echo "      units: $unique"
}

for t in "${targets[@]}"; do run_target "$t"; done

echo
if ((failed)); then
  echo "test-fuzz: FAIL"
  exit 1
fi
echo "test-fuzz: all harnesses passed"
