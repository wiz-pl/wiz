#!/usr/bin/env bash
# Verify that the seed reproduces the fixpoint.
#
#   S0 = cc(seed.c)                         the seed (built here if needed)
#   c1 = T(S0)                              the seed compiles the toolchain
#   B1 = cc(c1)                             stage 1
#   c2 = T(B1)                              stage 1 compiles the toolchain
#
# The check is c1 == c2 == the fixpoint's self1.c (== self2.c).  It is Gate 1 of
# wiz-notes/post-lean-workflow.md §2.5 with S0 in place of the Lean build.
#
#   usage: bootstrap/check-seed.sh [options]
#     --fixpoint DIR     fixpoint output dir, with run/input.wiz (default .lake/fixpoint)
#     --seed-c FILE      the C seed (default bootstrap/seed/seed.c)
#     --seed BIN         use this seed binary instead of building one
#     --out DIR          build/run directory (default bootstrap/seed/check)
#     --cc CMD           C compiler for seed.c and stage 1 (default cc)
#     --cflags FLAGS     C flags (default $SEED_CFLAGS; GC mode needs Boehm)
#     --ldflags FLAGS    link flags (default $SEED_LDFLAGS)
#     --seed-flags FLAGS flags for the seed build (default $SEED_FLAGS, usually -O0)
#     --stage-flags FLAGS flags for the stage-1 build (default $STAGE_FLAGS, -O2)
#     --keep             leave c1.c, c2.c and stage1 in the run directory
#     --help
set -euo pipefail

root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
fixpoint=${FIXPOINT:-$root/.lake/fixpoint}
seed_c=${SEED_C:-$root/bootstrap/seed/seed.c}
seed_bin=""
out=${CHECK_DIR:-$root/bootstrap/seed/check}
cc=${CC:-cc}
cflags=${SEED_CFLAGS:-}
ldflags=${SEED_LDFLAGS:-}
seed_flags=${SEED_FLAGS:-}
stage_flags=${STAGE_FLAGS:--O2}
keep=0

die() { printf 'check-seed: %s\n' "$*" >&2; exit 1; }
usage() { sed -n '2,26p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'; exit 0; }

while [ "$#" -gt 0 ]; do
  case "$1" in
    --fixpoint) [ "$#" -ge 2 ] || die "--fixpoint needs a directory"; fixpoint=$2; shift 2 ;;
    --seed-c)   [ "$#" -ge 2 ] || die "--seed-c needs a file"; seed_c=$2; shift 2 ;;
    --seed)     [ "$#" -ge 2 ] || die "--seed needs a file"; seed_bin=$2; shift 2 ;;
    --out)      [ "$#" -ge 2 ] || die "--out needs a directory"; out=$2; shift 2 ;;
    --cc)       [ "$#" -ge 2 ] || die "--cc needs a command"; cc=$2; shift 2 ;;
    --cflags)   [ "$#" -ge 2 ] || die "--cflags needs a value"; cflags=$2; shift 2 ;;
    --ldflags)  [ "$#" -ge 2 ] || die "--ldflags needs a value"; ldflags=$2; shift 2 ;;
    --seed-flags)  [ "$#" -ge 2 ] || die "--seed-flags needs a value"; seed_flags=$2; shift 2 ;;
    --stage-flags) [ "$#" -ge 2 ] || die "--stage-flags needs a value"; stage_flags=$2; shift 2 ;;
    --keep)     keep=1; shift ;;
    -h|--help)  usage ;;
    *) die "unknown option: $1 (try --help)" ;;
  esac
done

[ -f "$fixpoint/self1.c" ] || die "no self1.c in $fixpoint"
[ -f "$fixpoint/self2.c" ] || die "no self2.c in $fixpoint"
[ -f "$fixpoint/run/input.wiz" ] || die "no $fixpoint/run/input.wiz (the fixpoint's input)"
cmp -s "$fixpoint/self1.c" "$fixpoint/self2.c" || die "$fixpoint is not a fixpoint (self1.c != self2.c)"

mkdir -p "$out"
out=$(cd "$out" && pwd)
if [ -n "$seed_bin" ]; then
  seed_bin=$(cd "$(dirname "$seed_bin")" && pwd)/$(basename "$seed_bin")
fi

if [ -z "$seed_bin" ]; then
  [ -f "$seed_c" ] || die "no seed C at $seed_c (run bootstrap/make-seed.sh first)"
  seed_bin=$out/seed
  printf 'building seed: %s\n' "$seed_bin"
  # shellcheck disable=SC2086
  "$cc" $cflags $seed_flags -I "$root/selfhost" "$seed_c" -o "$seed_bin" $ldflags
fi
[ -x "$seed_bin" ] || die "seed is not executable: $seed_bin"

# The backend mode is a property of the C itself: RC C defines WIZ_RC.
mode=gc
mode_file=$seed_c
[ -f "$mode_file" ] || mode_file=$fixpoint/self1.c
if grep -q '^#define WIZ_RC' "$mode_file" 2>/dev/null; then mode=rc; fi
mode_args=()
[ "$mode" = rc ] && mode_args=(--rc)

rm -rf "$out/run"
mkdir -p "$out/run"
cp "$fixpoint/run/input.wiz" "$out/run/input.wiz"

printf '== seed -> c1 (mode %s)\n' "$mode"
s=$(date +%s%N)
( cd "$out/run" && "$seed_bin" "${mode_args[@]}" > "$out/c1.c" )
e=$(date +%s%N); t1=$(( (e - s) / 1000000 ))
echo "   ${t1} ms"
cmp -s "$out/c1.c" "$fixpoint/self1.c" || die "seed output != fixpoint self1.c ($(cmp "$out/c1.c" "$fixpoint/self1.c" 2>&1 | head -1))"
printf '   c1.c == self1.c (%s bytes)\n' "$(wc -c < "$out/c1.c" | tr -d ' ')"

printf '== c1 -> stage 1 (cc)\n'
s=$(date +%s%N)
# shellcheck disable=SC2086
"$cc" $cflags $stage_flags -w -I "$root/selfhost" "$out/c1.c" -o "$out/stage1" $ldflags
e=$(date +%s%N); t2=$(( (e - s) / 1000000 ))
echo "   ${t2} ms"

printf '== stage 1 -> c2\n'
s=$(date +%s%N)
( cd "$out/run" && "$out/stage1" "${mode_args[@]}" > "$out/c2.c" )
e=$(date +%s%N); t3=$(( (e - s) / 1000000 ))
echo "   ${t3} ms"
cmp -s "$out/c2.c" "$fixpoint/self1.c" || die "stage-1 output != fixpoint self1.c ($(cmp "$out/c2.c" "$fixpoint/self1.c" 2>&1 | head -1))"
printf '   c2.c == self1.c (%s bytes)\n' "$(wc -c < "$out/c2.c" | tr -d ' ')"

printf '\nPASS: seed reproduces the fixpoint (c1 == c2 == self1.c == self2.c)\n'
printf '  seed      %s\n' "$seed_bin"
printf '  fixpoint  %s\n' "$fixpoint"
printf '  mode      %s\n' "$mode"
printf '  timings   seed->c1 %s ms, cc %s ms, stage1->c2 %s ms\n' "$t1" "$t2" "$t3"

if [ "$keep" -eq 0 ]; then
  rm -f "$out/c1.c" "$out/c2.c"
fi
