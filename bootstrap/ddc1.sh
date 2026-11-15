#!/usr/bin/env bash
# DDC-1: build the seed with two different C compilers and compare the compilers
# they produce.
#
#   seed_A = A(seed.c)     seed_B = B(seed.c)
#   c_A    = T(seed_A)     c_B    = T(seed_B)        must be equal (and == self1.c)
#   S1_A   = A(c_A)        S1_B   = B(c_B)
#   d_A    = T(S1_A)       d_B    = T(S1_B)          must be equal (and == self1.c)
#
# The diversity is in the C compiler, not the Wiz lineage: a shared seed still
# defeats DDC-2, and a backdoor already in self1.c is reproduced faithfully by
# both sides.  See bootstrap/README.md.
#
#   usage: bootstrap/ddc1.sh [options]
#     --fixpoint DIR   fixpoint output dir, with run/input.wiz (default .lake/fixpoint)
#     --seed-c FILE    the C seed (default bootstrap/seed/seed.c)
#     --out DIR        build/run directory (default bootstrap/seed/ddc1)
#     --builds LIST    space-separated COMPILER:OPT, default "gcc:-O2 clang:-O2"
#                      e.g. 'gcc:-O0 gcc:-O2 clang:-O0 clang:-O2'
#     --stage-flags F  compiler flags for stage 1 (default the same OPT edge)
#     --cflags FLAGS   seed/stage C flags (default $SEED_CFLAGS)
#     --ldflags FLAGS  link flags (default $SEED_LDFLAGS)
#     --help
set -euo pipefail

root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
fixpoint=${FIXPOINT:-$root/.lake/fixpoint}
seed_c=${SEED_C:-$root/bootstrap/seed/seed.c}
out=${DDC_DIR:-$root/bootstrap/seed/ddc1}
builds=${DDC_BUILDS:-"gcc:-O2 clang:-O2"}
stage_flags_override=""
cflags=${SEED_CFLAGS:-}
ldflags=${SEED_LDFLAGS:-}

die() { printf 'ddc1: %s\n' "$*" >&2; exit 1; }
usage() { sed -n '2,25p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'; exit 0; }

while [ "$#" -gt 0 ]; do
  case "$1" in
    --fixpoint)    [ "$#" -ge 2 ] || die "--fixpoint needs a directory"; fixpoint=$2; shift 2 ;;
    --seed-c)      [ "$#" -ge 2 ] || die "--seed-c needs a file"; seed_c=$2; shift 2 ;;
    --out)         [ "$#" -ge 2 ] || die "--out needs a directory"; out=$2; shift 2 ;;
    --builds)      [ "$#" -ge 2 ] || die "--builds needs a list"; builds=$2; shift 2 ;;
    --stage-flags) [ "$#" -ge 2 ] || die "--stage-flags needs a value"; stage_flags_override=$2; shift 2 ;;
    --cflags)      [ "$#" -ge 2 ] || die "--cflags needs a value"; cflags=$2; shift 2 ;;
    --ldflags)     [ "$#" -ge 2 ] || die "--ldflags needs a value"; ldflags=$2; shift 2 ;;
    -h|--help)     usage ;;
    *) die "unknown option: $1 (try --help)" ;;
  esac
done

[ -f "$seed_c" ] || die "no seed C at $seed_c (run bootstrap/make-seed.sh first)"
[ -f "$fixpoint/self1.c" ] || die "no self1.c in $fixpoint"
[ -f "$fixpoint/self2.c" ] || die "no self2.c in $fixpoint"
[ -f "$fixpoint/run/input.wiz" ] || die "no $fixpoint/run/input.wiz"
cmp -s "$fixpoint/self1.c" "$fixpoint/self2.c" || die "$fixpoint is not a fixpoint"

mode=gc
if grep -q '^#define WIZ_RC' "$seed_c"; then mode=rc; fi
mode_args=()
[ "$mode" = rc ] && mode_args=(--rc)

rm -rf "$out"
mkdir -p "$out"
out=$(cd "$out" && pwd)
cp "$fixpoint/run/input.wiz" "$out/input.wiz"

printf 'DDC-1: seed %s, mode %s\n' "$seed_c" "$mode"
printf '  builds: %s\n' "$builds"
printf '%s\n' '---'

results=""
for spec in $builds; do
  comp=${spec%%:*}
  opt=${spec#*:}
  [ "$opt" != "$spec" ] || opt=""
  name="${comp//\//_}$opt"
  dir="$out/$name"
  mkdir -p "$dir"
  stage_flags=${stage_flags_override:-$opt}

  printf '== %s %s\n' "$comp" "$opt"
  # shellcheck disable=SC2086
  if ! "$comp" $opt $cflags -w -I "$root/selfhost" "$seed_c" -o "$dir/seed" $ldflags; then
    die "$comp $opt could not build the seed"
  fi
  seed_sha=$(sha256sum "$dir/seed" | awk '{print $1}')

  s=$(date +%s%N)
  ( cd "$dir" && cp "$out/input.wiz" input.wiz && "$dir/seed" "${mode_args[@]}" > c1.c 2> c1.err )
  e=$(date +%s%N); t1=$(( (e - s) / 1000000 ))
  [ ! -s "$dir/c1.err" ] || die "$comp $opt seed wrote diagnostics: $(head -1 "$dir/c1.err")"
  cmp -s "$dir/c1.c" "$fixpoint/self1.c" || die "$comp $opt seed output != self1.c"
  c1_sha=$(sha256sum "$dir/c1.c" | awk '{print $1}')
  printf '   seed   %s  sha %s\n' "$dir/seed" "$seed_sha"
  printf '   c1 == self1.c  sha %s  (%s ms)\n' "$c1_sha" "$t1"

  # shellcheck disable=SC2086
  if ! "$comp" $stage_flags $cflags -w -I "$root/selfhost" "$dir/c1.c" -o "$dir/stage1" $ldflags; then
    die "$comp $stage_flags could not build stage 1"
  fi
  s=$(date +%s%N)
  ( cd "$dir" && "$dir/stage1" "${mode_args[@]}" > c2.c 2> c2.err )
  e=$(date +%s%N); t2=$(( (e - s) / 1000000 ))
  [ ! -s "$dir/c2.err" ] || die "$comp stage 1 wrote diagnostics: $(head -1 "$dir/c2.err")"
  cmp -s "$dir/c2.c" "$fixpoint/self1.c" || die "$comp stage-1 output != self1.c"
  c2_sha=$(sha256sum "$dir/c2.c" | awk '{print $1}')
  stage_sha=$(sha256sum "$dir/stage1" | awk '{print $1}')
  printf '   stage1 sha %s\n' "$stage_sha"
  printf '   c2 == self1.c  sha %s  (%s ms)\n' "$c2_sha" "$t2"
  results="$results$name seed=$seed_sha c1=$c1_sha stage1=$stage_sha c2=$c2_sha\n"
done

printf '%s\n' '---'
printf 'result table:\n'
printf '%b' "$results"

# The emitted C is the artefact: every variant must equal the fixpoint's self1.c,
# which the loop already checked.  Binary equality is not required (different cc,
# different build paths, different .comment); report it when it happens.
set -- $builds
first=${1%%:*}
first_opt=${1#*:}; [ "$first_opt" != "$1" ] || first_opt=""
first_dir="$out/${first//\//_}$first_opt"
for spec in $builds; do
  comp=${spec%%:*}; opt=${spec#*:}; [ "$opt" != "$spec" ] || opt=""
  dir="$out/${comp//\//_}$opt"
  [ "$dir" = "$first_dir" ] && continue
  if cmp -s "$first_dir/stage1" "$dir/stage1"; then
    printf 'stage-1 binaries are byte-identical: %s == %s\n' "$first_dir" "$dir"
  else
    printf 'stage-1 binaries differ (expected across cc): %s vs %s\n' "$first_dir" "$dir"
  fi
done

printf '\nPASS: DDC-1 (every seed/stage-1 variant emitted self1.c)\n'
