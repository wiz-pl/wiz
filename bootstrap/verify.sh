#!/usr/bin/env bash
# One-command bootstrap check: generate the seed from a fixpoint, verify that the
# seed reproduces the fixpoint, and optionally run DDC-1.
#
#   usage: bootstrap/verify.sh --fixpoint DIR [--ddc] [--cc CMD]
#                              [--builds "gcc:-O2 clang:-O2"]
#                              [--cflags FLAGS] [--ldflags FLAGS]
#
# The fixpoint must already exist (scripts/fixpoint.sh); this script never runs
# Lean or a Wiz binary.
set -euo pipefail
root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
fixpoint=${FIXPOINT:-$root/.lake/fixpoint}
out=${SEED_DIR:-$root/bootstrap/seed}
cc=${CC:-cc}
cflags=${SEED_CFLAGS:-}
ldflags=${SEED_LDFLAGS:-}
builds=${DDC_BUILDS:-"gcc:-O2 clang:-O2"}
ddc=0

die() { printf 'verify: %s\n' "$*" >&2; exit 1; }
usage() { sed -n '2,10p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'; exit 0; }

while [ "$#" -gt 0 ]; do
  case "$1" in
    --fixpoint) [ "$#" -ge 2 ] || die "--fixpoint needs a directory"; fixpoint=$2; shift 2 ;;
    --out)      [ "$#" -ge 2 ] || die "--out needs a directory"; out=$2; shift 2 ;;
    --cc)       [ "$#" -ge 2 ] || die "--cc needs a command"; cc=$2; shift 2 ;;
    --cflags)   [ "$#" -ge 2 ] || die "--cflags needs a value"; cflags=$2; shift 2 ;;
    --ldflags)  [ "$#" -ge 2 ] || die "--ldflags needs a value"; ldflags=$2; shift 2 ;;
    --builds)   [ "$#" -ge 2 ] || die "--builds needs a list"; builds=$2; shift 2 ;;
    --ddc)      ddc=1; shift ;;
    -h|--help)  usage ;;
    *) die "unknown option: $1 (try --help)" ;;
  esac
done

common=(--fixpoint "$fixpoint" --cc "$cc" --cflags "$cflags" --ldflags "$ldflags")

printf '%s\n' '### 1. generate the seed'
"$root/bootstrap/make-seed.sh" "${common[@]}" --out "$out" --build

printf '\n%s\n' '### 2. seed reproduces the fixpoint'
"$root/bootstrap/check-seed.sh" "${common[@]}" --out "$out" --seed-c "$out/seed.c"

if [ "$ddc" -eq 1 ]; then
  printf '\n%s\n' '### 3. DDC-1'
  "$root/bootstrap/ddc1.sh" --fixpoint "$fixpoint" --out "$out/ddc1" \
    --seed-c "$out/seed.c" --builds "$builds" \
    --cflags "$cflags" --ldflags "$ldflags"
fi
