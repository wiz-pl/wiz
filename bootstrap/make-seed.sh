#!/usr/bin/env bash
# Generate the bootstrap seed from a fixpoint run, and (optionally) build it.
#
# The seed is the fixpoint's own stage-1 C: the compiler that the Lean build
# produced, after it has compiled the whole self-hosted toolchain once.  The C is
# deterministic and the fixpoint has already proved it equals the stage-2 C, so
# this script only copies it, records its provenance, and lets a plain `cc`
# produce the seed binary.  No Lean and no Wiz binary are involved here.
#
#   usage: bootstrap/make-seed.sh [options]
#     --fixpoint DIR     a fixpoint output dir (default .lake/fixpoint)
#     --out DIR          where seed.c / SEED / seed go (default bootstrap/seed)
#     --cc CMD           C compiler (default $CC, then cc)
#     --cflags FLAGS     extra C flags (default $SEED_CFLAGS)
#     --ldflags FLAGS    extra link flags (default $SEED_LDFLAGS)
#     --build            also compile seed.c -> seed
#     --allow-unverified accept a fixpoint dir whose self1.c != self2.c
#     --help
#
# GC-mode C needs the Boehm headers and library.  Source the repository's
# toolchain environment first (e.g. `. /workspace/wiz-env.sh`) so that
# WIZ_GC_CFLAGS / WIZ_GC_LDFLAGS are set, or pass --cflags/--ldflags.  RC-mode C
# (it defines WIZ_RC) needs neither.
set -euo pipefail

root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
fixpoint=${FIXPOINT:-$root/.lake/fixpoint}
out=${SEED_DIR:-$root/bootstrap/seed}
cc=${CC:-cc}
cflags=${SEED_CFLAGS:-}
ldflags=${SEED_LDFLAGS:-}
build=0
allow_unverified=0

die() { printf 'make-seed: %s\n' "$*" >&2; exit 1; }
usage() { sed -n '2,27p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'; exit 0; }

while [ "$#" -gt 0 ]; do
  case "$1" in
    --fixpoint) [ "$#" -ge 2 ] || die "--fixpoint needs a directory"; fixpoint=$2; shift 2 ;;
    --out)      [ "$#" -ge 2 ] || die "--out needs a directory"; out=$2; shift 2 ;;
    --cc)       [ "$#" -ge 2 ] || die "--cc needs a command"; cc=$2; shift 2 ;;
    --cflags)   [ "$#" -ge 2 ] || die "--cflags needs a value"; cflags=$2; shift 2 ;;
    --ldflags)  [ "$#" -ge 2 ] || die "--ldflags needs a value"; ldflags=$2; shift 2 ;;
    --build)    build=1; shift ;;
    --allow-unverified) allow_unverified=1; shift ;;
    -h|--help)  usage ;;
    *) die "unknown option: $1 (try --help)" ;;
  esac
done

[ -f "$fixpoint/self1.c" ] || die "no self1.c in $fixpoint"
[ -f "$fixpoint/self2.c" ] || die "no self2.c in $fixpoint (run scripts/fixpoint.sh first)"

# The fixpoint is the whole reason the seed is trustworthy: stage 1 and stage 2
# emitted the same C.  Refuse the artifact if it does not hold.
if cmp -s "$fixpoint/self1.c" "$fixpoint/self2.c"; then
  fixpoint_status="self1.c == self2.c"
else
  if [ "$allow_unverified" -eq 1 ]; then
    fixpoint_status="UNVERIFIED (self1.c != self2.c)"
    printf 'make-seed: warning: %s; continuing because --allow-unverified\n' "$fixpoint_status" >&2
  else
    die "$fixpoint is not a fixpoint (self1.c != self2.c); run scripts/fixpoint.sh, or pass --allow-unverified"
  fi
fi

mkdir -p "$out"
cp "$fixpoint/self1.c" "$out/seed.c"

mode=gc
if grep -q '^#define WIZ_RC' "$out/seed.c"; then mode=rc; fi

source_commit=$(git -C "$root" rev-parse HEAD 2>/dev/null || echo unknown)
sha_seed=$(sha256sum "$out/seed.c" | awk '{print $1}')
sha_fix=$(sha256sum "$fixpoint/self1.c" | awk '{print $1}')
sha_rt=$(sha256sum "$root/selfhost/rt.c" | awk '{print $1}')
sha_input=""
[ -f "$fixpoint/run/input.wiz" ] && sha_input=$(sha256sum "$fixpoint/run/input.wiz" | awk '{print $1}')
bytes=$(wc -c < "$out/seed.c" | tr -d ' ')
lines=$(wc -l < "$out/seed.c" | tr -d ' ')
cc_version=$("$cc" --version 2>/dev/null | head -1 || echo unknown)

{
  echo "format: 1"
  echo "mode: $mode"
  echo "source: $source_commit"
  echo "sha256: $sha_seed"
  echo "bytes: $bytes"
  echo "lines: $lines"
  echo "fixpoint: $fixpoint_status"
  echo "fixpoint_sha256: $sha_fix"
  echo "rt.c_sha256: $sha_rt"
  [ -n "$sha_input" ] && echo "input_sha256: $sha_input"
  echo "cc: $cc_version"
  echo "cflags: $cflags"
  echo "ldflags: $ldflags"
  echo "build: $cc $cflags -I $root/selfhost $out/seed.c -o $out/seed $ldflags"
} > "$out/SEED"

printf 'seed source: %s (%s)\n' "$out/seed.c" "$mode"
printf '  %s bytes, %s lines, sha256 %s\n' "$bytes" "$lines" "$sha_seed"
printf '  fixpoint: %s\n' "$fixpoint_status"
printf '  manifest: %s\n' "$out/SEED"

if [ "$build" -eq 1 ]; then
  start=$(date +%s%N)
  # shellcheck disable=SC2086
  "$cc" $cflags -I "$root/selfhost" "$out/seed.c" -o "$out/seed" $ldflags
  end=$(date +%s%N)
  ms=$(( (end - start) / 1000000 ))
  printf 'built: %s (%s bytes) in %d.%03d s\n' "$out/seed" "$(wc -c < "$out/seed" | tr -d ' ')" $((ms / 1000)) $((ms % 1000))
fi
