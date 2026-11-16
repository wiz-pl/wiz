#!/usr/bin/env bash
# The chain's step check at one commit (docs/bootstrap-chain.md, "The release is the
# fixpoint stage"): does the release, used as a predecessor, rebuild the same release?
#
#   A  Lean host -> seed.c (= C*) -> static cc -> wizc; wizc reproduces seed.c
#      -> wizc-x86_64-linux.tar.gz                              (.#wizc-release)
#   B  A's tarball, fetched by (commit, hash) through fetchToolchain, compiles self.wiz
#      -> c1 -> static cc -> stage1 -> c2 -> static cc -> wizc; wizc reproduces c2
#      -> packed like A                                         (bootstrapChain.step)
#
# Passes when c1 = c2 = seed.c, B's wizc = A's wizc and B's tarball = A's tarball, byte
# for byte. Prints one line per comparison and exits 1 on any difference.
#
#   usage (from a clean checkout; the flake is read at the commit, not the working tree):
#     heavy --mem 3G timeout 3600 scripts/chain-step-check.sh [--commit SHA] [--out DIR]
#
#   --commit SHA  the commit to check (default HEAD); A's tarball is registered in the
#                 store as the fixed-output path fetchToolchain names for it, so nothing
#                 is downloaded but the Lean host (Cachix)
#   --out DIR     where the result links go (default .scratch/chain-step); they are GC
#                 roots until removed
#
# Cost (prototype, 2026-11-16): A is a store hit when already built (else 15 min); B is
# three self-compiles and two cc runs, about 25-30 min, one builder at a time, about
# 2-3 GB at peak.
set -euo pipefail

root=$(git rev-parse --show-toplevel)
commit=HEAD
out=$root/.scratch/chain-step
while [ $# -gt 0 ]; do
  case "$1" in
    --commit) commit=$2; shift 2 ;;
    --out) out=$2; shift 2 ;;
    -h|--help) sed -n '2,/^set -euo/p' "$0" | sed '$d; s/^# \{0,1\}//'; exit 0 ;;
    *) echo "chain-step-check: unknown argument $1" >&2; exit 2 ;;
  esac
done
commit=$(git -C "$root" rev-parse --verify "$commit^{commit}")
system=$(nix eval --raw --impure --expr builtins.currentSystem)
mkdir -p "$out"
nixf=$root/scripts/chain-step.nix
build() { # ATTR LINK [extra args]: build one attribute of chain-step.nix, print its path
  local attr=$1 link=$2; shift 2
  nix build -L -f "$nixf" --argstr root "$root" --argstr commit "$commit" "$@" \
    --out-link "$out/$link" "$attr" >&2
  readlink -f "$out/$link"
}
h() { sha256sum "$1" | cut -d' ' -f1; }

echo "chain-step-check: commit $commit, system $system" >&2
echo "== A: the release from the Lean host" >&2
seed=$(build seed seed)
relA=$(build lean-release release-a)
tgz=wizc-$system.tar.gz
shaA=$(h "$relA/$tgz")
sri=$(nix hash convert --hash-algo sha256 --to sri "$shaA")
echo "   $tgz sha256 $shaA ($sri)" >&2

echo "== register A's tarball as fetchToolchain's fixed-output path" >&2
nix store add --mode flat --hash-algo sha256 --name "wizc-$system-$commit.tar.gz" \
  "$relA/$tgz" >&2

echo "== B: step { pred = A } (three self-compiles)" >&2
pred=$(build pred pred --argstr hash "$sri")
stepB=$(build step step-b --argstr hash "$sri")
c1=$(build c1 c1 --argstr hash "$sri")
stage1=$(build stage1 stage1 --argstr hash "$sri")
relB=$(build step-release release-b --argstr hash "$sri")

fail=0
cmp_line() { # WHAT FILE_A FILE_B
  local a b; a=$(h "$2"); b=$(h "$3")
  if [ "$a" = "$b" ]; then printf 'same    %-44s %s\n' "$1" "$a"
  else printf 'DIFFER  %-44s %s vs %s\n' "$1" "$a" "$b"; fail=1; fi
}
echo "commit $commit"
echo "seed.c (C*, Lean host)                               $(h "$seed/seed.c")"
cmp_line "A's fetched wizc = A's wizc" "$pred/bin/wizc" <(tar -xzOf "$relA/$tgz" "wizc-$system/bin/wizc")
cmp_line "c1 (A's wizc on self.wiz) = seed.c" "$c1" "$seed/seed.c"
cmp_line "c2 (stage1 on self.wiz) = seed.c" "$stage1/self.c" "$seed/seed.c"
cmp_line "stage1 wizc = A's wizc" "$stage1/bin/wizc" "$pred/bin/wizc"
cmp_line "B's wizc = A's wizc" "$stepB/bin/wizc" "$pred/bin/wizc"
cmp_line "B's tarball = A's tarball" "$relB/$tgz" "$relA/$tgz"
if [ $fail = 0 ]; then echo "chain-step-check: PASS"; else echo "chain-step-check: FAIL"; fi
exit $fail
