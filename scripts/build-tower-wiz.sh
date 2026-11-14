#!/bin/sh
# Build the Wiz tower (`tower/`, stage 26e) with a grail, into BINDIR/tower.
#
#   scripts/build-tower-wiz.sh [OUT] [GRAIL] [TOOLCHAIN FLAGS...]
#
# OUT defaults to .lake/build/bin/tower, GRAIL to .lake/build/bin/grail (the checkout's
# build). The remaining arguments go to `grail build` as toolchain flags (--cc, --cflags,
# --gmp, …), so a release can link the bundled static GMP; the Nix package passes its own.
#
# This is the binary `packages.tower` and the release tarball ship (stage 26h): tower no
# longer needs Lean at build time, the way `tower/` no longer needs it at run time.
set -eu
out=${1:-.lake/build/bin/tower}
grail=${2:-.lake/build/bin/grail}
if [ $# -ge 2 ]; then shift 2; else shift $#; fi
root=$(CDPATH= cd -- "$(dirname "$0")/.." && pwd)
case $out in /*) ;; *) out=$(pwd)/$out ;; esac
case $grail in
  */*) case $grail in /*) ;; *) grail=$(pwd)/$grail ;; esac ;;
esac
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
cp -R "$root/tower/." "$work/"
(
  cd "$work"
  HOME=${HOME:-"$work"} "$grail" build tower "$@"
)
mkdir -p "$(dirname "$out")"
# (the checkout's .lake/build/bin/tower is read-only: a lake output)
rm -f "$out"
cp "$work/.grail/bin/tower" "$out"
echo "$out"
