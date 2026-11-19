#!/usr/bin/env bash
# Build the prover driver. It reads a .cs file and its checked-in .cst spill, so it
# needs no native tree-sitter shim; the gmp flags come from grail.local.wiz.
set -eu
ROOT=$(CDPATH= cd -- "$(dirname "$0")/../../.." && pwd)
WIZ=${WIZ:-$ROOT/.lake/build/bin/wiz}
if [ ! -x "$WIZ" ]; then WIZ=$(command -v wiz || true); fi
[ -n "$WIZ" ] || { echo "build.sh: no wiz binary (set WIZ=...)" >&2; exit 2; }
CFLAGS=${CFLAGS:-$(sed -n 's/.*"cflags" "\(.*\)".*/\1/p' "$ROOT/grail.local.wiz")}
LDFLAGS=${LDFLAGS:-$(sed -n 's/.*"ldflags" "\(.*\)".*/\1/p' "$ROOT/grail.local.wiz")}
CC=${CC:-$(command -v cc || true)}
if [ -z "$CC" ]; then
  # A heavy/srun job can inherit a PATH without cc; take the Nix wrapper if present.
  CC=$(ls -d /nix/store/*-gcc-wrapper-*/bin/cc 2>/dev/null | head -1 || true)
fi
mkdir -p "$ROOT/scry/build"
cd "$ROOT/scry"
exec "$WIZ" build tools/ProverMain.wiz -I src -I ../lib -o build/prover \
  ${CC:+--cc "$CC"} --cflags "$CFLAGS" --ldflags "$LDFLAGS"
