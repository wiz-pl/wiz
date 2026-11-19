#!/usr/bin/env bash
# Build the prover driver. It reads a .cs file and its checked-in .cst spill, so it
# needs no native tree-sitter shim; the gmp flags come from grail.local.wiz.
set -eu
ROOT=$(CDPATH= cd -- "$(dirname "$0")/../../.." && pwd)
WIZ=${WIZ:-$ROOT/.lake/build/bin/wiz}
CFLAGS=${CFLAGS:-$(sed -n 's/.*"cflags" "\(.*\)".*/\1/p' "$ROOT/grail.local.wiz")}
LDFLAGS=${LDFLAGS:-$(sed -n 's/.*"ldflags" "\(.*\)".*/\1/p' "$ROOT/grail.local.wiz")}
CC=${CC:-$(command -v cc || true)}
mkdir -p "$ROOT/scry/build"
cd "$ROOT/scry"
if [ -n "$CC" ]; then
  exec "$WIZ" build tools/ProverMain.wiz -I src -I ../lib -o build/prover \
    --cc "$CC" --cflags "$CFLAGS" --ldflags "$LDFLAGS"
else
  exec "$WIZ" build tools/ProverMain.wiz -I src -I ../lib -o build/prover \
    --cflags "$CFLAGS" --ldflags "$LDFLAGS"
fi
