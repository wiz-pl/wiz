#!/usr/bin/env bash
# Build the prover drivers. Both read a .cs/.c file and its checked-in .cst spill, so
# they need no native tree-sitter shim; the gmp flags come from grail.local.wiz.
#
#   scry/build/prover       the dogfood driver (`prover FILE FN [--cut|--cover|…]`)
#   scry/build/scry-prove   the CLI command (`scry prove FILE --claim … [--json]`)
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
if [ "${WIZ_BUNDLED:-0}" = 1 ]; then
  # A packaged wiz wrapper already supplies its own --cc/--cflags/--ldflags and a
  # read-only cache; passing grail.local.wiz's paths would override them.
  "$WIZ" build tools/ProverMain.wiz -I src -I ../lib -o build/prover
  exec "$WIZ" build tools/ProveMain.wiz -I src -I ../lib -o build/scry-prove
fi
"$WIZ" build tools/ProverMain.wiz -I src -I ../lib -o build/prover \
  ${CC:+--cc "$CC"} --cflags "$CFLAGS" --ldflags "$LDFLAGS"
exec "$WIZ" build tools/ProveMain.wiz -I src -I ../lib -o build/scry-prove \
  ${CC:+--cc "$CC"} --cflags "$CFLAGS" --ldflags "$LDFLAGS"
