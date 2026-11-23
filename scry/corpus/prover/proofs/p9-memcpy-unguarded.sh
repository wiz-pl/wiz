#!/usr/bin/env bash
# P9: no guard at all. The cut is refuted with the use named (there is no guard to name).
set -eu
ROOT=$(CDPATH= cd -- "$(dirname "$0")/../../../.." && pwd)
PROVER=${PROVER:-$ROOT/scry/build/prover}
exec "$PROVER" "$ROOT/scry/corpus/prover/c/memcpy-unguarded.c" main --cut
