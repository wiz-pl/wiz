#!/usr/bin/env bash
# P8: a guard is before the copy but allows 64 into a 32-cell destination. The cut is
# refuted with the guard, the use, and the bound/capacity mismatch.
set -eu
ROOT=$(CDPATH= cd -- "$(dirname "$0")/../../../.." && pwd)
PROVER=${PROVER:-$ROOT/scry/build/prover}
exec "$PROVER" "$ROOT/scry/corpus/prover/c/memcpy-weak.c" main --cut
