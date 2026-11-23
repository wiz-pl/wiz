#!/usr/bin/env bash
# P7: every write is preceded by a check. The copy length n is checked against the
# destination's 32 cells before memcpy; the cut over all guard points must be proved.
set -eu
ROOT=$(CDPATH= cd -- "$(dirname "$0")/../../../.." && pwd)
PROVER=${PROVER:-$ROOT/scry/build/prover}
exec "$PROVER" "$ROOT/scry/corpus/prover/c/memcpy-safe.c" main --cut
