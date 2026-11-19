#!/usr/bin/env bash
# P1c: the memory-free method in the same fixture. It has no source and no sink
# (SRC=0, SINK=0), so the honest verdict is vacuous; this is the regression for the
# vacuity guard.
set -eu
ROOT=$(CDPATH= cd -- "$(dirname "$0")/../../../.." && pwd)
PROVER=${PROVER:-$ROOT/scry/build/prover}
exec "$PROVER" "$ROOT/scry/corpus/prover/synthetic/RecordSeeder.cs" \
  Fixtures.Hosting.RecordSeeder.EnsureAsync
