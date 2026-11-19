#!/usr/bin/env bash
# P3b: a path helper with no sink. The helper validates and normalises a name but
# returns a string; the lowered unit has no filesystem constructor, so the claim is
# vacuous at the sink set (this used to be a refused memory certificate).
set -eu
ROOT=$(CDPATH= cd -- "$(dirname "$0")/../../../.." && pwd)
PROVER=${PROVER:-$ROOT/scry/build/prover}
exec "$PROVER" "$ROOT/scry/corpus/prover/synthetic/PathHelper.cs" \
  Fixtures.Files.PathHelper.Resolve \
  --pack "$ROOT/scry/corpus/prover/packs/path.scry" --entry
