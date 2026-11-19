#!/usr/bin/env bash
# P5b: the helper's unsafe twin. The checker must reject it with a path.
set -eu
ROOT=$(CDPATH= cd -- "$(dirname "$0")/../../../.." && pwd)
PROVER=${PROVER:-$ROOT/scry/build/prover}
exec "$PROVER" "$ROOT/scry/corpus/prover/helper/Files.cs" \
  ProverDogfood.Files.UnsafeWrite \
  --pack "$ROOT/scry/corpus/prover/packs/files.scry" --cover
