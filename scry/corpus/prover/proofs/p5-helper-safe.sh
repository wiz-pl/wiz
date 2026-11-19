#!/usr/bin/env bash
# P5: the helper we wrote — a header value to a filesystem write, safely.
set -eu
ROOT=$(CDPATH= cd -- "$(dirname "$0")/../../../.." && pwd)
PROVER=${PROVER:-$ROOT/scry/build/prover}
exec "$PROVER" "$ROOT/scry/corpus/prover/helper/Files.cs" \
  ProverDogfood.Files.SafeWrite \
  --pack "$ROOT/scry/corpus/prover/packs/files.scry"
