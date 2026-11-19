#!/usr/bin/env bash
# P2: every SqlCommand argument is a constant or a parameter bind. The field read is
# covered by the memory invariant; no untrusted source reaches the command text.
set -eu
ROOT=$(CDPATH= cd -- "$(dirname "$0")/../../../.." && pwd)
PROVER=${PROVER:-$ROOT/scry/build/prover}
exec "$PROVER" "$ROOT/scry/corpus/prover/synthetic/ReportProvider.cs" \
  Fixtures.Data.ReportProvider.FetchAsync \
  --pack "$ROOT/scry/corpus/prover/packs/sql.scry" --entry --classify
