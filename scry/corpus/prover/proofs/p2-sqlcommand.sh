#!/usr/bin/env bash
# P2: no caller-supplied value reaches a SqlCommand's command text.
set -eu
ROOT=$(CDPATH= cd -- "$(dirname "$0")/../../../.." && pwd)
PROVER=${PROVER:-$ROOT/scry/build/prover}
exec "$PROVER" "$ROOT/scry/corpus/prover/real/SqlReportProvider.cs" \
  ReportService.Provider.SqlReportProvider.FetchRrnsAsync \
  --pack "$ROOT/scry/corpus/prover/packs/sql.scry" --entry --classify
