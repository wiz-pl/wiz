#!/usr/bin/env bash
# P3b (attempt): a request-supplied name must not reach a filesystem handle.
# Real Nexus file, LogFileReader.Resolve. REFUSED: a tainted location seed is present
# (the checker's memory fragment); see the note.
set -eu
ROOT=$(CDPATH= cd -- "$(dirname "$0")/../../../.." && pwd)
PROVER=${PROVER:-$ROOT/scry/build/prover}
exec "$PROVER" "$ROOT/scry/corpus/prover/real/LogFileReader.cs" \
  Crux.Dashboard.Api.LogViewer.LogFileReader.Resolve \
  --pack "$ROOT/scry/corpus/prover/packs/logpath.scry" --entry
