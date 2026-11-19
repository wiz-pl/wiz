#!/usr/bin/env bash
# P3: an unvalidated request header does not reach the event processor. The handler
# reads a header (a source) and passes the parsed body to the processor; the proof
# must show the header itself does not flow there.
set -eu
ROOT=$(CDPATH= cd -- "$(dirname "$0")/../../../.." && pwd)
PROVER=${PROVER:-$ROOT/scry/build/prover}
exec "$PROVER" "$ROOT/scry/corpus/prover/synthetic/EventEndpoint.cs" \
  Fixtures.Requests.EventEndpoint.HandleAsync \
  --pack "$ROOT/scry/corpus/prover/packs/events.scry"
