#!/usr/bin/env bash
# P1c: a real Crux.Api method that the checker accepts with the *empty* invariant.
# It has no source and no sink (SRC=0, SINK=0), so the acceptance is vacuous: this is
# the rubber-stamp case the report must not call "proved". Kept as a regression for
# the missing vacuity guard.
set -eu
ROOT=$(CDPATH= cd -- "$(dirname "$0")/../../../.." && pwd)
PROVER=${PROVER:-$ROOT/scry/build/prover}
exec "$PROVER" "$ROOT/scry/corpus/prover/real/BootstrapPartnerCredentialSeeder.cs" \
  Crux.Api.Hosting.BootstrapPartnerCredentialSeeder.EnsureAsync
