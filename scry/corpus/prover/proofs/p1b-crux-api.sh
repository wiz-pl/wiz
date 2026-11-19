#!/usr/bin/env bash
# P1b: the same claim over a real Crux.Api namespace (Nexus).
set -eu
ROOT=$(CDPATH= cd -- "$(dirname "$0")/../../../.." && pwd)
PROVER=${PROVER:-$ROOT/scry/build/prover}
exec "$PROVER" "$ROOT/scry/corpus/prover/real/BootstrapPartnerCredentialSeeder.cs" \
  Crux.Api.Hosting.BootstrapPartnerCredentialSeeder.RunAsync
