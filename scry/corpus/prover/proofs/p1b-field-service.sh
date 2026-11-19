#!/usr/bin/env bash
# P1b: a method that reads a field and calls a service, with no Console.ReadLine and
# no Process.Start. The memory fragment covers the field load, but the claim is
# vacuous (the source set is empty).
set -eu
ROOT=$(CDPATH= cd -- "$(dirname "$0")/../../../.." && pwd)
PROVER=${PROVER:-$ROOT/scry/build/prover}
exec "$PROVER" "$ROOT/scry/corpus/prover/synthetic/RecordSeeder.cs" \
  Fixtures.Hosting.RecordSeeder.RunAsync
