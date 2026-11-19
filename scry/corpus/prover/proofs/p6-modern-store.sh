#!/usr/bin/env bash
# P6: the frontend's modern C# fixture (record, `with`, LINQ, array) is REFUSED, not
# refuted: the checker's memory fragment does not cover `mstore`. Kept as the regression
# for the real-code gap: the prover cannot even produce a counterexample here.
set -eu
ROOT=$(CDPATH= cd -- "$(dirname "$0")/../../../.." && pwd)
PROVER=${PROVER:-$ROOT/scry/build/prover}
exec "$PROVER" "$ROOT/scry/corpus/csharp/taint/cwe78-modern-unsafe.cs" \
  Crux.Api.Endpoints.ReportEndpoints.Run
