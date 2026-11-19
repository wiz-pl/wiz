#!/usr/bin/env bash
# P6: the modern C# twin (record, `with`, LINQ, array). The field store and the later
# load are covered by the memory invariant, so the checker refutes the claim with a
# store -> load -> flow -> sink path instead of refusing for `mstore`.
set -eu
ROOT=$(CDPATH= cd -- "$(dirname "$0")/../../../.." && pwd)
PROVER=${PROVER:-$ROOT/scry/build/prover}
exec "$PROVER" "$ROOT/scry/corpus/csharp/taint/cwe78-modern-unsafe.cs" \
  Fixtures.Modern.CommandEndpoints.Run
