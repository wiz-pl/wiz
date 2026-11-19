#!/usr/bin/env bash
# P4: the same claim as P1 on the unsafe twin. The checker must reject it with a path.
set -eu
ROOT=$(CDPATH= cd -- "$(dirname "$0")/../../../.." && pwd)
PROVER=${PROVER:-$ROOT/scry/build/prover}
exec "$PROVER" "$ROOT/scry/corpus/csharp/taint/cwe78-process-unsafe.cs" \
  Fixtures.Runner.Main --cover
