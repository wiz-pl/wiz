#!/usr/bin/env bash
# P1: no Console.ReadLine value reaches Process.Start (the safe C# twin).
set -eu
ROOT=$(CDPATH= cd -- "$(dirname "$0")/../../../.." && pwd)
PROVER=${PROVER:-$ROOT/scry/build/prover}
exec "$PROVER" "$ROOT/scry/corpus/csharp/taint/cwe78-process-safe.cs" Fixtures.Runner.Main
