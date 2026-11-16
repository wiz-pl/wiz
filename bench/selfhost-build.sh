#!/usr/bin/env bash
# Build the two toolchains that bench/selfhost-bench.py compares: the Lean host
# (.lake/build/bin/wiz) and the self-hosted compiler with its driver and cache
# (bench/.build/selfhost, from scripts/GenSelfhost.lean's compiler.wiz).
#
#   usage: bench/selfhost-build.sh [OUT]
#
# OUT is the scratch directory (default bench/.build).  Run it under heavy; the
# self-hosted compiler build is the expensive half:
#
#   heavy --mem 6G bench/selfhost-build.sh
#
# The C toolchain flags come from the environment (the dev shell sets WIZ_CFLAGS,
# WIZ_LDFLAGS, WIZ_GC_CFLAGS and WIZ_GC_LDFLAGS).
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/.." && pwd)
OUT=${1:-$ROOT/bench/.build}
cd "$ROOT"

lake build wiz Tests.Elab
mkdir -p "$OUT"
OUT="$OUT" lake lean scripts/GenSelfhost.lean

# compiler.wiz is the self-hosted compiler with selfhost/Cli.wiz and Main.wiz: its
# `check`/`build` subcommands and --cache/--no-cache are what the harness uses.
./.lake/build/bin/wiz build "$OUT/compiler.wiz" -o "$OUT/selfhost" \
  --cflags "${WIZ_CFLAGS:-}" --ldflags "${WIZ_LDFLAGS:-}"

echo "built $ROOT/.lake/build/bin/wiz and $OUT/selfhost"
