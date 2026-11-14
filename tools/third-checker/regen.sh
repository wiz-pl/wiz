#!/usr/bin/env bash
# Regenerate corpus.dump by running the self-hosted kernel on the corpus.
#
# `wiz run` compiles the driver to C, so it needs a C compiler and the GMP/GC flags.
# Outside a devshell, this repo's usual way is `nix develop` (CI already has cc).  The
# committed dump means this is only needed when the corpus or the kernel changes.
set -euo pipefail
cd "$(dirname "$0")/../.."
if command -v cc >/dev/null 2>&1; then
  exec python3 tools/third-checker/harness.py --regen "$@"
fi
exec nix develop --command bash -lc \
  '. /workspace/wiz-env.sh 2>/dev/null || true; exec python3 tools/third-checker/harness.py --regen "$@"' \
  bash "$@"
