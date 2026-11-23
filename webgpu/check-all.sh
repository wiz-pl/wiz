#!/bin/sh
# The whole prototype harness: run the kernels on WebGPU, then check the subset boundary.
#
#   ./webgpu/check-all.sh
#
# check.sh needs deno + a Vulkan driver; the reject fixtures additionally need a Wiz
# binary (WIZ, or `wiz` on PATH).  A missing WIZ runs the value tests and exits 3, so a
# partial run is never mistaken for a pass.
set -eu
cd "$(dirname "$0")/.."

./webgpu/check.sh

if [ -n "${WIZ:-}" ]; then
  :
elif command -v wiz >/dev/null 2>&1; then
  WIZ=$(command -v wiz)
elif [ -x .lake/build/bin/wiz ]; then
  WIZ=$PWD/.lake/build/bin/wiz
else
  echo "check-all: no WIZ binary; the rejection fixtures were not run (set WIZ=/path/to/wiz)" >&2
  exit 3
fi
WIZ=$WIZ node webgpu/tests/reject.mjs
