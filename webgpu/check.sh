#!/bin/sh
# Validate and run the generated WGSL, comparing with the Wiz interpreter's numbers.
#
#   ./webgpu/check.sh
#
# Needs `deno` (its WebGPU is wgpu/naga) and, on headless Linux, a Vulkan driver.  Mesa's
# lavapipe is enough; set DENO, MESA and VULKAN_LOADER to override what `nix eval` finds.
set -eu
cd "$(dirname "$0")"

DENO=${DENO:-$(command -v deno || true)}
if [ -z "$DENO" ]; then
  echo "check.sh: no deno; set DENO=/path/to/deno" >&2
  exit 3
fi

if [ -z "${VK_ICD_FILENAMES:-}" ]; then
  MESA=${MESA:-$(nix eval --raw nixpkgs#mesa 2>/dev/null || true)}
  VULKAN_LOADER=${VULKAN_LOADER:-$(nix eval --raw nixpkgs#vulkan-loader 2>/dev/null || true)}
  if [ -n "$MESA" ] && [ -f "$MESA/share/vulkan/icd.d/lvp_icd.x86_64.json" ]; then
    export VK_ICD_FILENAMES=$MESA/share/vulkan/icd.d/lvp_icd.x86_64.json
    export LD_LIBRARY_PATH=$MESA/lib${VULKAN_LOADER:+:$VULKAN_LOADER/lib}${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}
  else
    echo "check.sh: no lavapipe ICD; set VK_ICD_FILENAMES (see the README)" >&2
    exit 3
  fi
fi

exec "$DENO" run --allow-read "$PWD/check.mjs"
