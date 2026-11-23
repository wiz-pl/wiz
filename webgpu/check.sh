#!/bin/sh
# Validate and run the generated WGSL, comparing with the Wiz interpreter's numbers.
#
#   ./webgpu/check.sh
#
# Needs `deno` (its WebGPU is wgpu/naga) and a Vulkan driver.  On a headless Linux box
# Mesa's lavapipe (llvmpipe) is enough.  DENO, MESA, VULKAN_LOADER and VK_ICD_FILENAMES
# override the auto-detection; `nix` is not required.
set -eu
cd "$(dirname "$0")"

find_deno() {
  if [ -n "${DENO:-}" ]; then printf '%s\n' "$DENO"; return 0; fi
  if command -v deno >/dev/null 2>&1; then command -v deno; return 0; fi
  for d in /nix/store/*-deno-*/bin/deno; do
    if [ -x "$d" ]; then printf '%s\n' "$d"; fi
  done | sort -V | tail -n 1
}

# The ICD json names the 64-bit lavapipe library; a 32-bit mesa in the store is not usable.
find_icd() {
  if [ -n "${VK_ICD_FILENAMES:-}" ] && [ -f "$VK_ICD_FILENAMES" ]; then
    printf '%s\n' "$VK_ICD_FILENAMES"; return 0
  fi
  if [ -n "${MESA:-}" ] && [ -f "$MESA/share/vulkan/icd.d/lvp_icd.x86_64.json" ]; then
    printf '%s\n' "$MESA/share/vulkan/icd.d/lvp_icd.x86_64.json"; return 0
  fi
  for j in /run/opengl-driver/share/vulkan/icd.d/lvp_icd.x86_64.json \
           /nix/store/*-mesa-*/share/vulkan/icd.d/lvp_icd.x86_64.json; do
    if [ -f "$j" ]; then
      lib=$(sed -n 's/.*"library_path"[[:space:]]*:[[:space:]]*"\([^"]*\)".*/\1/p' "$j")
      if [ -n "$lib" ] && [ -f "$lib" ]; then
        printf '%s\n' "$j"; return 0
      fi
    fi
  done
  return 1
}

find_loader() {
  if [ -n "${VULKAN_LOADER:-}" ]; then
    if [ -e "$VULKAN_LOADER/lib/libvulkan.so.1" ]; then printf '%s\n' "$VULKAN_LOADER/lib"; return 0; fi
    if [ -e "$VULKAN_LOADER/libvulkan.so.1" ]; then printf '%s\n' "$VULKAN_LOADER"; return 0; fi
  fi
  for d in /run/opengl-driver/lib /nix/store/*-vulkan-loader-*/lib; do
    if [ -e "$d/libvulkan.so.1" ]; then printf '%s\n' "$d"; return 0; fi
  done
  return 1
}

DENO=$(find_deno)
if [ -z "$DENO" ]; then
  echo "check.sh: no deno; set DENO=/path/to/deno" >&2
  exit 3
fi

if ICD=$(find_icd); then
  export VK_ICD_FILENAMES=$ICD
  lib=$(sed -n 's/.*"library_path"[[:space:]]*:[[:space:]]*"\([^"]*\)".*/\1/p' "$ICD")
  if [ -n "$lib" ]; then
    LD_LIBRARY_PATH=$(dirname "$lib")${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}
  fi
else
  echo "check.sh: no lavapipe ICD found; trying the system Vulkan driver" >&2
fi
if LOADER=$(find_loader); then
  LD_LIBRARY_PATH=$LOADER${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}
fi
export LD_LIBRARY_PATH=${LD_LIBRARY_PATH:-}

exec "$DENO" run --allow-read "$PWD/check.mjs"
