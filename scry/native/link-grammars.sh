#!/usr/bin/env bash
# Make scry's grammar out-links: scry/native/tree-sitter-c and
# scry/native/tree-sitter-c-sharp, symlinks into the Nix store (and GC roots) to the
# grammars flake.nix pins (`.#tree-sitter-c`, `.#tree-sitter-c-sharp`). scry's
# `link_c` lines compile their src/parser.c from there; both links are gitignored.
# Run it once per checkout, and again after a pin changes (native/README.md).
set -euo pipefail
root=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
cd "$root"
for g in tree-sitter-c tree-sitter-c-sharp; do
  nix build ".#$g" -o "scry/native/$g"
done
