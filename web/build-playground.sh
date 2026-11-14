#!/bin/sh
# Build the playground's Wasm module: the self-hosted Wiz frontend (selfhost/*.wiz,
# which is Wiz source) plus the Lean parser's tables, compiled to C by `wiz` and then to
# WebAssembly by Emscripten. The page (web/playground.html) calls its exported
# `wiz_playground_eval : String → String`, so there is no server and no main loop.
#
#   usage: web/build-playground.sh [OUT] [--gmp-src GMP.tar.xz]
#   (OUT default web/out; needs .lake/build/bin/wiz, i.e. `lake build wiz` first)
#
# This is web/build.sh's pipeline with a different source and export; the infoview's
# module (wiz-infoview.mjs) is unchanged and can live in the same OUT directory.
set -e
ROOT=$(cd "$(dirname "$0")/.." && pwd)
# without emcc on the PATH, run again with Emscripten from nixpkgs
if ! command -v emcc >/dev/null; then exec nix shell nixpkgs#emscripten -c "$0" "$@"; fi
GMPSRC=
case "${2:-}" in --gmp-src) GMPSRC=$(cd "$(dirname "$3")" && pwd)/$(basename "$3") ;; esac
OUT=$(mkdir -p "${1:-$ROOT/web/out}" && cd "${1:-$ROOT/web/out}" && pwd)
WIZ=${WIZ:-$ROOT/.lake/build/bin/wiz}

# 1. mini-gmp, as web/build.sh does (share web/out when both are built)
if [ ! -f "$OUT/gmp/mini-gmp.c" ]; then
  mkdir -p "$OUT/gmp"
  SRC=${GMPSRC:-$(nix build --no-link --print-out-paths nixpkgs#gmp.src)}
  tar -C "$OUT/gmp" --strip-components=2 -xf "$SRC" --wildcards '*/mini-gmp/mini-gmp.[ch]'
  printf '#include "mini-gmp.h"\n' > "$OUT/gmp/gmp.h"
fi

# 2. The engine's one Wiz file: IO and Std, the self-hosted frontend with its import
# lines dropped (it is written against the embedded Prelude), the parser tables
# (web/selfhost-tables.wiz, `web/gen-selfhost-tables.lean`), and the export.
ENGINE="$OUT/playground.wiz"
{
  printf 'import IO\nimport Std\n'
  sed '/^import/d' "$ROOT/selfhost/Lex.wiz" "$ROOT/selfhost/Parse.wiz" \
    "$ROOT/selfhost/Kernel.wiz" "$ROOT/selfhost/Frontend.wiz"
  cat "$ROOT/web/selfhost-tables.wiz"
  cat "$ROOT/web/playground-exports.wiz"
} > "$ENGINE"

# 3. Wiz → C → wasm. wasm64 as in web/build.sh; the export is called from
# web/playground.js, and returns a malloc'ed UTF-8 string the page frees.
(cd "$ROOT" && "$WIZ" --cc emcc --cflags "-I$OUT/gmp" --gmp "$OUT/gmp/mini-gmp.c" \
  --ldflags "-sMEMORY64=1 -sSTACK_SIZE=67108864 --no-entry \
-sALLOW_MEMORY_GROWTH -sMODULARIZE -sEXPORT_ES6 -sENVIRONMENT=web,node \
-sEXPORTED_FUNCTIONS=_wiz_playground_eval,_free \
-sEXPORTED_RUNTIME_METHODS=stringToNewUTF8,UTF8ToString \
-sDEFAULT_LIBRARY_FUNCS_TO_INCLUDE=\$stringToNewUTF8,\$UTF8ToString" \
  build "$ENGINE" -o "$OUT/wiz-playground.mjs" --no-main)
cp "$ROOT/web/playground.html" "$ROOT/web/playground.js" "$ROOT/web/playground-values.js" \
  "$ROOT/web/playground.css" "$OUT/"
echo "built $OUT/wiz-playground.mjs"
