#!/bin/sh
# Build the web module: web/Web.wiz → C (the Wiz compiler) → WebAssembly (Emscripten),
# with the reference-counting runtime and mini-gmp (GMP's portable subset) for bignums.
# The documentation's pages (`wiz doc --web`) render their signatures with it
# (`wiz_doc_*`, web/scroll.js); the standalone infoview page is JavaScript now
# (web/playground-lsp.js) and does not load it. The build also populates OUT with the pages'
# scripts, which is the directory `wiz lsp --ws` serves.
#   usage: web/build.sh [OUT] [--gmp-src GMP.tar.xz]
#   (OUT default web/out; needs .lake/build/bin/wiz. --gmp-src: mini-gmp from that GMP
#   source tarball instead of nixpkgs', for builds without nix, such as the release job)
# wasm64 (-sMEMORY64) keeps the runtime's 64-bit words and 62-bit small numbers as they
# are. Web.wiz is a library (stage 9g): the page calls its exports `wiz_doc_init` and
# `wiz_doc_step` on every event, so nothing waits inside Wasm (no Asyncify).
set -e
ROOT=$(cd "$(dirname "$0")/.." && pwd)
# without emcc on the PATH, run again with Emscripten from nixpkgs
if ! command -v emcc >/dev/null; then exec nix shell nixpkgs#emscripten -c "$0" "$@"; fi
GMPSRC=
case "${2:-}" in --gmp-src) GMPSRC=$(cd "$(dirname "$3")" && pwd)/$(basename "$3") ;; esac
OUT=$(mkdir -p "${1:-$ROOT/web/out}" && cd "${1:-$ROOT/web/out}" && pwd)
WIZ=${WIZ:-$ROOT/.lake/build/bin/wiz}

# 1. mini-gmp from GMP's source tarball, behind a <gmp.h>
if [ ! -f "$OUT/gmp/mini-gmp.c" ]; then
  mkdir -p "$OUT/gmp"
  SRC=${GMPSRC:-$(nix build --no-link --print-out-paths nixpkgs#gmp.src)}
  tar -C "$OUT/gmp" --strip-components=2 -xf "$SRC" --wildcards '*/mini-gmp/mini-gmp.[ch]'
  printf '#include "mini-gmp.h"\n' > "$OUT/gmp/gmp.h"
fi

# 2. Wiz → C → wasm, as an ES module the documentation's pages load (web/scroll.js):
# `wiz build` with emcc as the C compiler, mini-gmp in place of -lgmp (--gmp), and
# web/js.c by Web.wiz's `link_c "js.c"` (stage 9f). `--no-main` (9g): the module is
# Web.wiz's exports, linked without a `main` (emcc's --no-entry). It writes
# OUT/wiz-infoview.c beside the module (the name is historical: the infoview used to be
# this module; `wiz doc` and the toolchain look for wiz-infoview.mjs).
(cd "$ROOT" && "$WIZ" --cc emcc --cflags "-I$OUT/gmp -DWIZ_NO_THREADS" --gmp "$OUT/gmp/mini-gmp.c" \
  --ldflags "-sMEMORY64=1 -sSTACK_SIZE=33554432 --no-entry \
-sALLOW_MEMORY_GROWTH -sMODULARIZE -sEXPORT_ES6 -sENVIRONMENT=web,node \
-sEXPORTED_FUNCTIONS=_wiz_web_init,_wiz_web_step,_wiz_doc_init,_wiz_doc_step,_wiz_release,_free \
-sEXPORTED_RUNTIME_METHODS=stringToNewUTF8 \
-sDEFAULT_LIBRARY_FUNCS_TO_INCLUDE=\$stringToNewUTF8,\$UTF8ToString" \
  build web/Web.wiz -o "$OUT/wiz-infoview.mjs" --no-main)
cp "$ROOT/web/infoview.html" "$ROOT/web/infoview.js" "$ROOT/web/playground-lsp.js" \
  "$ROOT/web/lsp-client.js" "$ROOT/web/goals.js" "$ROOT/web/tagged.js" "$ROOT/web/scroll.js" \
  "$ROOT/web/scroll-search.js" "$ROOT/web/scroll.css" "$OUT/"
echo "built $OUT/wiz-infoview.mjs"
