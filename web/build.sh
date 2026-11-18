#!/bin/sh
# Build the web infoview: web/Web.wiz → C (the Wiz compiler) → WebAssembly (Emscripten),
# with the reference-counting runtime and mini-gmp (GMP's portable subset) for bignums.
#   usage: web/build.sh [OUT] [--gmp-src GMP.tar.xz] [--from DIR]
#   (OUT default web/out; needs .lake/build/bin/wiz. --gmp-src: mini-gmp from that GMP
#   source tarball instead of nixpkgs', for builds without nix, such as the release job.
#   --from DIR, or WIZ_WEB_FROM=DIR: copy the module a Nix build made instead
#   (`nix build .#wiz-web`), for CI and anyone who has the store path; local use is
#   unchanged.)
# wasm64 (-sMEMORY64) keeps the runtime's 64-bit words and 62-bit small numbers as they
# are. Web.wiz is a library (stage 9g): the page calls its exports `wiz_web_init` and
# `wiz_web_step` on every event, so nothing waits inside Wasm (no Asyncify).
set -e
ROOT=$(cd "$(dirname "$0")/.." && pwd)
GMPSRC=
FROM=${WIZ_WEB_FROM:-}
OUT_DIR=
while [ $# -gt 0 ]; do
  case "$1" in
    --gmp-src) GMPSRC=$(cd "$(dirname "$2")" && pwd)/$(basename "$2"); shift 2 ;;
    --from) FROM=$2; shift 2 ;;
    *) OUT_DIR=$1; shift ;;
  esac
done
OUT=$(mkdir -p "${OUT_DIR:-$ROOT/web/out}" && cd "${OUT_DIR:-$ROOT/web/out}" && pwd)
# A module built elsewhere (packages.wiz-web): same files, no Emscripten, no nix.
if [ -n "$FROM" ]; then
  [ -f "$FROM/wiz-infoview.mjs" ] || {
    echo "build: $FROM/wiz-infoview.mjs is missing (--from $FROM)" >&2; exit 1; }
  cp -R "$FROM"/. "$OUT"/
  echo "copied $OUT/wiz-infoview.mjs from $FROM"
  exit 0
fi
# without emcc on the PATH, run again with Emscripten from nixpkgs
if ! command -v emcc >/dev/null; then
  set --; [ -z "$OUT_DIR" ] || set -- "$OUT_DIR"
  [ -z "$GMPSRC" ] || set -- "$@" --gmp-src "$GMPSRC"
  exec nix shell nixpkgs#emscripten -c "$0" "$@"
fi
WIZ=${WIZ:-$ROOT/.lake/build/bin/wiz}

# 1. mini-gmp from GMP's source tarball, behind a <gmp.h>
if [ ! -f "$OUT/gmp/mini-gmp.c" ]; then
  mkdir -p "$OUT/gmp"
  SRC=${GMPSRC:-$(nix build --no-link --print-out-paths nixpkgs#gmp.src)}
  tar -C "$OUT/gmp" --strip-components=2 -xf "$SRC" --wildcards '*/mini-gmp/mini-gmp.[ch]'
  printf '#include "mini-gmp.h"\n' > "$OUT/gmp/gmp.h"
fi

# 2. Wiz → C → wasm, as an ES module that web/infoview.js imports: `wiz build` with emcc
# as the C compiler, mini-gmp in place of -lgmp (--gmp), and web/js.c by Web.wiz's
# `link_c "js.c"` (stage 9f). `--no-main` (9g): the module is Web.wiz's exports, linked
# without a `main` (emcc's --no-entry). It writes OUT/wiz-infoview.c beside the module.
(cd "$ROOT" && "$WIZ" --cc emcc --cflags "-I$OUT/gmp -DWIZ_NO_THREADS" --gmp "$OUT/gmp/mini-gmp.c" \
  --ldflags "-sMEMORY64=1 -sSTACK_SIZE=33554432 --no-entry \
-sALLOW_MEMORY_GROWTH -sMODULARIZE -sEXPORT_ES6 -sENVIRONMENT=web,node \
-sEXPORTED_FUNCTIONS=_wiz_web_init,_wiz_web_step,_wiz_doc_init,_wiz_doc_step,_wiz_release,_free \
-sEXPORTED_RUNTIME_METHODS=stringToNewUTF8 \
-sDEFAULT_LIBRARY_FUNCS_TO_INCLUDE=\$stringToNewUTF8,\$UTF8ToString" \
  build web/Web.wiz -o "$OUT/wiz-infoview.mjs" --no-main)
cp "$ROOT/web/infoview.html" "$ROOT/web/infoview.js" "$ROOT/web/tagged.js" "$ROOT/web/scroll.js" \
  "$ROOT/web/scroll-search.js" "$ROOT/web/scroll.css" "$OUT/"
echo "built $OUT/wiz-infoview.mjs"
