#!/bin/sh
# Build the documentation search's runtime: web/docs-ui.wiz (Web.Search) as
# wiz-docs-ui.mjs. `web/scroll-search.js` mounts it on `#results`; the index stays the
# page's script (`search.js`) and the box stays a DOM input.
#   usage: web/build-docs-ui.sh [OUT] [--gmp-src GMP.tar.xz] [--from DIR]
set -e
ROOT=$(cd "$(dirname "$0")/.." && pwd)
GMPSRC=
FROM=${WIZ_DOCS_UI_FROM:-}
OUT_DIR=
while [ $# -gt 0 ]; do
  case "$1" in
    --gmp-src) GMPSRC=$(cd "$(dirname "$2")" && pwd)/$(basename "$2"); shift 2 ;;
    --from) FROM=$2; shift 2 ;;
    *) OUT_DIR=$1; shift ;;
  esac
done
OUT=$(mkdir -p "${OUT_DIR:-$ROOT/web/out}" && cd "${OUT_DIR:-$ROOT/web/out}" && pwd)
if [ -n "$FROM" ]; then
  cp -R --no-preserve=mode "$FROM"/. "$OUT"/
  exit 0
fi
if ! command -v emcc >/dev/null; then
  set --; [ -z "$OUT_DIR" ] || set -- "$OUT_DIR"
  [ -z "$GMPSRC" ] || set -- "$@" --gmp-src "$GMPSRC"
  exec nix shell --inputs-from "$ROOT" nixpkgs#emscripten -c "$0" "$@"
fi
WIZ=${WIZ:-$ROOT/.lake/build/bin/wiz}
if [ ! -f "$OUT/gmp/mini-gmp.c" ]; then
  mkdir -p "$OUT/gmp"
  SRC=${GMPSRC:-$(nix build --inputs-from "$ROOT" --no-link --print-out-paths nixpkgs#gmp.src)}
  tar -C "$OUT/gmp" --strip-components=2 -xf "$SRC" --wildcards '*/mini-gmp/mini-gmp.[ch]'
  printf '#include "mini-gmp.h"\n' > "$OUT/gmp/gmp.h"
fi
(cd "$ROOT" && "$WIZ" -I "$ROOT/lib" --cc emcc --cflags "-I$OUT/gmp -DWIZ_NO_THREADS -ffile-prefix-map=$ROOT=. -ffile-prefix-map=$OUT=." \
  --gmp "$OUT/gmp/mini-gmp.c" \
  --ldflags "-sMEMORY64=1 -sSTACK_SIZE=33554432 --no-entry \
-sALLOW_MEMORY_GROWTH -sMODULARIZE -sEXPORT_ES6 -sENVIRONMENT=web,node \
-sEXPORTED_FUNCTIONS=_wiz_loom_init,_wiz_loom_html,_wiz_loom_step,_wiz_loom_effect,_wiz_retain,_free \
-sEXPORTED_RUNTIME_METHODS=stringToNewUTF8 \
-sDEFAULT_LIBRARY_FUNCS_TO_INCLUDE=\$stringToNewUTF8,\$UTF8ToString" \
  build web/docs-ui.wiz -o "$OUT/wiz-docs-ui.mjs" --no-main)
echo "built $OUT/wiz-docs-ui.mjs"
