#!/bin/sh
# Build the source reader's runtime: web/source-ui.wiz (Web.Source.View, the Loom
# LiveApp) as wiz-source-ui.mjs. web/source-static.js mounts it through
# web/framework/mount.js and answers its `hover`/`info` requests from the bundle.
#
#   usage: web/build-source-ui.sh [OUT] [--gmp-src GMP.tar.xz] [--from DIR]
#   (OUT default web/out; needs .lake/build/bin/wiz and the library in lib/.
#   --from DIR, or WIZ_SOURCE_UI_FROM=DIR: copy a module a Nix build made.)
#
# `scry web DIR --out BUNDLE --ui web/out/wiz-source-ui.mjs` copies the module into the
# bundle. Without it the export is data + SSR only and the page says so.
set -e
ROOT=$(cd "$(dirname "$0")/.." && pwd)
GMPSRC=
FROM=${WIZ_SOURCE_UI_FROM:-}
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
  [ -f "$FROM/wiz-source-ui.mjs" ] || {
    echo "build-source-ui: $FROM/wiz-source-ui.mjs is missing (--from $FROM)" >&2; exit 1; }
  cp -R --no-preserve=mode "$FROM"/. "$OUT"/
  echo "copied $OUT/wiz-source-ui.mjs from $FROM"
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
(cd "$ROOT" && "$WIZ" -I "$ROOT/lib" --cc emcc --cflags "-I$OUT/gmp -DWIZ_NO_THREADS" \
  --gmp "$OUT/gmp/mini-gmp.c" \
  --ldflags "-sMEMORY64=1 -sSTACK_SIZE=33554432 --no-entry \
-sALLOW_MEMORY_GROWTH -sMODULARIZE -sEXPORT_ES6 -sENVIRONMENT=web,node \
-sEXPORTED_FUNCTIONS=_wiz_loom_init,_wiz_loom_html,_wiz_loom_step,_wiz_loom_effect,_wiz_loom_requests,_wiz_loom_consume,_wiz_loom_editor_span,_wiz_loom_editor_index,_wiz_retain,_wiz_release,_free \
-sEXPORTED_RUNTIME_METHODS=stringToNewUTF8,UTF8ToString \
-sDEFAULT_LIBRARY_FUNCS_TO_INCLUDE=\$stringToNewUTF8,\$UTF8ToString" \
  build web/source-ui.wiz -o "$OUT/wiz-source-ui.mjs" --no-main)
echo "built $OUT/wiz-source-ui.mjs"
