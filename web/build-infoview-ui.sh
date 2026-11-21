#!/bin/sh
# Build the standalone infoview's runtime: web/infoview-ui.wiz (the page as one Loom
# app, with lib/Web/{Loom,Goals,Hover,InfoviewPage}.wiz) compiled to WebAssembly.
# The page mounts it with web/framework/mount.js; the language server stays a
# WebSocket in web/playground-lsp.js, so the runtime holds no socket.
#
#   usage: web/build-infoview-ui.sh [OUT] [--gmp-src GMP.tar.xz] [--from DIR]
set -e
ROOT=$(cd "$(dirname "$0")/.." && pwd)
GMPSRC=
FROM=${WIZ_INFOVIEW_UI_FROM:-}
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
  [ -f "$FROM/wiz-infoview-ui.mjs" ] || {
    echo "build-infoview-ui: $FROM/wiz-infoview-ui.mjs is missing (--from $FROM)" >&2; exit 1; }
  cp -R --no-preserve=mode "$FROM"/. "$OUT"/
  echo "copied $OUT/wiz-infoview-ui.mjs from $FROM"
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
  --ldflags "-sMEMORY64=1 -sSTACK_SIZE=67108864 --no-entry \
-sALLOW_MEMORY_GROWTH -sMODULARIZE -sEXPORT_ES6 -sENVIRONMENT=web,node \
-sEXPORTED_FUNCTIONS=_wiz_loom_init,_wiz_loom_html,_wiz_loom_step,_wiz_loom_effect,_wiz_loom_requests,_wiz_loom_consume,_wiz_loom_editor_index,_wiz_loom_editor_segments,_wiz_loom_editor_segments_index,_wiz_loom_editor_items,_wiz_loom_editor_popup,_wiz_loom_editor_move,_wiz_loom_editor_accept,_wiz_loom_editor_trigger,_wiz_loom_editor_position,_wiz_loom_editor_position_index,_wiz_loom_editor_offset,_wiz_loom_editor_offset_index,_wiz_loom_editor_utf16,_wiz_loom_editor_editor_offset,_wiz_loom_editor_line_end,_wiz_loom_editor_line_end_index,_wiz_loom_editor_indent,_wiz_retain,_wiz_release,_free \
-sEXPORTED_RUNTIME_METHODS=stringToNewUTF8,UTF8ToString \
-sDEFAULT_LIBRARY_FUNCS_TO_INCLUDE=\$stringToNewUTF8,\$UTF8ToString" \
  build web/infoview-ui.wiz -o "$OUT/wiz-infoview-ui.mjs" --no-main)
echo "built $OUT/wiz-infoview-ui.mjs"
