#!/bin/sh
# Build the playground's UI module: web/playground-ui.wiz (the page as one Loom app,
# with lib/Web/{Loom,Playground,Editor}.wiz) compiled to WebAssembly. The page mounts it
# with web/framework/driver.js and calls its `wiz_loom_*` exports; the engine is a
# separate module (web/build-playground.sh), so a user program's trap cannot lose the UI
# state, and no user code ever runs in this one.
#
#   usage: web/build-playground-ui.sh [OUT] [--gmp-src GMP.tar.xz] [--from DIR]
#   (OUT default web/out; needs .lake/build/bin/wiz and the library in lib/.
#   --from DIR, or WIZ_PLAYGROUND_UI_FROM=DIR: copy the module a Nix build made instead
#   (`nix build .#wiz-playground-ui`); local use is unchanged.)
#
# The page (`web/playground.js`) mounts it; there is no static fallback, so this is
# part of the playground build, not an option.
set -e
ROOT=$(cd "$(dirname "$0")/.." && pwd)
GMPSRC=
FROM=${WIZ_PLAYGROUND_UI_FROM:-}
OUT_DIR=
while [ $# -gt 0 ]; do
  case "$1" in
    --gmp-src) GMPSRC=$(cd "$(dirname "$2")" && pwd)/$(basename "$2"); shift 2 ;;
    --from) FROM=$2; shift 2 ;;
    *) OUT_DIR=$1; shift ;;
  esac
done
OUT=$(mkdir -p "${OUT_DIR:-$ROOT/web/out}" && cd "${OUT_DIR:-$ROOT/web/out}" && pwd)
# A module built elsewhere (packages.wiz-playground-ui): same files, no Emscripten, no nix.
if [ -n "$FROM" ]; then
  [ -f "$FROM/wiz-playground-ui.mjs" ] || {
    echo "build-playground-ui: $FROM/wiz-playground-ui.mjs is missing (--from $FROM)" >&2; exit 1; }
  cp -R --no-preserve=mode "$FROM"/. "$OUT"/
  echo "copied $OUT/wiz-playground-ui.mjs from $FROM"
  exit 0
fi
# without emcc on the PATH, run again with Emscripten from nixpkgs
if ! command -v emcc >/dev/null; then
  set --; [ -z "$OUT_DIR" ] || set -- "$OUT_DIR"
  [ -z "$GMPSRC" ] || set -- "$@" --gmp-src "$GMPSRC"
  exec nix shell nixpkgs#emscripten -c "$0" "$@"
fi
WIZ=${WIZ:-$ROOT/.lake/build/bin/wiz}

# mini-gmp, as web/build-playground.sh does (share OUT/gmp when both are built)
if [ ! -f "$OUT/gmp/mini-gmp.c" ]; then
  mkdir -p "$OUT/gmp"
  SRC=${GMPSRC:-$(nix build --no-link --print-out-paths nixpkgs#gmp.src)}
  tar -C "$OUT/gmp" --strip-components=2 -xf "$SRC" --wildcards '*/mini-gmp/mini-gmp.[ch]'
  printf '#include "mini-gmp.h"\n' > "$OUT/gmp/gmp.h"
fi

# Wiz → C → wasm. `-I lib` supplies the worktree's Web.Loom/Web.Playground/Web.Editor
# (a release toolchain's own library is searched first, so this is for a checkout).
(cd "$ROOT" && "$WIZ" -I "$ROOT/lib" --cc emcc --cflags "-I$OUT/gmp -DWIZ_NO_THREADS" \
  --gmp "$OUT/gmp/mini-gmp.c" \
  --ldflags "-sMEMORY64=1 -sSTACK_SIZE=67108864 --no-entry \
-sALLOW_MEMORY_GROWTH -sMODULARIZE -sEXPORT_ES6 -sENVIRONMENT=web,node \
-sEXPORTED_FUNCTIONS=_wiz_loom_init,_wiz_loom_html,_wiz_loom_step,_wiz_loom_effect,_wiz_loom_requests,_wiz_loom_consume,_wiz_loom_editor_index,_wiz_loom_editor_segments,_wiz_loom_editor_segments_index,_wiz_loom_editor_items,_wiz_loom_editor_popup,_wiz_loom_editor_move,_wiz_loom_editor_key,_wiz_loom_editor_accept,_wiz_loom_editor_trigger,_wiz_loom_editor_position,_wiz_loom_editor_position_index,_wiz_loom_editor_offset,_wiz_loom_editor_offset_index,_wiz_loom_editor_utf16,_wiz_loom_editor_editor_offset,_wiz_loom_editor_line_end,_wiz_loom_editor_line_end_index,_wiz_loom_editor_indent,_wiz_loom_editor_item_title,_wiz_loom_editor_ask_key,_wiz_loom_editor_span,_wiz_loom_editor_range_text,_wiz_loom_hover_target,_wiz_loom_index_build,_wiz_loom_index_size,_wiz_loom_index_term,_wiz_loom_index_goal,_wiz_loom_index_declarations,_wiz_loom_index_declaration,_wiz_retain,_wiz_release,_free \
-sEXPORTED_RUNTIME_METHODS=stringToNewUTF8,UTF8ToString \
-sDEFAULT_LIBRARY_FUNCS_TO_INCLUDE=\$stringToNewUTF8,\$UTF8ToString" \
  build web/playground-ui.wiz -o "$OUT/wiz-playground-ui.mjs" --no-main)
# The page loads the module and the mount contract at runtime; both live beside
# playground.js, also under a framework/ subdirectory for the framework's modules.
mkdir -p "$OUT/framework"
cp "$ROOT/web/framework/driver.js" "$ROOT/web/framework/runtime.js" \
  "$ROOT/web/framework/mount.js" "$OUT/framework/"
echo "built $OUT/wiz-playground-ui.mjs"
