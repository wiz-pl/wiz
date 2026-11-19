#!/bin/sh
# Build the playground's UI module: web/playground-ui.wiz (the page as one Loom app,
# with lib/Web/{Loom,Playground,Editor}.wiz) compiled to WebAssembly. The page mounts it
# with web/framework/driver.js and calls its `wiz_loom_*` exports; the engine is a
# separate module (web/build-playground.sh), so a user program's trap cannot lose the UI
# state, and no user code ever runs in this one.
#
#   usage: web/build-playground-ui.sh [OUT] [--gmp-src GMP.tar.xz]
#   (OUT default web/out; needs .lake/build/bin/wiz and the library in lib/)
#
# It is a second output beside web/build-playground.sh's wiz-playground.mjs; the page
# loads it only for `?ui=loom` and falls back to its static markup when it is absent.
set -e
ROOT=$(cd "$(dirname "$0")/.." && pwd)
# without emcc on the PATH, run again with Emscripten from nixpkgs
if ! command -v emcc >/dev/null; then exec nix shell nixpkgs#emscripten -c "$0" "$@"; fi
GMPSRC=
case "${2:-}" in --gmp-src) GMPSRC=$(cd "$(dirname "$3")" && pwd)/$(basename "$3") ;; esac
OUT=$(mkdir -p "${1:-$ROOT/web/out}" && cd "${1:-$ROOT/web/out}" && pwd)
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
-sEXPORTED_FUNCTIONS=_wiz_loom_init,_wiz_loom_html,_wiz_loom_step,_wiz_loom_show,_wiz_loom_fail,_wiz_loom_status,_wiz_loom_enable,_wiz_loom_engine,_wiz_loom_text,_wiz_retain,_wiz_release,_free \
-sEXPORTED_RUNTIME_METHODS=stringToNewUTF8,UTF8ToString \
-sDEFAULT_LIBRARY_FUNCS_TO_INCLUDE=\$stringToNewUTF8,\$UTF8ToString" \
  build web/playground-ui.wiz -o "$OUT/wiz-playground-ui.mjs" --no-main)
# The page loads the module and the driver at runtime (`?ui=loom`); both live beside
# playground.js, also under a framework/ subdirectory for the framework's modules.
mkdir -p "$OUT/framework"
cp "$ROOT/web/framework/driver.js" "$ROOT/web/framework/runtime.js" \
  "$ROOT/web/framework/mount.js" "$OUT/framework/"
echo "built $OUT/wiz-playground-ui.mjs"
