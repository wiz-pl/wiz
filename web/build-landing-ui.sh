#!/bin/sh
# Build the landing page's quantity island: lib/Web/Landing.wiz (a Loom LiveApp) as
# wiz-landing-ui.mjs, mounted by web/landing/app.js through web/framework/mount.js.
#
#   usage: web/build-landing-ui.sh [OUT] [--gmp-src GMP.tar.xz] [--from DIR]
#   (OUT default web/out; the module and runtime are written under OUT/landing/.
#   --from DIR, or WIZ_LANDING_UI_FROM=DIR: copy a module a Nix build made.)
#
# The page's static first paint is web/build-landing.sh's job: it runs
# web/landing/static_gen.wiz, which needs no Emscripten. This script needs `wiz` and
# `emcc` (or nix to supply Emscripten).
set -e
ROOT=$(cd "$(dirname "$0")/.." && pwd)
GMPSRC=
FROM=${WIZ_LANDING_UI_FROM:-}
OUT_DIR=
while [ $# -gt 0 ]; do
  case "$1" in
    --gmp-src) GMPSRC=$(cd "$(dirname "$2")" && pwd)/$(basename "$2"); shift 2 ;;
    --from) FROM=$2; shift 2 ;;
    *) OUT_DIR=$1; shift ;;
  esac
done
OUT=$(mkdir -p "${OUT_DIR:-$ROOT/web/out}/landing" && cd "${OUT_DIR:-$ROOT/web/out}/landing" && pwd)
if [ -n "$FROM" ]; then
  [ -f "$FROM/wiz-landing-ui.mjs" ] || {
    echo "build-landing-ui: $FROM/wiz-landing-ui.mjs is missing (--from $FROM)" >&2; exit 1; }
  cp -R --no-preserve=mode "$FROM"/. "$OUT"/
  echo "copied $OUT/wiz-landing-ui.mjs from $FROM"
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
# Wiz → C → wasm, the playground UI's flags without the editor/index exports: this app
# has state, SSR, a hash and one event, and nothing else crosses the boundary.
(cd "$ROOT" && "$WIZ" -I "$ROOT/lib" --cc emcc --cflags "-I$OUT/gmp -DWIZ_NO_THREADS -ffile-prefix-map=$ROOT=. -ffile-prefix-map=$OUT=." \
  --gmp "$OUT/gmp/mini-gmp.c" \
  --ldflags "-sMEMORY64=1 -sSTACK_SIZE=33554432 --no-entry \
-sALLOW_MEMORY_GROWTH -sMODULARIZE -sEXPORT_ES6 -sENVIRONMENT=web,node \
-sEXPORTED_FUNCTIONS=_wiz_loom_init,_wiz_loom_html,_wiz_loom_ssr_hash,_wiz_loom_step,_wiz_step,_wiz_retain,_wiz_release,_free \
-sEXPORTED_RUNTIME_METHODS=stringToNewUTF8,UTF8ToString \
-sDEFAULT_LIBRARY_FUNCS_TO_INCLUDE=\$stringToNewUTF8,\$UTF8ToString" \
  build web/landing_ui.wiz -o "$OUT/wiz-landing-ui.mjs" --no-main)
mkdir -p "$OUT/framework"
cp "$ROOT/web/framework/mount.js" "$ROOT/web/framework/driver.js" \
  "$ROOT/web/framework/runtime.js" "$ROOT/web/framework/adopt.js" "$OUT/framework/"
echo "built $OUT/wiz-landing-ui.mjs"
