#!/bin/sh
# Build the web module: web/Web.wiz → C (the Wiz compiler) → WebAssembly (Emscripten),
# with the reference-counting runtime and mini-gmp (GMP's portable subset) for bignums.
# The documentation's pages (`wiz doc --web`) render their signatures with it
# (`wiz_doc_*`, web/scroll.js); the standalone infoview page is JavaScript now
# (web/playground-lsp.js) and does not load it. The build also populates OUT with the pages'
# scripts, which is the directory `wiz lsp --ws` serves.
#   usage: web/build.sh [OUT] [--gmp-src GMP.tar.xz] [--from DIR] [--opt LEVEL]
#   (OUT default web/out; needs .lake/build/bin/wiz. --gmp-src: mini-gmp from that GMP
#   source tarball instead of nixpkgs', for builds without nix, such as the release job.
#   --from DIR, or WIZ_WEB_FROM=DIR: copy the module a Nix build made instead
#   (`nix build .#wiz-web`), for CI and anyone who has the store path; local use is
#   unchanged. --opt LEVEL: the C optimisation level (1, 2, 3); the default is the
#   compiler's -O2. emcc runs binaryen's `wasm-opt` at -O2 and up, which is the build's
#   memory peak; -O1 is kept to a smaller module for a machine that cannot fit it.)
# wasm64 (-sMEMORY64) keeps the runtime's 64-bit words and 62-bit small numbers as they
# are. Web.wiz is a library (stage 9g): the page calls its exports `wiz_doc_init` and
# `wiz_doc_step` on every event, so nothing waits inside Wasm (no Asyncify).
set -e
ROOT=$(cd "$(dirname "$0")/.." && pwd)
# without emcc on the PATH, run again with Emscripten from nixpkgs
if ! command -v emcc >/dev/null; then exec nix shell --inputs-from "$ROOT" nixpkgs#emscripten -c "$0" "$@"; fi
GMPSRC=
FROM=${WIZ_WEB_FROM:-}
OPT=
OUT_DIR=
while [ $# -gt 0 ]; do
  case "$1" in
    --gmp-src) GMPSRC=$(cd "$(dirname "$2")" && pwd)/$(basename "$2"); shift 2 ;;
    --from) FROM=$2; shift 2 ;;
    --opt) OPT=$2; shift 2 ;;
    *) OUT_DIR=$1; shift ;;
  esac
done
OUT=$(mkdir -p "${OUT_DIR:-$ROOT/web/out}" && cd "${OUT_DIR:-$ROOT/web/out}" && pwd)
# A module built elsewhere (packages.wiz-web): same files, no Emscripten, no nix.
if [ -n "$FROM" ]; then
  [ -f "$FROM/wiz-infoview.mjs" ] || {
    echo "build: $FROM/wiz-infoview.mjs is missing (--from $FROM)" >&2; exit 1; }
  # the store's files are read-only and its `gmp/` is a 0555 directory: `--no-preserve=mode`
  # (GNU cp) copies them writable, so this OUT can be built into later
  cp -R --no-preserve=mode "$FROM"/. "$OUT"/
  echo "copied $OUT/wiz-infoview.mjs from $FROM"
  exit 0
fi
# without emcc on the PATH, run again with Emscripten from nixpkgs
if ! command -v emcc >/dev/null; then
  set --; [ -z "$OUT_DIR" ] || set -- "$OUT_DIR"
  [ -z "$GMPSRC" ] || set -- "$@" --gmp-src "$GMPSRC"
  [ -z "$OPT" ] || set -- "$@" --opt "$OPT"
  exec nix shell nixpkgs#emscripten -c "$0" "$@"
fi
WIZ=${WIZ:-$ROOT/.lake/build/bin/wiz}
# (after the compiler's own -O2, so emcc's last -O wins)
# `-ffile-prefix-map`: the module is built in a checkout and written to an output
# directory whose absolute paths would otherwise be recorded in the Wasm (the release
# scan caught `/home/runner/work/wiz/wiz/web-out`). Map both to `.`; without `-g` the
# flags still rewrite `__FILE__`/the generated C's path.
CFLAGS="-I$OUT/gmp -DWIZ_NO_THREADS -ffile-prefix-map=$ROOT=. -ffile-prefix-map=$OUT=."
[ -z "$OPT" ] || CFLAGS="$CFLAGS -O$OPT"

# 1. mini-gmp from GMP's source tarball, behind a <gmp.h>
if [ ! -f "$OUT/gmp/mini-gmp.c" ]; then
  mkdir -p "$OUT/gmp"
  SRC=${GMPSRC:-$(nix build --inputs-from "$ROOT" --no-link --print-out-paths nixpkgs#gmp.src)}
  tar -C "$OUT/gmp" --strip-components=2 -xf "$SRC" --wildcards '*/mini-gmp/mini-gmp.[ch]'
  printf '#include "mini-gmp.h"\n' > "$OUT/gmp/gmp.h"
fi

# 2. Wiz → C → wasm, as an ES module the documentation's pages load (web/scroll.js):
# `wiz build` with emcc as the C compiler, mini-gmp in place of -lgmp (--gmp), and
# web/js.c by Web.wiz's `link_c "js.c"` (stage 9f). `--no-main` (9g): the module is
# Web.wiz's exports, linked without a `main` (emcc's --no-entry). It writes
# OUT/wiz-infoview.c beside the module (the name is historical: the infoview used to be
# this module; `wiz doc` and the toolchain look for wiz-infoview.mjs).
(cd "$ROOT" && "$WIZ" --cc emcc --cflags "$CFLAGS" --gmp "$OUT/gmp/mini-gmp.c" \
  --ldflags "-sMEMORY64=1 -sSTACK_SIZE=33554432 --no-entry \
-sALLOW_MEMORY_GROWTH -sMODULARIZE -sEXPORT_ES6 -sENVIRONMENT=web,node \
-sEXPORTED_FUNCTIONS=_wiz_web_init,_wiz_web_step,_wiz_doc_init,_wiz_doc_step,_wiz_release,_free \
-sEXPORTED_RUNTIME_METHODS=stringToNewUTF8 \
-sDEFAULT_LIBRARY_FUNCS_TO_INCLUDE=\$stringToNewUTF8,\$UTF8ToString" \
  build web/Web.wiz -o "$OUT/wiz-infoview.mjs" --no-main)
cp "$ROOT/web/infoview.html" "$ROOT/web/infoview.js" "$ROOT/web/playground-lsp.js" \
  "$ROOT/web/lsp-client.js" "$ROOT/web/widgets.js" "$ROOT/web/widgets.css" \
  "$ROOT/web/hover.js" "$ROOT/web/squiggles.js" \
  "$ROOT/web/completions.js" "$ROOT/web/scroll.js" "$ROOT/web/scroll-search.js" \
  "$ROOT/web/scroll.css" "$ROOT/web/highlight.css" "$ROOT/web/overlays.css" \
  "$ROOT/web/doc-live.js" "$ROOT/web/doc-live.css" "$OUT/"
mkdir -p "$OUT/framework"
cp "$ROOT/web/framework/mount.js" "$ROOT/web/framework/driver.js" \
  "$ROOT/web/framework/runtime.js" "$ROOT/web/framework/editor-text.js" "$OUT/framework/"
# 3. The standalone infoview's runtime (`web/infoview.js` mounts it, stage 5).
sh "$ROOT/web/build-infoview-ui.sh" "$OUT"
sh "$ROOT/web/build-docs-ui.sh" "$OUT"
sh "$ROOT/web/build-doc-live-ui.sh" "$OUT"
echo "built $OUT/wiz-infoview.mjs"
