#!/bin/sh
# Test the playground's output pane as a Loom component (lib/Web/Playground.wiz):
# render and diff it with the Wiz compiler, then apply the patches to the SSR HTML in
# the Node test double of the DOM (web/framework/minidom.mjs) and compare with the next
# state's SSR. No browser and no Emscripten (unlike web/test.sh).
#
#   usage: web/playground-loom-test.sh
#          WIZ=/path/to/wiz web/playground-loom-test.sh
set -eu
ROOT=$(cd "$(dirname "$0")/.." && pwd)
WIZ=${WIZ:-$ROOT/.lake/build/bin/wiz}
[ -x "$WIZ" ] || { echo "no wiz binary at $WIZ (build it, or set WIZ=)" >&2; exit 1; }
OUT=$(mktemp -d)
trap 'rm -rf "$OUT"' EXIT

set -- run -I "$ROOT/lib" "$ROOT/web/playground_loom_gen.wiz"
if [ -n "${WIZ_CFLAGS:-}" ]; then set -- "$@" --cflags "$WIZ_CFLAGS"; fi
if [ -n "${WIZ_LDFLAGS:-}" ]; then set -- "$@" --ldflags "$WIZ_LDFLAGS"; fi
"$WIZ" "$@" > "$OUT/fixture.json"
node "$ROOT/web/playground_loom_test.mjs" "$OUT/fixture.json"
