#!/bin/sh
# Test the browser half of lib/Web/React.wiz: render a component tree and its patches
# with the Wiz compiler, then apply the patches to the SSR HTML in a Node test double
# of the DOM (web/framework/minidom.mjs) and compare with the SSR of the next state.
# No browser and no Emscripten are needed (unlike web/test.sh).
#
#   usage: web/framework/test.sh
#          WIZ=/path/to/wiz web/framework/test.sh
set -eu
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
WIZ=${WIZ:-$ROOT/.lake/build/bin/wiz}
[ -x "$WIZ" ] || { echo "no wiz binary at $WIZ (build it, or set WIZ=)" >&2; exit 1; }
OUT=$(mktemp -d)
trap 'rm -rf "$OUT"' EXIT

# The compiler flags (GMP's include and library) come from /workspace/wiz-env.sh in the
# dev shell; without them a plain `wiz run` still works where GMP is in the default path.
set -- run "$ROOT/web/framework/gen.wiz"
if [ -n "${WIZ_CFLAGS:-}" ]; then set -- "$@" --cflags "$WIZ_CFLAGS"; fi
if [ -n "${WIZ_LDFLAGS:-}" ]; then set -- "$@" --ldflags "$WIZ_LDFLAGS"; fi
"$WIZ" "$@" > "$OUT/fixture.json"
node "$ROOT/web/framework/test.mjs" "$OUT/fixture.json"
