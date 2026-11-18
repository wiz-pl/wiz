#!/bin/sh
# Test the widget half with no browser: render every widget kind and an update with the
# Wiz compiler, then apply the patches in Node using web/framework/runtime.js and
# web/framework/minidom.mjs (the same pair the Loom framework test uses).
#
#   usage: web/widget/test.sh
#          WIZ=/path/to/wiz web/widget/test.sh
set -eu
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
WIZ=${WIZ:-$ROOT/.lake/build/bin/wiz}
[ -x "$WIZ" ] || { echo "no wiz binary at $WIZ (build it, or set WIZ=)" >&2; exit 1; }
OUT=$(mktemp -d)
trap 'rm -rf "$OUT"' EXIT

set -- run -I "$ROOT/lib" "$ROOT/web/widget/gen.wiz"
if [ -n "${WIZ_CFLAGS:-}" ]; then set -- "$@" --cflags "$WIZ_CFLAGS"; fi
if [ -n "${WIZ_LDFLAGS:-}" ]; then set -- "$@" --ldflags "$WIZ_LDFLAGS"; fi
"$WIZ" "$@" > "$OUT/fixture.json"
node "$ROOT/web/widget/test.mjs" "$OUT/fixture.json"
