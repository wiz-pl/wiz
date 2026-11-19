#!/bin/sh
# Test the playground's Loom components (lib/Web/Playground.wiz's output pane and
# lib/Web/Editor.wiz's editor): render and diff them with the Wiz compiler, then apply the
# patches to the SSR HTML in the Node test double of the DOM (web/framework/minidom.mjs)
# and compare with the next state's SSR. No browser and no Emscripten (unlike
# web/test.sh).
#
#   usage: web/playground-loom-test.sh
#          WIZ=/path/to/wiz web/playground-loom-test.sh
set -eu
ROOT=$(cd "$(dirname "$0")/.." && pwd)
WIZ=${WIZ:-$ROOT/.lake/build/bin/wiz}
[ -x "$WIZ" ] || { echo "no wiz binary at $WIZ (build it, or set WIZ=)" >&2; exit 1; }
OUT=$(mktemp -d)
trap 'rm -rf "$OUT"' EXIT

# The output pane (increment 1 of the Loom port).
set -- run -I "$ROOT/lib" "$ROOT/web/playground_loom_gen.wiz"
if [ -n "${WIZ_CFLAGS:-}" ]; then set -- "$@" --cflags "$WIZ_CFLAGS"; fi
if [ -n "${WIZ_LDFLAGS:-}" ]; then set -- "$@" --ldflags "$WIZ_LDFLAGS"; fi
"$WIZ" "$@" > "$OUT/fixture.json"
node "$ROOT/web/playground_loom_test.mjs" "$OUT/fixture.json"

# The editor (increment 2): a Loom.LiveApp whose input's payload is the textarea's text.
set -- run -I "$ROOT/lib" "$ROOT/web/playground_editor_gen.wiz"
if [ -n "${WIZ_CFLAGS:-}" ]; then set -- "$@" --cflags "$WIZ_CFLAGS"; fi
if [ -n "${WIZ_LDFLAGS:-}" ]; then set -- "$@" --ldflags "$WIZ_LDFLAGS"; fi
"$WIZ" "$@" > "$OUT/editor.json"
node "$ROOT/web/playground_editor_test.mjs" "$OUT/editor.json"
