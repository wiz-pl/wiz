#!/bin/sh
# Test the playground's React UI (?ui=react) without a browser and without Emscripten:
# concatenate web/ui-framework.wiz + web/playground-ui.wiz + the fixture, render the three
# models with `wiz run`, and hand the JSON to web/playground_ui_test.mjs, which applies the
# patch list to the SSR HTML in the minidom double and drives web/framework/driver.js's
# `startModel` with a fake Wasm module.
#
#   usage: web/test-playground-ui.sh
#          WIZ=/path/to/wiz web/test-playground-ui.sh
set -eu
ROOT=$(cd "$(dirname "$0")/.." && pwd)
WIZ=${WIZ:-$ROOT/.lake/build/bin/wiz}
[ -x "$WIZ" ] || { echo "no wiz binary at $WIZ (build it, or set WIZ=)" >&2; exit 1; }
OUT=$(mktemp -d)
trap 'rm -rf "$OUT"' EXIT

# One module: the framework's names, the pane's model/view, and the fixture's main.
SRC="$OUT/playground-ui.wiz"
{
  cat "$ROOT/web/ui-framework.wiz"
  cat "$ROOT/web/playground-ui.wiz"
  cat "$ROOT/web/playground-ui-fixture.wiz"
} > "$SRC"

set -- run "$SRC"
if [ -n "${WIZ_CFLAGS:-}" ]; then set -- "$@" --cflags "$WIZ_CFLAGS"; fi
if [ -n "${WIZ_LDFLAGS:-}" ]; then set -- "$@" --ldflags "$WIZ_LDFLAGS"; fi
"$WIZ" "$@" > "$OUT/fixture.json"
node "$ROOT/web/playground_ui_test.mjs" "$OUT/fixture.json"
