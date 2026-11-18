#!/bin/sh
# Test the playground's Loom UI (?ui=react) without a browser: concatenate
# web/ui-framework.wiz + web/playground-ui.wiz + the fixture, render the three models with
# `wiz run`, and hand the JSON to web/playground_ui_test.mjs, which applies the patch list
# to the SSR HTML in the minidom double and drives web/framework/driver.js's `startModel`
# with a fake Wasm module.
#
#   usage: web/test-playground-ui.sh [FIXTURE_OUT] [MODULE.mjs]
#          WIZ=/path/to/wiz web/test-playground-ui.sh
#
# FIXTURE_OUT keeps the rendered fixture there (web/test.sh reuses it after
# web/build-playground.sh has built the module); MODULE.mjs also checks the real Wasm
# module's `wiz_ui_html`/`wiz_ui_patch` against the same fixture.
set -eu
ROOT=$(cd "$(dirname "$0")/.." && pwd)
WIZ=${WIZ:-$ROOT/.lake/build/bin/wiz}
[ -x "$WIZ" ] || { echo "no wiz binary at $WIZ (build it, or set WIZ=)" >&2; exit 1; }
FIXTURE_OUT=${1:-}
MODULE=${2:-}
OUT=$(mktemp -d)
trap 'rm -rf "$OUT"' EXIT

# One module: the framework's names (and imports), the pane's model/view, the fixture's main.
SRC="$OUT/playground-ui.wiz"
{
  cat "$ROOT/web/ui-framework.wiz"
  cat "$ROOT/web/playground-ui.wiz"
  cat "$ROOT/web/playground-ui-fixture.wiz"
} > "$SRC"

set -- run "$SRC"
if [ -n "${WIZ_CFLAGS:-}" ]; then set -- "$@" --cflags "$WIZ_CFLAGS"; fi
if [ -n "${WIZ_LDFLAGS:-}" ]; then set -- "$@" --ldflags "$WIZ_LDFLAGS"; fi
FIXTURE="$OUT/fixture.json"
"$WIZ" "$@" > "$FIXTURE"

# Keep a copy for web/test.sh's Wasm check of the same fixture.
if [ -n "$FIXTURE_OUT" ]; then cp "$FIXTURE" "$FIXTURE_OUT"; fi
node "$ROOT/web/playground_ui_test.mjs" "$FIXTURE" "$MODULE"
