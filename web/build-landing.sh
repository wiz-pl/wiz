#!/bin/sh
# Build the landing page: `web/landing/index.html` (the template), the snippet files
# and — when `WIZ` is available — the Loom island's first paint.
#
#   usage: web/build-landing.sh [OUT] [--island JSON] [--from DIR]
#   (OUT default web/out. The page is written to OUT/landing/index.html; build-site.sh
#   publishes that, not the template. --island is web/landing/static_gen.wiz's JSON
#   (`wiz run -I lib web/landing/static_gen.wiz`); --from copies a page a Nix build
#   made, as the playground's scripts do.)
#
# This step needs no Emscripten: the Wasm module is web/build-landing-ui.sh. It needs
# `wiz` only for the island's SSR hash; without one the page is built with the static
# explainer, which is also the no-JavaScript form (a docs-only tree can use that).
set -e
ROOT=$(cd "$(dirname "$0")/.." && pwd)
OUT_DIR=
ISLAND=
FROM=
while [ $# -gt 0 ]; do
  case "$1" in
    --island) ISLAND=$2; shift 2 ;;
    --from) FROM=$2; shift 2 ;;
    *) OUT_DIR=$1; shift ;;
  esac
done
OUT=$(mkdir -p "${OUT_DIR:-$ROOT/web/out}/landing" && cd "${OUT_DIR:-$ROOT/web/out}/landing" && pwd)
if [ -n "$FROM" ]; then
  [ -f "$FROM/index.html" ] || {
    echo "build-landing: $FROM/index.html is missing (--from $FROM)" >&2; exit 1; }
  cp -R --no-preserve=mode "$FROM"/. "$OUT"/
  echo "copied $OUT/index.html from $FROM"
  exit 0
fi
if [ -z "$ISLAND" ]; then
  WIZ=${WIZ:-$ROOT/.lake/build/bin/wiz}
  if [ -x "$WIZ" ] && [ -f "$ROOT/web/landing/static_gen.wiz" ]; then
    TMP=$(mktemp)
    trap 'rm -f "$TMP"' EXIT
    "$WIZ" run -I "$ROOT/lib" "$ROOT/web/landing/static_gen.wiz" > "$TMP"
    ISLAND=$TMP
  else
    echo "build-landing: no $WIZ; the quantity section stays static (pass --island JSON)" >&2
  fi
fi
if [ -n "$ISLAND" ]; then
  python3 "$ROOT/web/build-landing.py" --root "$ROOT" --out "$OUT/index.html" --island "$ISLAND"
else
  python3 "$ROOT/web/build-landing.py" --root "$ROOT" --out "$OUT/index.html"
fi
cp "$ROOT/web/landing/landing.css" "$OUT/landing.css"
# The carousel enhancement and the island mount are part of the page when they exist
# (the first slices land them; a docs-only build may not have them yet).
for f in carousel.js app.js; do
  [ -f "$ROOT/web/landing/$f" ] && cp "$ROOT/web/landing/$f" "$OUT/$f"
done
# The mount contract is a static import of app.js; copy it beside the page, as
# build-playground-ui.sh does for the playground.
mkdir -p "$OUT/framework"
cp "$ROOT/web/framework/mount.js" "$ROOT/web/framework/driver.js" \
  "$ROOT/web/framework/runtime.js" "$ROOT/web/framework/adopt.js" "$OUT/framework/"
echo "built $OUT/index.html"
