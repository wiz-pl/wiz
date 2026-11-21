#!/bin/sh
# Tests for the generated benchmark page and the check that guards it: the generator's
# fixtures (web/build-bench_test.py), then a minimal assembled site whose benchmark page
# is generated from the JSON and whose local links must resolve (web/check-site.sh).
# No compiler, browser or Wasm build is needed: empty stand-ins are enough for the layout
# checks, which is what makes this runnable in the docs style job.
#
#   usage: web/test-bench.sh
set -eu
ROOT=$(cd "$(dirname "$0")/.." && pwd)
OUT=$(mktemp -d)
trap 'rm -rf "$OUT"' EXIT

python3 "$ROOT/web/build-bench_test.py"

# build-site.sh copies these; check-site.sh only asks that they exist.
SITE=$OUT/site
WEB=$OUT/web
mkdir -p "$WEB"
for f in docs/index.html docs/api.html docs/api.json docs/search.js docs/scroll.css \
         playground/index.html playground/playground.js playground/playground.css playground/overlays.css \
         playground/wiz-playground.mjs \
         playground/wiz-playground.wasm; do
  mkdir -p "$SITE/$(dirname "$f")"
  : > "$SITE/$f"
done
: > "$WEB/wiz-playground.mjs"
: > "$WEB/wiz-playground.wasm"
: > "$WEB/wiz-playground-ui.mjs"

sh "$ROOT/web/build-site.sh" "$SITE" "$WEB" >/dev/null
sh "$ROOT/web/check-site.sh" "$SITE"

# A benchmark page that is not the generated one must fail the site check.
cp "$SITE/bench/index.html" "$OUT/good.html"
sed 's/generated-bench-page/hand-written-page/' "$OUT/good.html" > "$SITE/bench/index.html"
if sh "$ROOT/web/check-site.sh" "$SITE" >/dev/null 2>&1; then
  echo "test-bench: check-site accepted a non-generated benchmark page" >&2
  exit 1
fi

echo "test-bench: ok (fixtures, generated page, site check)"
