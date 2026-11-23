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
: > "$WEB/wiz-playground-ui.wasm"
# build-site publishes the generated static-complete page, not the source template.
cat > "$WEB/playground.html" <<'PAGE'
<!doctype html><html><body>
<div id="app" data-wiz-island="loom/1" data-wiz-ssr="t1-00000000-0-0">
<header></header><main><textarea id="editor"></textarea><select id="preset"></select></main><footer></footer>
</div>
</body></html>
PAGE
# The landing page is generated too (web/build-landing.sh); this stand-in has the
# shape check-site.sh asks for, without a compiler or the Wasm island.
mkdir -p "$WEB/landing"
cp "$ROOT/web/landing/landing.css" "$WEB/landing/landing.css"
cat > "$WEB/landing/index.html" <<'PAGE'
<!doctype html><html lang="en"><head><meta charset="utf-8">
<title>Wiz — a dependently typed language, self-hosted</title>
<link rel="stylesheet" href="landing.css"></head><body>
<main id="main">
<div class="carousel" id="carousel" role="region" aria-label="Wiz code snippets">
<div class="carousel-tabs" role="tablist" aria-label="Snippets">
<a class="tab" role="tab" href="#/s/quantities" aria-controls="/s/quantities" aria-selected="true">Quantities</a>
<article class="slide" id="/s/quantities" role="tabpanel" tabindex="0" data-active>
<h2>Quantities</h2><pre tabindex="0"><code class="language-wiz">def identity {0 A : Type} (1 x : A) : A := x</code></pre>
</article></div>
<div id="quantity-app" data-wiz-island="loom/1" data-wiz-ssr="t1-00000000-0-0"><div class="q-app q0" id="quantity-widget"><select id="q-select"></select><section class="q-panel"></section><section class="q-panel"></section><section class="q-panel"></section></div></div>
</main></body></html>
PAGE
for f in app.js wiz-landing-ui.mjs wiz-landing-ui.wasm framework/mount.js \
         framework/driver.js framework/runtime.js framework/adopt.js; do
  mkdir -p "$WEB/landing/$(dirname "$f")"
  : > "$WEB/landing/$f"
done

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
