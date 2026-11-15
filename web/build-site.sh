#!/bin/sh
# Assemble the parts of the published site that `wiz doc` does not write:
#
#   /index.html            the landing page (web/landing/)
#   /landing.css
#   /playground/           the static playground: web/playground.html and its scripts,
#                          plus web/build-playground.sh's wiz-playground.mjs/.wasm
#
# The documentation is generated separately, into SITE/docs:
#
#   .lake/build/bin/wiz doc --lib -o doc-site/docs --web web/out --source-url …
#
# and the Wasm modules are built by web/build.sh and web/build-playground.sh into WEB.
#
#   usage: web/build-site.sh [SITE] [WEB]          (defaults: doc-site, web/out)
set -eu
ROOT=$(cd "$(dirname "$0")/.." && pwd)
SITE=${1:-$ROOT/doc-site}
WEB=${2:-$ROOT/web/out}
mkdir -p "$SITE/playground"

# The landing page, at the site root. Its links are relative (docs/, playground/), so
# the tree works at a domain root and under a project site's prefix alike.
cp "$ROOT/web/landing/index.html" "$SITE/index.html"
cp "$ROOT/web/landing/landing.css" "$SITE/landing.css"

# The playground page is index.html, so /playground/ is a directory index; its own
# links (playground.css, playground.js, wiz-playground.mjs) are relative to it.
cp "$ROOT/web/playground.html" "$SITE/playground/index.html"
for f in playground.js playground.css playground-values.js \
         lsp-client.js goals.js playground-lsp.js tagged.js; do
  cp "$ROOT/web/$f" "$SITE/playground/$f"
done

# The module and its side-car wasm; a missing one would publish a playground that
# cannot load, so stop here instead.
for f in wiz-playground.mjs wiz-playground.wasm; do
  if [ ! -f "$WEB/$f" ]; then
    echo "build-site: $WEB/$f is missing: run web/build-playground.sh $WEB first" >&2
    exit 1
  fi
  cp "$WEB/$f" "$SITE/playground/$f"
done

echo "site: landing at $SITE/index.html, playground at $SITE/playground/index.html"
