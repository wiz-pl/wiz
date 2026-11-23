#!/bin/sh
# Assemble the parts of the published site that `wiz doc` does not write:
#
#   /index.html            the landing page (web/landing/)
#   /landing.css
#   /bench/                benchmarks, generated from the checked-in JSON
#                          (web/build-bench.py → web/bench/index.html)
#   /guide/                the repository's prose documentation, rendered from
#                          Markdown by web/build-docs.py
#   /playground/           the playground: web/playground.html and its scripts, the
#                          Loom runtime (web/build-playground-ui.sh) and the engine
#                          (web/build-playground.sh's wiz-playground.mjs/.wasm)
#   /licenses/             the Wasm modules' notice (mini-gmp) and licence texts
#   /source/               the source reader: a `scry web` bundle plus its runtime
#                          (SOURCE_BUNDLE=DIR). The site build has no `scry` binary, so it
#                          cannot generate one; the publishing job builds scry and passes
#                          the directory (SITE_REQUIRE_SOURCE=1 makes its absence fatal).
#                          A docs-only build leaves SITE_REQUIRE_SOURCE unset and skips
#                          /source/, with a note, as `web/test-bench.sh` does.
#
# The documentation is generated separately, into SITE/docs:
#
#   .lake/build/bin/wiz doc --lib -o doc-site/docs --web web/out --source-url …
#
# and the Wasm modules are built by web/build.sh and web/build-playground.sh into WEB.
#
#   usage: web/build-site.sh [SITE] [WEB]          (defaults: doc-site, web/out)
#   SOURCE_BUNDLE=DIR web/source-bundle.sh's output; SITE_REQUIRE_SOURCE=1 for a release
set -eu
ROOT=$(cd "$(dirname "$0")/.." && pwd)
SITE=${1:-$ROOT/doc-site}
WEB=${2:-$ROOT/web/out}
mkdir -p "$SITE/playground" "$SITE/bench"

# The benchmark page is committed, so a JSON change that was not regenerated is a
# visible diff. Refuse to publish a stale copy: the numbers on the page must be the
# ones the checked-in JSON records.
python3 "$ROOT/web/build-bench.py" --check
cp "$ROOT/web/bench/index.html" "$SITE/bench/index.html"

# The landing page, at the site root. Its links are relative (docs/, bench/,
# playground/), so the tree works at a domain root and under a project site's prefix
# alike.
cp "$ROOT/web/landing/index.html" "$SITE/index.html"
cp "$ROOT/web/landing/landing.css" "$SITE/landing.css"

# The playground page is index.html, so /playground/ is a directory index; its own
# links (playground.css, playground.js, wiz-playground.mjs) are relative to it.
cp "$ROOT/web/playground.html" "$SITE/playground/index.html"
for f in playground.js playground.css overlays.css widgets.css \
         lsp-client.js widgets.js playground-lsp.js hover.js selfhost-lsp-shim.js \
         playground-engine.js squiggles.js completions.js; do
  cp "$ROOT/web/$f" "$SITE/playground/$f"
done
# The runtime's mount contract (web/framework/mount.js) is a static import of the
# playground's entry point: mount.js imports driver.js, which imports runtime.js, and both
# mount.js and driver.js import adopt.js (the island decision). Copy all of them.
mkdir -p "$SITE/playground/framework"
cp "$ROOT/web/framework/mount.js" "$ROOT/web/framework/driver.js" \
  "$ROOT/web/framework/runtime.js" "$ROOT/web/framework/editor-text.js" \
  "$ROOT/web/framework/adopt.js" "$SITE/playground/framework/"
# The page's two modules and the engine's side-car wasm. There is no static fallback:
# a missing module publishes a playground that cannot start, so stop here instead.
for f in wiz-playground.mjs wiz-playground.wasm wiz-playground-ui.mjs wiz-playground-ui.wasm; do
  if [ ! -f "$WEB/$f" ]; then
    echo "build-site: $WEB/$f is missing: run web/build-playground.sh and web/build-playground-ui.sh $WEB first" >&2
    exit 1
  fi
  cp "$WEB/$f" "$SITE/playground/$f"
done

# The static source reader: a `scry web` bundle plus the reader's Wasm runtime. A bundle
# is source + findings for one analysed tree, so the site does not synthesise one: an
# absent SOURCE_BUNDLE means no /source/ page, not an empty one. A *publishing* build
# (the docs job on master) sets SITE_REQUIRE_SOURCE=1: the reader is part of the product
# then, and a site without it is red here rather than quietly missing a page. A docs-only
# build (e.g. web/test-bench.sh) leaves it unset and skips /source/.
if [ -z "${SOURCE_BUNDLE:-}" ]; then
  if [ "${SITE_REQUIRE_SOURCE:-0}" = 1 ]; then
    echo "build-site: SITE_REQUIRE_SOURCE=1 but SOURCE_BUNDLE is unset." >&2
    echo "build-site: a publishing site must ship /source/: build scry, run" >&2
    echo "build-site:   web/source-bundle.sh SCRY DIR --ui \"\$(nix build .#wiz-source-ui --print-out-paths)\"" >&2
    echo "build-site: and pass SOURCE_BUNDLE=DIR. A docs-only build omits both." >&2
    exit 1
  fi
  echo "site: no /source/ (SOURCE_BUNDLE unset; docs-only build)"
else
  # A named bundle must be the complete reader, not a teaser: the SSR page, the host, and
  # both halves of the Emscripten runtime. `--ui` alone copies only the .mjs, so requiring
  # the wasm here is what keeps a page that cannot mount from being published.
  for f in index.html app.js app.css source-static.js \
           framework/mount.js framework/driver.js framework/runtime.js framework/adopt.js \
           wiz-source-ui.mjs wiz-source-ui.wasm \
           data/manifest.json data/findings.json; do
    if [ ! -f "$SOURCE_BUNDLE/$f" ]; then
      echo "build-site: $SOURCE_BUNDLE/$f is missing (SOURCE_BUNDLE is not a complete source bundle)" >&2
      exit 1
    fi
  done
  mkdir -p "$SITE/source"
  cp -R "$SOURCE_BUNDLE"/. "$SITE/source/"
  echo "site: source reader at $SITE/source/index.html"
fi

# The licences page: the Wasm modules (playground/, docs/) include GMP's mini-gmp, so
# the site carries its notice, the LGPL v3 and the GPL v3 (Wiz's LICENSE).
mkdir -p "$SITE/licenses"
cp "$ROOT/web/licenses/index.html" "$ROOT/web/licenses/LGPL-3.0.txt" "$SITE/licenses/"
cp "$ROOT/LICENSE" "$SITE/licenses/GPL-3.0.txt"

# Exported notebooks (docs/notebooks/*.html): checked-in, self-contained pages
# generated by tools/jupyter/wiz-nb. Copy them whole, with their relative links,
# under /notebooks/.
if [ -d "$ROOT/docs/notebooks" ]; then
  mkdir -p "$SITE/notebooks"
  for f in "$ROOT"/docs/notebooks/*.html; do
    [ -f "$f" ] && cp "$f" "$SITE/notebooks/$(basename "$f")"
  done
fi

# The prose documentation: the repository's Markdown (`docs/`, the README, and what
# they link to) rendered under /guide/, with each page's links rewritten to the
# rendered pages. A page on the site never sends the reader to a repository `.md`: the
# notebook pages' links are rewritten here too, so /notebooks/tour.html points at
# /guide/docs/… . Each page's "source" link names this commit (or `WIZ_SOURCE_URL`).
SOURCE_URL=${WIZ_SOURCE_URL:-https://github.com/wiz-pl/wiz/blob/$(git -C "$ROOT" rev-parse HEAD 2>/dev/null || echo master)}
python3 "$ROOT/web/build-docs.py" --site "$SITE" --source-url "$SOURCE_URL"

echo "site: landing at $SITE/index.html, docs at $SITE/docs, guide at $SITE/guide/docs/index.html, benchmarks at $SITE/bench/index.html, playground at $SITE/playground/index.html, notebooks at $SITE/notebooks/index.html${SOURCE_BUNDLE:+, source at $SITE/source/index.html}"
