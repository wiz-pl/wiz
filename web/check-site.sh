#!/bin/sh
# Check an assembled site without a server: the five entry points exist, every internal
# link of every page resolves, no page links to a repository Markdown file, every
# rendered page carries its source link, and the playground's module graph is complete.
# External links (http, https, mailto, data) are not fetched. Run by CI after
# web/build-site.sh, and usable locally on a `doc-site` tree.
#
#   usage: web/check-site.sh [SITE]                (default: doc-site)
set -u
ROOT=$(cd "$(dirname "$0")/.." && pwd)
SITE=${1:-doc-site}
fail=0

need() {
  if [ ! -f "$SITE/$1" ]; then
    echo "check-site: missing $SITE/$1" >&2
    fail=1
  fi
}

# The site's four entry points and the documentation's scripts.
need index.html
need landing.css
need bench/index.html
need docs/index.html
need docs/api.html
need docs/api.json
need docs/search.js
need docs/scroll.css
need playground/index.html
need playground/playground.js
need playground/framework/mount.js
need playground/framework/driver.js
need playground/framework/runtime.js
need playground/playground.css
need playground/overlays.css
need playground/widgets.css
need playground/lsp-client.js
need playground/widgets.js
need playground/playground-lsp.js
need playground/hover.js
need playground/framework/editor-text.js
need playground/squiggles.js
need playground/completions.js
need playground/selfhost-lsp-shim.js
need playground/playground-engine.js
need playground/wiz-playground.mjs
need playground/wiz-playground.wasm
# The page's runtime (its browser half, mount/driver/runtime, is checked above).
need playground/wiz-playground-ui.mjs
need playground/wiz-playground-ui.wasm
need notebooks/index.html
need licenses/index.html
need licenses/LGPL-3.0.txt
need licenses/GPL-3.0.txt
need guide/docs/index.html
need guide/guide.css

# Every local ES import of the playground's scripts resolves: a page whose module graph
# is broken would load and then do nothing, which an HTTP check would not see.
check_imports() {
  for file in "$SITE"/playground/*.js "$SITE"/playground/framework/*.js; do
    [ -f "$file" ] || continue
    dir=$(dirname "$file")
    for spec in $(grep -o 'from *"[.]/[^"]*"' "$file" | sed 's/^from *"//; s/"$//'); do
      if [ ! -f "$dir/$spec" ]; then
        echo "check-site: $(basename "$file"): import '$spec' does not resolve" >&2
        fail=1
      fi
    done
  done
}
check_imports

# Every local href/src of FILE resolves under BASE (a directory → its index.html).
# A link that starts with `/` is refused: it would break a project-site prefix.
check_links() {
  file=$1
  base=$2
  list=$(mktemp)
  grep -o 'href="[^"]*"' "$file" > "$list" 2>/dev/null || true
  grep -o 'src="[^"]*"' "$file" >> "$list" 2>/dev/null || true
  sort -u "$list" -o "$list"
  while IFS= read -r attr; do
    link=${attr#*=}
    link=${link#\"}
    link=${link%\"}
    case "$link" in
      ''|'#'*|http://*|https://*|mailto:*|data:*|javascript:*) continue ;;
    esac
    path=${link%%#*}
    path=${path%%\?*}
    [ -n "$path" ] || continue
    case "$path" in
      /*)
        echo "check-site: $file: absolute link '$link' (the site must stay relocatable)" >&2
        fail=1
        continue
        ;;
    esac
    case "$path" in
      */) target="$base/${path}index.html" ;;
      *)  target="$base/$path" ;;
    esac
    if [ ! -f "$target" ]; then
      echo "check-site: $file: link '$link' does not resolve to $target" >&2
      fail=1
    fi
  done < "$list"
  rm -f "$list"
}

if [ -f "$SITE/index.html" ]; then
  check_links "$SITE/index.html" "$SITE"
fi
# The benchmark page must still be the generated one: a hand-written stub, a truncated
# file or one that dropped the environment-dependence warning is not publishable.
if [ -f "$SITE/bench/index.html" ]; then
  for want in 'generated-bench-page' 'environment-dependent' 'How to reproduce'; do
    if ! grep -qF "$want" "$SITE/bench/index.html"; then
      echo "check-site: bench/index.html is not the generated page (missing '$want')" >&2
      fail=1
    fi
  done
  check_links "$SITE/bench/index.html" "$SITE/bench"
fi
if [ -f "$SITE/playground/index.html" ]; then
  check_links "$SITE/playground/index.html" "$SITE/playground"
fi
if [ -f "$SITE/licenses/index.html" ]; then
  check_links "$SITE/licenses/index.html" "$SITE/licenses"
fi
if [ -f "$SITE/notebooks/index.html" ]; then
  check_links "$SITE/notebooks/index.html" "$SITE/notebooks"
fi

# The whole tree: every page's internal links resolve (fragments too), no page links to
# a repository Markdown file, and every module, guide and notebook page has its source
# link.
python3 "$ROOT/web/check-links.py" "$SITE" || fail=1

if [ "$fail" -eq 0 ]; then
  echo "check-site: ok ($SITE: landing, docs, guide, benchmarks, playground, notebooks, licenses)"
else
  echo "check-site: FAILED" >&2
fi
exit "$fail"
