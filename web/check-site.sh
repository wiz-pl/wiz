#!/bin/sh
# Check an assembled site without a server: the four entry points exist, the landing
# page's and the benchmark page's local links resolve, and the playground's page and
# assets are all there. External links (http, https, mailto, data) are not fetched.
# Run by CI after web/build-site.sh, and usable locally on a `doc-site` tree.
#
#   usage: web/check-site.sh [SITE]                (default: doc-site)
set -u
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
need playground/playground.css
need playground/playground-values.js
need playground/lsp-client.js
need playground/goals.js
need playground/playground-lsp.js
need playground/tagged.js
need playground/selfhost-lsp-shim.js
need playground/wiz-playground.mjs
need playground/wiz-playground.wasm
need playground/playground-tour.wiz
need notebooks/index.html

# The playground fetches its default program from the site (`playground-tour.wiz`,
# beside the page); check-site must see the same file the page asks for, with the
# `import Prelude` the engine needs and a command that shows it is the tour.
if [ -f "$SITE/playground/playground-tour.wiz" ]; then
  if ! head -1 "$SITE/playground/playground-tour.wiz" | grep -qx 'import Prelude'; then
    echo "check-site: playground/playground-tour.wiz does not start with 'import Prelude'" >&2
    fail=1
  fi
  if ! grep -q '^#eval ' "$SITE/playground/playground-tour.wiz"; then
    echo "check-site: playground/playground-tour.wiz has no #eval (not the tour?)" >&2
    fail=1
  fi
fi

# Every local ES import of the playground's scripts resolves: a page whose module graph
# is broken would load and then do nothing, which an HTTP check would not see.
check_imports() {
  for file in "$SITE"/playground/*.js; do
    [ -f "$file" ] || continue
    for spec in $(grep -o 'from *"[.]/[^"]*"' "$file" | sed 's/^from *"//; s/"$//'); do
      if [ ! -f "$SITE/playground/$spec" ]; then
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
if [ -f "$SITE/notebooks/index.html" ]; then
  check_links "$SITE/notebooks/index.html" "$SITE/notebooks"
fi

if [ "$fail" -eq 0 ]; then
  echo "check-site: ok ($SITE: landing, docs, benchmarks, playground, notebooks)"
else
  echo "check-site: FAILED" >&2
fi
exit "$fail"
