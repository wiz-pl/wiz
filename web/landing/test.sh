#!/bin/sh
# The landing page's own gate, in the order the page is built:
#
#   1. the snippets compile, and the build highlighter's bytes equal `wiz doc`'s
#      (web/landing_check.py);
#   2. the generated page is made of the snippet files, its tabs/panels agree, exactly
#      one is selected, the copy buttons are hidden, and the playground links decode
#      back to the files (web/landing_page_test.mjs);
#   3. the page test is not vacuous: a page with one snippet byte changed must fail it.
#
# The Wasm half (the quantity island) is web/landing_ui_test.mjs, which needs
# web/build-landing-ui.sh's module; the browser half is web/landing_chrome_test.mjs.
#
#   usage: web/landing/test.sh            (needs a built wiz: WIZ=…/bin/wiz)
set -eu
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
WIZ=${WIZ:-$ROOT/.lake/build/bin/wiz}
if [ ! -x "$WIZ" ]; then
  WIZ=$(command -v wiz || true)
fi
[ -n "$WIZ" ] || { echo "landing test: no wiz (set WIZ)" >&2; exit 2; }
export WIZ
OUT=$(mktemp -d)
trap 'rm -rf "$OUT"' EXIT

python3 "$ROOT/web/landing_check.py" --root "$ROOT" --wiz "$WIZ"
sh "$ROOT/web/build-landing.sh" "$OUT/web"
node "$ROOT/web/landing_page_test.mjs" "$OUT/web/landing/index.html" "$ROOT"

# Negative control: the page test must reject a page whose code no longer matches the
# snippet file. (A test that only reads the page would pass a page built from a stale
# snippet; this is the check that it is anchored to the files.)
sed "s/identity/ident/" "$OUT/web/landing/index.html" > "$OUT/broken.html"
if node "$ROOT/web/landing_page_test.mjs" "$OUT/broken.html" "$ROOT" >/dev/null 2>&1; then
  echo "landing test: the page test accepted a changed snippet" >&2
  exit 1
fi
echo "ok: the page test rejects a page that drifted from its snippet"

echo "landing test: ok"
