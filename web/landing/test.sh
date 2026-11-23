#!/bin/sh
# The landing page's gate, in the order the page is built:
#
#   1. the snippets compile, and the build highlighter's bytes equal `wiz doc`'s
#      (web/landing_check.py);
#   2. the page is made of the snippet files, its tabs/panels agree, exactly one is
#      selected, the copy buttons are hidden, and the playground links decode back to
#      the files (web/landing_page_test.mjs), with a negative control;
#   3. with a Wasm module (--ui DIR, the output of web/build-landing-ui.sh) the Loom
#      island's SSR, adoption and one-setAttr step are checked under Node
#      (web/landing_ui_test.mjs);
#   4. with --chrome PATH the whole thing is a real browser load, with JavaScript off
#      and on (web/landing_chrome_test.mjs).
#
# --require-ui makes a missing module a failure (CI's web job builds it first); without
# it a docs-only run tests the static page, which is also its JavaScript-off form.
#
#   usage: web/landing/test.sh [--ui DIR] [--require-ui] [--chrome PATH]
set -eu
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
WIZ=${WIZ:-$ROOT/.lake/build/bin/wiz}
if [ ! -x "$WIZ" ]; then
  WIZ=$(command -v wiz || true)
fi
[ -n "$WIZ" ] || { echo "landing test: no wiz (set WIZ)" >&2; exit 2; }
export WIZ
UI=
REQUIRE_UI=0
CHROME=
while [ $# -gt 0 ]; do
  case "$1" in
    --ui) UI=$2; shift 2 ;;
    --require-ui) REQUIRE_UI=1; shift ;;
    --chrome) CHROME=$2; shift 2 ;;
    *) echo "landing test: unknown argument $1" >&2; exit 2 ;;
  esac
done
OUT=$(mktemp -d)
trap 'rm -rf "$OUT"' EXIT

python3 "$ROOT/web/landing_check.py" --root "$ROOT" --wiz "$WIZ"

if [ -n "$UI" ]; then
  sh "$ROOT/web/build-landing-ui.sh" "$OUT/web" --from "$UI" >/dev/null
fi
if [ -f "$OUT/web/landing/wiz-landing-ui.mjs" ]; then
  # The island's first paint is `wiz run`, which compiles with cc.
  sh "$ROOT/web/build-landing.sh" "$OUT/web"
  node "$ROOT/web/landing_ui_test.mjs" "$OUT/web"
else
  if [ "$REQUIRE_UI" = 1 ]; then
    echo "landing test: --require-ui but no module (build web/build-landing-ui.sh)" >&2
    exit 1
  fi
  echo "landing test: no Wasm module: the island tests are skipped (the static page is the no-JS form)" >&2
  sh "$ROOT/web/build-landing.sh" "$OUT/web" --no-island
fi

node "$ROOT/web/landing_page_test.mjs" "$OUT/web/landing/index.html" "$ROOT"

# Negative control: the page test must reject a page whose code no longer matches the
# snippet file; otherwise it would pass a page built from a stale snippet.
sed "s/identity/ident/" "$OUT/web/landing/index.html" > "$OUT/broken.html"
if node "$ROOT/web/landing_page_test.mjs" "$OUT/broken.html" "$ROOT" >/dev/null 2>&1; then
  echo "landing test: the page test accepted a changed snippet" >&2
  exit 1
fi
echo "ok: the page test rejects a page that drifted from its snippet"

# The site layout build-site.sh publishes (index.html at the root, assets under
# landing/), so the browser test loads the same URLs the published page does.
SITE="$OUT/site"
mkdir -p "$SITE/landing/framework"
cp "$OUT/web/landing/index.html" "$SITE/index.html"
cp "$OUT/web/landing/landing.css" "$SITE/landing.css"
for f in app.js carousel.js wiz-landing-ui.mjs wiz-landing-ui.wasm; do
  [ -f "$OUT/web/landing/$f" ] && cp "$OUT/web/landing/$f" "$SITE/landing/$f"
done
for f in "$OUT/web/landing/framework/"*.js; do
  [ -f "$f" ] && cp "$f" "$SITE/landing/framework/"
done

# The byte budget of the page's transferred scripts and module (gzip; the `.gz` side of
# a CDN transfer is smaller, so this is the conservative number).
gz() { gzip -9 -c "$1" | wc -c | tr -d ' '; }
js_bytes=0
for f in app.js carousel.js framework/mount.js framework/driver.js framework/runtime.js framework/adopt.js; do
  [ -f "$SITE/landing/$f" ] && js_bytes=$((js_bytes + $(gz "$SITE/landing/$f")))
done
wasm_bytes=0
[ -f "$SITE/landing/wiz-landing-ui.wasm" ] && wasm_bytes=$(gz "$SITE/landing/wiz-landing-ui.wasm")
echo "landing bytes (gzip): js ${js_bytes} B, wasm ${wasm_bytes} B"
[ "$js_bytes" -le 24576 ] || { echo "landing test: JS is over the 24 KiB gz budget" >&2; exit 1; }
[ "$wasm_bytes" -le 133120 ] || { echo "landing test: Wasm is over the 130 KiB gz budget" >&2; exit 1; }

if [ -n "$CHROME" ]; then
  node "$ROOT/web/landing_chrome_test.mjs" "$CHROME" "$SITE"
fi

echo "landing test: ok"
