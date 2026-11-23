#!/bin/sh
# Build a complete `/source/` bundle: `scry web`'s data and SSR, the host files, and the
# reader's Wasm runtime.
#
# `scry web DIR --out BUNDLE --ui FILE` copies the `.mjs` but not Emscripten's side-car
# `.wasm`, so a bundle made with `--ui` alone loads, fails to instantiate the runtime and
# leaves the SSR plus a `data-wiz-error` line. This wrapper copies both halves and checks
# every file the page imports, so the smoke test and the site see the product rather than
# a near-miss.
#
# `scry web`'s `index.html` still tells a no-JS reader that the page needs JavaScript.
# The SSR *is* the page (WEB-1.3: the JS-off page is the product), so this rewrites that
# one sentence instead of shipping a false warning.
#
#   usage: web/source-bundle.sh SCRY OUT [--ui DIR] [--assets DIR] [--target PATH]
#                                   [--source FILE]...
#
#   SCRY      a built scry binary (scry/.grail/bin/scry, or `nix run .#wiz -- ...` is not
#             enough: `grail build scry` is the binary this reads)
#   OUT       the bundle directory (created/overwritten by `scry web`)
#   --ui DIR  a directory with wiz-source-ui.mjs and wiz-source-ui.wasm; usually
#             `nix build .#wiz-source-ui --print-out-paths`
#   --assets  the checkout's web/ directory (default: this script's ../web)
#   --target  the C file or directory to analyse (default: scry/tests/fixtures/report)
#   --source  a file to copy in verbatim with no analysis (repeatable); a Wiz file here
#             is what the live host (`?lsp=`) answers hover and definition about
set -eu
ROOT=$(cd "$(dirname "$0")/.." && pwd)
[ $# -ge 2 ] || {
  echo "usage: web/source-bundle.sh SCRY OUT [--ui DIR] [--assets DIR] [--target PATH] [--source FILE]..." >&2
  exit 2
}
SCRY=$1
OUT=$2
shift 2
UI=${WIZ_SOURCE_UI_FROM:-}
ASSETS=$ROOT/web
TARGET=scry/tests/fixtures/report
SOURCES=""
while [ $# -gt 0 ]; do
  case "$1" in
    --ui) UI=$2; shift 2 ;;
    --assets) ASSETS=$2; shift 2 ;;
    --target) TARGET=$2; shift 2 ;;
    --source) SOURCES="$SOURCES
$2"; shift 2 ;;
    -h|--help) sed -n '2,36p' "$0"; exit 0 ;;
    *) echo "source-bundle: unknown argument $1" >&2; exit 2 ;;
  esac
done
[ -f "$SCRY" ] || { echo "source-bundle: no scry binary at $SCRY" >&2; exit 1; }
case "$SCRY" in /*) ;; *) SCRY=$(cd "$(dirname "$SCRY")" && pwd)/$(basename "$SCRY") ;; esac
[ -d "$ASSETS" ] || { echo "source-bundle: no assets directory at $ASSETS" >&2; exit 1; }
if [ -n "$UI" ]; then
  for f in wiz-source-ui.mjs wiz-source-ui.wasm; do
    [ -f "$UI/$f" ] || { echo "source-bundle: $UI/$f is missing (not a .#wiz-source-ui output)" >&2; exit 1; }
  done
fi

# `scry web` resolves the target relative to the checkout root, and finds the host's
# `web/` from there; run it there so a caller can pass a repository-relative target.
mkdir -p "$OUT"
OUT=$(cd "$OUT" && pwd)
# Rebuild the extra arguments with `set --`, one word per argument, so a path with a
# space survives (`--source` lines are newline-separated above).
set --
[ -n "$UI" ] && set -- "$@" --ui "$UI/wiz-source-ui.mjs"
oldIFS=$IFS
IFS='
'
for s in $SOURCES; do
  [ -n "$s" ] && set -- "$@" --source "$s"
done
IFS=$oldIFS
(cd "$ROOT" && "$SCRY" web "$TARGET" --out "$OUT" --assets "$ASSETS" "$@")

need() {
  [ -f "$OUT/$1" ] || { echo "source-bundle: scry web wrote no $OUT/$1" >&2; exit 1; }
}
for f in index.html app.js app.css source-static.js source-live.js \
         framework/mount.js framework/driver.js framework/runtime.js framework/adopt.js \
         data/manifest.json data/findings.json; do
  need "$f"
done

# The runtime, both halves. `scry web --ui` copies only the module; `source-app.js` imports
# it by a relative path and Emscripten fetches the wasm beside it.
runtime=no
if [ -n "$UI" ]; then
  # -f: the store's files are read-only, and a second run of this script must be able to
  # replace the copy it made (the heavy smoke job re-exports into the same directory).
  cp --no-preserve=mode -f "$UI/wiz-source-ui.mjs" "$OUT/wiz-source-ui.mjs"
  cp --no-preserve=mode -f "$UI/wiz-source-ui.wasm" "$OUT/wiz-source-ui.wasm"
  runtime=yes
fi

# The page is complete with scripting off; say so. (The generated sentence is in
# `Scry.webIndexHtml`; a generator change that drops it makes this fail, deliberately.)
python3 - "$OUT/index.html" <<'PY'
import re
import sys

path = sys.argv[1]
with open(path, encoding="utf-8") as f:
    html = f.read()
note = ("<noscript><p>This page is complete without JavaScript: the source, the "
        "findings and their spans are in it. Scripting adds the hover card and "
        "selection.</p></noscript>")
html, count = re.subn(r"<noscript>.*?</noscript>", note, html, count=1, flags=re.S)
if count != 1:
    sys.exit("source-bundle: %s has no <noscript> to replace" % path)
with open(path, "w", encoding="utf-8") as f:
    f.write(html)
PY

findings=$(python3 -c 'import json,sys; print(len(json.load(open(sys.argv[1], encoding="utf-8"))["findings"]))' \
  "$OUT/data/findings.json")
echo "source bundle: $OUT ($findings finding(s), runtime: $runtime)"
