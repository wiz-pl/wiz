#!/bin/sh
# Serve the web infoview: `wiz lsp --ws PORT --no-stdio` (the language server on a
# WebSocket on 127.0.0.1:PORT; one server for every page, each page its own editor), and
# the page itself over HTTP on PORT+1.
#   usage: web/bridge.sh [PORT] [WIZ]      then open http://127.0.0.1:PORT+1/infoview.html
# WIZ is the command that starts the server (default: wiz); it gets
# `lsp --ws PORT --no-stdio` appended.
set -e
PORT=${1:-8765}
WIZ=${2:-wiz}
HERE=$(cd "$(dirname "$0")" && pwd)
OUT=${WIZ_WEB_OUT:-$HERE/out}
[ -f "$OUT/wiz-infoview.mjs" ] || { echo "build the page first: web/build.sh" >&2; exit 1; }
# The infoview page is JavaScript now (web/playground-lsp.js and the modules under it);
# copy them beside the page so an older OUT still works.
cp "$HERE/infoview.html" "$HERE/infoview.js" "$HERE/playground-lsp.js" "$HERE/lsp-client.js" \
   "$HERE/goals.js" "$HERE/tagged.js" "$OUT/"
python3 -m http.server --bind 127.0.0.1 --directory "$OUT" $((PORT + 1)) >/dev/null 2>&1 &
HTTP=$!
trap 'kill $HTTP 2>/dev/null' EXIT INT TERM
echo "infoview: http://127.0.0.1:$((PORT + 1))/infoview.html?port=$PORT"
# (the server's library is lib/ under the directory it runs in: the repository's)
cd "$HERE/.."
$WIZ lsp --ws "$PORT" --no-stdio
