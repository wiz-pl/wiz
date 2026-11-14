#!/bin/sh
# Smoke tests of the web infoview and the playground: build the pages (web/build.sh,
# web/build-playground.sh); run the infoview's Wasm module under Node with
# infoview/stub_server.py (canned goals) as the server (web/node_test.mjs), and the
# playground's under Node (web/playground_test.mjs); then serve the infoview with
# web/bridge.sh in front of the real server (`wiz lsp --ws`, .lake/build/bin/wiz), load
# it in headless Chromium (web/chrome_test.mjs, over the DevTools protocol), put the
# cursor in the page's proof, click a subterm and look for the goals and what the subterm
# is in the DOM.
#   usage: web/test.sh [PORT]       (needs nix for emscripten and chromium)
set -e
ROOT=$(cd "$(dirname "$0")/.." && pwd)
PORT=${1:-18765}
OUT=$(mktemp -d)
trap 'if [ -n "$BRIDGE" ]; then pkill -P "$BRIDGE" 2>/dev/null || true; kill "$BRIDGE" 2>/dev/null || true; fi; rm -rf "$OUT"' EXIT
WIZ=${WIZ:-$ROOT/.lake/build/bin/wiz}
"$ROOT/web/build.sh" "$OUT" >/dev/null
"$ROOT/web/build-playground.sh" "$OUT" >/dev/null
node "$ROOT/web/node_test.mjs" "$OUT" python3 "$ROOT/infoview/stub_server.py" --stdio > "$OUT/node.txt"
for want in 'class="names">A</span>' 'data-ref="5"' 'info: <span class="kind">const</span> <code>Nat : Type</code>'; do
  if grep -qF "$want" "$OUT/node.txt"; then echo "ok (node): $want"; else echo "FAIL (node): missing $want"; cat "$OUT/node.txt"; exit 1; fi
done
# (11ab) the playground's module: the self-hosted checker, one evaluation
node "$ROOT/web/playground_test.mjs" "$OUT" > "$OUT/playground.txt"
if grep -qF 'playground: all checks passed' "$OUT/playground.txt"; then echo "ok (playground, node)"; else echo "FAIL (playground, node)"; cat "$OUT/playground.txt"; exit 1; fi
# (11s) the documentation pages' half of the module, on a page `wiz doc` made (the
# Wasm module's own JSON: the declaration `pick` alone)
mkdir -p "$OUT/doc/src"
printf 'import Prelude\n/-- A colour. -/\ninductive C where\n  | red\n/-- The colour. -/\ndef pick (n : Nat) : C := C.red\n' > "$OUT/doc/src/Col.wiz"
"$WIZ" doc "$OUT/doc/src" -o "$OUT/doc/site" --web "$OUT" >/dev/null
python3 -c 'import json,sys; d=json.load(open(sys.argv[1])); d["decls"]=[x for x in d["decls"] if x["name"]=="pick"]; json.dump(d,open(sys.argv[1],"w"))' "$OUT/doc/site/Col.json"
node "$ROOT/web/doc_node_test.mjs" "$OUT" "$OUT/doc/site/Col.json" > "$OUT/doc.txt"
for want in 'class="tt k-const" data-ref=' 'info: <span class="kind">const</span> <code>Nat : Type</code>' 'tt k-pi sel'; do
  if grep -qF "$want" "$OUT/doc.txt"; then echo "ok (doc, node): $want"; else echo "FAIL (doc, node): missing $want"; cat "$OUT/doc.txt"; exit 1; fi
done
[ -n "$WIZ_WEB_NO_BROWSER" ] && exit 0
if command -v chromium >/dev/null; then CHROME=$(command -v chromium); else CHROME=$(nix shell nixpkgs#chromium -c sh -c 'command -v chromium'); fi
# (11s) the documentation page in Chromium: signatures rendered by the Wasm module
(cd "$OUT/doc/site" && exec python3 -m http.server $((PORT + 2)) --bind 127.0.0.1) > "$OUT/http.log" 2>&1 &
HTTP=$!
sleep 1
node "$ROOT/web/doc_chrome_test.mjs" "$CHROME" "http://127.0.0.1:$((PORT + 2))/Col.html" > "$OUT/doc-chrome.txt"
kill $HTTP
for want in 'interactive: true' 'hover: <span class="kind">const</span> <code>' 'selected: <span class="tt '; do
  if grep -qF "$want" "$OUT/doc-chrome.txt"; then echo "ok (doc, chromium): $want"; else echo "FAIL (doc, chromium): missing $want"; cat "$OUT/doc-chrome.txt"; exit 1; fi
done
WIZ_WEB_OUT=$OUT "$ROOT/web/bridge.sh" "$PORT" "$WIZ" > "$OUT/bridge.log" 2>&1 &
BRIDGE=$!
sleep 3
node "$ROOT/web/chrome_test.mjs" "$CHROME" "http://127.0.0.1:$((PORT + 1))/infoview.html?port=$PORT" > "$OUT/chrome.txt"
ok=1
for want in 'status: connected' 'class="names">A</span>' 'data-ref="' 'tt k-const sel' 'info: <span class="kind">const</span> <code>Nat : Type</code>'; do
  if grep -qF "$want" "$OUT/chrome.txt"; then echo "ok (chromium): $want"; else echo "FAIL (chromium): missing $want"; ok=0; fi
done
[ $ok = 1 ] || { cat "$OUT/chrome.txt" "$OUT/bridge.log"; exit 1; }
