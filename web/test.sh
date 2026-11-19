#!/bin/sh
# Smoke tests of the web infoview and the playground: build the pages (web/build.sh,
# web/build-playground.sh); the generated benchmark page's fixtures and the site check
# (web/test-bench.sh); run the infoview's Wasm module under Node with
# infoview/stub_server.py (canned goals) as the server (web/node_test.mjs), and the
# playground's under Node (web/playground_test.mjs); the playground's pure state and
# URL encoding (web/playground-state_test.mjs) run first; then serve the infoview with
# web/bridge.sh in front of the real server (`wiz lsp --ws`, .lake/build/bin/wiz), load
# it in headless Chromium (web/chrome_test.mjs, over the DevTools protocol), put the
# cursor in the page's proof, click a subterm and look for the goals and what the subterm
# is in the DOM.
#   usage: web/test.sh [PORT]       (needs nix for emscripten and chromium)
#   WIZ_WEB_FROM=DIR and WIZ_PLAYGROUND_FROM=DIR: copy the modules a Nix build made
#   (`nix build .#wiz-web .#wiz-playground`) instead of building them, as CI does.
set -e
ROOT=$(cd "$(dirname "$0")/.." && pwd)
PORT=${1:-18765}
OUT=$(mktemp -d)
trap 'if [ -n "$BRIDGE" ]; then pkill -P "$BRIDGE" 2>/dev/null || true; kill "$BRIDGE" 2>/dev/null || true; fi; rm -rf "$OUT"' EXIT
WIZ=${WIZ:-$ROOT/.lake/build/bin/wiz}
# (11ab) the playground's pure state and URL encoding need neither the build nor a
# browser; run it first so a broken share link fails fast.
node "$ROOT/web/playground-state_test.mjs" > "$OUT/playground-state.txt"
if grep -qF 'playground state: all checks passed' "$OUT/playground-state.txt"; then
  echo "ok (playground state, node)"
else
  echo "FAIL (playground state, node)"; cat "$OUT/playground-state.txt"; exit 1
fi
# (11s) the search box's ranking and rendering (no build or browser needed)
node "$ROOT/web/scroll-search_test.mjs" > "$OUT/search.txt"
grep -qF 'scroll-search: all checks passed' "$OUT/search.txt" && echo "ok (search)" || {
  echo "FAIL (search)"; cat "$OUT/search.txt"; exit 1; }
# (bench) the benchmark page's generator fixtures and the site check's rules for it
"$ROOT/web/test-bench.sh" > "$OUT/bench.txt"
grep -qF 'test-bench: ok' "$OUT/bench.txt" && echo "ok (bench page)" || {
  echo "FAIL (bench page)"; cat "$OUT/bench.txt"; exit 1; }
# (playground-lsp) the language client and goals panel against a mock WebSocket server
# (no Wasm build, no browser)
node "$ROOT/web/playground_lsp_test.mjs" > "$OUT/lsp.txt"
if grep -qF 'playground lsp: all checks passed' "$OUT/lsp.txt"; then echo "ok (playground, lsp)"; else
  echo "FAIL (playground, lsp)"; cat "$OUT/lsp.txt"; exit 1; fi
# (infoview-page) the standalone infoview page's URL rule and status line (the pane is
# the playground's, above)
node "$ROOT/web/infoview_page_test.mjs" > "$OUT/infoview-page.txt"
if grep -qF 'infoview page: all checks passed' "$OUT/infoview-page.txt"; then echo "ok (infoview page)"; else
  echo "FAIL (infoview page)"; cat "$OUT/infoview-page.txt"; exit 1; fi
# (editor features) the hover card and go-to-definition: the content rules and the
# widget (minidom), no server and no Wasm build
node "$ROOT/web/hover_test.mjs" > "$OUT/hover.txt"
if grep -qF 'hover: all checks passed' "$OUT/hover.txt"; then echo "ok (playground, hover)"; else
  echo "FAIL (playground, hover)"; cat "$OUT/hover.txt"; exit 1; fi
# (playground-selfhost-lsp) ?lsp=selfhost: the in-page server shim, with a stub engine
node "$ROOT/web/selfhost_lsp_test.mjs" > "$OUT/selfhost-lsp.txt"
if grep -qF 'selfhost lsp: all checks passed' "$OUT/selfhost-lsp.txt"; then echo "ok (playground, selfhost lsp)"; else
  echo "FAIL (playground, selfhost lsp)"; cat "$OUT/selfhost-lsp.txt"; exit 1; fi
# (playground editor) the pure model: positions, squiggle ranges, completion lists
node "$ROOT/web/editor_test.mjs" > "$OUT/editor.txt"
if grep -qF 'editor model: all checks passed' "$OUT/editor.txt"; then echo "ok (editor model)"; else
  echo "FAIL (editor model)"; cat "$OUT/editor.txt"; exit 1; fi
# (playground editor) the two overlays against the minidom double
node "$ROOT/web/editor_dom_test.mjs" > "$OUT/editor-dom.txt"
if grep -qF 'editor dom: all checks passed' "$OUT/editor-dom.txt"; then echo "ok (editor dom)"; else
  echo "FAIL (editor dom)"; cat "$OUT/editor-dom.txt"; exit 1; fi
# (loom overlays) the overlays under the Loom page's child-index patch paths: enabling
# squiggles must not move the textarea (web/loom_overlay_test.mjs)
node "$ROOT/web/loom_overlay_test.mjs" > "$OUT/loom-overlay.txt"
if grep -qF 'loom overlay: all checks passed' "$OUT/loom-overlay.txt"; then echo "ok (loom overlay)"; else
  echo "FAIL (loom overlay)"; cat "$OUT/loom-overlay.txt"; exit 1; fi
# (playground-exit) the engine guard: exit(3), abort/OOM and traps from a stub module
node "$ROOT/web/playground_engine_test.mjs" > "$OUT/engine.txt"
if grep -qF 'playground engine: all checks passed' "$OUT/engine.txt"; then echo "ok (playground, engine guard)"; else
  echo "FAIL (playground, engine guard)"; cat "$OUT/engine.txt"; exit 1; fi
"$ROOT/web/build.sh" "$OUT" >/dev/null
"$ROOT/web/build-playground.sh" "$OUT" >/dev/null
"$ROOT/web/build-playground-ui.sh" "$OUT" >/dev/null
node "$ROOT/web/node_test.mjs" "$OUT" python3 "$ROOT/infoview/stub_server.py" --stdio > "$OUT/node.txt"
for want in 'class="names">A</span>' 'data-ref="5"' 'info: <span class="kind">const</span> <code>Nat : Type</code>'; do
  if grep -qF "$want" "$OUT/node.txt"; then echo "ok (node): $want"; else echo "FAIL (node): missing $want"; cat "$OUT/node.txt"; exit 1; fi
done
# (11ab) the playground's module: the self-hosted checker, every example
node "$ROOT/web/playground_test.mjs" "$OUT" > "$OUT/playground.txt"
if grep -qF 'playground: all checks passed' "$OUT/playground.txt"; then echo "ok (playground, node)"; else echo "FAIL (playground, node)"; cat "$OUT/playground.txt"; exit 1; fi
# (loom) the whole page as one Loom app (?ui=loom): its module mounted under Node with
# the framework's driver and DOM double, then the page's wiz_loom_* calls
node "$ROOT/web/playground_ui_test.mjs" "$OUT" > "$OUT/ui.txt"
if grep -qF 'playground ui: all checks passed' "$OUT/ui.txt"; then echo "ok (playground, loom ui)"; else echo "FAIL (playground, loom ui)"; cat "$OUT/ui.txt"; exit 1; fi
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
if [ -n "$WIZ_WEB_NO_BROWSER" ]; then
  echo "ok (browser skipped: WIZ_WEB_NO_BROWSER)"
  exit 0
fi
if command -v chromium >/dev/null; then CHROME=$(command -v chromium); else CHROME=$(nix shell --inputs-from "$ROOT" nixpkgs#chromium -c sh -c 'command -v chromium'); fi
# (11s) the documentation page in Chromium: signatures rendered by the Wasm module
(cd "$OUT/doc/site" && exec python3 -m http.server $((PORT + 2)) --bind 127.0.0.1) > "$OUT/http.log" 2>&1 &
HTTP=$!
sleep 1
node "$ROOT/web/doc_chrome_test.mjs" "$CHROME" "http://127.0.0.1:$((PORT + 2))/Col.html" > "$OUT/doc-chrome.txt"
kill $HTTP
for want in 'interactive: true' 'hover: <span class="kind">const</span> <code>' 'selected: <span class="tt ' 'search name: 1' 'search docs: 1' 'search signature: 1'; do
  if grep -qF "$want" "$OUT/doc-chrome.txt"; then echo "ok (doc, chromium): $want"; else echo "FAIL (doc, chromium): missing $want"; cat "$OUT/doc-chrome.txt"; exit 1; fi
done
# (#430) the server's token: the page's URL carries it to its WebSocket
TOKEN=$(od -An -tx1 -N16 /dev/urandom | tr -d ' \n')
WIZ_LSP_TOKEN=$TOKEN WIZ_WEB_OUT=$OUT "$ROOT/web/bridge.sh" "$PORT" "$WIZ" > "$OUT/bridge.log" 2>&1 &
BRIDGE=$!
sleep 3
node "$ROOT/web/chrome_test.mjs" "$CHROME" "http://127.0.0.1:$((PORT + 1))/infoview.html?port=$PORT&token=$TOKEN" > "$OUT/chrome.txt"
ok=1
# The page's markup is web/goals.js's (the playground's renderer) since the two infoviews
# were unified: a goal's hypothesis is a `.names` span (with its own title/span
# attributes), a tagged subterm is `.tt k-KIND` with `data-ref`, a clicked one carries
# `sel`, and the selected subterm is in `#info` as `.selection`.
for want in 'status: connected' 'class="names"' 'title="A">A</span>' 'data-ref="' 'tt k-const sel' \
            'info: <div class="selection">' 'class="kind">const</span>'; do
  if grep -qF "$want" "$OUT/chrome.txt"; then echo "ok (chromium): $want"; else echo "FAIL (chromium): missing $want"; ok=0; fi
done
[ $ok = 1 ] || { cat "$OUT/chrome.txt" "$OUT/bridge.log"; exit 1; }
