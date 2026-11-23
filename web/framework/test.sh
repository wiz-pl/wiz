#!/bin/sh
# Test the browser half of lib/Web/Loom.wiz: render a component tree and its patches
# with the Wiz compiler, then apply the patches to the SSR HTML in a Node test double
# of the DOM (web/framework/minidom.mjs) and compare with the SSR of the next state.
# No browser and no Emscripten are needed (unlike web/test.sh).
#
#   usage: web/framework/test.sh
#          WIZ=/path/to/wiz web/framework/test.sh
set -eu
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
WIZ=${WIZ:-$ROOT/.lake/build/bin/wiz}
[ -x "$WIZ" ] || { echo "no wiz binary at $WIZ (build it, or set WIZ=)" >&2; exit 1; }
OUT=$(mktemp -d)
trap 'rm -rf "$OUT"' EXIT

# The compiler flags (GMP's include and library) come from /workspace/wiz-env.sh in the
# dev shell; without them a plain `wiz run` still works where GMP is in the default path.
# `-I lib`: the framework's own modules (lib/Web/Loom.wiz) are in the checkout's library,
# which a toolchain built before the rename or from another commit does not have.
set -- run -I "$ROOT/lib" "$ROOT/web/framework/gen.wiz"
if [ -n "${WIZ_CFLAGS:-}" ]; then set -- "$@" --cflags "$WIZ_CFLAGS"; fi
if [ -n "${WIZ_LDFLAGS:-}" ]; then set -- "$@" --ldflags "$WIZ_LDFLAGS"; fi
"$WIZ" "$@" > "$OUT/fixture.json"
node "$ROOT/web/framework/test.mjs" "$OUT/fixture.json"
# The driver's ABI (event strings, payloads, onStep, js_patch): Node only, no wiz.
node "$ROOT/web/framework/driver_test.mjs"
# The mount contract (one export; element, module, events, host capabilities): Node only.
node "$ROOT/web/framework/mount_test.mjs"
# The wire envelope/monitor and the adopt/replace contract: Node only.
node "$ROOT/web/framework/wire_test.mjs"
# The page is the mount contract (no ABI calls of its own): source-level, Node only.
node "$ROOT/web/playground_entry_test.mjs"
# A runtime that cannot start is a text reason, not a second UI: Node only.
node "$ROOT/web/playground_start_test.mjs"
# The editor overlays over the Loom page's child-index patch paths: Node only.
node "$ROOT/web/loom_overlay_test.mjs"
