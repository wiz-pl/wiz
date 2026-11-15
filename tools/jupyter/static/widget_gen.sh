#!/bin/sh
# Regenerate the widget fixture and its DOM goldens (needs a wiz binary; the test
# itself does not):
#
#   WIZ=.lake/build/bin/wiz tools/jupyter/static/widget_gen.sh
#
# This runs widget_gen.wiz, parses the patch strings `React.patchesJson` produced, and
# writes widget_fixture.json plus goldens/widget_{initial,after_click,after_input}.html
# from the Wiz SSR (the oracle).  The comm golden is the front end's output; capture it
# with `node tools/jupyter/static/widget_test.mjs --update` (which rewrites all four).
set -eu
ROOT=$(cd "$(dirname "$0")/../../.." && pwd)
HERE=$ROOT/tools/jupyter/static
WIZ=${WIZ:-$ROOT/.lake/build/bin/wiz}
[ -x "$WIZ" ] || { echo "no wiz binary at $WIZ (build it, or set WIZ=)" >&2; exit 1; }
OUT=$(mktemp -d)
trap 'rm -rf "$OUT"' EXIT

# The compiler flags (GMP's include and library) come from the dev shell; without them
# a plain `wiz run` still works where GMP is in the default path.
set -- run "$HERE/widget_gen.wiz"
if [ -n "${WIZ_CFLAGS:-}" ]; then set -- "$@" --cflags "$WIZ_CFLAGS"; fi
if [ -n "${WIZ_LDFLAGS:-}" ]; then set -- "$@" --ldflags "$WIZ_LDFLAGS"; fi
"$WIZ" "$@" > "$OUT/raw.json"

node - "$OUT/raw.json" "$HERE" <<'JS'
const fs = require("node:fs");
const path = require("node:path");
const [rawPath, here] = process.argv.slice(2);
const fixture = JSON.parse(fs.readFileSync(rawPath, "utf8"));

// `React.patchesJson` is a JSON string in the fixture; the test wants the patch list.
for (const step of Object.values(fixture.steps)) step.patch = JSON.parse(step.patch);
fs.writeFileSync(path.join(here, "widget_fixture.json"), JSON.stringify(fixture, null, 2) + "\n");

const goldens = path.join(here, "goldens");
fs.mkdirSync(goldens, { recursive: true });
fs.writeFileSync(path.join(goldens, "widget_initial.html"), fixture.html + "\n");
fs.writeFileSync(path.join(goldens, "widget_after_click.html"), fixture.steps.click.html + "\n");
fs.writeFileSync(path.join(goldens, "widget_after_input.html"), fixture.steps.input.html + "\n");

console.log("wrote widget_fixture.json and 3 DOM goldens");
JS

echo "next: node tools/jupyter/static/widget_test.mjs --update   # also pins widget_comm.json"
