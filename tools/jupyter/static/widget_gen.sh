#!/bin/sh
# Regenerate the widget fixture and its DOM goldens (needs a wiz binary; the test
# itself does not):
#
#   WIZ=.lake/build/bin/wiz tools/jupyter/static/widget_gen.sh
#
# This runs widget_gen.wiz (using the checkout's lib/ for Web.Widget), turns the three
# `WIZ_WIDGET:` display strings into the fixture the front-end test reads, and writes
# goldens/widget_{initial,after_click,after_input}.html from the Wiz SSR (the oracle).
# The comm golden is the front end's output; capture it with
# `node tools/jupyter/static/widget_test.mjs --update` (which rewrites all four).
set -eu
ROOT=$(cd "$(dirname "$0")/../../.." && pwd)
HERE=$ROOT/tools/jupyter/static
WIZ=${WIZ:-$ROOT/.lake/build/bin/wiz}
[ -x "$WIZ" ] || { echo "no wiz binary at $WIZ (build it, or set WIZ=)" >&2; exit 1; }
OUT=$(mktemp -d)
trap 'rm -rf "$OUT"' EXIT

# The compiler flags (GMP's include and library) come from the dev shell; without them
# a plain `wiz run` still works where GMP is in the default path.
set -- run -I "$ROOT/lib" "$HERE/widget_gen.wiz"
if [ -n "${WIZ_CFLAGS:-}" ]; then set -- "$@" --cflags "$WIZ_CFLAGS"; fi
if [ -n "${WIZ_LDFLAGS:-}" ]; then set -- "$@" --ldflags "$WIZ_LDFLAGS"; fi
"$WIZ" "$@" > "$OUT/raw.json"

node - "$OUT/raw.json" "$HERE" <<'JS'
const fs = require("node:fs");
const path = require("node:path");
const [rawPath, here] = process.argv.slice(2);
const raw = JSON.parse(fs.readFileSync(rawPath, "utf8"));

// A display value is `WIZ_WIDGET:` plus the bundle JSON.
const bundle = (value) => JSON.parse(value.slice("WIZ_WIDGET:".length));
const display = bundle(raw.display);
const click = bundle(raw.click);
const input = bundle(raw.input);

const step = (payload, update) => ({
  payload,
  bundle: update,
  patches: update.patches || [],
  html: update.html,
});

const fixture = {
  target_name: raw.target_name,
  comm_id: raw.comm_id,
  display,
  html: display.html,
  steps: {
    click: step({ method: "event", widget_id: "inc", event: "click", value: "count 1" }, click),
    input: step({ method: "event", widget_id: "level", event: "input", value: "3" }, input),
  },
};

fs.writeFileSync(path.join(here, "widget_fixture.json"),
  JSON.stringify(fixture, null, 2) + "\n");

const goldens = path.join(here, "goldens");
fs.mkdirSync(goldens, { recursive: true });
fs.writeFileSync(path.join(goldens, "widget_initial.html"), display.html + "\n");
fs.writeFileSync(path.join(goldens, "widget_after_click.html"), click.html + "\n");
fs.writeFileSync(path.join(goldens, "widget_after_input.html"), input.html + "\n");

console.log("wrote widget_fixture.json and 3 DOM goldens");
JS

echo "next: node tools/jupyter/static/widget_test.mjs --update   # also pins widget_comm.json"
