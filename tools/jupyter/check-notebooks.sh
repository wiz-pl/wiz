#!/bin/sh
# Export every notebook in docs/notebooks/ twice and fail unless both exports are
# byte-identical and every link of the notebooks' index page resolves.
#
# The exported pages are not committed (tools/jupyter/export-notebooks.sh builds them
# for the site and `nix build .#notebook-pages`), so what keeps them from rotting is
# that they are regenerated from the notebook every time; this checks that the export
# stays deterministic. No kernel or network is needed, only Python 3.
#
#   usage: tools/jupyter/check-notebooks.sh
set -eu
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
sh "$ROOT/tools/jupyter/export-notebooks.sh" "$tmp/a"
sh "$ROOT/tools/jupyter/export-notebooks.sh" "$tmp/b"
if ! diff -r "$tmp/a" "$tmp/b" >/dev/null; then
  echo "check-notebooks: two exports of docs/notebooks differ (the export is not deterministic)" >&2
  diff -r "$tmp/a" "$tmp/b" | head -40 >&2
  exit 1
fi
status=0
for href in $(sed -n 's/.*href="\([^"#:]*\)".*/\1/p' "$tmp/a/index.html"); do
  if [ ! -f "$tmp/a/$href" ]; then
    echo "check-notebooks: index.html links $href, which no notebook exports" >&2
    status=1
  fi
done
[ "$status" -eq 0 ] && echo "check-notebooks: $(ls "$tmp/a" | wc -l | tr -d ' ') pages, deterministic"
exit "$status"
