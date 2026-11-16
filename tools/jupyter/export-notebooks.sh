#!/bin/sh
# Export every docs/notebooks/*.ipynb to OUT/NAME.html and copy the hand-written
# docs/notebooks/index.html beside them: the site's /notebooks/ directory.
#
# The pages are generated, not committed (`nix build .#notebook-pages` runs this, and
# web/build-site.sh runs it into the site). The export is deterministic and needs no
# kernel or network, only Python 3: the notebook's stored outputs are rendered.
#
#   usage: tools/jupyter/export-notebooks.sh OUT
set -eu
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
OUT=${1:?usage: tools/jupyter/export-notebooks.sh OUT}
mkdir -p "$OUT"
found=0
for notebook in "$ROOT"/docs/notebooks/*.ipynb; do
  [ -f "$notebook" ] || continue
  found=1
  name=$(basename "$notebook" .ipynb)
  python3 "$ROOT/tools/jupyter/export.py" export "$notebook" --out "$OUT/$name.html" >/dev/null
done
if [ "$found" -eq 0 ]; then
  echo "export-notebooks: no notebooks in docs/notebooks" >&2
  exit 1
fi
cp "$ROOT/docs/notebooks/index.html" "$OUT/index.html"
