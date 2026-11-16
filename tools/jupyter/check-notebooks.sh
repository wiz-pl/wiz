#!/bin/sh
# Re-export every checked-in notebook and fail when an export is stale.
#
# The notebooks in docs/notebooks/ and their exported pages are committed
# together: `--check` renders the notebook in memory and compares it with the
# file, so the docs cannot keep a page that no longer matches its notebook.
# No kernel or network is needed, only Python 3.
#
#   usage: tools/jupyter/check-notebooks.sh
set -eu
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
status=0
found=0
for notebook in "$ROOT"/docs/notebooks/*.ipynb; do
  [ -f "$notebook" ] || continue
  found=1
  if ! python3 "$ROOT/tools/jupyter/export.py" export "$notebook" --check; then
    status=1
  fi
done
if [ "$found" -eq 0 ]; then
  echo "check-notebooks: no notebooks in docs/notebooks" >&2
  exit 1
fi
exit "$status"
