#!/usr/bin/env bash
# Validate a static grail index (stage 23m): names, versions, archive SHA-256s, semver
# requirements, module-prefix conflicts, and the repository manifest (`index.wiz`).
#
#   scripts/grail-index-check.sh [INDEX] [--fetch]
#
# INDEX is a directory, a single-file index, or (with --fetch) a git URL. With no
# argument the current directory is checked, which is what an index repository's CI
# wants. **No network by default**: remote archives are counted but not downloaded, and
# a URL index is refused without --fetch.
set -euo pipefail

root=$(cd "$(dirname "$0")/.." && pwd)
grail=${GRAIL:-}
if [ -z "$grail" ]; then
  if [ -x "$root/.lake/build/bin/grail" ]; then
    grail="$root/.lake/build/bin/grail"
  elif command -v grail >/dev/null 2>&1; then
    grail=$(command -v grail)
  else
    echo "grail-index-check: no grail binary (run 'lake build grail', or set GRAIL)" >&2
    exit 2
  fi
fi

exec "$grail" index check "$@"
