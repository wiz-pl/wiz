#!/bin/sh
# Run the wiz-mcp tests: unit tests first, then the end-to-end smoke test.
# The smoke test exits 2 when this checkout has no built wiz; report that as a
# skip (not a pass) and keep the unit-test result.
set -u

here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo=$(CDPATH= cd -- "$here/../.." && pwd)

python3 -m unittest discover -s "$here/tests" -p 'test_*.py' -v || exit 1

if python3 "$here/tests/smoke.py" --wiz "${WIZ:-$repo/.lake/build/bin/wiz}" "$@"; then
    exit 0
else
    status=$?
    if [ "$status" -eq 2 ]; then
        echo "smoke: SKIPPED (no built wiz; this is not a pass)"
        exit 0
    fi
    exit "$status"
fi
