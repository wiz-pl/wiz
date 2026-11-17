#!/bin/sh
# Start the wiz-mcp bridge for the workspace in the current directory, choosing
# the wiz executable so that a worktree without its own build still works.
#
# Order (the first that exists wins; the choice is logged to stderr):
#   1. $WIZ_BIN                     an explicit choice
#   2. ./.lake/build/bin/wiz        this worktree's own build (matches its lib/)
#   3. `tower which wiz`            the tower toolchain for this directory
#                                   (a `wiz-toolchain` file, an override, or the default)
#   4. `wiz` on PATH
#
# Arguments are passed to wiz_mcp.py (e.g. --idle 600 --timeout 300).
# stdout is the MCP transport: nothing else may write to it.
set -u
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)

wiz=${WIZ_BIN:-}
src="WIZ_BIN"
if [ -z "$wiz" ] && [ -x ./.lake/build/bin/wiz ]; then
    wiz=./.lake/build/bin/wiz; src="worktree build"
fi
if [ -z "$wiz" ] && command -v tower >/dev/null 2>&1; then
    p=$(tower which wiz 2>/dev/null) && [ -x "$p" ] && { wiz=$p; src="tower ($(tower show 2>/dev/null | head -n 1))"; }
fi
if [ -z "$wiz" ]; then
    wiz=wiz; src="PATH"
fi
echo "wiz-mcp: wiz = $wiz [$src]" >&2
exec python3 "$here/wiz_mcp.py" --wiz "$wiz" "$@"
