#!/bin/sh
# Start the read-only Scry MCP server for the workspace in the current directory.
#
# scry is the first that exists of: $SCRY_BIN, ./scry/.grail/bin/scry (this
# worktree's build), `scry` on PATH. The rule pack defaults to
# ./lib/Scry/rules/default.scry. Arguments are passed to scry_mcp.py.
# stdout is the MCP transport: nothing else may write to it.
set -u
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
exec python3 "$here/scry_mcp.py" "$@"
