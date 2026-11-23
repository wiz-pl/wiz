#!/bin/sh
# Start the read-only Scry MCP server for the workspace in the current directory.
#
# scry is the first that exists of: $SCRY_BIN, then `scry` on PATH. A build in
# this tree (./scry/.grail/bin/scry) is deliberately not used automatically:
# the workspace is the tree under review, so running a program from it would be
# repo-controlled code execution. Pass --scry PATH (or set $SCRY_BIN) to opt in.
# The rule pack defaults to ./lib/Scry/rules/default.scry. Arguments are passed
# to scry_mcp.py. stdout is the MCP transport: nothing else may write to it.
set -u
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
exec python3 "$here/scry_mcp.py" "$@"
