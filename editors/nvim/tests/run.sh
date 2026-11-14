#!/bin/sh
# The wiz.nvim tests (the `nvim` test group runs this from the repository root):
# headless Neovim, with the plugin from this checkout and the real `wiz lsp`.
#   WIZ  the wiz executable (default: this checkout's .lake/build/bin/wiz, else `wiz`)
#   GRAIL the grail executable (default: this checkout's .lake/build/bin/grail, else `grail`)
#   NVIM the nvim executable (default: `nvim`)
set -eu
here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../../.." && pwd)
nvim=${NVIM:-nvim}
if ! command -v "$nvim" >/dev/null 2>&1; then
  echo "skipped: no nvim on PATH"
  exit 0
fi
if [ -z "${WIZ:-}" ]; then
  if [ -x "$repo/.lake/build/bin/wiz" ]; then WIZ=$repo/.lake/build/bin/wiz; else WIZ=wiz; fi
fi
if [ -z "${GRAIL:-}" ]; then
  if [ -x "$repo/.lake/build/bin/grail" ]; then GRAIL=$repo/.lake/build/bin/grail; else GRAIL=grail; fi
fi
export WIZ GRAIL WIZ_LIB="${WIZ_LIB:-$repo/lib}"
cd "$here/.."
# `-l` runs the script; it ends with cquit (status 1) when a test fails. Progress lines
# end in \r: keep only the results. `○` is a gap (a missing feature), not a failure.
status=0
out=$("$nvim" --headless --clean -u tests/minimal_init.lua -l tests/run.lua 2>&1) || status=$?
printf '%s\n' "$out" | tr '\r' '\n' | grep -v '^  … ' | sed 's/-- INSERT --//g'
exit "$status"
