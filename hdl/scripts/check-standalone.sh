#!/bin/sh
# G1: build and test the Hdl package from a copy of `hdl/` alone (separate-repos.md G1,
# roadmap/hdl-next.md P1.3). Nothing from the checkout is used except the toolchain: no
# escaping path, no root `lib/`, no build output — `grail` finds the std `lib/` that
# belongs to the `grail` binary, and the package's own roots are relative to
# `hdl/grail.wiz` (`Package.lib "hdl" "src"`, `Package.tests "examples" "examples"`).
#
#   hdl/scripts/check-standalone.sh                 # GRAIL, else grail on PATH
#   GRAIL=/path/to/bin/grail hdl/scripts/check-standalone.sh
#
# `grail test` covers the 32 golden examples' messages (and the two `-- test: run`
# examples' output); the yosys/Icarus/formal assertions stay in the Lean `=hdl-*`
# groups, which read the package through `HDL_ROOT` (default `hdl`).
set -eu

here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
pkg_dir=$(dirname -- "$here")
grail=${GRAIL:-grail}
if [ -x "$grail" ]; then
  :
elif ! command -v "$grail" >/dev/null 2>&1; then
  echo "check-standalone: no grail (set GRAIL, or put the toolchain on PATH)" >&2
  exit 2
fi

work=$(mktemp -d "${TMPDIR:-/tmp}/hdl-standalone.XXXXXX")
trap 'rm -rf "$work"' EXIT INT TERM
pkg=$work/hdl
mkdir -p "$pkg"

# Copy the package only: the checkout's lib/, examples/, .grail and build output stay out.
(cd "$pkg_dir" && tar --exclude=./.grail -cf - .) | (cd "$pkg" && tar -xf -)

cd "$pkg"
echo "hdl standalone: $pkg"
echo "grail: $("$grail" --version 2>/dev/null | head -n 1)"
"$grail" build
# The temporal UART example is a slow simulation; the 300 s grail default is too
# tight (it timed out at exactly 300 s in CI).
"$grail" test --test-timeout 900
echo "hdl standalone: ok ($pkg: build + test)"
