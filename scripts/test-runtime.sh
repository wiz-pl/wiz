#!/usr/bin/env bash
# The C runtime compiles on its own: `runtime/wiz_rt.h` (value representation, tags,
# object layouts, prototypes) plus the six area files (`runtime/rt_*.inc`), as a
# translation unit that is not generated code.
#
# `cc -fsyntax-only -Wall -Wextra`, in both ABI settings:
#   * WIZ_API= (empty): every entry point is an external symbol, as in the LLVM
#     backend's runtime object (Wiz/Compiler/Build.lean, compileLLVM);
#   * WIZ_API=static: every entry point is `static`, as in a generated C program.
# The header's prototypes are checked against the definitions by this compile, so they
# cannot drift silently.
#
# Usage: scripts/test-runtime.sh (from anywhere; run it through `heavy` or light)
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
tmp=$(mktemp -d "${TMPDIR:-/tmp}/wiz-test-runtime.XXXXXX")
trap 'rm -rf "$tmp"' EXIT

# GMP's include directory: the dev shell's WIZ_CFLAGS (or the toolchain's own `cc`).
cflags=${WIZ_CFLAGS:-}

cat > "$tmp/runtime.c" <<'EOF'
/* The runtime as one translation unit: the ABI header, then the areas in the order of
   the old runtime/wiz.c. */
#include "wiz_rt.h"
#include "rt_core.inc"
#include "rt_num.inc"
#include "rt_words.inc"
#include "rt_data.inc"
#include "rt_sys.inc"
#include "rt_con.inc"
EOF

check() { # check DESCRIPTION CC-ARGS…
  local what=$1; shift
  if ! cc -fsyntax-only -Wall -Wextra -I "$root/runtime" $cflags "$@" "$tmp/runtime.c"; then
    echo "test-runtime: FAIL: the runtime does not compile ($what)" >&2
    exit 1
  fi
  echo "ok: $what"
}

check "WIZ_API= (the object ABI)" -DWIZ_API=
check "WIZ_API=static (a generated C program)" -DWIZ_API=static

echo "test-runtime: all checks passed"
