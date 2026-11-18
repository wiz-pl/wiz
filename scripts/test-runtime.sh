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
ldflags=${WIZ_LDFLAGS:-}
libs="-lgmp -lpthread -lm"

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

# ---- behaviour the compiler's tests need a whole program for, checked against the
# runtime alone (one C file, both ABI settings) ----

cat > "$tmp/longlist.c" <<'EOF'
/* A long list is dropped and printed iteratively: a work list, not one C frame per
   cell (a cons list a million long must not overflow the stack: a SIGSEGV would also
   bypass `wiz_panic`, exit 3). */
#define _GNU_SOURCE
#include <stdio.h>
#include "wiz_rt.h"
#include "rt_core.inc"
#include "rt_num.inc"
#include "rt_words.inc"
#include "rt_data.inc"
#include "rt_sys.inc"
#include "rt_con.inc"

static wiz_val cons_list(size_t n) {
  wiz_val l = WIZ_BOX(0);
  for (size_t i = 0; i < n; i++) {
    wiz_val fs[2] = { WIZ_BOX(0), l };
    l = wiz_con(1, 2, fs);
  }
  return l;
}

int main(void) {
  wiz_val l = cons_list(1000000);
  wiz_dec(l);                 /* one dec of a million cells */
  l = cons_list(200000);
  wiz_print(l);               /* output goes to /dev/null */
  putchar('\n');
  wiz_dec(l);
  return 0;
}
EOF

run_prog() { # run_prog DESCRIPTION SOURCE CC-ARGS…
  local what=$1 src=$2; shift 2
  local exe="$tmp/prog"
  if ! cc -O0 -w -I "$root/runtime" $cflags "$@" "$src" -o "$exe" $ldflags $libs; then
    echo "test-runtime: FAIL: the check program does not link ($what)" >&2
    exit 1
  fi
  # a 1 MB stack: the recursion the runtime must not do
  if ! sh -c 'ulimit -s 1024; exec "$0" > /dev/null' "$exe"; then
    echo "test-runtime: FAIL: the check program failed ($what)" >&2
    exit 1
  fi
  echo "ok: $what"
}

cat > "$tmp/ffi-null.c" <<'EOF'
/* A NULL `char *` from C is the empty string (`wiz_out_string` calls strlen), and a
   seek offset that does not fit in `off_t` is EINVAL, not a narrowing conversion or
   `-INT64_MIN` (signed-overflow UB). */
#define _GNU_SOURCE
#include <errno.h>
#include <stdio.h>
#include <string.h>
#include "wiz_rt.h"
#include "rt_core.inc"
#include "rt_num.inc"
#include "rt_words.inc"
#include "rt_data.inc"
#include "rt_sys.inc"
#include "rt_con.inc"

int main(void) {
  wiz_val s = wiz_out_string(NULL);
  /* String.mk (List Char): an empty list is WIZ_BOX(0) */
  if (wiz_tag(wiz_field_ref(s, 0)) != 0) { fprintf(stderr, "NULL string is not empty\n"); return 1; }
  wiz_dec(s);
  wiz_sys_file h = { tmpfile(), 1 };
  if (!h.f) return 1;
  /* `.back 2^63`: `-INT64_MIN` is signed-overflow UB (UBSan reports it) */
  uint64_t r = wiz_sys_file_seek(&h, 1, (uint64_t)INT64_MAX + 1, 1);
  if (r != 0 || wiz_sys_errno() != EINVAL) { fprintf(stderr, "back 2^63 was not EINVAL\n"); return 1; }
  /* `.back 2^63+5`: narrowing made the old code seek *forward* and succeed */
  r = wiz_sys_file_seek(&h, 1, (uint64_t)INT64_MAX + 6, 1);
  if (r != 0 || wiz_sys_errno() != EINVAL) { fprintf(stderr, "back 2^63+5 was not EINVAL\n"); return 1; }
  r = wiz_sys_file_seek(&h, 0, UINT64_MAX, 0);
  if (r != 0 || wiz_sys_errno() != EINVAL) { fprintf(stderr, "start 2^64-1 was not EINVAL\n"); return 1; }
  fclose(h.f);
  return 0;
}
EOF

for api in "" "static"; do
  run_prog "a long list is dropped and printed iteratively (WIZ_API=$api)" "$tmp/longlist.c" -DWIZ_API=$api
  run_prog "a NULL char* is empty and an out-of-range seek is EINVAL (WIZ_API=$api)" "$tmp/ffi-null.c" -DWIZ_API=$api
done

echo "test-runtime: all checks passed"
