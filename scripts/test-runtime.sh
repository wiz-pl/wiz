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
# It also checks the pointer-width guard (`runtime/wiz_abi.h`):
#   * the 32-bit and 64-bit selections of `WIZ_WORD_BITS`/`WIZ_SMALL_BITS`/
#     `WIZ_MAX_SMALL`, through `-DWIZ_ABI_TEST_WORD_BITS` (this always runs, even on a
#     host without a 32-bit toolchain);
#   * the 30-bit path's runtime logic on this host: the same test seam selects 30-bit
#     small ints and the checked `WIZ_BOX`, and a small program runs the small/GMP
#     boundary, `dropMoved` masks and machine words (always runs);
#   * 16- and 128-bit words are rejected at compile time (the runtime must never take
#     the 62-bit small-int path silently);
#   * with a real `-m32` toolchain and a 32-bit GMP: the runtime compiles for 32-bit,
#     and the same runtime test runs on a real 32-bit word. Without one, that part is
#     skipped — the selection and its logic above still ran.
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

# ---- pointer width: the selection is compile-time and cannot be 62 bits on a 32-bit
# word (runtime/wiz_abi.h). These run on any host (no -m32 needed).

cat > "$tmp/abi32.c" <<'EOF'
/* The 32-bit selection, compiled on this host: WIZ_ABI_TEST_WORD_BITS is the test seam
   that lets the branch be checked where -m32 is not installed. */
#define WIZ_ABI_TEST_WORD_BITS 32
#include "wiz_abi.h"
_Static_assert(WIZ_WORD_BITS == 32, "the test forces a 32-bit word");
_Static_assert(WIZ_SMALL_BITS == 30, "a 32-bit word must not select the 62-bit small int");
_Static_assert(WIZ_MAX_SMALL == (((uintptr_t)1 << 30) - 1), "the 32-bit small range");
/* the tagged shift of the largest small int is still below 2^32 */
_Static_assert((WIZ_MAX_SMALL << 1) + 1 <= (uintptr_t)0xFFFFFFFFu, "the tag and shift fit");
EOF

cat > "$tmp/abi64.c" <<'EOF'
/* The shipped 64-bit representation: 62-bit small ints (do not change it). On a 32-bit
   host this selection is not applicable; the file then just compiles. */
#include "wiz_abi.h"
#if UINTPTR_MAX > 0xFFFFFFFFu
_Static_assert(WIZ_WORD_BITS == 64, "a 64-bit host selects a 64-bit word");
_Static_assert(WIZ_SMALL_BITS == 62, "the 64-bit small int is 62 bits");
_Static_assert(WIZ_MAX_SMALL == (((uintptr_t)1 << 62) - 1), "the 64-bit small range");
#endif
EOF

cat > "$tmp/abi16.c" <<'EOF'
#define WIZ_ABI_TEST_WORD_BITS 16
#include "wiz_abi.h"
EOF

cat > "$tmp/abi128.c" <<'EOF'
#define WIZ_ABI_TEST_WORD_BITS 128
#include "wiz_abi.h"
EOF

for f in abi32 abi64; do
  if ! cc -fsyntax-only -Wall -Wextra -I "$root/runtime" "$tmp/$f.c"; then
    echo "test-runtime: FAIL: $f.c does not compile" >&2
    exit 1
  fi
  echo "ok: pointer width, $f selection"
done

for f in abi16 abi128; do
  if cc -fsyntax-only -Wall -Wextra -I "$root/runtime" "$tmp/$f.c" >"$tmp/$f.log" 2>&1; then
    echo "test-runtime: FAIL: $f.c compiled; an unsupported pointer width must be an error" >&2
    exit 1
  fi
  if ! grep -q "unsupported pointer width" "$tmp/$f.log"; then
    echo "test-runtime: FAIL: $f.c failed without the width guard:" >&2
    cat "$tmp/$f.log" >&2
    exit 1
  fi
  echo "ok: pointer width, $f rejected"
done

cat > "$tmp/abi32main.c" <<'EOF'
/* A runtime test for the 32-bit selection: the small/GMP boundary, the checked
   `WIZ_BOX`, and machine words. It is compiled with -DWIZ_ABI_TEST_WORD_BITS=32 on
   this host (or with a real -m32 below). */
#include <stdio.h>
#include <stdint.h>
#include "wiz_rt.h"

static int fails = 0;
#define CHECK(c) do { if (!(c)) { fprintf(stderr, "FAIL: %s\n", #c); fails++; } } while (0)

int main(void) {
  _Static_assert(WIZ_WORD_BITS == 32, "this test selects a 32-bit word");
  _Static_assert(WIZ_SMALL_BITS == 30, "the 32-bit small int is 30 bits");
  CHECK(WIZ_IS_SCALAR(wiz_out_nat(WIZ_MAX_SMALL)));
  CHECK(wiz_in_nat(wiz_out_nat(WIZ_MAX_SMALL)) == (uint64_t)WIZ_MAX_SMALL);
  uint64_t first = (uint64_t)WIZ_MAX_SMALL + 1;      /* 2^30: the first GMP Nat */
  CHECK(!WIZ_IS_SCALAR(wiz_out_nat(first)));
  CHECK(wiz_in_nat(wiz_out_nat(first)) == first);
  CHECK(!WIZ_IS_SCALAR(WIZ_BOX(1073741824UL)));      /* a 2^30 literal: checked box */
  CHECK(wiz_in_nat(WIZ_BOX(1073741824UL)) == 1073741824UL);
  CHECK(wiz_in_nat(wiz_nat_lit("1073741824")) == first);
  /* small + small is above the small range: GMP, exact */
  CHECK(wiz_in_nat(wiz_nat_add(wiz_out_nat(WIZ_MAX_SMALL), wiz_out_nat(WIZ_MAX_SMALL)))
        == 2 * (uint64_t)WIZ_MAX_SMALL);
  /* the largest small squared needs 60 bits: GMP, exact */
  {
    uint64_t m = WIZ_MAX_SMALL;
    CHECK(wiz_in_nat(wiz_nat_mul(wiz_out_nat(m), wiz_out_nat(m))) == m * m);
  }
  CHECK(wiz_in_nat(wiz_nat_shiftLeft(WIZ_BOX(1), WIZ_BOX(30))) == first);
  CHECK(wiz_in_nat(wiz_nat_shiftRight(wiz_out_nat(first), WIZ_BOX(30))) == 1);
  /* a 64-bit machine word above the small range: a raw box, not a truncated scalar */
  CHECK(wiz_in_nat(wiz_word_to_bits(wiz_word_of_bits(wiz_out_nat(1ULL << 40)))) == (1ULL << 40));
  /* a drop mask with a bit above the 32-bit small range is a GMP Nat: `dropMoved`
     reads and consumes it (a 31-field constructor, field 30 moved) */
  {
    wiz_val o = wiz_ctor_new(0, 31);
    for (uint32_t i = 0; i < 31; i++) ((wiz_ctor *)o)->fields[i] = WIZ_BOX(i);
    wiz_val r = wiz_drop_moved(o, WIZ_BOX((uint64_t)1 << 30));
    CHECK(WIZ_IS_SCALAR(r));
    wiz_dec(r);
  }
  return fails ? 1 : 0;
}
EOF

# ---- the 30-bit path's *logic*, executed on this host: WIZ_ABI_TEST_WORD_BITS makes
# the runtime select 30-bit small ints and the checked WIZ_BOX even though the storage
# word is 64-bit. This runs everywhere (no -m32 needed); a real -m32 build below also
# checks the 32-bit word itself.
if ! cc -O1 -DWIZ_API= -DWIZ_ABI_TEST_WORD_BITS=32 -I "$root/runtime" $cflags \
      -c "$tmp/runtime.c" -o "$tmp/runtime30.o"; then
  echo "test-runtime: FAIL: compiling the runtime with the 32-bit selection failed" >&2
  exit 1
fi
if ! cc -O1 -DWIZ_API= -DWIZ_ABI_TEST_WORD_BITS=32 -I "$root/runtime" $cflags \
      "$tmp/abi32main.c" "$tmp/runtime30.o" ${WIZ_LDFLAGS:-} -lgmp -lpthread \
      -o "$tmp/abi32main-host"; then
  echo "test-runtime: FAIL: linking the 32-bit-selection runtime test failed" >&2
  exit 1
fi
if ! "$tmp/abi32main-host"; then
  echo "test-runtime: FAIL: the 32-bit-selection runtime test failed" >&2
  exit 1
fi
echo "ok: the 32-bit selection's runtime logic (small/GMP boundary, checked WIZ_BOX, machine words, drop mask)"

# ---- a real 32-bit compile and run, when this machine has the toolchain for it. The
# probe uses the system GMP (the dev shell's WIZ_CFLAGS/WIZ_LDFLAGS are for the host
# width), so its failure just means "no 32-bit GMP/libc here".

cat > "$tmp/probe32.c" <<'EOF'
#include <stdint.h>
#include <gmp.h>
#include <pthread.h>
int main(void) {
  mpz_t z; mpz_init(z); mpz_clear(z);
  return sizeof(uintptr_t) == 4 ? 0 : 1;
}
EOF

if cc -m32 "$tmp/probe32.c" -lgmp -lpthread -o "$tmp/probe32" >/dev/null 2>&1 &&
   "$tmp/probe32"; then
  echo "ok: a 32-bit toolchain and GMP are available"
  if ! cc -m32 -fsyntax-only -Wall -Wextra -I "$root/runtime" -DWIZ_API= "$tmp/runtime.c"; then
    echo "test-runtime: FAIL: the runtime does not compile with -m32" >&2
    exit 1
  fi
  echo "ok: the runtime compiles with -m32 (WIZ_API=)"
  if ! cc -m32 -O1 -DWIZ_API= -I "$root/runtime" -c "$tmp/runtime.c" -o "$tmp/runtime32.o"; then
    echo "test-runtime: FAIL: compiling the runtime for 32-bit failed" >&2
    exit 1
  fi
  if ! cc -m32 -O1 -DWIZ_API= -I "$root/runtime" "$tmp/abi32main.c" "$tmp/runtime32.o" \
        -lgmp -lpthread -o "$tmp/abi32main"; then
    # 8-byte atomics on i386 may be calls into libatomic
    if ! cc -m32 -O1 -DWIZ_API= -I "$root/runtime" "$tmp/abi32main.c" "$tmp/runtime32.o" \
          -lgmp -lpthread -latomic -o "$tmp/abi32main"; then
      echo "test-runtime: FAIL: linking the 32-bit runtime test failed" >&2
      exit 1
    fi
  fi
  if ! "$tmp/abi32main"; then
    echo "test-runtime: FAIL: the 32-bit runtime test failed" >&2
    exit 1
  fi
  echo "ok: a real -m32 build and run (the 32-bit word itself)"
else
  echo "skip: no 32-bit toolchain with GMP (the 30-bit path logic was still run above)"
fi

echo "test-runtime: all checks passed"
