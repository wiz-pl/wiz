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
# cannot drift silently. Both again with -DWIZ_NO_THREADS (the one-thread build of the
# Wasm pages, concurrency plan R2), and once with -DWIZ_RC_ATOMIC (every count atomic).
#
# Then a small C program (nothreads.c below), linked against the runtime, run threaded and
# with WIZ_NO_THREADS: MVars and locks that never block work in both (and the one-thread
# build never marks anything shared); `wiz_run_main` runs main on a thread of its own
# only in the threaded build; and with WIZ_NO_THREADS, `Chan.fork` and waits that could
# never end stop with a clear message (exit 3).
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
check "WIZ_API=, WIZ_NO_THREADS" -DWIZ_API= -DWIZ_NO_THREADS
check "WIZ_API=static, WIZ_NO_THREADS" -DWIZ_API=static -DWIZ_NO_THREADS
check "WIZ_API=static, WIZ_RC_ATOMIC (every count atomic)" -DWIZ_API=static -DWIZ_RC_ATOMIC

cat > "$tmp/nothreads.c" <<'EOF'
#include "runtime.c"
#ifdef WIZ_NO_THREADS
static const int one_thread = 1;
#else
static const int one_thread = 0;
#endif
static pthread_t main_tid;
static int same_thread = -1;
static wiz_val entry(void) { same_thread = pthread_equal(pthread_self(), main_tid) != 0; return WIZ_BOX(7); }
#define EXPECT(c) do { if (!(c)) { fprintf(stderr, "nothreads.c:%d: %s\n", __LINE__, #c); return 1; } } while (0)
int main(int argc, char **argv) {
  const char *what = argc > 1 ? argv[1] : "";
  if (!strcmp(what, "ok")) {
    /* an MVar that never blocks; a heap value through it stays unshared with one thread */
    wiz_val mv = wiz_mvar_new_full(WIZ_BOX(41));
    wiz_inc(mv); EXPECT(wiz_mvar_take(mv) == WIZ_BOX(41));
    wiz_val o = wiz_ctor_new(5, 0);
    wiz_inc(mv); wiz_mvar_put(mv, o);
    wiz_inc(mv); wiz_val back = wiz_mvar_take(mv);
    EXPECT(back == o);
    EXPECT(((wiz_hdr *)o)->rc == (one_thread ? 1 : -1));
    wiz_dec(back);
    wiz_val l = wiz_lock_new();
    wiz_inc(l); wiz_val g = wiz_lock_acquire(l);
    wiz_lock_release(l, g); /* consumes the last reference to the lock */
    wiz_dec(mv);
    EXPECT(wiz_live == 0);
    puts("ok");
    return 0;
  }
  if (!strcmp(what, "main")) {
    main_tid = pthread_self();
    int rc = wiz_run_main(entry, 0);
    EXPECT(rc == 0);
    EXPECT(same_thread == one_thread);
    return 0;
  }
  if (!strcmp(what, "fork")) { wiz_chan_fork(WIZ_BOX(0)); puts("forked"); return 0; }
  if (!strcmp(what, "take")) { wiz_mvar_take(wiz_mvar_new()); puts("took"); return 0; }
  if (!strcmp(what, "put")) { wiz_mvar_put(wiz_mvar_new_full(WIZ_BOX(1)), WIZ_BOX(2)); puts("put"); return 0; }
  if (!strcmp(what, "lock")) {
    wiz_val l = wiz_lock_new(); wiz_inc(l); wiz_inc(l);
    wiz_lock_acquire(l); wiz_lock_acquire(l); puts("acquired twice"); return 0;
  }
  return 1;
}
EOF

# GMP's library: the dev shell's WIZ_LDFLAGS, else the system's
ldflags=${WIZ_LDFLAGS:-}
build() { # build EXE CC-ARGS…
  local exe=$1; shift
  if ! cc -O1 -w -I "$root/runtime" -I "$tmp" $cflags "$@" -o "$exe" "$tmp/nothreads.c" $ldflags -lgmp -lpthread; then
    echo "test-runtime: FAIL: nothreads.c does not build ($*)" >&2
    exit 1
  fi
}
build "$tmp/mt" -DWIZ_API=static
build "$tmp/st" -DWIZ_API=static -DWIZ_NO_THREADS
build "$tmp/at" -DWIZ_API=static -DWIZ_RC_ATOMIC

expect() { # expect DESCRIPTION EXIT-CODE STDOUT STDERR-FRAGMENT (empty: no stderr) EXE ARGS…
  local what=$1 code=$2 out=$3 err=$4; shift 4
  local got_out got_code=0
  got_out=$("$@" 2>"$tmp/err") || got_code=$?
  if [ "$got_code" != "$code" ] || [ "$got_out" != "$out" ] \
     || { [ -n "$err" ] && ! grep -qF -- "$err" "$tmp/err"; } || { [ -z "$err" ] && [ -s "$tmp/err" ]; }; then
    echo "test-runtime: FAIL: $what: exit $got_code (want $code), stdout '$got_out' (want '$out'), stderr:" >&2
    cat "$tmp/err" >&2
    exit 1
  fi
  echo "ok: $what"
}
expect "threaded: MVars and locks" 0 ok "" "$tmp/mt" ok
expect "threaded: main runs on a thread of its own" 0 7 "" "$tmp/mt" main
expect "WIZ_RC_ATOMIC: MVars and locks" 0 ok "" "$tmp/at" ok
expect "WIZ_NO_THREADS: MVars and locks, nothing marked shared" 0 ok "" "$tmp/st" ok
expect "WIZ_NO_THREADS: main runs on the calling thread" 0 7 "" "$tmp/st" main
expect "WIZ_NO_THREADS: Chan.fork stops with a clear message" 3 "" \
  "wiz: Chan.fork: threads are not available in this build (WIZ_NO_THREADS)" "$tmp/st" fork
expect "WIZ_NO_THREADS: taking from an empty MVar stops" 3 "" \
  "wiz: MVar.take of an empty MVar would wait forever: threads are not available" "$tmp/st" take
expect "WIZ_NO_THREADS: putting into a full MVar stops" 3 "" \
  "wiz: MVar.put into a full MVar would wait forever: threads are not available" "$tmp/st" put
expect "WIZ_NO_THREADS: acquiring a held lock stops" 3 "" \
  "wiz: Lock.acquire of a held lock would wait forever: threads are not available" "$tmp/st" lock

echo "test-runtime: all checks passed"
