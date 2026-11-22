#!/usr/bin/env bash
# The C runtime compiles on its own: `runtime/wiz_rt.h` (value representation, tags,
# object layouts, prototypes) plus the seven area files (`runtime/rt_*.inc`), as a
# translation unit that is not generated code.
#
# `cc -fsyntax-only -Wall -Wextra`, in both ABI settings:
#   * WIZ_API= (empty): every entry point is an external symbol, as in the LLVM
#     backend's runtime object (Wiz/Compiler/Build.lean, compileLLVM);
#   * WIZ_API=static: every entry point is `static`, as in a generated C program.
# The header's prototypes are checked against the definitions by this compile, so they
# cannot drift silently. Both again with -DWIZ_NO_THREADS (the one-thread build of the
# Wasm pages, concurrency plan R2), once with -DWIZ_RC_ATOMIC (every count atomic), and
# once with __EMSCRIPTEN__ (without and with __EMSCRIPTEN_PTHREADS__), which checks the
# header's Emscripten auto-enable translates the one-thread runtime.
#
# Then a small C program (nothreads.c below), linked against the runtime, run threaded and
# with WIZ_NO_THREADS: MVars and locks that never block work in both (and the one-thread
# build never marks anything shared); a channel that sends before it receives carries a
# message on one thread; `wiz_run_main` runs main on a thread of its own only in the
# threaded build; and with WIZ_NO_THREADS, `Chan.fork` and waits that could never end
# (an empty or full MVar, a held lock, a channel with no message) stop with a clear
# message (exit 3).
#
# The WIZ_NO_THREADS binary is built against a stub <pthread.h> (stub/pthread.h below) and
# linked without -lpthread, so this checks the real claim: a build with no threads needs
# no pthreads (Emscripten without -pthread, the target of R2). The threaded binaries link
# real pthreads.
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
#include "rt_storage.inc"
#include "rt_con.inc"
/* the header's Emscripten auto-enable must have taken effect (see the check below) */
#ifdef WIZ_EXPECT_NO_THREADS
#ifndef WIZ_NO_THREADS
#error "WIZ_NO_THREADS should be on: __EMSCRIPTEN__ without __EMSCRIPTEN_PTHREADS__"
#endif
#endif
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
# Emscripten without -pthread: the header turns WIZ_NO_THREADS on by itself. This is not
# an Emscripten build (there is no emcc or emscripten sysroot here), but it compiles the
# auto-enable's translation unit with the same defines, and the runtime.c guard fails if
# the macro did not take effect. With __EMSCRIPTEN_PTHREADS__ the threaded path stays on.
check "WIZ_API=static, __EMSCRIPTEN__ without pthreads (the auto-enable)" \
  -DWIZ_API=static -D__EMSCRIPTEN__ -DWIZ_EXPECT_NO_THREADS
check "WIZ_API=static, __EMSCRIPTEN__ with pthreads (no auto-enable)" \
  -DWIZ_API=static -D__EMSCRIPTEN__ -D__EMSCRIPTEN_PTHREADS__

# The one-thread build's claim is that it needs no threads at all. glibc now has the
# pthread entry points in libc, so "links without -lpthread" proves nothing; instead every
# pthread name the runtime uses is redirected by -Wl,--wrap= to stub in stubpthread.c.
# Mutexes and condition variables become no-ops (on one thread nothing contends, and every
# wait that could block is a `wiz_no_threads` stop), and pthread_create stops the program
# if it is ever reached (it is not: `wiz_spawn` stops first).
cat > "$tmp/stubpthread.c" <<'EOF'
/* Stub pthread entry points for the WIZ_NO_THREADS binary (see -Wl,--wrap). */
#include <stdio.h>
#include <stdlib.h>
int __wrap_pthread_mutex_init(void *m, const void *a) { (void)m; (void)a; return 0; }
int __wrap_pthread_mutex_destroy(void *m) { (void)m; return 0; }
int __wrap_pthread_mutex_lock(void *m) { (void)m; return 0; }
int __wrap_pthread_mutex_unlock(void *m) { (void)m; return 0; }
int __wrap_pthread_cond_init(void *c, const void *a) { (void)c; (void)a; return 0; }
int __wrap_pthread_cond_destroy(void *c) { (void)c; return 0; }
int __wrap_pthread_cond_broadcast(void *c) { (void)c; return 0; }
int __wrap_pthread_cond_wait(void *c, void *m) { (void)c; (void)m; return 0; }
int __wrap_pthread_attr_init(void *a) { (void)a; return 0; }
int __wrap_pthread_attr_destroy(void *a) { (void)a; return 0; }
int __wrap_pthread_attr_setstacksize(void *a, unsigned long n) { (void)a; (void)n; return 0; }
int __wrap_pthread_attr_setdetachstate(void *a, int d) { (void)a; (void)d; return 0; }
unsigned long __wrap_pthread_self(void) { return 0; }
int __wrap_pthread_equal(unsigned long a, unsigned long b) { return a == b; }
int __wrap_pthread_sigmask(int how, const void *set, void *old) {
  (void)how; (void)set; (void)old; return 0;
}
int __wrap_pthread_create(void *t, const void *a, void *(*f)(void *), void *p) {
  (void)t; (void)a; (void)f; (void)p;
  fprintf(stderr, "stub pthread: pthread_create was called in the one-thread build\n");
  exit(99);
}
EOF

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
/* A channel whose two ends stay in this thread. `Chan.fork` is the only Wiz-level way to
   make one and it needs a thread, so this reaches the send/recv paths of the one-thread
   build directly: a message queued before the receive never waits. */
static wiz_chan *one_chan(void) {
  wiz_chan *ch = (wiz_chan *)calloc(1, sizeof(wiz_chan));
  pthread_mutex_init(&ch->mu, NULL);
  pthread_cond_init(&ch->cv, NULL);
  ch->ends = 2;
  for (int s = 0; s < 2; s++) { ch->end[s].ch = ch; ch->end[s].side = s; }
  return ch;
}
/* The recovery boundary (rt_con.inc, `wiz_stop_run`): a Wiz closure String → String. */
static wiz_val guard_ok(wiz_val *a) { wiz_dec(a[0]); return wiz_out_string("survived"); }
static wiz_val guard_exit(wiz_val *a) { wiz_dec(a[0]); wiz_sys_exit(7); }
static wiz_val guard_write(wiz_val *a) { wiz_dec(a[0]); wiz_io_write_file("/nonexistent-wiz-test/x", "x"); }
#ifdef WIZ_NO_THREADS
static wiz_val guard_stop(wiz_val *a) { wiz_dec(a[0]); wiz_no_threads("Guard.test"); }
#endif
static wiz_val guard_closure(wiz_val (*fn)(wiz_val *)) { return wiz_clo_new(fn, 1, 0, NULL); }

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
  if (!strcmp(what, "chan")) {
    /* send before receive: the message is buffered, so no wait, on any number of threads */
    wiz_chan *ch = one_chan();
    wiz_val a = wiz_out_ptr(&ch->end[0], wiz_chan_end_fin);
    wiz_val b = wiz_out_ptr(&ch->end[1], wiz_chan_end_fin);
    EXPECT(wiz_chan_send(a, WIZ_BOX(42)) == a);
    wiz_val r = wiz_chan_recv(b); /* consumes b and the message */
    EXPECT(((wiz_ctor *)r)->fields[0] == WIZ_BOX(42));
    wiz_dec(r); /* drops the endpoint inside the pair (b) */
    wiz_dec(a);
    EXPECT(wiz_live == 0);
    puts("chan 42");
    return 0;
  }
  if (!strcmp(what, "recv")) {
    /* an empty channel: only another thread could send into it */
    wiz_chan *ch = one_chan();
    wiz_chan_recv(wiz_out_ptr(&ch->end[1], wiz_chan_end_fin));
    puts("received");
    return 0;
  }
  if (!strcmp(what, "main")) {
    main_tid = pthread_self();
    int rc = wiz_run_main(entry, 0);
    EXPECT(rc == 0);
    EXPECT(same_thread == one_thread);
    return 0;
  }
  if (!strcmp(what, "guard")) {
    /* a clean stop inside the boundary longjmps back with its code; the runtime (and
       whatever the embedding host keeps beside it) survives; the next call runs */
    char *t = wiz_stop_run(guard_closure(guard_exit));
    EXPECT(t != NULL && t[0] == 0);
    EXPECT(wiz_stop_code_value(0) == 8);       /* exit 7 is reported as 7 + 1 */
    EXPECT(!strcmp(wiz_stop_run(guard_closure(guard_ok)), "survived"));
    EXPECT(wiz_stop_code_value(0) == 0);       /* ran to the end */
    EXPECT(!strcmp(wiz_stop_run(guard_closure(guard_write)), ""));
    EXPECT(wiz_stop_code_value(0) == 2);       /* the failed write exits 1 */
    EXPECT(!strcmp(wiz_stop_run(guard_closure(guard_ok)), "survived"));
    puts("survived");
    return 0;
  }
#ifdef WIZ_NO_THREADS
  if (!strcmp(what, "guard-nothreads")) {
    /* the one-threaded refusal is caught the same way, after printing its message */
    EXPECT(wiz_stop_run(guard_closure(guard_stop))[0] == 0);
    EXPECT(wiz_stop_code_value(0) == 4);       /* exit 3 is reported as 3 + 1 */
    EXPECT(!strcmp(wiz_stop_run(guard_closure(guard_ok)), "survived"));
    puts("survived");
    return 0;
  }
#endif
  if (!strcmp(what, "sysexit")) { wiz_sys_exit(7); puts("not reached"); return 0; }
  if (!strcmp(what, "fork")) { wiz_chan_fork(WIZ_BOX(0)); puts("forked"); return 0; }
  if (!strcmp(what, "take")) { wiz_mvar_take(wiz_mvar_new()); puts("took"); return 0; }
  if (!strcmp(what, "put")) { wiz_mvar_put(wiz_mvar_new_full(WIZ_BOX(1)), WIZ_BOX(2)); puts("put"); return 0; }
  if (!strcmp(what, "lock")) {
    wiz_val l = wiz_lock_new(); wiz_inc(l); wiz_inc(l);
    wiz_lock_acquire(l); wiz_lock_acquire(l); puts("acquired twice"); return 0;
  }
  /* (audit F15) the expansive number natives refuse a result above 2^24 bits, the same
     bound as the interpreter's `maxBits`: a clean exit 3, not a GMP allocation. */
  if (!strcmp(what, "natshift")) { wiz_nat_shiftLeft(WIZ_BOX(1), WIZ_BOX(1000000000)); puts("shifted"); return 0; }
  if (!strcmp(what, "natpow")) { wiz_nat_pow(WIZ_BOX(2), WIZ_BOX(1000000000)); puts("powered"); return 0; }
  if (!strcmp(what, "natpow-base3")) { wiz_nat_pow(WIZ_BOX(3), WIZ_BOX(20000000)); puts("powered"); return 0; }
  if (!strcmp(what, "natbound-ok")) {
    /* the bases whose result stays small are never refused */
    EXPECT(wiz_nat_shiftLeft(WIZ_BOX(0), WIZ_BOX(1000000000)) == WIZ_BOX(0));
    EXPECT(wiz_nat_pow(WIZ_BOX(0), WIZ_BOX(1000000000)) == WIZ_BOX(0));
    EXPECT(wiz_nat_pow(WIZ_BOX(1), WIZ_BOX(1000000000)) == WIZ_BOX(1));
    /* a result just under the bound is computed: 2^1000 has 1001 bits, 5·2^200 has 203 */
    wiz_val big = wiz_nat_pow(WIZ_BOX(2), WIZ_BOX(1000));
    EXPECT(wiz_is_big(big) && mpz_sizeinbase(((wiz_big *)big)->z, 2) == 1001);
    wiz_dec(big);
    wiz_val sh = wiz_nat_shiftLeft(WIZ_BOX(5), WIZ_BOX(200));
    EXPECT(wiz_is_big(sh) && mpz_sizeinbase(((wiz_big *)sh)->z, 2) == 203);
    wiz_dec(sh);
    puts("bounded");
    return 0;
  }
  /* (audit F17) `wiz_sys_remove_all` never follows a link, so a link (reached with a
     trailing slash, which `lstat`/`opendir` would resolve) is removed as a link and the
     tree it names survives; a real tree containing a link goes without entering it. */
  if (!strcmp(what, "rmrf-link")) {
    char base[] = "/tmp/wiz-rmrf-XXXXXX", p[512];
    EXPECT(mkdtemp(base) != NULL);
    snprintf(p, sizeof p, "%s/d", base); EXPECT(mkdir(p, 0700) == 0);
    snprintf(p, sizeof p, "%s/outside", base); EXPECT(mkdir(p, 0700) == 0);
    snprintf(p, sizeof p, "%s/outside/keep", base);
    FILE *f = fopen(p, "w"); EXPECT(f != NULL); fputs("kept", f); fclose(f);
    snprintf(p, sizeof p, "%s/outside", base);
    { char l[512]; snprintf(l, sizeof l, "%s/d/link", base); EXPECT(symlink(p, l) == 0); }
    { char l[512]; snprintf(l, sizeof l, "%s/d/link/", base); EXPECT(wiz_sys_remove_all(l) == 0); }
    struct stat st;
    snprintf(p, sizeof p, "%s/outside/keep", base); EXPECT(lstat(p, &st) == 0);
    snprintf(p, sizeof p, "%s/d/link", base); EXPECT(lstat(p, &st) != 0);
    snprintf(p, sizeof p, "%s/d", base); EXPECT(lstat(p, &st) == 0); /* the parent stays */
    EXPECT(wiz_sys_remove_all(base) == 0);
    EXPECT(lstat(base, &st) != 0);
    puts("rmrf link");
    return 0;
  }
  if (!strcmp(what, "rmrf-tree")) {
    char base[] = "/tmp/wiz-rmrf-XXXXXX", p[512];
    EXPECT(mkdtemp(base) != NULL);
    snprintf(p, sizeof p, "%s/tree", base); EXPECT(mkdir(p, 0700) == 0);
    snprintf(p, sizeof p, "%s/tree/sub", base); EXPECT(mkdir(p, 0700) == 0);
    snprintf(p, sizeof p, "%s/tree/sub/file", base);
    FILE *f = fopen(p, "w"); EXPECT(f != NULL); fputs("x", f); fclose(f);
    snprintf(p, sizeof p, "%s/outside", base); EXPECT(mkdir(p, 0700) == 0);
    snprintf(p, sizeof p, "%s/outside/keep", base);
    f = fopen(p, "w"); EXPECT(f != NULL); fputs("k", f); fclose(f);
    snprintf(p, sizeof p, "%s/tree/sub/link", base);
    { char o[512]; snprintf(o, sizeof o, "%s/outside", base); EXPECT(symlink(o, p) == 0); }
    snprintf(p, sizeof p, "%s/tree", base); EXPECT(wiz_sys_remove_all(p) == 0);
    struct stat st;
    snprintf(p, sizeof p, "%s/outside/keep", base); EXPECT(lstat(p, &st) == 0);
    snprintf(p, sizeof p, "%s/tree", base); EXPECT(lstat(p, &st) != 0);
    EXPECT(wiz_sys_remove_all(base) == 0);
    puts("rmrf tree");
    return 0;
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
build "$tmp/at" -DWIZ_API=static -DWIZ_RC_ATOMIC
# the one-thread build: no -lpthread, every pthread name wrapped to the stub
wrap=""
for f in mutex_init mutex_destroy mutex_lock mutex_unlock cond_init cond_destroy \
         cond_broadcast cond_wait attr_init attr_destroy attr_setstacksize \
         attr_setdetachstate self equal sigmask create; do
  wrap="$wrap -Wl,--wrap=pthread_$f"
done
if ! cc -O1 -w -I "$root/runtime" -I "$tmp" $cflags -DWIZ_API=static -DWIZ_NO_THREADS \
     -o "$tmp/st" "$tmp/nothreads.c" "$tmp/stubpthread.c" $ldflags -lgmp $wrap; then
  echo "test-runtime: FAIL: the WIZ_NO_THREADS build does not link with stub pthreads" >&2
  exit 1
fi
if nm -u "$tmp/st" | grep -q pthread; then
  echo "test-runtime: FAIL: the WIZ_NO_THREADS binary still needs pthread symbols:" >&2
  nm -u "$tmp/st" | grep pthread >&2
  exit 1
fi
echo "ok: WIZ_NO_THREADS links and runs with stub pthreads and no pthread symbols"

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
expect "threaded: a channel sends before it receives" 0 "chan 42" "" "$tmp/mt" chan
expect "WIZ_RC_ATOMIC: MVars and locks" 0 ok "" "$tmp/at" ok
expect "WIZ_NO_THREADS: MVars and locks, nothing marked shared" 0 ok "" "$tmp/st" ok
expect "WIZ_NO_THREADS: main runs on the calling thread" 0 7 "" "$tmp/st" main
expect "WIZ_NO_THREADS: a channel sends before it receives" 0 "chan 42" "" "$tmp/st" chan
expect "WIZ_NO_THREADS: Chan.fork stops with a clear message" 3 "" \
  "wiz: Chan.fork: threads are not available in this build (WIZ_NO_THREADS)" "$tmp/st" fork
expect "WIZ_NO_THREADS: receiving on an empty channel stops" 3 "" \
  "wiz: Chan.recv on an empty channel would wait forever: threads are not available" "$tmp/st" recv
expect "WIZ_NO_THREADS: taking from an empty MVar stops" 3 "" \
  "wiz: MVar.take of an empty MVar would wait forever: threads are not available" "$tmp/st" take
expect "WIZ_NO_THREADS: putting into a full MVar stops" 3 "" \
  "wiz: MVar.put into a full MVar would wait forever: threads are not available" "$tmp/st" put
expect "WIZ_NO_THREADS: acquiring a held lock stops" 3 "" \
  "wiz: Lock.acquire of a held lock would wait forever: threads are not available" "$tmp/st" lock
# The recovery boundary (rt_con.inc): an armed `wiz_stop_run` catches a clean stop, so
# the runtime survives with the code; with no boundary armed, `exit` is still `exit`.
expect "the boundary catches Process.exit and the next call runs" 0 survived \
  "wiz: /nonexistent-wiz-test/x: No such file or directory" "$tmp/mt" guard
expect "WIZ_NO_THREADS: the boundary catches the refusal" 0 survived \
  "wiz: Guard.test: threads are not available in this build (WIZ_NO_THREADS)" "$tmp/st" guard-nothreads
expect "no boundary: Process.exit still exits with its code" 7 "" "" "$tmp/mt" sysexit
# (audit F15) the compiled number natives refuse a result above 2^24 bits, the same bound
# as the interpreter's `maxBits`: a clean error, not a 125 MB (or larger) GMP allocation.
expect "Nat.shiftLeft refuses a shift above 2^24 bits" 3 "" \
  "wiz: Nat.shiftLeft: the result would have more than 16777216 bits" "$tmp/mt" natshift
expect "Nat.pow refuses an exponent above 2^24 bits" 3 "" \
  "wiz: Nat.pow: the result would have more than 16777216 bits" "$tmp/mt" natpow
expect "Nat.pow refuses a base > 1 whose log bound reaches 2^24 bits" 3 "" \
  "wiz: Nat.pow: the result would have more than 16777216 bits" "$tmp/mt" natpow-base3
expect "0/1 bases are not refused, and a result under the bound computes" 0 bounded "" "$tmp/mt" natbound-ok
# (audit F17) the recursive delete walks from an opened descriptor and never follows a link.
expect "removeAll removes a link, not the tree it names (a trailing slash)" 0 "rmrf link" "" "$tmp/mt" rmrf-link
expect "removeAll removes a tree without entering a link inside it" 0 "rmrf tree" "" "$tmp/mt" rmrf-tree

echo "test-runtime: all checks passed"
