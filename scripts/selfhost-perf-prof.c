/* A call-counting, TSC-timing profiler for a C file compiled with
 * -finstrument-functions (scripts/selfhost-perf.sh does that; nothing in the
 * repository is compiled this way).
 *
 * GCC calls __cyg_profile_func_enter/__cyg_profile_func_exit on entry to and exit
 * from every function of a translation unit compiled with -finstrument-functions.
 * The hooks time the call with rdtsc and accumulate, per function address, the
 * number of calls, the inclusive ticks and the exclusive ticks (the inclusive time
 * minus the time spent in instrumented callees).  At exit they print one line per
 * function, plus a first line with the clock's tick count over the process' life:
 *
 *   ticks <total-ticks> <seconds>
 *   fn <address-hex> <calls> <excl-ticks> <incl-ticks>
 *
 * Addresses are resolved offline (`nm -n --defined-only`) because the generated C
 * has static functions, which dladdr does not see.  Nothing here is a sampling
 * profiler: the numbers are exact call counts and wall-clock shares, inflated by
 * the instrumentation itself (one rdtsc pair and a hash probe per call), which is
 * why the script reports shares, not absolute seconds, for the function table.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

static inline uint64_t rdtsc(void) {
  unsigned lo, hi;
  __asm__ __volatile__("rdtsc" : "=a"(lo), "=d"(hi));
  return ((uint64_t)hi << 32) | (uint64_t)lo;
}

#define NCAP (1u << 20)
typedef struct {
  uint64_t fn, calls, excl, incl;
} Ent;
static Ent tab[NCAP];
static uint64_t ticks_begin, ticks_end;
static double wall_begin;
static int started;

#define DEPTH (1u << 15)
static uint64_t st_ts[DEPTH], st_fn[DEPTH], st_child[DEPTH];
static int depth;
static long dropped;

static Ent *slot(uint64_t fn) {
  uint64_t i = (fn >> 4) * 0x9e3779b97f4a7c15ULL;
  i &= NCAP - 1;
  while (tab[i].fn && tab[i].fn != fn) i = (i + 1) & (NCAP - 1);
  if (!tab[i].fn) tab[i].fn = fn;
  return &tab[i];
}

static void dump(void) __attribute__((no_instrument_function));
static void dump(void) {
  ticks_end = rdtsc();
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  double secs = (double)ts.tv_sec + (double)ts.tv_nsec / 1e9 - wall_begin;
  printf("ticks %llu %.6f\n", (unsigned long long)(ticks_end - ticks_begin), secs);
  if (dropped)
    fprintf(stderr, "selfhost-perf-prof: %ld calls past depth %u were not timed\n",
            dropped, DEPTH);
  for (unsigned i = 0; i < NCAP; i++)
    if (tab[i].fn)
      printf("fn %llx %llu %llu %llu\n", (unsigned long long)tab[i].fn,
             (unsigned long long)tab[i].calls, (unsigned long long)tab[i].excl,
             (unsigned long long)tab[i].incl);
  fflush(stdout);
}

void __cyg_profile_func_enter(void *fn, void *site) __attribute__((no_instrument_function));
static void prof_start(void) __attribute__((no_instrument_function));
static void prof_start(void) {
  started = 1;
  ticks_begin = rdtsc();
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  wall_begin = (double)ts.tv_sec + (double)ts.tv_nsec / 1e9;
  atexit(dump);
}

void __cyg_profile_func_enter(void *fn, void *site) {
  (void)site;
  if (!started) prof_start();
  uint64_t t = rdtsc();
  if (depth < (int)DEPTH) {
    st_fn[depth] = (uint64_t)fn;
    st_ts[depth] = t;
    st_child[depth] = 0;
    depth++;
  } else {
    dropped++;
  }
}

void __cyg_profile_func_exit(void *fn, void *site) __attribute__((no_instrument_function));
void __cyg_profile_func_exit(void *fn, void *site) {
  (void)fn;
  (void)site;
  uint64_t t = rdtsc();
  if (depth <= 0) return;
  depth--;
  uint64_t d = t - st_ts[depth];
  uint64_t child = st_child[depth];
  Ent *e = slot(st_fn[depth]);
  e->calls++;
  e->excl += d - child;
  e->incl += d;
  if (depth > 0) st_child[depth - 1] += d;
}
