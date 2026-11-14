/* The runtime's threads: a channel message between the main thread and a forked one,
   MVars as completion signals and as a mutex-protected counter, and a lock shared by
   four threads. ThreadSanitizer builds this program too. */
#include "corpus.h"
#include <string.h>

#define WORKERS 4
#define INCREMENTS 200

/* args: done (captured), endpoint, world */
static wiz_val recv_child(wiz_val *args) {
  wiz_val done = args[0], endpoint = args[1];
  wiz_dec(args[2]); /* the world */
  wiz_val pair = wiz_chan_recv(endpoint);
  wiz_val msg = wiz_field_at(share(pair), WIZ_BOX(0));
  wiz_val c = wiz_field_at(pair, WIZ_BOX(1));
  check(wiz_str_eq(msg, wiz_str_of_cstr("shared text")), "the message crossed the thread");
  wiz_chan_close(c);
  wiz_mvar_put(done, WIZ_BOX(1));
  return WIZ_BOX(0);
}

/* args: lock, counter, done (captured), endpoint, world */
static wiz_val counter_child(wiz_val *args) {
  wiz_val lock = args[0], counter = args[1], done = args[2], endpoint = args[3];
  wiz_dec(args[4]); /* the world */
  wiz_chan_close(endpoint); /* this child has nothing to say on its channel */
  for (int i = 0; i < INCREMENTS; i++) {
    /* each call consumes a reference; the worker keeps its own (the extra inc) */
    wiz_inc(lock);
    wiz_val guard = wiz_lock_acquire(lock);
    wiz_inc(lock);
    wiz_inc(counter);
    wiz_val p = wiz_mvar_take_hole(counter);
    wiz_val old = wiz_field_at(share(p), WIZ_BOX(0));
    wiz_val hole = wiz_field_at(p, WIZ_BOX(1));
    uint64_t n = nat_of(old) + 1;
    wiz_inc(counter);
    wiz_mvar_fill(counter, hole, wiz_out_nat(n));
    wiz_lock_release(lock, guard);
  }
  wiz_dec(lock);
  wiz_dec(counter);
  wiz_mvar_put(done, WIZ_BOX(1));
  return WIZ_BOX(0);
}

static wiz_val entry(void) {
  /* a channel from the main thread to a forked one, and an MVar as its completion */
  wiz_val done = wiz_mvar_new();
  wiz_inc(done); /* one reference for the child, one kept here */
  wiz_val captured[1] = {done};
  wiz_val child = wiz_clo_new(recv_child, 3, 1, captured);
  wiz_val endpoint = wiz_chan_fork(child); /* the child gets the other end */
  wiz_val endpoint2 = wiz_chan_send(endpoint, wiz_str_of_cstr("shared text"));
  wiz_chan_close(endpoint2);
  check(nat_of(wiz_mvar_take(done)) == 1, "the child finished");

  /* four threads bump one counter under a lock; each announces its end on an MVar */
  wiz_val lock = wiz_lock_new();
  wiz_val counter = wiz_mvar_new_full(WIZ_BOX(0));
  wiz_val ready = wiz_mvar_new();
  for (int i = 0; i < WORKERS; i++) {
    wiz_inc(lock);
    wiz_inc(counter);
    wiz_inc(ready);
    wiz_val cap[3] = {lock, counter, ready};
    wiz_val worker = wiz_clo_new(counter_child, 5, 3, cap); /* + endpoint + world */
    wiz_val e = wiz_chan_fork(worker);
    wiz_chan_close(e);
  }
  for (int i = 0; i < WORKERS; i++) {
    if (i + 1 < WORKERS) wiz_inc(ready); /* each take consumes a reference */
    wiz_val v = wiz_mvar_take(ready);
    check(nat_of(v) == 1, "a worker finished");
  }
  check(nat_of(wiz_mvar_take(counter)) == WORKERS * INCREMENTS, "the lock protected every increment");
  wiz_dec(lock);

  /* a value written to an MVar and read back without taking it */
  wiz_val mv = wiz_mvar_new_full(wiz_out_nat(9));
  wiz_inc(mv); /* read and take each consume a reference */
  check(nat_of(wiz_mvar_read(mv)) == 9, "MVar.read");
  check(nat_of(wiz_mvar_take(mv)) == 9, "MVar.take");

  printf("threads: ok\n");
  return WIZ_BOX(0);
}

int main(void) {
  int rc = wiz_run_main(entry, 0);
  if (wiz_corpus_failures) fprintf(stderr, "corpus: %d check(s) failed\n", wiz_corpus_failures);
  return wiz_corpus_failures ? 1 : rc;
}
