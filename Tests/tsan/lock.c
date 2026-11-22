/* Shared state for the lock tests in Tests/tsan: plain `uint64_t`, no atomics and no
   pthread calls, so only the Wiz `Lock` can make the accesses safe.  The runtime's own
   MVars and channels are atomic by themselves, so a test of mutual exclusion needs
   memory the runtime does not synchronise (docs/stages/25-concurrency.md, 25d). */

#include <stdint.h>
#include <sched.h>

/* volatile: the load and the store stay on either side of the loop below (the point is
   a lost update, not the optimiser's opinion), and the accesses are still plain, not
   atomic */
static volatile uint64_t counter = 0;
static volatile uint64_t inside = 0;
static volatile uint64_t overlap = 0;

/* A read-modify-write with work between the load and the store: two threads that are
   not excluded lose increments, and the loop is not a timing measurement (it runs on
   every call, held or not). */
uint64_t lock_bump(uint64_t k) {
  uint64_t v = counter;
  for (volatile int i = 0; i < 64; i++) { }
  counter = v + k;
  return counter;
}

/* The overlap detector: called on entry to and exit from the critical section.  With
   the lock working, `inside` is always 1 here; any other value means two threads were
   in the critical section at once. */
uint64_t lock_enter(void) {
  if (++inside != 1) overlap = 1;
  return inside;
}
uint64_t lock_leave(void) { return --inside; }

/* Give the scheduler a chance to run another thread *inside* the critical section.
   With the lock working the others are blocked in acquire, so this changes nothing;
   with a lock that does not exclude it lets a second thread in, so the overlap detector
   fires even when the job is confined to one CPU (a Slurm `heavy` job is). */
uint64_t lock_yield(void) { sched_yield(); return 0; }

uint64_t lock_counter(void) { return counter; }
uint64_t lock_overlap(void) { return overlap; }
