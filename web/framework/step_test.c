/* The i32 word entry (web/step.c, `wiz-web/1`) against the runtime that ships:
   web/framework/step_gen.wiz exports the app's i64 entry (`wiz_loom_step`) and links
   this file, so the words in, the words out and the payload rule are checked on the
   generated wrapper rather than on a stub.

   The ABI's payload address is 32 bits, and so is the state word. A wasm64 module's
   linear memory is below 4 GiB by construction; a 64-bit host process is not, so the
   payload is placed on a page mmap asked for below 4 GiB (Linux's MAP_32BIT). The state
   stays a Nat (kind `n`: a plain 64-bit number the test can compare) for that reason;
   step_gen.wiz explains why the pages' kind `w` value word goes through the same shim
   unchanged. Without a 32-bit page there is nothing to test, and that is reported as a
   failure, not skipped: the entry's whole contract is the width.

   The probe's name has no `wiz_` prefix on purpose: C.lean's glue emits a prototype
   only for a foreign function outside that prefix (a `wiz_*` C function is assumed to be
   declared by the runtime's own headers), and an undeclared `wiz_step_probe` is an
   implicit-declaration error in the generated C. For the same reason this file cannot
   call the runtime's `wiz_in_nat`/`wiz_out_nat`: `WIZ_API` is `static` in the program's
   translation unit, so a `link_c` file only sees the generated exports — which is why
   the fixture's state is a `Nat` (kind `n`, a plain `uint64_t`) and not a record. */
#include <stdarg.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#ifdef __linux__
#include <sys/mman.h>
#endif

typedef uintptr_t wiz_val;   /* as runtime/wiz_rt.h and web/step.c spend it */

/* the generated export of step_gen.wiz's `loomStep` (C.lean's export wrapper: the Nat
   as a 64-bit word, the String as a borrowed UTF-8 pointer) */
extern wiz_val wiz_loom_step(wiz_val state, const char *payload);

/* web/step.c: the entry under test */
int32_t wiz_step(int32_t state, int32_t payload, int32_t len);

static int failures;
static char report[2048];
static size_t used;
static char *page;   /* below 4 GiB, when MAP_32BIT gave us one */

static void say(const char *fmt, ...) {
  va_list ap;
  int n;
  if (used + 1 >= sizeof report) return;
  va_start(ap, fmt);
  n = vsnprintf(report + used, sizeof report - used, fmt, ap);
  va_end(ap);
  if (n > 0) used += (size_t)n < sizeof report - used ? (size_t)n : sizeof report - used - 1;
}

static void expect(int cond, const char *what) {
  if (cond) say("ok: %s\n", what);
  else { failures++; say("FAIL: %s\n", what); }
}

/* The state as the ABI's first word, and back: the low 32 bits, unsigned. (The fixture's
   `Nat` reaches the generated wrapper as a `uint64_t`, so the number itself is the word.) */
static int32_t word_of_nat(uint64_t n) { return (int32_t)(uint32_t)(uintptr_t)n; }
static uint64_t nat_of_word(int32_t word) { return (uint64_t)(uint32_t)word; }

/* A step through the three words: `text` is copied to the 32-bit page, NUL-terminated
   as the host's allocation is; `len` is the declared byte length (-1: read to the NUL). */
static uint64_t word_step(uint64_t state, const char *text, int32_t len) {
  size_t n = strlen(text);
  memcpy(page, text, n + 1);
  return nat_of_word(wiz_step(word_of_nat(state), (int32_t)(uintptr_t)page, len));
}

char *step_probe(void) {
#ifdef MAP_32BIT
  void *p = mmap(NULL, 4096, PROT_READ | PROT_WRITE,
    MAP_PRIVATE | MAP_ANONYMOUS | MAP_32BIT, -1, 0);
  if (p != MAP_FAILED && (uintptr_t)p <= 0xFFFFFFFFu) page = (char *)p;
#endif
  if (!page) {
    failures++;
    say("FAIL: no 32-bit address for the payload (a 64-bit pointer cannot pass through\n"
        "      the ABI's int32 word); this needs Linux's MAP_32BIT\n");
  } else {
    /* ## the three words carry the state, the payload and its length */
    expect(word_step(2, "a\n0\n", 4) == 6,
      "the payload's text reaches the step (2 + the 4 characters of \"a\\n0\\n\")");
    expect(word_step(7, "abc", 2) == 9,
      "a shorter len steps only that many bytes (7 + \"ab\")");
    expect(word_step(7, "abc", -1) == 10, "len = -1 reads to the NUL (7 + \"abc\")");

    /* A host buffer that is not terminated within len: the shim copies exactly len.
       'Q' sits at the address the shim probes, so dropping len would step it too. */
    memcpy(page, "xyzQ", 4);
    expect(nat_of_word(wiz_step(word_of_nat(1), (int32_t)(uintptr_t)page, 3)) == 4,
      "a payload without a NUL at len is stepped at len, not past it (1 + \"xyz\")");

    /* ## the words are unsigned: a state whose word has the top bit set round-trips.
       `0x80000001` as an int32_t is negative; a sign-extending cast would hand the step
       `0xFFFFFFFF80000001` (a different, big Nat) and the answer would not be
       `0x80000005`. */
    expect(word_step(2147483649u, "abcd", 4) == 2147483653u,
      "a state word above 0x7FFFFFFF round-trips (0x80000001 + 4)");

    /* ## the i64 entry, which the Node tests still drive, agrees */
    expect(nat_of_word((int32_t)(uint32_t)(uintptr_t)
        wiz_loom_step((wiz_val)2, "a\n0\n")) == 6,
      "the i64 entry (state, payload) gives the same next state");
  }
  if (failures == 0) say("step: all checks passed\n");
  else say("step: %d failed\n", failures);
  return report;
}
