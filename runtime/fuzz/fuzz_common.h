/* Shared helpers for the C runtime's libFuzzer harnesses.

   Each harness is one translation unit that includes this header and links against
   `runtime/fuzz/runtime.c` (the runtime built as an object, `-DWIZ_API=`). The input is
   a small bytecode: a harness may interpret any byte string, but it only ever calls the
   runtime in the way generated code does (owned arguments, valid field indices, a
   value of the right kind for each operation). A harness therefore finds bugs in the
   runtime, not in deliberately invalid calls.

   Every root is dropped before `LLVMFuzzerTestOneInput` returns, and the harness checks
   `wiz_live_objects()` against its entry value: a mismatch is an aborted input, so a
   leak found by one iteration does not depend on LeakSanitizer's process-exit check. */

#ifndef WIZ_FUZZ_COMMON_H
#define WIZ_FUZZ_COMMON_H

#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* the harness includes the header for its declarations; the definitions live in
   runtime.c, compiled with -DWIZ_API= (external linkage) */
#ifndef WIZ_API
#define WIZ_API
#endif
#include "wiz_rt.h"

typedef struct {
  const uint8_t *data;
  size_t len;
  size_t pos;
} fz_input;

/* an exhausted input reads as zero bytes; loop bounds use `fz_more`/`fz_len`, so it
   cannot make an operation run forever */
static inline uint8_t fz_u8(fz_input *in) {
  return in->pos < in->len ? in->data[in->pos++] : 0;
}
static inline int fz_more(const fz_input *in) { return in->pos < in->len; }
static inline size_t fz_below(fz_input *in, size_t n) {
  return n ? (size_t)(fz_u8(in) % n) : 0;
}
/* 0..8 bytes, little endian, for operands where the whole word is interesting */
static inline uint64_t fz_u64(fz_input *in) {
  uint64_t v = 0;
  unsigned n = (unsigned)(fz_u8(in) & 7u);
  for (unsigned i = 0; i <= n; i++) v |= (uint64_t)fz_u8(in) << (8u * i);
  return v;
}
/* a short NUL-terminated string; no NULs inside it */
static inline void fz_text(fz_input *in, char *buf, size_t cap) {
  size_t n = fz_below(in, cap ? cap - 1 : 0);
  for (size_t i = 0; i < n; i++) {
    uint8_t c = fz_u8(in);
    if (c == 0) c = 'a' + (uint8_t)(fz_u8(in) % 26u);
    buf[i] = (char)c;
  }
  if (cap) buf[n] = 0;
}

static inline wiz_val fz_share(wiz_val v) { wiz_inc(v); return v; }

static inline wiz_val fz_take(wiz_val *slots, unsigned i) {
  wiz_val v = slots[i];
  slots[i] = 0;
  return v;
}
static inline void fz_put(wiz_val *slots, unsigned i, wiz_val v) {
  if (slots[i]) wiz_dec(slots[i]);
  slots[i] = v;
}
static inline void fz_drop_all(wiz_val *slots, unsigned n) {
  for (unsigned i = 0; i < n; i++) if (slots[i]) { wiz_dec(slots[i]); slots[i] = 0; }
}

static inline int fz_is_ctor(wiz_val v) {
  return v && !WIZ_IS_SCALAR(v) && ((const wiz_hdr *)v)->tag < WIZ_TAG_FIRST_SPECIAL;
}
static inline uint32_t fz_size(wiz_val v) {
  return fz_is_ctor(v) ? ((const wiz_hdr *)v)->size : 0;
}
/* the first slot holding a constructor, or -1 */
static inline int fz_find_ctor(const wiz_val *slots, unsigned n) {
  for (unsigned i = 0; i < n; i++) if (fz_is_ctor(slots[i])) return (int)i;
  return -1;
}

/* report a leak found by an iteration (the runner treats the abort as a crash) */
static inline void fz_check_live(long before) {
  long after = wiz_live_objects();
  if (after != before) {
    fprintf(stderr, "fuzz: %ld object(s) leaked by this input\n", after - before);
    abort();
  }
}

#endif /* WIZ_FUZZ_COMMON_H */
