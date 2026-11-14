/* The corpus's harness: the runtime, the checks, and a few helpers shared by the
   programs. Each program is one translation unit. Built two ways (scripts/test-
   sanitizers.sh): as an object (`-DWIZ_API=`, the LLVM backend's ABI) with the runtime
   in its own translation unit, and inline (`-DWIZ_CORPUS_INLINE`, `-DWIZ_API=static`),
   as generated C embeds it. */
#include "wiz_rt.h"

#ifdef WIZ_CORPUS_INLINE
#include "rt_core.inc"
#include "rt_num.inc"
#include "rt_words.inc"
#include "rt_data.inc"
#include "rt_sys.inc"
#include "rt_con.inc"
#endif

static int wiz_corpus_failures;

/* a second reference to `v` (as a value, for a call that consumes its argument) */
static inline wiz_val share(wiz_val v) { wiz_inc(v); return v; }

static inline void check(int cond, const char *what) {
  if (!cond) {
    fprintf(stderr, "corpus: FAIL: %s\n", what);
    wiz_corpus_failures++;
  }
}

/* the number a Nat value holds (consumes it) */
static inline uint64_t nat_of(wiz_val v) { return wiz_in_nat(v); }

/* a list cell (no fields: a Wiz list is `cons` and `nil`) */
static inline wiz_val cons(wiz_val h, wiz_val t) {
  wiz_val c = wiz_ctor_new(1, 2);
  wiz_set(c, 0, h);
  wiz_set(c, 1, t);
  return c;
}

/* the i-th number of a list, borrowed: the caller still owns `l` */
static inline uint64_t list_nat(wiz_val l, int i) {
  wiz_val c = l;
  wiz_inc(c);
  for (; i > 0 && wiz_tag(c) == 1; i--) c = wiz_field_at(c, WIZ_BOX(1));
  uint64_t n = 0;
  if (wiz_tag(c) == 1) n = nat_of(wiz_field_at(c, WIZ_BOX(0)));
  else wiz_dec(c);
  return n;
}

/* whether a list holds `n` elements */
static inline int list_len_is(wiz_val l, uint64_t n) {
  wiz_val c = l;
  wiz_inc(c);
  uint64_t k = 0;
  for (; wiz_tag(c) == 1; k++) c = wiz_field_at(c, WIZ_BOX(1));
  wiz_dec(c);
  return k == n;
}

static inline const char *string_of_list(wiz_val l) {
  size_t n = 0;
  wiz_val c = l;
  wiz_inc(c);
  for (; wiz_tag(c) == 1; n++) c = wiz_field_at(c, WIZ_BOX(1));
  wiz_dec(c);
  char *s = (char *)malloc(4 * n + 1);
  size_t k = 0;
  c = l;
  wiz_inc(c);
  for (; wiz_tag(c) == 1; ) {
    wiz_val ch = wiz_field_at(share(c), WIZ_BOX(0));
    wiz_val cp = wiz_field_at(ch, WIZ_BOX(0));
    uint32_t u = (uint32_t)nat_of(cp);
    if (u < 0x80) s[k++] = (char)u;
    else if (u < 0x800) { s[k++] = (char)(0xC0 | (u >> 6)); s[k++] = (char)(0x80 | (u & 0x3F)); }
    else if (u < 0x10000) { s[k++] = (char)(0xE0 | (u >> 12)); s[k++] = (char)(0x80 | ((u >> 6) & 0x3F)); s[k++] = (char)(0x80 | (u & 0x3F)); }
    else { s[k++] = (char)(0xF0 | (u >> 18)); s[k++] = (char)(0x80 | ((u >> 12) & 0x3F)); s[k++] = (char)(0x80 | ((u >> 6) & 0x3F)); s[k++] = (char)(0x80 | (u & 0x3F)); }
    c = wiz_field_at(c, WIZ_BOX(1));
  }
  wiz_dec(c);
  s[k] = 0;
  wiz_val t = wiz_str_of_cstr(s);
  free(s);
  return wiz_str_to_cstr(t);
}

/* the C string of a `String` value (String.mk l), borrowed; the runtime's scratch */
static inline const char *string_text(wiz_val str) {
  wiz_val l = wiz_field_at(share(str), WIZ_BOX(0));
  const char *s = string_of_list(l);
  wiz_dec(l);
  return s;
}
