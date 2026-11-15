/* Constructors, fields, reference counting, closures and reuse.

   The input is a sequence of operations on a small pool of owned roots. Constructors
   take their fields from other roots (or make a fresh scalar/string), so a value graph
   can be built and then taken apart with `field_at`, `proj`, `reset`/`reuse` and
   `drop_moved`; `inc`/`dup`/`dec` exercise the ownership paths, including a shared
   object's copy-on-write. Closures are applied partially and fully, memoised
   suspensions are forced, and a closed top-level definition is built once. */
#include "fuzz_common.h"

#define VSLOTS 10
#define VSTEPS 256

static wiz_val fz_discard2(wiz_val *args) {
  wiz_dec(args[0]);
  wiz_dec(args[1]);
  return WIZ_BOX(0);
}

static wiz_val fz_memo_fn(wiz_val *args) {
  wiz_dec(args[0]);
  return wiz_str_of_cstr("memo");
}

static int fz_caf_builds;
static wiz_val fz_caf_slot;
static wiz_val fz_caf_build(void) {
  fz_caf_builds++;
  return wiz_str_of_cstr("a constant");
}

static const char *fz_words[] = {"", "a", "left", "world", "aλ✓𝄞", "shared", "x"};

static wiz_val fz_fresh(fz_input *in) {
  char buf[24];
  switch (fz_below(in, 7)) {
  case 0: return WIZ_BOX(fz_u64(in) & 0xFF);
  case 1: return wiz_out_nat(fz_u64(in));
  case 2: return wiz_out_u64(fz_u64(in));
  case 3: return wiz_out_f64((double)(int64_t)fz_u64(in));
  case 4: fz_text(in, buf, sizeof buf); return wiz_str_of_cstr(buf);
  case 5: return wiz_str_of_cstr(fz_words[fz_below(in, sizeof fz_words / sizeof fz_words[0])]);
  default: return WIZ_BOX(0);
  }
}

static wiz_val fz_fill_ctor(fz_input *in, wiz_val *slots, wiz_val c, uint32_t n) {
  for (uint32_t i = 0; i < n; i++) {
    unsigned j = (unsigned)fz_below(in, VSLOTS);
    wiz_set(c, i, slots[j] ? fz_take(slots, j) : fz_fresh(in));
  }
  return c;
}
static wiz_val fz_new_ctor(fz_input *in, wiz_val *slots) {
  uint32_t tag = (uint32_t)fz_below(in, 16);
  uint32_t n = (uint32_t)fz_below(in, 5);
  return fz_fill_ctor(in, slots, wiz_ctor_new(tag, n), n);
}

static int fz_find_tag(const wiz_val *slots, unsigned n, uint32_t tag) {
  for (unsigned i = 0; i < n; i++)
    if (slots[i] && !WIZ_IS_SCALAR(slots[i]) && ((const wiz_hdr *)slots[i])->tag == tag) return (int)i;
  return -1;
}

static void fz_run(fz_input *in) {
  wiz_val s[VSLOTS] = {0};
  for (unsigned step = 0; step < VSTEPS && fz_more(in); step++) {
    unsigned a = (unsigned)fz_below(in, VSLOTS);
    unsigned op = (unsigned)fz_below(in, 19);
    switch (op) {
    case 0: fz_put(s, a, fz_new_ctor(in, s)); break;
    case 1: { /* set a constructor's field */
      int x = fz_find_ctor(s, VSLOTS);
      if (x < 0) break;
      uint32_t n = fz_size(s[x]);
      if (n == 0) break;
      uint32_t i = (uint32_t)fz_below(in, n);
      /* a fresh leaf: taking a field from another root could build a reference
         cycle, which no Wiz value has (the lowering passes only acyclic values) */
      wiz_val v = fz_fresh(in);
      /* `wiz_set` is a raw field store (the lowering uses it on fresh or reset
         cells); replacing a live field has to drop the old reference first */
      wiz_dec(((wiz_ctor *)s[x])->fields[i]);
      ((wiz_ctor *)s[x])->fields[i] = v;
      break;
    }
    case 2: { /* proj (borrowed) */
      int x = fz_find_ctor(s, VSLOTS);
      if (x < 0) break;
      uint32_t n = fz_size(s[x]);
      if (n == 0) break;
      wiz_val f = wiz_proj(s[x], (uint32_t)fz_below(in, n));
      wiz_inc(f);
      fz_put(s, a, f);
      break;
    }
    case 3: { /* field_at (consumes the cell, returns an owned field) */
      int x = fz_find_ctor(s, VSLOTS);
      if (x < 0) break;
      uint32_t n = fz_size(s[x]);
      if (n == 0) break;
      fz_put(s, a, wiz_field_at(fz_take(s, (unsigned)x), WIZ_BOX(fz_below(in, n))));
      break;
    }
    case 4: fz_put(s, a, wiz_tag_of(s[a] ? fz_take(s, a) : fz_fresh(in))); break;
    case 5: fz_put(s, a, wiz_nat_tag(s[a] ? fz_take(s, a) : fz_fresh(in))); break;
    case 6: if (s[a]) { wiz_inc(s[a]); wiz_dec(s[a]); } else s[a] = fz_fresh(in); break;
    case 7: if (s[a]) wiz_dec(fz_take(s, a)); break;
    case 8: { /* duplicate a root (two owned references) */
      unsigned b = (unsigned)fz_below(in, VSLOTS);
      if (!s[b]) s[b] = fz_fresh(in);
      if (a == b) { wiz_inc(s[a]); wiz_dec(s[a]); }
      else fz_put(s, a, fz_share(s[b]));
      break;
    }
    case 9: { /* reset and reuse: a unique constructor's cell is filled again */
      wiz_val v = s[a] ? fz_take(s, a) : fz_new_ctor(in, s);
      uint32_t n = (uint32_t)fz_below(in, 5);
      wiz_val r = wiz_reuse(wiz_reset(v), (uint32_t)fz_below(in, 16), n);
      fz_put(s, a, n ? fz_fill_ctor(in, s, r, n) : r);
      break;
    }
    case 10: { /* reuse with a scalar token: a fresh cell, or a scalar for n == 0 */
      uint32_t n = (uint32_t)fz_below(in, 5);
      wiz_val r = wiz_reuse(WIZ_BOX(0), (uint32_t)fz_below(in, 16), n);
      fz_put(s, a, n ? fz_fill_ctor(in, s, r, n) : r);
      break;
    }
    case 11: { /* drop_moved: the fields in the mask move out to the caller */
      int x = fz_find_ctor(s, VSLOTS);
      if (x < 0) break;
      uint32_t n = fz_size(s[x]);
      uint64_t mask = n >= 63 ? fz_u64(in) : fz_u64(in) & (((uint64_t)1 << n) - 1);
      wiz_val moved[62];
      unsigned k = 0;
      for (uint32_t i = 0; i < n && i < 62; i++)
        if ((mask >> i) & 1) moved[k++] = ((const wiz_ctor *)s[x])->fields[i];
      wiz_val r = wiz_drop_moved(fz_take(s, (unsigned)x), WIZ_BOX(mask));
      /* each masked field is a reference the caller now owns (moved out of a unique
         cell, or incremented in a shared one); this harness only needs one root */
      for (unsigned i = 0; i < k; i++) wiz_dec(moved[i]);
      fz_put(s, a, r);
      break;
    }
    case 12: { /* a closure capturing 0..3 roots */
      uint32_t n = (uint32_t)fz_below(in, 4);
      wiz_val cap[3] = {WIZ_BOX(0), WIZ_BOX(0), WIZ_BOX(0)};
      for (uint32_t i = 0; i < n; i++) {
        unsigned b = (unsigned)fz_below(in, VSLOTS);
        cap[i] = s[b] ? fz_share(s[b]) : fz_fresh(in);
      }
      fz_put(s, a, wiz_clo_new(fz_discard2, 2, n, n ? cap : NULL));
      break;
    }
    case 13: { /* apply a closure to 0..2 owned arguments */
      int x = fz_find_tag(s, VSLOTS, WIZ_TAG_CLO);
      if (x < 0) break;
      uint32_t n = (uint32_t)fz_below(in, 3);
      wiz_val args[2] = {WIZ_BOX(0), WIZ_BOX(0)};
      for (uint32_t i = 0; i < n; i++) {
        unsigned b = (unsigned)fz_below(in, VSLOTS);
        args[i] = s[b] ? fz_share(s[b]) : fz_fresh(in);
      }
      fz_put(s, a, wiz_apply(fz_take(s, (unsigned)x), n, n ? args : NULL));
      break;
    }
    case 14: { /* a memoised suspension, either forced or dropped unforced */
      wiz_val body = wiz_clo_new(fz_memo_fn, 1, 0, NULL);
      fz_put(s, a, wiz_memo(WIZ_BOX(0), body));
      break;
    }
    case 15: { /* force a thunk */
      int x = fz_find_tag(s, VSLOTS, WIZ_TAG_THUNK);
      if (x < 0) break;
      wiz_val unit = WIZ_BOX(0);
      fz_put(s, a, wiz_apply(fz_take(s, (unsigned)x), 1, &unit));
      break;
    }
    case 16: fz_put(s, a, wiz_caf_init(&fz_caf_slot, fz_caf_build)); break;
    case 17: fz_put(s, a, wiz_io_result(fz_fresh(in), WIZ_BOX(0))); break;
    case 18: fz_put(s, a, wiz_raw_box(fz_u64(in))); break;
    }
  }
  fz_drop_all(s, VSLOTS);
}

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
  long before = wiz_live_objects();
  fz_input in = {data, size, 0};
  fz_run(&in);
  if (fz_caf_builds > 1) abort(); /* a closed definition is built once */
  fz_check_live(before);
  return 0;
}
