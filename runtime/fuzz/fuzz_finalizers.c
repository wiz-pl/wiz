/* Foreign objects and their finalizers, plus the runtime's own finalizer-bearing
   objects (MVars, locks) and memoised suspensions.

   A finalizer increments `fz_made` when the foreign object is made and `fz_freed`
   when it runs; at the end of an input the two must agree. The object is also put in
   constructors, arrays, maps, an MVar and a lazy cell, and shared through `wiz_retain`
   / `wiz_release`, so a missed or doubled finalizer is a crash (a leak check catches
   the first, ASAN the second). The input never calls a finalizer's pointer after the
   object that owns it is dropped. */
#include "fuzz_common.h"

#define ESLOTS 6
#define CSLOTS 3
#define TSLOTS 2
#define FSTEPS 192

typedef struct {
  uint64_t magic;
  uint64_t id;
} fz_ext;

#define FZ_EXT_MAGIC 0x57495a46555a5aULL

static uint64_t fz_made, fz_freed, fz_static_made, fz_static_freed;
static int fz_static_value;

static void fz_ext_fin(void *p) {
  fz_ext *e = (fz_ext *)p;
  if (e->magic != FZ_EXT_MAGIC) abort(); /* a double finalizer, or a corrupt object */
  e->magic = 0;
  fz_freed++;
  free(e);
}
static void fz_static_fin(void *p) {
  if (p != &fz_static_value) abort();
  fz_static_freed++;
}

static wiz_val fz_ext_new(fz_input *in) {
  fz_ext *e = (fz_ext *)malloc(sizeof *e);
  if (!e) abort();
  e->magic = FZ_EXT_MAGIC;
  e->id = fz_u64(in);
  fz_made++;
  return wiz_out_ptr(e, fz_ext_fin);
}

static wiz_val fz_atom(fz_input *in) {
  char buf[20];
  switch (fz_below(in, 4)) {
  case 0: return WIZ_BOX(fz_u8(in) & 0x7F);
  case 1: return wiz_out_nat(fz_u64(in));
  case 2: fz_text(in, buf, sizeof buf); return wiz_str_of_cstr(buf);
  default: return WIZ_BOX(0);
  }
}

static wiz_val fz_memo_ext_fn(wiz_val *args) {
  wiz_dec(args[0]);
  fz_ext *e = (fz_ext *)malloc(sizeof *e);
  if (!e) abort();
  e->magic = FZ_EXT_MAGIC;
  e->id = 0;
  fz_made++;
  return wiz_out_ptr(e, fz_ext_fin);
}

static int fz_find_tag(const wiz_val *s, unsigned n, uint32_t tag) {
  for (unsigned i = 0; i < n; i++)
    if (s[i] && !WIZ_IS_SCALAR(s[i]) && ((const wiz_hdr *)s[i])->tag == tag) return (int)i;
  return -1;
}

static void fz_run(fz_input *in) {
  wiz_val ext[ESLOTS] = {0}, con[CSLOTS] = {0}, thunk[TSLOTS] = {0}, val = 0;
  for (unsigned step = 0; step < FSTEPS && fz_more(in); step++) {
    unsigned a = (unsigned)fz_below(in, ESLOTS);
    unsigned op = (unsigned)fz_below(in, 13);
    switch (op) {
    case 0: fz_put(ext, a, fz_ext_new(in)); break;
    case 1: { /* a shared foreign object: each slot owns one reference */
      unsigned b = (unsigned)fz_below(in, ESLOTS);
      if (!ext[b]) ext[b] = fz_ext_new(in);
      if (a == b) { wiz_inc(ext[a]); wiz_dec(ext[a]); }
      else fz_put(ext, a, fz_share(ext[b]));
      break;
    }
    case 2: if (ext[a]) { wiz_val v = fz_take(ext, a); wiz_retain((void *)v); wiz_release((void *)v); wiz_release((void *)v); } break;
    case 3: if (ext[a]) { (void)wiz_in_ptr(ext[a]); wiz_dec(fz_take(ext, a)); } break;
    case 4: { /* a NULL pointer: the runtime does not call the finalizer for it */
      fz_put(ext, a, wiz_out_ptr(NULL, fz_ext_fin));
      break;
    }
    case 5: { /* a borrowed static pointer, with and without a finalizer */
      if (fz_below(in, 2)) { fz_static_made++; fz_put(ext, a, wiz_out_ptr(&fz_static_value, fz_static_fin)); }
      else fz_put(ext, a, wiz_out_ptr(&fz_static_value, NULL));
      break;
    }
    case 6: { /* a foreign object embedded in a constructor */
      uint32_t n = 1 + (uint32_t)fz_below(in, 3);
      wiz_val c = wiz_ctor_new((uint32_t)fz_below(in, 8), n);
      if (!ext[a]) ext[a] = fz_ext_new(in);
      wiz_set(c, 0, fz_take(ext, a));
      for (uint32_t i = 1; i < n; i++) wiz_set(c, i, fz_atom(in));
      fz_put(con, (unsigned)fz_below(in, CSLOTS), c);
      break;
    }
    case 7: { /* ... in an array */
      if (!ext[a]) ext[a] = fz_ext_new(in);
      wiz_val arr = wiz_array_push(wiz_array_empty(), fz_take(ext, a));
      arr = wiz_array_push(arr, fz_atom(in));
      fz_put(con, (unsigned)fz_below(in, CSLOTS), arr);
      break;
    }
    case 8: { /* ... in a map (the key is a fresh string) */
      char key[12];
      fz_text(in, key, sizeof key);
      if (!ext[a]) ext[a] = fz_ext_new(in);
      wiz_val m = wiz_map_insert(wiz_map_empty(), wiz_str_of_cstr(key), fz_take(ext, a));
      fz_put(con, (unsigned)fz_below(in, CSLOTS), m);
      break;
    }
    case 9: { /* a suspension whose body makes a foreign object */
      wiz_val body = wiz_clo_new(fz_memo_ext_fn, 1, 0, NULL);
      fz_put(thunk, (unsigned)fz_below(in, TSLOTS), wiz_memo(WIZ_BOX(0), body));
      break;
    }
    case 10: { /* force a suspension */
      int t = fz_find_tag(thunk, TSLOTS, WIZ_TAG_THUNK);
      if (t < 0) break;
      wiz_val unit = WIZ_BOX(0);
      fz_put(ext, a, wiz_apply(fz_take(thunk, (unsigned)t), 1, &unit));
      break;
    }
    case 11: { /* a shared lazy cell: observing it drops its old field */
      if (!ext[a]) ext[a] = fz_ext_new(in);
      uint32_t tag = fz_below(in, 2) ? 1001u : 1000u;
      wiz_val cell = wiz_ctor_new(tag, 1);
      wiz_set(cell, 0, fz_take(ext, a));
      wiz_inc(cell); /* the extra reference that makes the cell shared */
      fz_put(con, (unsigned)fz_below(in, CSLOTS), cell);
      wiz_val r = wiz_lazy_set(cell, fz_atom(in));
      if (val) wiz_dec(val);
      val = r;
      break;
    }
    default: { /* an MVar owns and hands over the foreign object */
      if (!ext[a]) ext[a] = fz_ext_new(in);
      wiz_val mv = wiz_mvar_new_full(fz_take(ext, a));
      fz_put(ext, a, wiz_mvar_take(mv));
      break;
    }
    }
  }
  fz_drop_all(ext, ESLOTS);
  fz_drop_all(con, CSLOTS);
  fz_drop_all(thunk, TSLOTS);
  if (val) wiz_dec(val);
  if (fz_freed != fz_made || fz_static_freed != fz_static_made) {
    fprintf(stderr, "fuzz: finalizers ran %llu/%llu and %llu/%llu times\n",
            (unsigned long long)fz_freed, (unsigned long long)fz_made,
            (unsigned long long)fz_static_freed, (unsigned long long)fz_static_made);
    abort();
  }
}

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
  long before = wiz_live_objects();
  fz_input in = {data, size, 0};
  fz_run(&in);
  fz_check_live(before);
  return 0;
}
