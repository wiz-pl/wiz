/* Strings, Bytes, Array, StrMap, word arrays/maps and Wiz `String`s.

   The input drives one of several typed pools, so each call gets a value of the kind
   the runtime expects. Indices, slices and defaults come from the input (including
   values past the end, and GMP-sized indices), so the bounds and copy-on-write paths
   are exercised; every returned value is either kept in a slot or dropped here. */
#include "fuzz_common.h"

#define DSLOTS 3
#define DSTEPS 320

static const char *fz_words[] = {"", "a", "hello", " world", "one", "two", "three",
                                 "aλ✓𝄞", "abcdef"};

static void fz_text_word(fz_input *in, char *buf, size_t cap) {
  if (fz_below(in, 2)) {
    const char *w = fz_words[fz_below(in, sizeof fz_words / sizeof fz_words[0])];
    size_t n = strlen(w);
    if (n >= cap) n = cap - 1;
    memcpy(buf, w, n);
    buf[n] = 0;
  } else {
    fz_text(in, buf, cap);
  }
}

static wiz_val fz_str(fz_input *in) {
  char buf[40];
  fz_text_word(in, buf, sizeof buf);
  return wiz_str_of_cstr(buf);
}
static void fz_key_text(fz_input *in, char *buf, size_t cap) { fz_text_word(in, buf, cap); }
static wiz_val fz_key(fz_input *in) {
  char buf[40];
  fz_text_word(in, buf, sizeof buf);
  return wiz_str_of_cstr(buf);
}

/* any value an array or map can hold */
static wiz_val fz_atom(fz_input *in) {
  char buf[24];
  switch (fz_below(in, 5)) {
  case 0: return WIZ_BOX(fz_u8(in) & 0x7F);
  case 1: return wiz_out_nat(fz_u64(in));
  case 2: return wiz_out_u64(fz_u64(in));
  case 3: fz_text(in, buf, sizeof buf); return wiz_str_of_cstr(buf);
  default: return WIZ_BOX(0);
  }
}

/* a word for a U8/U32/U64 array or a U64 map key */
static wiz_val fz_word(fz_input *in) {
  return wiz_word_of_nat(64, wiz_out_nat(fz_u64(in)));
}
/* a Nat index; sometimes a GMP number, which every index takes as out of range */
static wiz_val fz_index(fz_input *in) {
  if (fz_below(in, 8) == 0) return wiz_nat_shiftLeft(wiz_out_nat(1), wiz_out_nat(70));
  return wiz_out_nat(fz_u64(in) & 0xFF);
}

static unsigned fz_other(fz_input *in, unsigned a, unsigned n) {
  unsigned b = (unsigned)fz_below(in, n - 1);
  return b >= a ? b + 1 : b;
}

static wiz_val fz_warray_empty(uint32_t w) {
  return w == 1 ? wiz_u8array_empty() : w == 4 ? wiz_u32array_empty() : wiz_u64array_empty();
}

static void fz_strings(fz_input *in, wiz_val *s) {
  unsigned a = (unsigned)fz_below(in, DSLOTS);
  unsigned op = (unsigned)fz_below(in, 10);
  switch (op) {
  case 0: fz_put(s, a, fz_str(in)); break;
  case 1: { /* a Wiz String, round-tripped through its UTF-8 C string */
    char buf[40];
    fz_text_word(in, buf, sizeof buf);
    wiz_val str = wiz_out_string(buf);
    char *back = wiz_in_string(str);
    free(back);
    break;
  }
  case 2: if (s[a]) (void)wiz_str_size(fz_share(s[a])); else s[a] = fz_str(in); break;
  case 3: if (s[a]) (void)wiz_str_byte(fz_share(s[a]), fz_u64(in)); else s[a] = fz_str(in); break;
  case 4: { /* slice, including from > to and both past the end */
    if (!s[a]) s[a] = fz_str(in);
    size_t n = ((const wiz_str *)s[a])->len;
    uint64_t from = fz_below(in, n + 3), to = fz_below(in, n + 3);
    fz_put(s, a, wiz_str_slice(fz_take(s, a), from, to));
    break;
  }
  case 5: { /* append */
    unsigned b = fz_other(in, a, DSLOTS);
    if (!s[b]) s[b] = fz_str(in);
    if (!s[a]) s[a] = fz_str(in);
    fz_put(s, a, wiz_str_append(fz_take(s, a), fz_take(s, b)));
    break;
  }
  case 6: { /* eq: both references are shared, so the slots keep their values */
    unsigned b = (unsigned)fz_below(in, DSLOTS);
    if (!s[a]) s[a] = fz_str(in);
    if (!s[b]) s[b] = fz_str(in);
    (void)wiz_str_eq(fz_share(s[a]), fz_share(s[b]));
    break;
  }
  case 7: {
    unsigned b = (unsigned)fz_below(in, DSLOTS);
    if (!s[a]) s[a] = fz_str(in);
    if (!s[b]) s[b] = fz_str(in);
    (void)wiz_str_lt(fz_share(s[a]), fz_share(s[b]));
    break;
  }
  case 8: { /* the borrowed C string of the runtime's scratch */
    if (!s[a]) s[a] = fz_str(in);
    const char *p = wiz_str_to_cstr(fz_share(s[a]));
    volatile size_t n = strlen(p);
    (void)n;
    break;
  }
  default: { /* String.mk (List Char) and wiz_in_string */
    char buf[40];
    fz_text_word(in, buf, sizeof buf);
    wiz_val str = wiz_out_string(buf);
    char *back = wiz_in_string(str);
    free(back);
    break;
  }
  }
}

static void fz_bytess(fz_input *in, wiz_val *s) {
  unsigned a = (unsigned)fz_below(in, DSLOTS);
  unsigned op = (unsigned)fz_below(in, 9);
  switch (op) {
  case 0: fz_put(s, a, wiz_bytes_empty()); break;
  case 1: { char buf[40]; fz_text_word(in, buf, sizeof buf); fz_put(s, a, wiz_bytes_of_string(buf)); break; }
  case 2: if (s[a]) fz_put(s, a, wiz_bytes_push(fz_take(s, a), fz_u8(in))); else s[a] = wiz_bytes_of_string("x"); break;
  case 3: if (s[a]) (void)wiz_bytes_size(fz_share(s[a])); else s[a] = wiz_bytes_empty(); break;
  case 4: if (s[a]) (void)wiz_bytes_get(fz_share(s[a]), fz_u64(in)); else s[a] = wiz_bytes_empty(); break;
  case 5: { /* slice */
    if (!s[a]) s[a] = wiz_bytes_empty();
    size_t n = ((const wiz_bytes *)s[a])->len;
    uint64_t start = fz_below(in, n + 3), len = fz_below(in, n + 3);
    fz_put(s, a, wiz_bytes_slice(fz_take(s, a), start, len));
    break;
  }
  case 6: { /* append */
    unsigned b = fz_other(in, a, DSLOTS);
    if (!s[a]) s[a] = wiz_bytes_empty();
    if (!s[b]) s[b] = wiz_bytes_empty();
    fz_put(s, a, wiz_bytes_append(fz_take(s, a), fz_take(s, b)));
    break;
  }
  case 7: {
    unsigned b = (unsigned)fz_below(in, DSLOTS);
    if (!s[a]) s[a] = wiz_bytes_empty();
    if (!s[b]) s[b] = wiz_bytes_empty();
    (void)wiz_bytes_eq(fz_share(s[a]), fz_share(s[b]));
    break;
  }
  default: { /* copy-on-write from a shared buffer, then the C string */
    if (!s[a]) s[a] = wiz_bytes_empty();
    wiz_val copy = wiz_bytes_push(fz_share(s[a]), fz_u8(in));
    const char *p = wiz_bytes_to_string(copy);
    volatile size_t n = strlen(p);
    (void)n;
    break;
  }
  }
}

static void fz_arrays(fz_input *in, wiz_val *s) {
  unsigned a = (unsigned)fz_below(in, DSLOTS);
  unsigned op = (unsigned)fz_below(in, 6);
  switch (op) {
  case 0: fz_put(s, a, wiz_array_empty()); break;
  case 1: if (s[a]) fz_put(s, a, wiz_array_push(fz_take(s, a), fz_atom(in))); else s[a] = wiz_array_empty(); break;
  case 2: if (s[a]) (void)wiz_array_size(fz_share(s[a])); else s[a] = wiz_array_empty(); break;
  case 3: { /* get with a default (both the found and the missing path) */
    if (!s[a]) s[a] = wiz_array_empty();
    wiz_dec(wiz_array_get(fz_share(s[a]), fz_u64(in), fz_atom(in)));
    break;
  }
  case 4: { /* set; out of range consumes x and leaves the array */
    if (!s[a]) s[a] = wiz_array_empty();
    fz_put(s, a, wiz_array_set(fz_take(s, a), fz_u64(in), fz_atom(in)));
    break;
  }
  default: { /* push onto a shared array: the copy path */
    if (!s[a]) s[a] = wiz_array_empty();
    wiz_val copy = wiz_array_push(fz_share(s[a]), fz_atom(in));
    wiz_dec(copy);
    break;
  }
  }
}

/* a model of the text map's keys (values are opaque, as for the word map) */
#define MMODEL 64
#define MKEY 64
typedef struct { char k[MMODEL][MKEY]; unsigned n; } fz_smodel;
static int fz_sm_find(const fz_smodel *m, const char *k) {
  for (unsigned i = 0; i < m->n; i++) if (strcmp(m->k[i], k) == 0) return (int)i;
  return -1;
}
static void fz_sm_insert(fz_smodel *m, const char *k) {
  if (fz_sm_find(m, k) < 0 && m->n < MMODEL) {
    snprintf(m->k[m->n], MKEY, "%s", k);
    m->n++;
  }
}
static void fz_sm_size_is(wiz_val map, const fz_smodel *m) {
  uint64_t n = wiz_map_size(fz_share(map)); /* a plain count, not a tagged value */
  if (n != m->n) abort();
}

static void fz_maps(fz_input *in, wiz_val *s, fz_smodel *m) {
  unsigned a = (unsigned)fz_below(in, DSLOTS);
  unsigned op = (unsigned)fz_below(in, 6);
  fz_smodel *sm = &m[a];
  switch (op) {
  case 0: fz_put(s, a, wiz_map_empty()); sm->n = 0; break;
  case 1: { /* insert (a new key or a replacement) */
    char key[MKEY];
    fz_key_text(in, key, sizeof key);
    if (!s[a]) s[a] = wiz_map_empty();
    wiz_val val = fz_atom(in);
    if (fz_sm_find(sm, key) < 0 && sm->n == MMODEL) { wiz_dec(val); break; }
    fz_put(s, a, wiz_map_insert(fz_take(s, a), wiz_str_of_cstr(key), val));
    fz_sm_insert(sm, key);
    fz_sm_size_is(s[a], sm);
    break;
  }
  case 2: { /* find: a missing key returns the default object itself */
    char key[MKEY];
    fz_key_text(in, key, sizeof key);
    if (!s[a]) s[a] = wiz_map_empty();
    int present = fz_sm_find(sm, key) >= 0;
    wiz_val miss = wiz_str_of_cstr("__missing__");
    wiz_inc(miss); /* keep a reference for the comparison */
    wiz_val r = wiz_map_find(fz_share(s[a]), wiz_str_of_cstr(key), miss);
    if (present ? (r == miss) : (r != miss)) abort();
    wiz_dec(r);
    wiz_dec(miss);
    break;
  }
  case 3: if (!s[a]) s[a] = wiz_map_empty(); fz_sm_size_is(s[a], sm); break;
  case 4: { /* insert into the map, then into a shared copy (the copy path) */
    char k1[MKEY], k2[MKEY];
    fz_key_text(in, k1, sizeof k1);
    fz_key_text(in, k2, sizeof k2);
    if (!s[a]) s[a] = wiz_map_empty();
    wiz_val val1 = fz_atom(in), val2 = fz_atom(in);
    if (fz_sm_find(sm, k1) < 0 && sm->n == MMODEL) { wiz_dec(val1); wiz_dec(val2); break; }
    fz_put(s, a, wiz_map_insert(fz_take(s, a), wiz_str_of_cstr(k1), val1));
    fz_sm_insert(sm, k1);
    /* the copy is discarded: the original (and the model) are unchanged */
    wiz_val copy = wiz_map_insert(fz_share(s[a]), wiz_str_of_cstr(k2), val2);
    wiz_dec(copy);
    fz_sm_size_is(s[a], sm);
    break;
  }
  default: { /* a find on a shared copy; the original (and the model) are unchanged */
    char key[MKEY];
    fz_key_text(in, key, sizeof key);
    if (!s[a]) s[a] = wiz_map_empty();
    wiz_val copy = wiz_map_insert(fz_share(s[a]), wiz_str_of_cstr(key), fz_atom(in));
    wiz_val o = wiz_map_find(copy, wiz_str_of_cstr(key), fz_atom(in));
    wiz_dec(o);
    break;
  }
  }
}

static void fz_warrays(fz_input *in, wiz_val *s, uint32_t *width) {
  unsigned a = (unsigned)fz_below(in, DSLOTS);
  unsigned op = (unsigned)fz_below(in, 8);
  switch (op) {
  case 0: {
    static const uint32_t widths[] = {1, 4, 8};
    width[a] = widths[fz_below(in, 3)];
    fz_put(s, a, fz_warray_empty(width[a]));
    break;
  }
  case 1: if (s[a]) fz_put(s, a, wiz_warray_push(fz_take(s, a), fz_word(in))); else { width[a] = 8; s[a] = wiz_u64array_empty(); } break;
  case 2: if (s[a]) wiz_dec(wiz_warray_size(fz_share(s[a]))); else { width[a] = 8; s[a] = wiz_u64array_empty(); } break;
  case 3: if (s[a]) wiz_dec(wiz_warray_get(fz_share(s[a]), fz_index(in), fz_word(in))); else { width[a] = 8; s[a] = wiz_u64array_empty(); } break;
  case 4: if (s[a]) fz_put(s, a, wiz_warray_set(fz_take(s, a), fz_index(in), fz_word(in))); else { width[a] = 8; s[a] = wiz_u64array_empty(); } break;
  case 5: { /* slice */
    if (!s[a]) { width[a] = 8; s[a] = wiz_u64array_empty(); }
    wiz_val start = fz_index(in), n = fz_index(in);
    fz_put(s, a, wiz_warray_slice(fz_take(s, a), start, n));
    break;
  }
  case 6: { /* append arrays of one width; a shared source exercises the copy */
    unsigned b = fz_other(in, a, DSLOTS);
    if (!s[a]) { width[a] = 8; s[a] = wiz_u64array_empty(); }
    if (!s[b] || width[b] != width[a]) { width[b] = width[a]; if (s[b]) wiz_dec(fz_take(s, b)); s[b] = fz_warray_empty(width[b]); }
    fz_put(s, a, wiz_warray_append(fz_take(s, a), fz_take(s, b)));
    break;
  }
  default: { /* pop, then the model's list */
    if (!s[a]) { width[a] = 8; s[a] = wiz_u64array_empty(); }
    wiz_val v = wiz_warray_pop(fz_take(s, a));
    wiz_val l = wiz_warray_to_list(v);
    wiz_dec(l);
    break;
  }
  }
}

/* a model of the word map's keys, for the operations that have an observable
   answer (presence, size, erase); values are opaque here */
#define WMODEL 64
typedef struct { uint64_t k[WMODEL]; unsigned n; } fz_wmodel;
static int fz_wm_find(const fz_wmodel *m, uint64_t k) {
  for (unsigned i = 0; i < m->n; i++) if (m->k[i] == k) return (int)i;
  return -1;
}
static void fz_wm_insert(fz_wmodel *m, uint64_t k) {
  if (fz_wm_find(m, k) < 0 && m->n < WMODEL) m->k[m->n++] = k;
}
static void fz_wm_erase(fz_wmodel *m, uint64_t k) {
  int i = fz_wm_find(m, k);
  if (i >= 0) m->k[i] = m->k[--m->n];
}
static void fz_wm_size_is(wiz_val map, const fz_wmodel *m) {
  wiz_val n = wiz_wmap_size(fz_share(map));
  if (!WIZ_IS_SCALAR(n) || WIZ_UNBOX(n) != m->n) abort();
  wiz_dec(n);
}

static void fz_wmaps(fz_input *in, wiz_val *s, fz_wmodel *m) {
  unsigned a = (unsigned)fz_below(in, DSLOTS);
  unsigned op = (unsigned)fz_below(in, 8);
  fz_wmodel *wm = &m[a];
  switch (op) {
  case 0: fz_put(s, a, wiz_wmap_empty()); wm->n = 0; break;
  case 1: { /* insert (a new key or a replacement) */
    uint64_t k = fz_u64(in);
    wiz_val key = wiz_word_of_nat(64, wiz_out_nat(k));
    wiz_val val = fz_atom(in);
    if (!s[a]) s[a] = wiz_wmap_empty();
    if (fz_wm_find(wm, k) < 0 && wm->n == WMODEL) { wiz_dec(key); wiz_dec(val); break; }
    fz_put(s, a, wiz_wmap_insert(fz_take(s, a), key, val));
    fz_wm_insert(wm, k);
    fz_wm_size_is(s[a], wm);
    break;
  }
  case 2: { /* find: the Option's tag is presence */
    uint64_t k = fz_u64(in);
    if (!s[a]) s[a] = wiz_wmap_empty();
    int present = fz_wm_find(wm, k) >= 0;
    wiz_val o = wiz_wmap_find(fz_share(s[a]), wiz_word_of_nat(64, wiz_out_nat(k)));
    if ((wiz_tag(o) == 1) != present) abort();
    wiz_dec(o);
    break;
  }
  case 3: { /* find with a default: a missing key returns that exact value */
    uint64_t k = fz_u64(in);
    if (!s[a]) s[a] = wiz_wmap_empty();
    int present = fz_wm_find(wm, k) >= 0;
    wiz_val d = fz_atom(in);
    wiz_val r = wiz_wmap_find_d(fz_share(s[a]), wiz_word_of_nat(64, wiz_out_nat(k)), d);
    if (!present && r != d) abort();
    wiz_dec(r);
    break;
  }
  case 4: { /* contains */
    uint64_t k = fz_u64(in);
    if (!s[a]) s[a] = wiz_wmap_empty();
    int present = fz_wm_find(wm, k) >= 0;
    int got = wiz_wmap_contains(fz_share(s[a]), wiz_word_of_nat(64, wiz_out_nat(k)));
    if (got != present) abort();
    break;
  }
  case 5: { /* erase, then the model's size must agree */
    uint64_t k = fz_u64(in);
    if (!s[a]) s[a] = wiz_wmap_empty();
    fz_put(s, a, wiz_wmap_erase(fz_take(s, a), wiz_word_of_nat(64, wiz_out_nat(k))));
    fz_wm_erase(wm, k);
    fz_wm_size_is(s[a], wm);
    break;
  }
  case 6: if (!s[a]) s[a] = wiz_wmap_empty(); fz_wm_size_is(s[a], wm); break;
  default: { /* the sorted entries as a list; the map is consumed */
    if (!s[a]) s[a] = wiz_wmap_empty();
    wiz_val l = wiz_wmap_to_list(fz_take(s, a));
    wiz_dec(l);
    wm->n = 0;
    break;
  }
  }
}

static void fz_run(fz_input *in) {
  wiz_val str[DSLOTS] = {0}, bytes[DSLOTS] = {0}, arr[DSLOTS] = {0}, map[DSLOTS] = {0};
  wiz_val war[DSLOTS] = {0}, wmap[DSLOTS] = {0};
  uint32_t width[DSLOTS] = {8, 8, 8};
  fz_wmodel wm[DSLOTS] = {{0}};
  fz_smodel sm[DSLOTS] = {0};
  for (unsigned step = 0; step < DSTEPS && fz_more(in); step++) {
    switch (fz_below(in, 6)) {
    case 0: fz_strings(in, str); break;
    case 1: fz_bytess(in, bytes); break;
    case 2: fz_arrays(in, arr); break;
    case 3: fz_maps(in, map, sm); break;
    case 4: fz_warrays(in, war, width); break;
    default: fz_wmaps(in, wmap, wm); break;
    }
  }
  fz_drop_all(str, DSLOTS);
  fz_drop_all(bytes, DSLOTS);
  fz_drop_all(arr, DSLOTS);
  fz_drop_all(map, DSLOTS);
  fz_drop_all(war, DSLOTS);
  fz_drop_all(wmap, DSLOTS);
}

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
  long before = wiz_live_objects();
  fz_input in = {data, size, 0};
  fz_run(&in);
  fz_check_live(before);
  return 0;
}
