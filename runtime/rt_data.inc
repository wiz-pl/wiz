
/* a constructor value: a flat object ⟨tag f₁ … fₙ⟩, or just the tag without fields */
static wiz_val wiz_con(uint32_t tag, uint32_t n, wiz_val *fields) {
  if (n == 0) return WIZ_BOX(tag);
  wiz_val r = wiz_ctor_new(tag, n);
  for (uint32_t i = 0; i < n; i++) WIZ_SET(r, i, fields[i]);
  return r;
}
static wiz_val wiz_field_ref(wiz_val v, uint32_t i) { /* borrowed */
  return ((wiz_ctor *)v)->fields[i];
}

WIZ_API int wiz_in_bool(wiz_val v) { int b = (int)wiz_tag(v); wiz_dec(v); return b; }
WIZ_API wiz_val wiz_out_bool(int b) { return wiz_con(b ? 1 : 0, 0, NULL); }

/* String := String.mk (List Char), Char := Char.mk Nat; C strings are UTF-8 */
WIZ_API char *wiz_in_string(wiz_val s) {
  size_t cap = 16, len = 0;
  char *buf = (char *)malloc(cap);
  wiz_val l = wiz_field_ref(s, 0);
  while (wiz_tag(l) == 1) {
    wiz_val ch = wiz_field_ref(l, 0);
    wiz_val cp = wiz_field_ref(ch, 0);
    uint32_t c = WIZ_IS_SCALAR(cp) ? (uint32_t)WIZ_UNBOX(cp) : 0xFFFD;
    if (len + 5 > cap) { cap *= 2; buf = (char *)realloc(buf, cap); }
    if (c < 0x80) buf[len++] = (char)c;
    else if (c < 0x800) { buf[len++] = 0xC0 | (c >> 6); buf[len++] = 0x80 | (c & 0x3F); }
    else if (c < 0x10000) { buf[len++] = 0xE0 | (c >> 12); buf[len++] = 0x80 | ((c >> 6) & 0x3F); buf[len++] = 0x80 | (c & 0x3F); }
    else { buf[len++] = 0xF0 | (c >> 18); buf[len++] = 0x80 | ((c >> 12) & 0x3F); buf[len++] = 0x80 | ((c >> 6) & 0x3F); buf[len++] = 0x80 | (c & 0x3F); }
    l = wiz_field_ref(l, 1);
  }
  buf[len] = 0;
  wiz_dec(s);
  return buf;
}
WIZ_API wiz_val wiz_out_string(const char *s) {
  /* decode UTF-8 into code points, then build the list from the end */
  size_t n = strlen(s), k = 0;
  uint32_t *cps = (uint32_t *)malloc((n + 1) * sizeof(uint32_t));
  for (size_t i = 0; i < n;) {
    unsigned char c = (unsigned char)s[i];
    uint32_t cp; int len;
    if (c < 0x80) { cp = c; len = 1; }
    else if ((c >> 5) == 6) { cp = c & 0x1F; len = 2; }
    else if ((c >> 4) == 14) { cp = c & 0x0F; len = 3; }
    else { cp = c & 0x07; len = 4; }
    for (int j = 1; j < len && i + j < n; j++) cp = (cp << 6) | ((unsigned char)s[i + j] & 0x3F);
    cps[k++] = cp;
    i += len;
  }
  wiz_val list = wiz_con(0, 0, NULL);
  for (size_t i = k; i > 0; i--) {
    wiz_val chf[1] = {WIZ_BOX(cps[i - 1])};
    wiz_val fs[2] = {wiz_con(0, 1, chf), list};
    list = wiz_con(1, 2, fs);
  }
  free(cps);
  wiz_val sf[1] = {list};
  return wiz_con(0, 1, sf);
}

/* an `IO` result: the pair (value, world) */
WIZ_API wiz_val wiz_io_result(wiz_val v, wiz_val world) {
  wiz_val p = wiz_ctor_new(0, 2);
  WIZ_SET(p, 0, v); WIZ_SET(p, 1, world);
  return p;
}

/* ---- callbacks and exported functions (stage 9g) ----
   These three are part of the C interface whatever WIZ_API is. C code that holds a
   Wiz value (the context of a callback it keeps, a handle an exported function
   returned) owns one reference and gives it back with `wiz_release`; `wiz_retain`
   takes one more. `wiz_live_objects` counts the objects alive, for leak tests. */
void wiz_release(void *v) { wiz_dec((wiz_val)v); }
void wiz_retain(void *v) { wiz_inc((wiz_val)v); }
long wiz_live_objects(void) { return (long)wiz_live; }
/* the value of an `IO` result (value, world), which is consumed */
static wiz_val wiz_io_value(wiz_val r) {
  wiz_val v = ((wiz_ctor *)r)->fields[0];
  wiz_inc(v);
  wiz_dec(r);
  return v;
}

/* foreign pointers: borrowed for a call (the wrapper drops the reference after it) */
WIZ_API void *wiz_in_ptr(wiz_val v) { return ((wiz_ext *)v)->ptr; }
WIZ_API wiz_val wiz_out_ptr(void *p, void (*fin)(void *)) {
  wiz_ext *e = (wiz_ext *)wiz_alloc(sizeof(wiz_ext), WIZ_TAG_EXT, 0);
  e->ptr = p;
  e->fin = fin;
  return (wiz_val)e;
}

/* byte buffers: functional, but updated in place when unique (Perceus) */
WIZ_API wiz_val wiz_bytes_empty(void) {
  wiz_bytes *b = (wiz_bytes *)wiz_alloc(sizeof(wiz_bytes), WIZ_TAG_BYTES, 0);
  b->len = 0; b->cap = 0; b->data = NULL;
  return (wiz_val)b;
}
static wiz_val wiz_bytes_unique(wiz_val v) {
  wiz_bytes *b = (wiz_bytes *)v;
  if (WIZ_RC(&b->h) == 1) return v;
  wiz_bytes *c = (wiz_bytes *)wiz_bytes_empty();
  c->len = c->cap = b->len;
  c->data = (unsigned char *)malloc(b->len ? b->len : 1);
  memcpy(c->data, b->data, b->len);
  wiz_dec(v);
  return (wiz_val)c;
}
WIZ_API wiz_val wiz_bytes_push(wiz_val v, uint64_t x) {
  v = wiz_bytes_unique(v);
  wiz_bytes *b = (wiz_bytes *)v;
  if (b->len == b->cap) { b->cap = b->cap ? 2 * b->cap : 8; b->data = (unsigned char *)realloc(b->data, b->cap); }
  b->data[b->len++] = (unsigned char)x;
  return v;
}
WIZ_API uint64_t wiz_bytes_size(wiz_val v) { uint64_t n = ((wiz_bytes *)v)->len; wiz_dec(v); return n; }
WIZ_API uint64_t wiz_bytes_get(wiz_val v, uint64_t i) {
  wiz_bytes *b = (wiz_bytes *)v;
  uint64_t r = i < b->len ? b->data[i] : 0;
  wiz_dec(v);
  return r;
}
WIZ_API wiz_val wiz_bytes_of_string(const char *s) {
  wiz_val v = wiz_bytes_empty();
  for (const char *p = s; *p; p++) v = wiz_bytes_push(v, (unsigned char)*p);
  return v;
}
static __thread char *wiz_scratch = NULL;
WIZ_API const char *wiz_bytes_to_string(wiz_val v) {
  wiz_bytes *b = (wiz_bytes *)v;
  free(wiz_scratch);
  wiz_scratch = (char *)malloc(b->len + 1);
  memcpy(wiz_scratch, b->data, b->len);
  wiz_scratch[b->len] = 0;
  wiz_dec(v);
  return wiz_scratch;
}

/* ---- arrays: functional, updated in place when unique ---- */

WIZ_API wiz_val wiz_array_empty(void) {
  wiz_array *a = (wiz_array *)wiz_alloc(sizeof(wiz_array), WIZ_TAG_ARRAY, 0);
  a->len = a->cap = 0; a->data = NULL;
  return (wiz_val)a;
}
static wiz_val wiz_array_unique(wiz_val v) {
  wiz_array *a = (wiz_array *)v;
  if (WIZ_RC(&a->h) == 1) return v;
  wiz_array *c = (wiz_array *)wiz_array_empty();
  c->len = c->cap = a->len;
  c->data = (wiz_val *)malloc((a->len ? a->len : 1) * sizeof(wiz_val));
  for (size_t i = 0; i < a->len; i++) { c->data[i] = a->data[i]; wiz_inc(a->data[i]); }
  wiz_dec(v);
  return (wiz_val)c;
}
WIZ_API wiz_val wiz_array_push(wiz_val v, wiz_val x) {
  v = wiz_array_unique(v);
  wiz_array *a = (wiz_array *)v;
  if (a->len == a->cap) { a->cap = a->cap ? 2 * a->cap : 8; a->data = (wiz_val *)realloc(a->data, a->cap * sizeof(wiz_val)); }
  a->data[a->len++] = x;
  return v;
}
WIZ_API uint64_t wiz_array_size(wiz_val v) { uint64_t n = ((wiz_array *)v)->len; wiz_dec(v); return n; }
/* the element at i (a new reference), or the default */
WIZ_API wiz_val wiz_array_get(wiz_val v, uint64_t i, wiz_val dflt) {
  wiz_array *a = (wiz_array *)v;
  wiz_val r;
  if (i < a->len) { r = a->data[i]; wiz_inc(r); wiz_dec(dflt); } else r = dflt;
  wiz_dec(v);
  return r;
}
WIZ_API wiz_val wiz_array_set(wiz_val v, uint64_t i, wiz_val x) {
  if (i >= ((wiz_array *)v)->len) { wiz_dec(x); return v; }
  v = wiz_array_unique(v);
  wiz_array *a = (wiz_array *)v;
  wiz_dec(a->data[i]);
  a->data[i] = x;
  return v;
}

/* ---- text ---- */

static wiz_val wiz_str_new(const char *s, size_t n) {
  wiz_str *t = (wiz_str *)wiz_alloc(sizeof(wiz_str) + n + 1, WIZ_TAG_STR, 0);
  t->len = n;
  memcpy(t->data, s, n);
  t->data[n] = 0;
  return (wiz_val)t;
}
WIZ_API wiz_val wiz_str_of_cstr(const char *s) { return wiz_str_new(s, strlen(s)); }
WIZ_API const char *wiz_str_to_cstr(wiz_val v) {
  wiz_str *t = (wiz_str *)v;
  free(wiz_scratch);
  wiz_scratch = (char *)malloc(t->len + 1);
  memcpy(wiz_scratch, t->data, t->len + 1);
  wiz_dec(v);
  return wiz_scratch;
}
WIZ_API wiz_val wiz_str_append(wiz_val a, wiz_val b) {
  wiz_str *x = (wiz_str *)a, *y = (wiz_str *)b;
  wiz_str *t = (wiz_str *)wiz_alloc(sizeof(wiz_str) + x->len + y->len + 1, WIZ_TAG_STR, 0);
  t->len = x->len + y->len;
  memcpy(t->data, x->data, x->len);
  memcpy(t->data + x->len, y->data, y->len + 1);
  wiz_dec(a); wiz_dec(b);
  return (wiz_val)t;
}
WIZ_API uint64_t wiz_str_size(wiz_val v) { uint64_t n = ((wiz_str *)v)->len; wiz_dec(v); return n; }
WIZ_API uint64_t wiz_str_byte(wiz_val v, uint64_t i) {
  wiz_str *t = (wiz_str *)v;
  uint64_t r = i < t->len ? (unsigned char)t->data[i] : 0;
  wiz_dec(v);
  return r;
}
WIZ_API wiz_val wiz_str_slice(wiz_val v, uint64_t from, uint64_t to) {
  wiz_str *t = (wiz_str *)v;
  if (to > t->len) to = t->len;
  if (from > to) from = to;
  wiz_val r = wiz_str_new(t->data + from, to - from);
  wiz_dec(v);
  return r;
}
WIZ_API int wiz_str_eq(wiz_val a, wiz_val b) {
  wiz_str *x = (wiz_str *)a, *y = (wiz_str *)b;
  int r = x->len == y->len && memcmp(x->data, y->data, x->len) == 0;
  wiz_dec(a); wiz_dec(b);
  return r;
}
WIZ_API int wiz_str_lt(wiz_val a, wiz_val b) {
  wiz_str *x = (wiz_str *)a, *y = (wiz_str *)b;
  size_t n = x->len < y->len ? x->len : y->len;
  int c = memcmp(x->data, y->data, n);
  int r = c < 0 || (c == 0 && x->len < y->len);
  wiz_dec(a); wiz_dec(b);
  return r;
}

/* ---- maps from text: functional, updated in place when unique ---- */

static uint64_t wiz_str_hash(wiz_str *t) {
  uint64_t h = 1469598103934665603ULL;
  for (size_t i = 0; i < t->len; i++) { h ^= (unsigned char)t->data[i]; h *= 1099511628211ULL; }
  return h;
}
static int wiz_str_same(wiz_str *x, wiz_str *y) { return x->len == y->len && memcmp(x->data, y->data, x->len) == 0; }
WIZ_API wiz_val wiz_map_empty(void) {
  wiz_map *m = (wiz_map *)wiz_alloc(sizeof(wiz_map), WIZ_TAG_MAP, 0);
  m->count = 0; m->cap = 8;
  m->keys = (wiz_val *)calloc(8, sizeof(wiz_val));
  m->vals = (wiz_val *)calloc(8, sizeof(wiz_val));
  return (wiz_val)m;
}
static wiz_val wiz_map_unique(wiz_val v) {
  wiz_map *m = (wiz_map *)v;
  if (WIZ_RC(&m->h) == 1) return v;
  wiz_map *c = (wiz_map *)wiz_alloc(sizeof(wiz_map), WIZ_TAG_MAP, 0);
  c->count = m->count; c->cap = m->cap;
  c->keys = (wiz_val *)calloc(m->cap, sizeof(wiz_val));
  c->vals = (wiz_val *)calloc(m->cap, sizeof(wiz_val));
  for (size_t i = 0; i < m->cap; i++)
    if (m->keys[i]) { c->keys[i] = m->keys[i]; c->vals[i] = m->vals[i]; wiz_inc(m->keys[i]); wiz_inc(m->vals[i]); }
  wiz_dec(v);
  return (wiz_val)c;
}
static void wiz_map_put(wiz_map *m, wiz_val k, wiz_val x) {
  size_t i = wiz_str_hash((wiz_str *)k) & (m->cap - 1);
  while (m->keys[i] && !wiz_str_same((wiz_str *)m->keys[i], (wiz_str *)k)) i = (i + 1) & (m->cap - 1);
  if (m->keys[i]) { wiz_dec(m->keys[i]); wiz_dec(m->vals[i]); } else m->count++;
  m->keys[i] = k; m->vals[i] = x;
}
WIZ_API wiz_val wiz_map_insert(wiz_val v, wiz_val k, wiz_val x) {
  v = wiz_map_unique(v);
  wiz_map *m = (wiz_map *)v;
  if (2 * (m->count + 1) > m->cap) {
    size_t oc = m->cap;
    wiz_val *ok = m->keys, *ov = m->vals;
    m->cap *= 2; m->count = 0;
    m->keys = (wiz_val *)calloc(m->cap, sizeof(wiz_val));
    m->vals = (wiz_val *)calloc(m->cap, sizeof(wiz_val));
    for (size_t i = 0; i < oc; i++) if (ok[i]) wiz_map_put(m, ok[i], ov[i]);
    free(ok); free(ov);
  }
  wiz_map_put(m, k, x);
  return v;
}
/* the value for k (a new reference), or the default */
WIZ_API wiz_val wiz_map_find(wiz_val v, wiz_val k, wiz_val dflt) {
  wiz_map *m = (wiz_map *)v;
  size_t i = wiz_str_hash((wiz_str *)k) & (m->cap - 1);
  wiz_val r = dflt;
  while (m->keys[i]) {
    if (wiz_str_same((wiz_str *)m->keys[i], (wiz_str *)k)) { r = m->vals[i]; wiz_inc(r); wiz_dec(dflt); break; }
    i = (i + 1) & (m->cap - 1);
  }
  wiz_dec(v); wiz_dec(k);
  return r;
}
WIZ_API uint64_t wiz_map_size(wiz_val v) { uint64_t n = ((wiz_map *)v)->count; wiz_dec(v); return n; }

/* ---- unboxed arrays of words (lib/WordArray.wiz): functional, updated in place when
   unique ----
   The model is `mk (toList : List (UIntN w))` for w = 8, 32, 64 (`U8Array`, `U32Array`,
   `U64Array`); these implement its operations, on `width`-byte elements. Each consumes
   its arguments. Indices are `NatObj`s: one of 2^62 or more (a GMP number) is out of
   range, as in the model. */

/* an index (consumed): a big number is past every array */
static uint64_t wiz_index(wiz_val n) {
  if (WIZ_IS_SCALAR(n)) return WIZ_UNBOX(n);
  wiz_dec(n);
  return UINT64_MAX;
}
/* a word's bits (consumed); words in these structures are below 2^64 */
static uint64_t wiz_word_take(wiz_val v) {
  uint64_t b = 0;
  if (!wiz_word_in(v, &b)) wiz_panic("a word above 64 bits in a word array or map");
  wiz_dec(v);
  return b;
}
static wiz_val wiz_warray_new(uint32_t width, size_t cap) {
  wiz_warray *a = (wiz_warray *)wiz_alloc(sizeof(wiz_warray), WIZ_TAG_WARRAY, 0);
  a->len = 0; a->cap = cap; a->width = width;
  a->data = cap ? malloc(cap * width) : NULL;
  if (cap && !a->data) wiz_panic("out of memory");
  return (wiz_val)a;
}
static inline uint64_t wiz_warray_at(const wiz_warray *a, size_t i) {
  switch (a->width) {
  case 1: return ((const uint8_t *)a->data)[i];
  case 4: return ((const uint32_t *)a->data)[i];
  default: return ((const uint64_t *)a->data)[i];
  }
}
static inline void wiz_warray_put(wiz_warray *a, size_t i, uint64_t x) {
  switch (a->width) {
  case 1: ((uint8_t *)a->data)[i] = (uint8_t)x; break;
  case 4: ((uint32_t *)a->data)[i] = (uint32_t)x; break;
  default: ((uint64_t *)a->data)[i] = x;
  }
}
/* room for n elements */
static void wiz_warray_reserve(wiz_warray *a, size_t n) {
  if (n <= a->cap) return;
  size_t c = a->cap ? 2 * a->cap : 8;
  if (c < n) c = n;
  a->data = realloc(a->data, c * a->width);
  if (!a->data) wiz_panic("out of memory");
  a->cap = c;
}
/* v itself if unique, else a copy (with room for `extra` more) */
static wiz_val wiz_warray_unique(wiz_val v, size_t extra) {
  wiz_warray *a = (wiz_warray *)v;
  if (WIZ_RC(&a->h) == 1) return v;
  wiz_warray *c = (wiz_warray *)wiz_warray_new(a->width, a->len + extra);
  if (a->len) memcpy(c->data, a->data, a->len * a->width);
  c->len = a->len;
  wiz_dec(v);
  return (wiz_val)c;
}
/* the model's constructor: a list of words as an array */
static wiz_val wiz_warray_of_list(uint32_t width, wiz_val l) {
  size_t n = 0;
  for (wiz_val c = l; wiz_tag(c) == 1; c = wiz_field_ref(c, 1)) n++;
  wiz_warray *a = (wiz_warray *)wiz_warray_new(width, n);
  for (wiz_val c = l; wiz_tag(c) == 1; c = wiz_field_ref(c, 1)) {
    uint64_t b = 0;
    if (!wiz_word_in(wiz_field_ref(c, 0), &b)) wiz_panic("a word above 64 bits in a word array");
    wiz_warray_put(a, a->len++, b);
  }
  wiz_dec(l);
  return (wiz_val)a;
}
WIZ_API wiz_val wiz_u8array_empty(void) { return wiz_warray_new(1, 0); }
WIZ_API wiz_val wiz_u32array_empty(void) { return wiz_warray_new(4, 0); }
WIZ_API wiz_val wiz_u64array_empty(void) { return wiz_warray_new(8, 0); }
WIZ_API wiz_val wiz_u8array_of_list(wiz_val l) { return wiz_warray_of_list(1, l); }
WIZ_API wiz_val wiz_u32array_of_list(wiz_val l) { return wiz_warray_of_list(4, l); }
WIZ_API wiz_val wiz_u64array_of_list(wiz_val l) { return wiz_warray_of_list(8, l); }
/* the model's field: the elements as a list */
WIZ_API wiz_val wiz_warray_to_list(wiz_val v) {
  wiz_warray *a = (wiz_warray *)v;
  wiz_val l = WIZ_BOX(0);
  for (size_t i = a->len; i > 0; i--) {
    wiz_val fs[2] = {wiz_word_out(wiz_warray_at(a, i - 1)), l};
    l = wiz_con(1, 2, fs);
  }
  wiz_dec(v);
  return l;
}
WIZ_API wiz_val wiz_warray_size(wiz_val v) { size_t n = ((wiz_warray *)v)->len; wiz_dec(v); return WIZ_BOX(n); }
/* the element at i, or the default */
WIZ_API wiz_val wiz_warray_get(wiz_val v, wiz_val i, wiz_val d) {
  wiz_warray *a = (wiz_warray *)v;
  uint64_t k = wiz_index(i);
  wiz_val r = d;
  if (k < a->len) { r = wiz_word_out(wiz_warray_at(a, k)); wiz_dec(d); }
  wiz_dec(v);
  return r;
}
/* x at i (nothing changes when i is out of range) */
WIZ_API wiz_val wiz_warray_set(wiz_val v, wiz_val i, wiz_val x) {
  uint64_t k = wiz_index(i), b = wiz_word_take(x);
  if (k >= ((wiz_warray *)v)->len) return v;
  v = wiz_warray_unique(v, 0);
  wiz_warray_put((wiz_warray *)v, k, b);
  return v;
}
WIZ_API wiz_val wiz_warray_push(wiz_val v, wiz_val x) {
  uint64_t b = wiz_word_take(x);
  v = wiz_warray_unique(v, 1);
  wiz_warray *a = (wiz_warray *)v;
  wiz_warray_reserve(a, a->len + 1);
  wiz_warray_put(a, a->len++, b);
  return v;
}
/* without its last element (empty stays empty) */
WIZ_API wiz_val wiz_warray_pop(wiz_val v) {
  if (((wiz_warray *)v)->len == 0) return v;
  v = wiz_warray_unique(v, 0);
  ((wiz_warray *)v)->len--;
  return v;
}
/* elements [start, start + n), cut at the end */
WIZ_API wiz_val wiz_warray_slice(wiz_val v, wiz_val start, wiz_val n) {
  wiz_warray *a = (wiz_warray *)v;
  uint64_t s = wiz_index(start), k = wiz_index(n);
  if (s > a->len) s = a->len;
  if (k > a->len - s) k = a->len - s;
  if (s == 0 && WIZ_RC(&a->h) == 1) { a->len = k; return v; }
  wiz_warray *c = (wiz_warray *)wiz_warray_new(a->width, k);
  if (k) memcpy(c->data, (char *)a->data + s * a->width, k * a->width);
  c->len = k;
  wiz_dec(v);
  return (wiz_val)c;
}
/* a's elements, then b's (one element width: the types agree) */
WIZ_API wiz_val wiz_warray_append(wiz_val a, wiz_val b) {
  wiz_warray *y = (wiz_warray *)b;
  size_t n = y->len;
  if (n) {
    a = wiz_warray_unique(a, n);
    wiz_warray *x = (wiz_warray *)a;
    wiz_warray_reserve(x, x->len + n);
    memcpy((char *)x->data + x->len * x->width, y->data, n * x->width);
    x->len += n;
  }
  wiz_dec(b);
  return a;
}
/* For C code (`link_c`, `glue`) given a word array as a Wiz value: its elements, `len`
   contiguous `uint8_t`/`uint32_t`/`uint64_t`s, borrowed (valid while the caller holds the
   array, which it must not update meanwhile); and a new array copied from C memory.
   Part of the C interface whatever WIZ_API is, like `wiz_release`. */
void *wiz_warray_data(wiz_val v) { return ((wiz_warray *)v)->data; }
size_t wiz_warray_len(wiz_val v) { return ((wiz_warray *)v)->len; }
wiz_val wiz_warray_of_c(uint32_t width, const void *p, size_t n) {
  if (width != 1 && width != 4 && width != 8) wiz_panic("wiz_warray_of_c: width 1, 4 or 8");
  wiz_warray *a = (wiz_warray *)wiz_warray_new(width, n);
  if (n) memcpy(a->data, p, n * width);
  a->len = n;
  return (wiz_val)a;
}

/* ---- maps from 64-bit words (lib/WordMap.wiz): functional, updated in place when
   unique ----
   The model is `mk (entries : List (U64 × V))` with the keys strictly increasing, so
   the list read back (`wiz_wmap_to_list`) is sorted. */

static inline uint64_t wiz_mix64(uint64_t x) {
  x ^= x >> 33; x *= 0xff51afd7ed558ccdULL;
  x ^= x >> 33; x *= 0xc4ceb9fe1a85ec53ULL;
  x ^= x >> 33;
  return x;
}
static wiz_wmap *wiz_wmap_alloc(size_t cap) {
  wiz_wmap *m = (wiz_wmap *)wiz_alloc(sizeof(wiz_wmap), WIZ_TAG_WMAP, 0);
  m->count = 0; m->cap = cap;
  m->keys = (uint64_t *)malloc(cap * sizeof(uint64_t));
  m->vals = (wiz_val *)calloc(cap, sizeof(wiz_val));
  if (!m->keys || !m->vals) wiz_panic("out of memory");
  return m;
}
WIZ_API wiz_val wiz_wmap_empty(void) { return (wiz_val)wiz_wmap_alloc(8); }
/* the slot holding k, or the empty slot where it would go */
static size_t wiz_wmap_slot(const wiz_wmap *m, uint64_t k) {
  size_t mask = m->cap - 1, i = wiz_mix64(k) & mask;
  while (m->vals[i] && m->keys[i] != k) i = (i + 1) & mask;
  return i;
}
static wiz_val wiz_wmap_unique(wiz_val v) {
  wiz_wmap *m = (wiz_wmap *)v;
  if (WIZ_RC(&m->h) == 1) return v;
  wiz_wmap *c = wiz_wmap_alloc(m->cap);
  c->count = m->count;
  memcpy(c->keys, m->keys, m->cap * sizeof(uint64_t));
  for (size_t i = 0; i < m->cap; i++) if ((c->vals[i] = m->vals[i])) wiz_inc(m->vals[i]);
  wiz_dec(v);
  return (wiz_val)c;
}
static void wiz_wmap_put(wiz_wmap *m, uint64_t k, wiz_val x) {
  if (2 * (m->count + 1) > m->cap) {
    size_t oc = m->cap;
    uint64_t *ok = m->keys;
    wiz_val *ov = m->vals;
    m->cap = 2 * oc;
    m->keys = (uint64_t *)malloc(m->cap * sizeof(uint64_t));
    m->vals = (wiz_val *)calloc(m->cap, sizeof(wiz_val));
    if (!m->keys || !m->vals) wiz_panic("out of memory");
    for (size_t i = 0; i < oc; i++)
      if (ov[i]) { size_t j = wiz_wmap_slot(m, ok[i]); m->keys[j] = ok[i]; m->vals[j] = ov[i]; }
    free(ok); free(ov);
  }
  size_t i = wiz_wmap_slot(m, k);
  if (m->vals[i]) wiz_dec(m->vals[i]); else { m->count++; m->keys[i] = k; }
  m->vals[i] = x;
}
WIZ_API wiz_val wiz_wmap_insert(wiz_val v, wiz_val k, wiz_val x) {
  uint64_t key = wiz_word_take(k);
  v = wiz_wmap_unique(v);
  wiz_wmap_put((wiz_wmap *)v, key, x);
  return v;
}
/* the value for k as an `Option` */
WIZ_API wiz_val wiz_wmap_find(wiz_val v, wiz_val k) {
  wiz_wmap *m = (wiz_wmap *)v;
  size_t i = wiz_wmap_slot(m, wiz_word_take(k));
  wiz_val r = WIZ_BOX(0);
  if (m->vals[i]) { wiz_val fs[1] = {m->vals[i]}; wiz_inc(fs[0]); r = wiz_con(1, 1, fs); }
  wiz_dec(v);
  return r;
}
/* the value for k, or the default */
WIZ_API wiz_val wiz_wmap_find_d(wiz_val v, wiz_val k, wiz_val d) {
  wiz_wmap *m = (wiz_wmap *)v;
  size_t i = wiz_wmap_slot(m, wiz_word_take(k));
  wiz_val r = d;
  if (m->vals[i]) { r = m->vals[i]; wiz_inc(r); wiz_dec(d); }
  wiz_dec(v);
  return r;
}
WIZ_API int wiz_wmap_contains(wiz_val v, wiz_val k) {
  wiz_wmap *m = (wiz_wmap *)v;
  int r = m->vals[wiz_wmap_slot(m, wiz_word_take(k))] != 0;
  wiz_dec(v);
  return r;
}
/* without k: empty its slot, then shift back the entries after it that may move */
WIZ_API wiz_val wiz_wmap_erase(wiz_val v, wiz_val k) {
  uint64_t key = wiz_word_take(k);
  if (!((wiz_wmap *)v)->vals[wiz_wmap_slot((wiz_wmap *)v, key)]) return v;
  v = wiz_wmap_unique(v);
  wiz_wmap *m = (wiz_wmap *)v;
  size_t mask = m->cap - 1, i = wiz_wmap_slot(m, key);
  wiz_dec(m->vals[i]);
  m->vals[i] = 0;
  m->count--;
  for (size_t j = (i + 1) & mask; m->vals[j]; j = (j + 1) & mask) {
    size_t home = wiz_mix64(m->keys[j]) & mask;
    /* the entry at j may fill the hole at i unless its home lies in (i, j] (cyclically) */
    if (((j - home) & mask) >= ((j - i) & mask)) {
      m->keys[i] = m->keys[j]; m->vals[i] = m->vals[j]; m->vals[j] = 0;
      i = j;
    }
  }
  return v;
}
WIZ_API wiz_val wiz_wmap_size(wiz_val v) { size_t n = ((wiz_wmap *)v)->count; wiz_dec(v); return WIZ_BOX(n); }
typedef struct { uint64_t k; wiz_val v; } wiz_wmap_ent;
static int wiz_wmap_ent_cmp(const void *a, const void *b) {
  uint64_t x = ((const wiz_wmap_ent *)a)->k, y = ((const wiz_wmap_ent *)b)->k;
  return x < y ? -1 : x > y;
}
/* the model's field: the entries as pairs, by increasing key */
WIZ_API wiz_val wiz_wmap_to_list(wiz_val v) {
  wiz_wmap *m = (wiz_wmap *)v;
  wiz_wmap_ent *es = (wiz_wmap_ent *)malloc((m->count ? m->count : 1) * sizeof(wiz_wmap_ent));
  size_t n = 0;
  for (size_t i = 0; i < m->cap; i++) if (m->vals[i]) { es[n].k = m->keys[i]; es[n].v = m->vals[i]; n++; }
  qsort(es, n, sizeof(wiz_wmap_ent), wiz_wmap_ent_cmp);
  wiz_val l = WIZ_BOX(0);
  for (size_t i = n; i > 0; i--) {
    wiz_inc(es[i - 1].v);
    wiz_val p[2] = {wiz_word_out(es[i - 1].k), es[i - 1].v};
    wiz_val fs[2] = {wiz_con(0, 2, p), l};
    l = wiz_con(1, 2, fs);
  }
  free(es);
  wiz_dec(v);
  return l;
}
/* the model's constructor: a list of (key, value) pairs as a map */
WIZ_API wiz_val wiz_wmap_of_list(wiz_val l) {
  wiz_wmap *m = wiz_wmap_alloc(8);
  for (wiz_val c = l; wiz_tag(c) == 1; c = wiz_field_ref(c, 1)) {
    wiz_val p = wiz_field_ref(c, 0), k = wiz_field_ref(p, 0), x = wiz_field_ref(p, 1);
    uint64_t b = 0;
    if (!wiz_word_in(k, &b)) wiz_panic("a key above 64 bits in a word map");
    wiz_inc(x);
    wiz_wmap_put(m, b, x);
  }
  wiz_dec(l);
  return (wiz_val)m;
}

/* ---- intern tables (lib/Intern.wiz): functional, updated in place when unique ----
   The model is `mk (strs : List String)`, distinct strings in the order they were
   interned; a string's id is its index. A `String` is `String.mk (List Char)` and a
   `Char` is `Char.mk Nat` (see `wiz_in_string`): hashed and compared by code points. */

static uint64_t wiz_string_hash(wiz_val s) {
  uint64_t h = 1469598103934665603ULL;
  for (wiz_val l = wiz_field_ref(s, 0); wiz_tag(l) == 1; l = wiz_field_ref(l, 1)) {
    wiz_val cp = wiz_field_ref(wiz_field_ref(l, 0), 0);
    h ^= WIZ_IS_SCALAR(cp) ? WIZ_UNBOX(cp) : mpz_get_ui(((wiz_big *)cp)->z);
    h *= 1099511628211ULL;
  }
  return h;
}
static int wiz_nat_same(wiz_val a, wiz_val b) {
  if (WIZ_IS_SCALAR(a) || WIZ_IS_SCALAR(b)) return a == b;
  return mpz_cmp(((wiz_big *)a)->z, ((wiz_big *)b)->z) == 0;
}
static int wiz_string_same(wiz_val a, wiz_val b) {
  if (a == b) return 1;
  wiz_val x = wiz_field_ref(a, 0), y = wiz_field_ref(b, 0);
  for (; wiz_tag(x) == 1 && wiz_tag(y) == 1; x = wiz_field_ref(x, 1), y = wiz_field_ref(y, 1))
    if (x == y) return 1; /* a shared tail */
    else if (!wiz_nat_same(wiz_field_ref(wiz_field_ref(x, 0), 0), wiz_field_ref(wiz_field_ref(y, 0), 0))) return 0;
  return wiz_tag(x) == wiz_tag(y);
}
static wiz_itab *wiz_itab_alloc(size_t scap, size_t cap) {
  wiz_itab *t = (wiz_itab *)wiz_alloc(sizeof(wiz_itab), WIZ_TAG_ITAB, 0);
  t->count = 0; t->scap = scap; t->cap = cap;
  t->strs = (wiz_val *)malloc(scap * sizeof(wiz_val));
  t->hashes = (uint64_t *)malloc(scap * sizeof(uint64_t));
  t->slots = (uint32_t *)calloc(cap, sizeof(uint32_t));
  if (!t->strs || !t->hashes || !t->slots) wiz_panic("out of memory");
  return t;
}
WIZ_API wiz_val wiz_itab_empty(void) { return (wiz_val)wiz_itab_alloc(8, 16); }
/* the index slot holding s (hash h), or the empty slot where it would go */
static size_t wiz_itab_slot(const wiz_itab *t, uint64_t h, wiz_val s) {
  size_t mask = t->cap - 1, i = wiz_mix64(h) & mask;
  for (; t->slots[i]; i = (i + 1) & mask) {
    uint32_t id = t->slots[i] - 1;
    if (t->hashes[id] == h && wiz_string_same(t->strs[id], s)) break;
  }
  return i;
}
static wiz_val wiz_itab_unique(wiz_val v) {
  wiz_itab *t = (wiz_itab *)v;
  if (WIZ_RC(&t->h) == 1) return v;
  wiz_itab *c = wiz_itab_alloc(t->scap, t->cap);
  c->count = t->count;
  for (size_t i = 0; i < t->count; i++) { c->strs[i] = t->strs[i]; wiz_inc(t->strs[i]); }
  memcpy(c->hashes, t->hashes, t->count * sizeof(uint64_t));
  memcpy(c->slots, t->slots, t->cap * sizeof(uint32_t));
  wiz_dec(v);
  return (wiz_val)c;
}
/* s's id, adding s (consumed) if it is new */
static uint32_t wiz_itab_add(wiz_itab *t, wiz_val s) {
  uint64_t h = wiz_string_hash(s);
  size_t i = wiz_itab_slot(t, h, s);
  if (t->slots[i]) { wiz_dec(s); return t->slots[i] - 1; }
  if (t->count >= 0xFFFFFFFEu) wiz_panic("an intern table with 2^32 strings");
  if (t->count == t->scap) {
    t->scap *= 2;
    t->strs = (wiz_val *)realloc(t->strs, t->scap * sizeof(wiz_val));
    t->hashes = (uint64_t *)realloc(t->hashes, t->scap * sizeof(uint64_t));
    if (!t->strs || !t->hashes) wiz_panic("out of memory");
  }
  uint32_t id = (uint32_t)t->count++;
  t->strs[id] = s; t->hashes[id] = h;
  if (2 * t->count > t->cap) {
    free(t->slots);
    t->cap *= 2;
    t->slots = (uint32_t *)calloc(t->cap, sizeof(uint32_t));
    if (!t->slots) wiz_panic("out of memory");
    for (uint32_t k = 0; k < t->count; k++) {
      size_t j = wiz_mix64(t->hashes[k]) & (t->cap - 1);
      while (t->slots[j]) j = (j + 1) & (t->cap - 1);
      t->slots[j] = k + 1;
    }
  } else t->slots[i] = id + 1;
  return id;
}
/* (the table with s, s's id) */
WIZ_API wiz_val wiz_itab_intern(wiz_val v, wiz_val s) {
  wiz_itab *t = (wiz_itab *)v;
  uint64_t h = wiz_string_hash(s);
  uint32_t id;
  size_t i = wiz_itab_slot(t, h, s);
  if (t->slots[i]) { id = t->slots[i] - 1; wiz_dec(s); }
  else { v = wiz_itab_unique(v); id = wiz_itab_add((wiz_itab *)v, s); }
  wiz_val p[2] = {v, WIZ_BOX(id)};
  return wiz_con(0, 2, p);
}
/* s's id as an `Option` (the table is unchanged) */
WIZ_API wiz_val wiz_itab_find(wiz_val v, wiz_val s) {
  wiz_itab *t = (wiz_itab *)v;
  size_t i = wiz_itab_slot(t, wiz_string_hash(s), s);
  wiz_val r = WIZ_BOX(0);
  if (t->slots[i]) { wiz_val fs[1] = {WIZ_BOX(t->slots[i] - 1)}; r = wiz_con(1, 1, fs); }
  wiz_dec(v); wiz_dec(s);
  return r;
}
/* the string with this id (a `U32`), or "" */
WIZ_API wiz_val wiz_itab_lookup(wiz_val v, wiz_val id) {
  wiz_itab *t = (wiz_itab *)v;
  uint64_t k = wiz_word_take(id);
  wiz_val r;
  if (k < t->count) { r = t->strs[k]; wiz_inc(r); }
  else { wiz_val fs[1] = {WIZ_BOX(0)}; r = wiz_con(0, 1, fs); }
  wiz_dec(v);
  return r;
}
WIZ_API wiz_val wiz_itab_size(wiz_val v) { size_t n = ((wiz_itab *)v)->count; wiz_dec(v); return WIZ_BOX(n); }
/* the model's field: the strings, by id */
WIZ_API wiz_val wiz_itab_to_list(wiz_val v) {
  wiz_itab *t = (wiz_itab *)v;
  wiz_val l = WIZ_BOX(0);
  for (size_t i = t->count; i > 0; i--) {
    wiz_inc(t->strs[i - 1]);
    wiz_val fs[2] = {t->strs[i - 1], l};
    l = wiz_con(1, 2, fs);
  }
  wiz_dec(v);
  return l;
}
/* the model's constructor: distinct strings (the module keeps them so), by id */
WIZ_API wiz_val wiz_itab_of_list(wiz_val l) {
  wiz_itab *t = wiz_itab_alloc(8, 16);
  for (wiz_val c = l; wiz_tag(c) == 1; c = wiz_field_ref(c, 1)) {
    wiz_val s = wiz_field_ref(c, 0);
    wiz_inc(s);
    wiz_itab_add(t, s);
  }
  wiz_dec(l);
  return (wiz_val)t;
}

WIZ_API void wiz_io_write_file(const char *path, const char *text) {
  FILE *f = fopen(path, "wb");
  if (f) { fputs(text, f); fclose(f); }
}

/* files, for the library */
WIZ_API const char *wiz_io_read_file(const char *path) {
  FILE *f = fopen(path, "rb");
  free(wiz_scratch);
  wiz_scratch = NULL;
  if (!f) { wiz_scratch = (char *)calloc(1, 1); return wiz_scratch; }
  size_t cap = 1024, len = 0;
  wiz_scratch = (char *)malloc(cap);
  size_t n;
  while ((n = fread(wiz_scratch + len, 1, cap - len - 1, f)) > 0) {
    len += n;
    if (len + 1 == cap) { cap *= 2; wiz_scratch = (char *)realloc(wiz_scratch, cap); }
  }
  wiz_scratch[len] = 0;
  fclose(f);
  return wiz_scratch;
}

/* the program's arguments (without its name), saved by `main` (stage 21k) */
static int wiz_argc;
static char **wiz_argv;
WIZ_API void wiz_set_args(int argc, char **argv) { wiz_argc = argc; wiz_argv = argv; }
WIZ_API uint64_t wiz_io_arg_count(void) { return wiz_argc > 1 ? (uint64_t)(wiz_argc - 1) : 0; }
WIZ_API const char *wiz_io_arg(uint64_t i) { return i + 1 < (uint64_t)wiz_argc ? wiz_argv[i + 1] : ""; }

/* functions for the library to bind */
WIZ_API void wiz_io_println(const char *s) { puts(s); fflush(stdout); }
WIZ_API void wiz_io_print(const char *s) { fputs(s, stdout); fflush(stdout); }
WIZ_API uint64_t wiz_u64_id(uint64_t a) { return a; }
WIZ_API uint64_t wiz_u64_add(uint64_t a, uint64_t b) { return a + b; }
WIZ_API uint64_t wiz_u64_sub(uint64_t a, uint64_t b) { return a - b; }
WIZ_API uint64_t wiz_u64_mul(uint64_t a, uint64_t b) { return a * b; }
WIZ_API uint64_t wiz_u64_div(uint64_t a, uint64_t b) { return b ? a / b : 0; }
WIZ_API uint64_t wiz_u64_mod(uint64_t a, uint64_t b) { return b ? a % b : a; }
WIZ_API int wiz_u64_lt(uint64_t a, uint64_t b) { return a < b; }
WIZ_API int wiz_u64_eq(uint64_t a, uint64_t b) { return a == b; }
WIZ_API double wiz_f64_of_nat(uint64_t a) { return (double)a; }
WIZ_API double wiz_f64_add(double a, double b) { return a + b; }
WIZ_API double wiz_f64_sub(double a, double b) { return a - b; }
WIZ_API double wiz_f64_mul(double a, double b) { return a * b; }
WIZ_API double wiz_f64_div(double a, double b) { return a / b; }
WIZ_API int wiz_f64_lt(double a, double b) { return a < b; }
WIZ_API const char *wiz_f64_show(double a) { static __thread char buf[64]; snprintf(buf, sizeof buf, "%.17g", a); return buf; }
WIZ_API const char *wiz_nat_show(uint64_t a) { static __thread char buf[32]; snprintf(buf, sizeof buf, "%llu", (unsigned long long)a); return buf; }

/* (P2) The step budget of a proof's read-back in the self-hosted toolchain (selfhost/Kernel.wiz,
   `forceProof`; `Budget` in Wiz/Core/Term.lean is the Lean frontend's): a counter behind a
   pure interface, as in Lean. `start` begins a budget of `steps` closure instantiations
   (1: it did; 0: one is already running, the caller counts on it), `tick` takes one step
   (1, or 0 once it ran out; always 1 when no budget runs), `end` stops it (1: it did not
   run out). Only the read-back of a suspended proof starts one, so the kernel's own
   evaluation never finds one running. (Per thread, like the read-back.) */
static __thread int wiz_proof_on = 0;
static __thread uint64_t wiz_proof_left = 0;
WIZ_API int wiz_proof_start(uint64_t steps) { if (wiz_proof_on) return 0; wiz_proof_on = 1; wiz_proof_left = steps + 1; return 1; }
WIZ_API int wiz_proof_tick(uint64_t x) { (void)x; if (!wiz_proof_on) return 1; if (wiz_proof_left <= 1) { wiz_proof_left = 0; return 0; } wiz_proof_left--; return 1; }
WIZ_API int wiz_proof_end(uint64_t x) { (void)x; wiz_proof_on = 0; return wiz_proof_left > 0; }
