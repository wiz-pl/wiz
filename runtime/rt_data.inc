
#include <errno.h>

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

/* ---- UTF-8 (one rule: `Bytes`, `String` at the C boundary, the interpreters and the
   self-hosted runtime; docs/libraries.md, "Byte buffers") ----

   The length of a sequence is the lead byte's top bits: 0xxxxxxx 1, 110xxxxx 2,
   1110xxxx 3, 11110xxx 4; a byte that is none of those (10xxxxxx, 11111xxx) is not a
   lead. A sequence is *valid* when its continuation bytes (10xxxxxx) are all there and
   the scalar is not overlong (below 80, 800, 10000 for 2, 3, 4 bytes), not a surrogate
   (D800 … DFFF) and at most 10FFFF. `Bytes.toUtf8` reports the offset of the lead byte
   of the first invalid sequence; the C-string decoders cannot fail, so they write
   U+FFFD for it and resume after the bytes the lead claimed (one for a non-lead). A
   non-scalar code point is encoded as U+FFFD too, by every encoder. */

/* the length a lead byte claims, and its low bits */
static int wiz_utf8_span(unsigned char c, uint32_t *cp) {
  if (c < 0x80) { *cp = c; return 1; }
  if ((c >> 5) == 6) { *cp = c & 0x1F; return 2; }
  if ((c >> 4) == 14) { *cp = c & 0x0F; return 3; }
  if ((c >> 3) == 30) { *cp = c & 0x07; return 4; }
  *cp = 0xFFFD; return 1; /* not a lead: 10xxxxxx, 11111xxx */
}
/* the scalar of `len` bytes at `p`, or U+FFFD if the sequence is not valid */
static uint32_t wiz_utf8_scalar(int len, uint32_t cp, const unsigned char *p) {
  for (int j = 1; j < len; j++) {
    if ((p[j] & 0xC0) != 0x80) return 0xFFFD;
    cp = (cp << 6) | (p[j] & 0x3F);
  }
  if ((len == 2 && cp < 0x80) || (len == 3 && cp < 0x800) || (len == 4 && cp < 0x10000)) return 0xFFFD;
  if ((cp >= 0xD800 && cp <= 0xDFFF) || cp > 0x10FFFF) return 0xFFFD;
  return cp;
}
/* a code point as the encoders write it: a non-scalar value is U+FFFD */
static uint32_t wiz_utf8_code(uint64_t c) {
  return (c > 0x10FFFF || (c >= 0xD800 && c <= 0xDFFF)) ? 0xFFFD : (uint32_t)c;
}

/* String := String.mk (List Char), Char := Char.mk Nat; C strings are UTF-8 */
WIZ_API char *wiz_in_string(wiz_val s) {
  size_t cap = 16, len = 0;
  char *buf = (char *)malloc(cap);
  wiz_val l = wiz_field_ref(s, 0);
  while (wiz_tag(l) == 1) {
    wiz_val ch = wiz_field_ref(l, 0);
    wiz_val cp = wiz_field_ref(ch, 0);
    uint32_t c = wiz_utf8_code(WIZ_IS_SCALAR(cp) ? (uint64_t)WIZ_UNBOX(cp) : 0xFFFD);
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
  /* a C function may return NULL: `strchr`/`strstr`/`memchr` on a miss, `getenv` for an
     unset variable, `realpath` on failure. `import_c` types `char *` as `String` (a C
     header says nothing about nullability), so read NULL as "", like the struct-field
     marshalling does (`C.lean`, `c.f ? c.f : ""`), `wiz_sys_getenv` below, and the
     self-hosted runtime's `rt_out_str`. */
  if (!s) s = "";
  /* decode UTF-8 into code points, then build the list from the end */
  size_t n = strlen(s), k = 0;
  uint32_t *cps = (uint32_t *)malloc((n + 1) * sizeof(uint32_t));
  for (size_t i = 0; i < n;) {
    uint32_t cp;
    int len = wiz_utf8_span((unsigned char)s[i], &cp);
    cps[k++] = i + (size_t)len > n ? 0xFFFD
             : wiz_utf8_scalar(len, cp, (const unsigned char *)s + i);
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

/* ---- text ----

   A `wiz_str` is an immutable value: there is no `cap` field, so the unused header
   word stores the buffer's capacity in bytes (`wiz_hdr.size`, 0 when the capacity is
   not known or exceeds the header's 32-bit word). `wiz_str_append` may then extend a
   *unique* buffer in place, exactly as `wiz_bytes_push` does; a shared or aliased
   string is copied first. The aliasing argument is the reference count: the caller
   owns one reference (the language calls `wiz_str_append(a, b)` with both operands
   consumed), so `WIZ_RC(a) == 1` means no other value can observe the buffer. `a == b`
   is excluded even then, because `Str.append s s` passes the same object twice and
   copying its bytes while they are read is only safe when the buffer is not realloc'd.
   Capacity grows geometrically (`max(8, 2 * cap)`), which is what makes a loop of
   appends amortised linear; a copy-on-share allocates the exact new length. */

static size_t wiz_str_cap(wiz_str *t) {
  size_t cap = t->h.size;
  return cap ? cap : t->len; /* a capacity too large for the header is treated as exact */
}
static void wiz_str_set_cap(wiz_str *t, size_t cap) {
  t->h.size = cap <= 0xFFFFFFFFu ? (uint32_t)cap : 0;
}
static wiz_val wiz_str_new(const char *s, size_t n) {
  wiz_str *t = (wiz_str *)wiz_alloc(sizeof(wiz_str) + n + 1, WIZ_TAG_STR, 0);
  t->len = n;
  wiz_str_set_cap(t, n);
  memcpy(t->data, s, n);
  t->data[n] = 0;
  return (wiz_val)t;
}
WIZ_API wiz_val wiz_str_empty(void) { return wiz_str_new("", 0); }
WIZ_API wiz_val wiz_str_of_cstr(const char *s) { return wiz_str_new(s, strlen(s)); }
WIZ_API const char *wiz_str_to_cstr(wiz_val v) {
  wiz_str *t = (wiz_str *)v;
  free(wiz_scratch);
  wiz_scratch = (char *)malloc(t->len + 1);
  memcpy(wiz_scratch, t->data, t->len + 1);
  wiz_dec(v);
  return wiz_scratch;
}
/* append `n` bytes, growing the buffer in place when `v` is unique */
static wiz_val wiz_str_grow(wiz_val v, size_t n) {
  wiz_str *t = (wiz_str *)v;
  size_t need = t->len + n;
  if (need > wiz_str_cap(t)) {
    size_t cap = wiz_str_cap(t);
    if (cap < 8) cap = 8;
    while (cap < need) cap *= 2;
    t = (wiz_str *)wiz_xrealloc(t, sizeof(wiz_str) + cap + 1);
    wiz_str_set_cap(t, cap);
  }
  return (wiz_val)t;
}
WIZ_API wiz_val wiz_str_append(wiz_val a, wiz_val b) {
  wiz_str *x = (wiz_str *)a, *y = (wiz_str *)b;
  size_t n = y->len;
  if (a != b && WIZ_RC(&x->h) == 1) {
    /* unique and not self-append: no other value can see the buffer */
    x = (wiz_str *)wiz_str_grow(a, n);
    memcpy(x->data + x->len, y->data, n + 1);
    x->len += n;
    wiz_dec(b);
    return (wiz_val)x;
  }
  size_t need = x->len + y->len;
  wiz_str *t = (wiz_str *)wiz_alloc(sizeof(wiz_str) + need + 1, WIZ_TAG_STR, 0);
  t->len = need;
  wiz_str_set_cap(t, need);
  memcpy(t->data, x->data, x->len);
  memcpy(t->data + x->len, y->data, y->len + 1);
  wiz_dec(a); wiz_dec(b);
  return (wiz_val)t;
}
WIZ_API wiz_val wiz_str_push(wiz_val v, uint64_t byte) {
  if (WIZ_RC(&((wiz_str *)v)->h) == 1) {
    v = wiz_str_grow(v, 1);
    wiz_str *t = (wiz_str *)v;
    t->data[t->len++] = (char)(unsigned char)byte;
    t->data[t->len] = 0;
    return v;
  }
  char c = (char)(unsigned char)byte;
  wiz_str *x = (wiz_str *)v;
  wiz_str *t = (wiz_str *)wiz_alloc(sizeof(wiz_str) + x->len + 2, WIZ_TAG_STR, 0);
  t->len = x->len + 1;
  wiz_str_set_cap(t, t->len);
  memcpy(t->data, x->data, x->len);
  t->data[x->len] = c;
  t->data[x->len + 1] = 0;
  wiz_dec(v);
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

/* An `IO` call has no error channel, so a file operation that fails is reported on
   standard error and the program stops with 1: it must not look like success. The stop
   is clean (`wiz_clean_exit`, rt_core.inc): an armed boundary catches it, the native
   CLI exits. */
__attribute__((noreturn)) static void wiz_io_fail(const char *path, int e) {
  fprintf(stderr, "wiz: %s: %s\n", path, strerror(e));
  wiz_clean_exit(1);
}

/* `IO.writeFile`: the text as UTF-8 up to its first NUL (the `String` representation
   ends there; `FS.writeBytes` is for binary data). A bad path, a full disk (a short
   write, or `fclose` flushing the last buffer) is reported and stops the program. */
WIZ_API void wiz_io_write_file(const char *path, const char *text) {
  FILE *f = fopen(path, "wb");
  int e = 0;
  if (!f) e = errno;
  else {
    size_t n = strlen(text);
    if (fwrite(text, 1, n, f) != n) e = errno ? errno : EIO;
    if (fclose(f) < 0 && !e) e = errno;
  }
  if (e) wiz_io_fail(path, e);
}

/* `IO.readFile`: the whole file into the `wiz_scratch` buffer, as text up to the first
   NUL. A path that does not exist reads as empty text: the library's callers (the
   module loader's candidate paths) ask "is there a file here?" with a read, so absence is
   an answer, and a missing file and an empty one look alike. Any other failure (a
   directory, no permission, a read error, out of memory) is reported and stops the
   program, as `IO.writeFile` does: it is not the empty text. `FS.readFile` in lib/Sys.wiz
   is the variant with an `EIO` error channel. */
WIZ_API const char *wiz_io_read_file(const char *path) {
  FILE *f = fopen(path, "rb");
  int e = f ? 0 : errno;
  free(wiz_scratch);
  wiz_scratch = NULL;
  if (!f) {
    if (e == ENOENT) return wiz_scratch = (char *)wiz_xcalloc(1, 1);
    wiz_io_fail(path, e);
  }
  size_t cap = 1024, len = 0;
  wiz_scratch = (char *)malloc(cap);
  if (!wiz_scratch) { fclose(f); wiz_io_fail(path, ENOMEM); }
  size_t n;
  while ((n = fread(wiz_scratch + len, 1, cap - len - 1, f)) > 0) {
    len += n;
    if (len + 1 == cap) {
      cap *= 2;
      char *nb = (char *)realloc(wiz_scratch, cap);
      if (!nb) {
        free(wiz_scratch); wiz_scratch = NULL; fclose(f); wiz_io_fail(path, ENOMEM);
      }
      wiz_scratch = nb;
    }
  }
  if (ferror(f)) e = errno ? errno : EIO; /* a read error is not the end of the file */
  fclose(f);
  if (e) {
    free(wiz_scratch); wiz_scratch = NULL;
    wiz_io_fail(path, e);
  }
  wiz_scratch[len] = 0;
  return wiz_scratch;
}

/* the program's arguments (without its name), saved by `main` (stage 21k) */
static int wiz_argc;
static char **wiz_argv;
WIZ_API void wiz_set_args(int argc, char **argv) { wiz_argc = argc; wiz_argv = argv; }
WIZ_API uint64_t wiz_io_arg_count(void) { return wiz_argc > 1 ? (uint64_t)(wiz_argc - 1) : 0; }
WIZ_API const char *wiz_io_arg(uint64_t i) {
  /* `i + 1` overflows at 2^64-1: compare against the count instead (and never index
     past argv) */
  return i < (wiz_argc > 1 ? (uint64_t)(wiz_argc - 1) : 0) ? wiz_argv[i + 1] : "";
}

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
/* ---- shortest round-trip `Float64` printing (R6) ---------------------------

   Ryu (Ulf Adams, PLDI 2018), the 64-bit `d2s` algorithm with the small lookup
   tables (`RYU_OPTIMIZE_SIZE`), ported to C99 and prefixed `wiz_ryu_`. It emits the
   shortest decimal that parses back to the same double, so `Float64.toString` is
   deterministic and round-trips: the result no longer depends on the libc's
   `%.17g` (whose last digit is unspecified and which is not shortest). The form is
   scientific (`1E0`, `-0E0`, `5E-324`, `1.7976931348623157E308`); the non-finite
   values print as `NaN`, `Infinity` and `-Infinity` (a NaN's sign bit is not part
   of its value). `-0.0` keeps its sign.

   Ported from https://github.com/ulfjack/ryu: Copyright 2018 Ulf Adams,
   licensed under the Apache License 2.0 or the Boost Software License 1.0 (the
   upstream repository carries both notices). */

#define WIZ_RYU_MANTISSA_BITS 52
#define WIZ_RYU_EXPONENT_BITS 11
#define WIZ_RYU_BIAS 1023
#define WIZ_RYU_POW5_INV_BITCOUNT 125
#define WIZ_RYU_POW5_BITCOUNT 125
#define WIZ_RYU_POW5_TABLE_SIZE 26

typedef struct { uint64_t mantissa; int32_t exponent; } wiz_ryu_fd;

static uint32_t wiz_ryu_decimal_length17(uint64_t v) {
  if (v >= 10000000000000000ull) return 17;
  if (v >= 1000000000000000ull) return 16;
  if (v >= 100000000000000ull) return 15;
  if (v >= 10000000000000ull) return 14;
  if (v >= 1000000000000ull) return 13;
  if (v >= 100000000000ull) return 12;
  if (v >= 10000000000ull) return 11;
  if (v >= 1000000000ull) return 10;
  if (v >= 100000000ull) return 9;
  if (v >= 10000000ull) return 8;
  if (v >= 1000000ull) return 7;
  if (v >= 100000ull) return 6;
  if (v >= 10000ull) return 5;
  if (v >= 1000ull) return 4;
  if (v >= 100ull) return 3;
  if (v >= 10ull) return 2;
  return 1;
}

/* ceil(log_2(5^e)), 0 <= e <= 3528 */
static int32_t wiz_ryu_pow5bits(int32_t e) {
  return (int32_t)((((uint32_t)e * 1217359u) >> 19) + 1);
}
/* floor(log_10(2^e)), 0 <= e <= 1650 */
static uint32_t wiz_ryu_log10pow2(int32_t e) {
  return ((uint32_t)e * 78913u) >> 18;
}
/* floor(log_10(5^e)), 0 <= e <= 2620 */
static uint32_t wiz_ryu_log10pow5(int32_t e) {
  return ((uint32_t)e * 732923u) >> 20;
}
static uint64_t wiz_ryu_div5(uint64_t x) { return x / 5; }
static uint64_t wiz_ryu_div10(uint64_t x) { return x / 10; }
static uint64_t wiz_ryu_div100(uint64_t x) { return x / 100; }

static uint32_t wiz_ryu_pow5factor(uint64_t value) {
  const uint64_t m_inv_5 = 14757395258967641293ull; /* 5 * m_inv_5 = 1 (mod 2^64) */
  const uint64_t n_div_5 = 3689348814741910323ull;  /* 2^64 / 5 */
  uint32_t count = 0;
  for (;;) {
    value *= m_inv_5;
    if (value > n_div_5) break;
    ++count;
  }
  return count;
}
static int wiz_ryu_multiple_of_power_of_5(uint64_t value, uint32_t p) {
  return wiz_ryu_pow5factor(value) >= p;
}
static int wiz_ryu_multiple_of_power_of_2(uint64_t value, uint32_t p) {
  return (value & ((1ull << p) - 1)) == 0;
}

/* (wasm32 uses the 64-bit-only path: no `__int128` codegen assumption for the
   playground/Wasm build) */
#if defined(__SIZEOF_INT128__) && !defined(WIZ_RYU_ONLY_64_BIT_OPS) && \
    !defined(__EMSCRIPTEN__) && !defined(__wasm__)
#define WIZ_RYU_HAS_U128 1
typedef __uint128_t wiz_ryu_u128;
static uint64_t wiz_ryu_mulshift64(uint64_t m, const uint64_t *mul, int32_t j) {
  const wiz_ryu_u128 b0 = (wiz_ryu_u128)m * mul[0];
  const wiz_ryu_u128 b2 = (wiz_ryu_u128)m * mul[1];
  return (uint64_t)(((b0 >> 64) + b2) >> (j - 64));
}
static uint64_t wiz_ryu_mulshiftall64(uint64_t m, const uint64_t *mul, int32_t j,
    uint64_t *vp, uint64_t *vm, uint32_t mmshift) {
  *vp = wiz_ryu_mulshift64(4 * m + 2, mul, j);
  *vm = wiz_ryu_mulshift64(4 * m - 1 - mmshift, mul, j);
  return wiz_ryu_mulshift64(4 * m, mul, j);
}
#else
/* the reference's 64-bit-only path: no `__int128`, no intrinsics */
static uint64_t wiz_ryu_umul128(uint64_t a, uint64_t b, uint64_t *hi) {
  const uint32_t alo = (uint32_t)a, ahi = (uint32_t)(a >> 32);
  const uint32_t blo = (uint32_t)b, bhi = (uint32_t)(b >> 32);
  const uint64_t b00 = (uint64_t)alo * blo;
  const uint64_t b01 = (uint64_t)alo * bhi;
  const uint64_t b10 = (uint64_t)ahi * blo;
  const uint64_t b11 = (uint64_t)ahi * bhi;
  const uint32_t b00lo = (uint32_t)b00, b00hi = (uint32_t)(b00 >> 32);
  const uint64_t mid1 = b10 + b00hi;
  const uint32_t mid1lo = (uint32_t)mid1, mid1hi = (uint32_t)(mid1 >> 32);
  const uint64_t mid2 = b01 + mid1lo;
  const uint32_t mid2lo = (uint32_t)mid2, mid2hi = (uint32_t)(mid2 >> 32);
  *hi = b11 + mid1hi + mid2hi;
  return ((uint64_t)mid2lo << 32) | b00lo;
}
static uint64_t wiz_ryu_shiftright128(uint64_t lo, uint64_t hi, uint32_t dist) {
  return (hi << (64 - dist)) | (lo >> dist);
}
static uint64_t wiz_ryu_mulshift64(uint64_t m, const uint64_t *mul, int32_t j) {
  uint64_t high1;
  const uint64_t low1 = wiz_ryu_umul128(m, mul[1], &high1);
  uint64_t high0;
  (void)wiz_ryu_umul128(m, mul[0], &high0);
  const uint64_t sum = high0 + low1;
  if (sum < high0) ++high1;
  return wiz_ryu_shiftright128(sum, high1, (uint32_t)(j - 64));
}
static uint64_t wiz_ryu_mulshiftall64(uint64_t m, const uint64_t *mul, int32_t j,
    uint64_t *vp, uint64_t *vm, uint32_t mmshift) {
  *vp = wiz_ryu_mulshift64(4 * m + 2, mul, j);
  *vm = wiz_ryu_mulshift64(4 * m - 1 - mmshift, mul, j);
  return wiz_ryu_mulshift64(4 * m, mul, j);
}
#endif

/* 1/5^i, scaled to 125 bits (every 26th entry), and the corrections that make the
   intermediate entries exact. Generated by Ryu's `PrintDoubleLookupTable`. */
static const uint64_t wiz_ryu_pow5_inv_split2[15][2] = {
  {                    1u, 2305843009213693952u },
  {  5955668970331000884u, 1784059615882449851u },
  {  8982663654677661702u, 1380349269358112757u },
  {  7286864317269821294u, 2135987035920910082u },
  {  7005857020398200553u, 1652639921975621497u },
  { 17965325103354776697u, 1278668206209430417u },
  {  8928596168509315048u, 1978643211784836272u },
  { 10075671573058298858u, 1530901034580419511u },
  {   597001226353042382u, 1184477304306571148u },
  {  1527430471115325346u, 1832889850782397517u },
  { 12533209867169019542u, 1418129833677084982u },
  {  5577825024675947042u, 2194449627517475473u },
  { 11006974540203867551u, 1697873161311732311u },
  { 10313493231639821582u, 1313665730009899186u },
  { 12701016819766672773u, 2032799256770390445u }
};
static const uint32_t wiz_ryu_pow5_inv_offsets[22] = {
  0x54544554, 0x04055545, 0x10041000, 0x00400414, 0x40010000, 0x41155555,
  0x00000454, 0x00010044, 0x40000000, 0x44000041, 0x50454450, 0x55550054,
  0x51655554, 0x40004000, 0x01000001, 0x00010500, 0x51515411, 0x05555554,
  0x50411500, 0x40040000, 0x05040110, 0x00000000
};
/* 5^i, scaled to 125 bits (every 26th entry), and the corrections. */
static const uint64_t wiz_ryu_pow5_split2[13][2] = {
  {                    0u, 1152921504606846976u },
  {                    0u, 1490116119384765625u },
  {  1032610780636961552u, 1925929944387235853u },
  {  7910200175544436838u, 1244603055572228341u },
  { 16941905809032713930u, 1608611746708759036u },
  { 13024893955298202172u, 2079081953128979843u },
  {  6607496772837067824u, 1343575221513417750u },
  { 17332926989895652603u, 1736530273035216783u },
  { 13037379183483547984u, 2244412773384604712u },
  {  1605989338741628675u, 1450417759929778918u },
  {  9630225068416591280u, 1874621017369538693u },
  {   665883850346957067u, 1211445438634777304u },
  { 14931890668723713708u, 1565756531257009982u }
};
static const uint32_t wiz_ryu_pow5_offsets[21] = {
  0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x40000000, 0x59695995,
  0x55545555, 0x56555515, 0x41150504, 0x40555410, 0x44555145, 0x44504540,
  0x45555550, 0x40004000, 0x96440440, 0x55565565, 0x54454045, 0x40154151,
  0x55559155, 0x51405555, 0x00000105
};
static const uint64_t wiz_ryu_pow5_table[WIZ_RYU_POW5_TABLE_SIZE] = {
  1ull, 5ull, 25ull, 125ull, 625ull, 3125ull, 15625ull, 78125ull, 390625ull,
  1953125ull, 9765625ull, 48828125ull, 244140625ull, 1220703125ull, 6103515625ull,
  30517578125ull, 152587890625ull, 762939453125ull, 3814697265625ull,
  19073486328125ull, 95367431640625ull, 476837158203125ull,
  2384185791015625ull, 11920928955078125ull, 59604644775390625ull,
  298023223876953125ull
};

#if defined(WIZ_RYU_HAS_U128)
static void wiz_ryu_compute_pow5(uint32_t i, uint64_t *result) {
  const uint32_t base = i / WIZ_RYU_POW5_TABLE_SIZE;
  const uint32_t base2 = base * WIZ_RYU_POW5_TABLE_SIZE;
  const uint32_t offset = i - base2;
  const uint64_t *mul = wiz_ryu_pow5_split2[base];
  if (offset == 0) { result[0] = mul[0]; result[1] = mul[1]; return; }
  const uint64_t m = wiz_ryu_pow5_table[offset];
  const wiz_ryu_u128 b0 = (wiz_ryu_u128)m * mul[0];
  const wiz_ryu_u128 b2 = (wiz_ryu_u128)m * mul[1];
  const uint32_t delta = (uint32_t)(wiz_ryu_pow5bits((int32_t)i) - wiz_ryu_pow5bits((int32_t)base2));
  const wiz_ryu_u128 shifted = (b0 >> delta) + (b2 << (64 - delta)) +
    ((wiz_ryu_pow5_offsets[i / 16] >> ((i % 16) << 1)) & 3);
  result[0] = (uint64_t)shifted;
  result[1] = (uint64_t)(shifted >> 64);
}
static void wiz_ryu_compute_inv_pow5(uint32_t i, uint64_t *result) {
  const uint32_t base = (i + WIZ_RYU_POW5_TABLE_SIZE - 1) / WIZ_RYU_POW5_TABLE_SIZE;
  const uint32_t base2 = base * WIZ_RYU_POW5_TABLE_SIZE;
  const uint32_t offset = base2 - i;
  const uint64_t *mul = wiz_ryu_pow5_inv_split2[base];
  if (offset == 0) { result[0] = mul[0]; result[1] = mul[1]; return; }
  const uint64_t m = wiz_ryu_pow5_table[offset];
  const wiz_ryu_u128 b0 = (wiz_ryu_u128)m * (mul[0] - 1);
  const wiz_ryu_u128 b2 = (wiz_ryu_u128)m * mul[1];
  const uint32_t delta = (uint32_t)(wiz_ryu_pow5bits((int32_t)base2) - wiz_ryu_pow5bits((int32_t)i));
  const wiz_ryu_u128 shifted = ((b0 >> delta) + (b2 << (64 - delta))) + 1 +
    ((wiz_ryu_pow5_inv_offsets[i / 16] >> ((i % 16) << 1)) & 3);
  result[0] = (uint64_t)shifted;
  result[1] = (uint64_t)(shifted >> 64);
}
#else
static void wiz_ryu_compute_pow5(uint32_t i, uint64_t *result) {
  const uint32_t base = i / WIZ_RYU_POW5_TABLE_SIZE;
  const uint32_t base2 = base * WIZ_RYU_POW5_TABLE_SIZE;
  const uint32_t offset = i - base2;
  const uint64_t *mul = wiz_ryu_pow5_split2[base];
  if (offset == 0) { result[0] = mul[0]; result[1] = mul[1]; return; }
  const uint64_t m = wiz_ryu_pow5_table[offset];
  uint64_t high1;
  const uint64_t low1 = wiz_ryu_umul128(m, mul[1], &high1);
  uint64_t high0;
  const uint64_t low0 = wiz_ryu_umul128(m, mul[0], &high0);
  const uint64_t sum = high0 + low1;
  if (sum < high0) ++high1;
  const uint32_t delta = (uint32_t)(wiz_ryu_pow5bits((int32_t)i) - wiz_ryu_pow5bits((int32_t)base2));
  result[0] = wiz_ryu_shiftright128(low0, sum, delta) +
    ((wiz_ryu_pow5_offsets[i / 16] >> ((i % 16) << 1)) & 3);
  result[1] = wiz_ryu_shiftright128(sum, high1, delta);
}
static void wiz_ryu_compute_inv_pow5(uint32_t i, uint64_t *result) {
  const uint32_t base = (i + WIZ_RYU_POW5_TABLE_SIZE - 1) / WIZ_RYU_POW5_TABLE_SIZE;
  const uint32_t base2 = base * WIZ_RYU_POW5_TABLE_SIZE;
  const uint32_t offset = base2 - i;
  const uint64_t *mul = wiz_ryu_pow5_inv_split2[base];
  if (offset == 0) { result[0] = mul[0]; result[1] = mul[1]; return; }
  const uint64_t m = wiz_ryu_pow5_table[offset];
  uint64_t high1;
  const uint64_t low1 = wiz_ryu_umul128(m, mul[1], &high1);
  uint64_t high0;
  const uint64_t low0 = wiz_ryu_umul128(m, mul[0] - 1, &high0);
  const uint64_t sum = high0 + low1;
  if (sum < high0) ++high1;
  const uint32_t delta = (uint32_t)(wiz_ryu_pow5bits((int32_t)base2) - wiz_ryu_pow5bits((int32_t)i));
  result[0] = wiz_ryu_shiftright128(low0, sum, delta) + 1 +
    ((wiz_ryu_pow5_inv_offsets[i / 16] >> ((i % 16) << 1)) & 3);
  result[1] = wiz_ryu_shiftright128(sum, high1, delta);
}
#endif

/* the shortest decimal `mantissa * 10^exponent` in the rounding interval of the
   double `ieeeMantissa * 2^...`; the port of Ryu's `d2d`. */
static wiz_ryu_fd wiz_ryu_d2d(uint64_t ieeeMantissa, uint32_t ieeeExponent) {
  int32_t e2;
  uint64_t m2;
  if (ieeeExponent == 0) {
    e2 = 1 - WIZ_RYU_BIAS - WIZ_RYU_MANTISSA_BITS - 2;
    m2 = ieeeMantissa;
  } else {
    e2 = (int32_t)ieeeExponent - WIZ_RYU_BIAS - WIZ_RYU_MANTISSA_BITS - 2;
    m2 = (1ull << WIZ_RYU_MANTISSA_BITS) | ieeeMantissa;
  }
  const int even = (m2 & 1) == 0;
  const int acceptBounds = even;
  const uint64_t mv = 4 * m2;
  const uint32_t mmShift = (ieeeMantissa != 0 || ieeeExponent <= 1) ? 1 : 0;
  uint64_t vr, vp, vm;
  int32_t e10;
  int vmIsTrailingZeros = 0, vrIsTrailingZeros = 0;
  uint64_t pow5[2];
  if (e2 >= 0) {
    const uint32_t q = wiz_ryu_log10pow2(e2) - (e2 > 3);
    e10 = (int32_t)q;
    const int32_t k = WIZ_RYU_POW5_INV_BITCOUNT + wiz_ryu_pow5bits((int32_t)q) - 1;
    const int32_t i = -e2 + (int32_t)q + k;
    wiz_ryu_compute_inv_pow5(q, pow5);
    vr = wiz_ryu_mulshiftall64(m2, pow5, i, &vp, &vm, mmShift);
    if (q <= 21) {
      const uint32_t mvMod5 = (uint32_t)mv - 5 * (uint32_t)wiz_ryu_div5(mv);
      if (mvMod5 == 0) {
        vrIsTrailingZeros = wiz_ryu_multiple_of_power_of_5(mv, q);
      } else if (acceptBounds) {
        vmIsTrailingZeros = wiz_ryu_multiple_of_power_of_5(mv - 1 - mmShift, q);
      } else {
        if (wiz_ryu_multiple_of_power_of_5(mv + 2, q)) --vp;
      }
    }
  } else {
    const uint32_t q = wiz_ryu_log10pow5(-e2) - (-e2 > 1);
    e10 = (int32_t)q + e2;
    const int32_t i = -e2 - (int32_t)q;
    const int32_t k = wiz_ryu_pow5bits(i) - WIZ_RYU_POW5_BITCOUNT;
    const int32_t j = (int32_t)q - k;
    wiz_ryu_compute_pow5((uint32_t)i, pow5);
    vr = wiz_ryu_mulshiftall64(m2, pow5, j, &vp, &vm, mmShift);
    if (q <= 1) {
      vrIsTrailingZeros = 1;
      if (acceptBounds) vmIsTrailingZeros = mmShift == 1;
      else --vp;
    } else if (q < 63) {
      vrIsTrailingZeros = wiz_ryu_multiple_of_power_of_2(mv, q);
    }
  }
  int32_t removed = 0;
  uint8_t lastRemovedDigit = 0;
  uint64_t output;
  if (vmIsTrailingZeros || vrIsTrailingZeros) {
    for (;;) {
      const uint64_t vpDiv10 = wiz_ryu_div10(vp);
      const uint64_t vmDiv10 = wiz_ryu_div10(vm);
      if (vpDiv10 <= vmDiv10) break;
      const uint32_t vmMod10 = (uint32_t)vm - 10 * (uint32_t)vmDiv10;
      const uint64_t vrDiv10 = wiz_ryu_div10(vr);
      const uint32_t vrMod10 = (uint32_t)vr - 10 * (uint32_t)vrDiv10;
      vmIsTrailingZeros &= vmMod10 == 0;
      vrIsTrailingZeros &= lastRemovedDigit == 0;
      lastRemovedDigit = (uint8_t)vrMod10;
      vr = vrDiv10;
      vp = vpDiv10;
      vm = vmDiv10;
      ++removed;
    }
    if (vmIsTrailingZeros) {
      for (;;) {
        const uint64_t vmDiv10 = wiz_ryu_div10(vm);
        const uint32_t vmMod10 = (uint32_t)vm - 10 * (uint32_t)vmDiv10;
        if (vmMod10 != 0) break;
        const uint64_t vpDiv10 = wiz_ryu_div10(vp);
        const uint64_t vrDiv10 = wiz_ryu_div10(vr);
        const uint32_t vrMod10 = (uint32_t)vr - 10 * (uint32_t)vrDiv10;
        vrIsTrailingZeros &= lastRemovedDigit == 0;
        lastRemovedDigit = (uint8_t)vrMod10;
        vr = vrDiv10;
        vp = vpDiv10;
        vm = vmDiv10;
        ++removed;
      }
    }
    if (vrIsTrailingZeros && lastRemovedDigit == 5 && vr % 2 == 0) {
      lastRemovedDigit = 4;
    }
    output = vr + ((vr == vm && (!acceptBounds || !vmIsTrailingZeros)) || lastRemovedDigit >= 5);
  } else {
    int roundUp = 0;
    const uint64_t vpDiv100 = wiz_ryu_div100(vp);
    const uint64_t vmDiv100 = wiz_ryu_div100(vm);
    if (vpDiv100 > vmDiv100) {
      const uint64_t vrDiv100 = wiz_ryu_div100(vr);
      const uint32_t vrMod100 = (uint32_t)vr - 100 * (uint32_t)vrDiv100;
      roundUp = vrMod100 >= 50;
      vr = vrDiv100;
      vp = vpDiv100;
      vm = vmDiv100;
      removed += 2;
    }
    for (;;) {
      const uint64_t vpDiv10 = wiz_ryu_div10(vp);
      const uint64_t vmDiv10 = wiz_ryu_div10(vm);
      if (vpDiv10 <= vmDiv10) break;
      const uint64_t vrDiv10 = wiz_ryu_div10(vr);
      const uint32_t vrMod10 = (uint32_t)vr - 10 * (uint32_t)vrDiv10;
      roundUp = vrMod10 >= 5;
      vr = vrDiv10;
      vp = vpDiv10;
      vm = vmDiv10;
      ++removed;
    }
    output = vr + (vr == vm || roundUp);
  }
  wiz_ryu_fd fd;
  fd.mantissa = output;
  fd.exponent = e10 + removed;
  return fd;
}

/* the small-integer fast path: an integral double below 2^53 has an exact decimal
   value; trailing zeros move into the exponent for the scientific form. */
static int wiz_ryu_d2d_small_int(uint64_t ieeeMantissa, uint32_t ieeeExponent, wiz_ryu_fd *v) {
  const uint64_t m2 = (1ull << WIZ_RYU_MANTISSA_BITS) | ieeeMantissa;
  const int32_t e2 = (int32_t)ieeeExponent - WIZ_RYU_BIAS - WIZ_RYU_MANTISSA_BITS;
  if (e2 > 0 || e2 < -52) return 0;
  const uint64_t mask = (1ull << -e2) - 1;
  if ((m2 & mask) != 0) return 0;
  v->mantissa = m2 >> -e2;
  v->exponent = 0;
  return 1;
}

/* `d.dddE±x` (or `dE±x`) from the decimal `mantissa * 10^exponent`. */
static int wiz_ryu_to_chars(wiz_ryu_fd v, int sign, char *result) {
  int index = 0;
  if (sign) result[index++] = '-';
  uint64_t output = v.mantissa;
  const uint32_t olength = wiz_ryu_decimal_length17(output);
  char digits[20];
  uint32_t i = 0;
  do {
    digits[i++] = (char)('0' + (output % 10));
    output /= 10;
  } while (output != 0);
  /* `digits` is least-significant first; the first printed digit is the leading one */
  for (uint32_t d = 0; d < olength; ++d) {
    result[index++] = digits[olength - 1 - d];
    if (d == 0 && olength > 1) result[index++] = '.';
  }
  result[index++] = 'E';
  int32_t exp = v.exponent + (int32_t)olength - 1;
  if (exp < 0) { result[index++] = '-'; exp = -exp; }
  if (exp >= 100) {
    result[index++] = (char)('0' + exp / 100);
    result[index++] = (char)('0' + (exp / 10) % 10);
    result[index++] = (char)('0' + exp % 10);
  } else if (exp >= 10) {
    result[index++] = (char)('0' + exp / 10);
    result[index++] = (char)('0' + exp % 10);
  } else {
    result[index++] = (char)('0' + exp);
  }
  return index;
}

/* NaN (sign ignored: not part of the value), ±Infinity, ±0 */
static int wiz_ryu_special(char *result, int sign, int exponent, int mantissa) {
  if (mantissa) { memcpy(result, "NaN", 3); return 3; }
  int i = 0;
  if (sign) result[i++] = '-';
  if (exponent) { memcpy(result + i, "Infinity", 8); return i + 8; }
  memcpy(result + i, "0E0", 3);
  return i + 3;
}

/* The shortest round-tripping text for `f` (no terminator); returns its length. */
static int wiz_ryu_d2s(double f, char *result) {
  uint64_t bits;
  memcpy(&bits, &f, sizeof bits);
  const int sign = (int)((bits >> (WIZ_RYU_MANTISSA_BITS + WIZ_RYU_EXPONENT_BITS)) & 1);
  const uint64_t ieeeMantissa = bits & ((1ull << WIZ_RYU_MANTISSA_BITS) - 1);
  const uint32_t ieeeExponent =
    (uint32_t)((bits >> WIZ_RYU_MANTISSA_BITS) & ((1u << WIZ_RYU_EXPONENT_BITS) - 1));
  if (ieeeExponent == ((1u << WIZ_RYU_EXPONENT_BITS) - 1u) ||
      (ieeeExponent == 0 && ieeeMantissa == 0)) {
    return wiz_ryu_special(result, sign, (int)ieeeExponent, (int)ieeeMantissa);
  }
  wiz_ryu_fd v;
  if (wiz_ryu_d2d_small_int(ieeeMantissa, ieeeExponent, &v)) {
    for (;;) {
      const uint64_t q = v.mantissa / 10;
      if (v.mantissa != 10 * q) break;
      v.mantissa = q;
      ++v.exponent;
    }
  } else {
    v = wiz_ryu_d2d(ieeeMantissa, ieeeExponent);
  }
  return wiz_ryu_to_chars(v, sign, result);
}

WIZ_API const char *wiz_f64_show(double a) {
  static __thread char buf[40];
  int n = wiz_ryu_d2s(a, buf);
  buf[n] = 0;
  return buf;
}
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

/* The kernel evaluator's per-command budget: one tick per structural elimination
   (`vIndW`/`vSfix`/`vScase`), not per beta step. It is its own counter so a command's
   budget does not make the proof read-back's `wiz_proof_*` budget run for ordinary
   evaluation. */
static __thread int wiz_kernel_on = 0;
static __thread uint64_t wiz_kernel_left = 0;
WIZ_API int wiz_kernel_start(uint64_t steps) { if (wiz_kernel_on) return 0; wiz_kernel_on = 1; wiz_kernel_left = steps + 1; return 1; }
WIZ_API int wiz_kernel_tick(uint64_t x) { (void)x; if (!wiz_kernel_on) return 1; if (wiz_kernel_left <= 1) { wiz_kernel_left = 0; return 0; } wiz_kernel_left--; return 1; }
WIZ_API int wiz_kernel_end(uint64_t x) { (void)x; wiz_kernel_on = 0; return wiz_kernel_left > 0; }
