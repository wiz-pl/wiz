
/* objects allocated minus objects freed, per thread (see `wiz_live_exited`) */
static __thread int64_t wiz_live = 0;
/* read a count that another thread may be changing (if the object is shared) */
#define WIZ_RC(h) __atomic_load_n(&(h)->rc, __ATOMIC_RELAXED)

/* with WIZ_LEAKS set, remember every live object, to list the leaked ones at exit */
static int wiz_leaks = -1;
static void *wiz_watch = NULL;
static void **wiz_track_tab = NULL;
static size_t wiz_track_cap = 0, wiz_track_n = 0;
static size_t wiz_track_slot(void *p) {
  size_t i = ((uintptr_t)p >> 4) * 11400714819323198485ull & (wiz_track_cap - 1);
  while (wiz_track_tab[i] && wiz_track_tab[i] != p) i = (i + 1) & (wiz_track_cap - 1);
  return i;
}
static pthread_mutex_t wiz_track_mu = PTHREAD_MUTEX_INITIALIZER;
static void wiz_track_init(void) {
  wiz_leaks = getenv("WIZ_LEAKS") != NULL;
  if (getenv("WIZ_WATCH")) wiz_watch = (void *)strtoull(getenv("WIZ_WATCH"), NULL, 16);
}
static void wiz_track_(void *p);
static void wiz_track(void *p) {
  if (wiz_leaks < 0) wiz_track_init();
  if (!wiz_leaks) return;
  pthread_mutex_lock(&wiz_track_mu);
  wiz_track_(p);
  pthread_mutex_unlock(&wiz_track_mu);
}
static void wiz_track_(void *p) {
  if (2 * (wiz_track_n + 1) > wiz_track_cap) {
    void **old = wiz_track_tab; size_t oc = wiz_track_cap;
    wiz_track_cap = oc ? 2 * oc : 1024;
    wiz_track_tab = (void **)calloc(wiz_track_cap, sizeof(void *));
    wiz_track_n = 0;
    for (size_t i = 0; i < oc; i++) if (old[i] && old[i] != (void *)1) { wiz_track_tab[wiz_track_slot(old[i])] = old[i]; wiz_track_n++; }
    free(old);
  }
  wiz_track_tab[wiz_track_slot(p)] = p;
  wiz_track_n++;
}
static void wiz_untrack_(void *p);
static void wiz_untrack(void *p) {
  if (wiz_leaks != 1) return;
  pthread_mutex_lock(&wiz_track_mu);
  wiz_untrack_(p);
  pthread_mutex_unlock(&wiz_track_mu);
}
static void wiz_untrack_(void *p) {
  /* rebuild the probe chain after removing */
  size_t i = wiz_track_slot(p);
  if (wiz_track_tab[i] != p) return;
  wiz_track_tab[i] = NULL; wiz_track_n--;
  for (size_t j = (i + 1) & (wiz_track_cap - 1); wiz_track_tab[j]; j = (j + 1) & (wiz_track_cap - 1)) {
    void *q = wiz_track_tab[j]; wiz_track_tab[j] = NULL; wiz_track_n--;
    wiz_track_tab[wiz_track_slot(q)] = q; wiz_track_n++;
  }
}

static void wiz_panic(const char *msg) {
  fprintf(stderr, "wiz: %s\n", msg);
  exit(3);
}

static void *wiz_alloc(size_t bytes, uint32_t tag, uint32_t size) {
  wiz_hdr *h = (wiz_hdr *)malloc(bytes);
  if (!h) wiz_panic("out of memory");
  h->rc = 1;
  h->tag = tag;
  h->size = size;
  wiz_live++;
  wiz_track(h);
  return h;
}

WIZ_API wiz_val wiz_ctor_new(uint32_t tag, uint32_t n) {
  wiz_ctor *o = (wiz_ctor *)wiz_alloc(sizeof(wiz_ctor) + n * sizeof(wiz_val), tag, n);
  return (wiz_val)o;
}
#define WIZ_SET(o, i, v) (((wiz_ctor *)(o))->fields[i] = (v))

/* with WIZ_WATCH=<address> (and WIZ_LEAKS), log the reference count changes of one object */
static void wiz_watch_log(const char *what, wiz_val v, void *from) {
  if ((void *)v == wiz_watch) fprintf(stderr, "  %s %p: rc %ld, from %p\n", what, (void *)v, (long)((wiz_hdr *)v)->rc, from);
}
WIZ_API void wiz_inc(wiz_val v) {
  if (!WIZ_IS_SCALAR(v)) {
    wiz_hdr *h = (wiz_hdr *)v;
    int64_t rc = WIZ_RC(h);
    if (rc > 0) h->rc = rc + 1;
    else if (rc < 0) __atomic_fetch_sub(&h->rc, 1, __ATOMIC_RELAXED);
  }
  if (wiz_watch) wiz_watch_log("inc", v, __builtin_return_address(0));
}

static void wiz_free(wiz_val v);

WIZ_API void wiz_dec(wiz_val v) {
  if (wiz_watch) wiz_watch_log("dec", v, __builtin_return_address(0));
  if (WIZ_IS_SCALAR(v)) return;
  wiz_hdr *h = (wiz_hdr *)v;
  int64_t rc = WIZ_RC(h);
  if (rc > 1) h->rc = rc - 1;
  else if (rc == 1) wiz_free(v);
  else if (rc < 0 && __atomic_add_fetch(&h->rc, 1, __ATOMIC_ACQ_REL) == 0) wiz_free(v);
}

static void wiz_free(wiz_val v) {
  wiz_hdr *h = (wiz_hdr *)v;
  if (h->tag == WIZ_TAG_CLO) {
    wiz_clo *c = (wiz_clo *)v;
    for (uint32_t i = 0; i < h->size; i++) wiz_dec(c->args[i]);
  } else if (h->tag == WIZ_TAG_BIG) {
    mpz_clear(((wiz_big *)v)->z);
  } else if (h->tag == WIZ_TAG_RAW) {
    /* raw machine words: nothing inside to drop */
  } else if (h->tag == WIZ_TAG_EXT) {
    wiz_ext *e = (wiz_ext *)v;
    if (e->fin && e->ptr) e->fin(e->ptr);
  } else if (h->tag == WIZ_TAG_BYTES) {
    free(((wiz_bytes *)v)->data);
  } else if (h->tag == WIZ_TAG_ARRAY) {
    wiz_array *a = (wiz_array *)v;
    for (size_t i = 0; i < a->len; i++) wiz_dec(a->data[i]);
    free(a->data);
  } else if (h->tag == WIZ_TAG_STR) {
    /* the text is inline */
  } else if (h->tag == WIZ_TAG_THUNK) {
    wiz_thunk *t = (wiz_thunk *)v;
    if (t->fn) wiz_dec(t->fn); else wiz_dec(t->val);
  } else if (h->tag == WIZ_TAG_MAP) {
    wiz_map *m = (wiz_map *)v;
    for (size_t i = 0; i < m->cap; i++) if (m->keys[i]) { wiz_dec(m->keys[i]); wiz_dec(m->vals[i]); }
    free(m->keys); free(m->vals);
  } else if (h->tag == WIZ_TAG_WARRAY) {
    free(((wiz_warray *)v)->data);
  } else if (h->tag == WIZ_TAG_WMAP) {
    wiz_wmap *m = (wiz_wmap *)v;
    for (size_t i = 0; i < m->cap; i++) if (m->vals[i]) wiz_dec(m->vals[i]);
    free(m->keys); free(m->vals);
  } else if (h->tag == WIZ_TAG_ITAB) {
    wiz_itab *t = (wiz_itab *)v;
    for (size_t i = 0; i < t->count; i++) wiz_dec(t->strs[i]);
    free(t->strs); free(t->hashes); free(t->slots);
  } else {
    wiz_ctor *o = (wiz_ctor *)v;
    for (uint32_t i = 0; i < h->size; i++) wiz_dec(o->fields[i]);
  }
  wiz_live--;
  wiz_untrack(h);
  free(h);
}

/* A shared constant (a hoisted constant, or the value of a closed top-level definition):
   never freed, and not counted as live (so not a leak). Everything it reaches that one
   thread owns (rc > 0) becomes immortal too (rc 0), whatever its kind: the value of a
   closed definition may hold closures, suspensions, numbers, arrays … An object shared
   between threads (rc < 0) keeps its count: other threads may be changing it, and it
   stays alive as long as the constant holds its reference. Iterative (a constant may be
   a long list). */
static void wiz_immortal(wiz_val v) {
  if (WIZ_IS_SCALAR(v) || ((wiz_hdr *)v)->rc <= 0) return;
  size_t cap = 64, n = 0;
  wiz_val *st = (wiz_val *)malloc(cap * sizeof(wiz_val));
  st[n++] = v;
#define WIZ_PUSH(x) do { wiz_val y_ = (x); if (!WIZ_IS_SCALAR(y_) && ((wiz_hdr *)y_)->rc > 0) { \
    if (n == cap) { cap *= 2; st = (wiz_val *)realloc(st, cap * sizeof(wiz_val)); } st[n++] = y_; } } while (0)
  while (n) {
    wiz_val x = st[--n];
    wiz_hdr *h = (wiz_hdr *)x;
    if (h->rc <= 0) continue; /* reached twice, or immortal or shared already */
    h->rc = 0;
    wiz_live--;
    wiz_untrack(h);
    switch (h->tag) {
    case WIZ_TAG_CLO: for (uint32_t i = 0; i < h->size; i++) WIZ_PUSH(((wiz_clo *)x)->args[i]); break;
    case WIZ_TAG_THUNK: { wiz_thunk *t = (wiz_thunk *)x; WIZ_PUSH(t->fn ? t->fn : t->val); break; }
    case WIZ_TAG_ARRAY: { wiz_array *a = (wiz_array *)x; for (size_t i = 0; i < a->len; i++) WIZ_PUSH(a->data[i]); break; }
    case WIZ_TAG_MAP: { wiz_map *m = (wiz_map *)x;
      for (size_t i = 0; i < m->cap; i++)
        if (m->keys[i]) { WIZ_PUSH(m->keys[i]); WIZ_PUSH(m->vals[i]); }
      break; }
    case WIZ_TAG_WMAP: { wiz_wmap *m = (wiz_wmap *)x;
      for (size_t i = 0; i < m->cap; i++) if (m->vals[i]) WIZ_PUSH(m->vals[i]);
      break; }
    case WIZ_TAG_ITAB: { wiz_itab *t = (wiz_itab *)x;
      for (size_t i = 0; i < t->count; i++) WIZ_PUSH(t->strs[i]);
      break; }
    case WIZ_TAG_BIG: case WIZ_TAG_RAW: case WIZ_TAG_EXT: case WIZ_TAG_BYTES: case WIZ_TAG_STR: case WIZ_TAG_WARRAY: break;
    default: for (uint32_t i = 0; i < h->size; i++) WIZ_PUSH(((wiz_ctor *)x)->fields[i]);
    }
  }
#undef WIZ_PUSH
  free(st);
}

/* The value of a closed top-level definition (a CAF), computed on its first use and
   kept for the rest of the run, immortal. The generated code reads `*slot` itself and
   calls this only while it is still 0 (no value is 0: scalars are odd). Threads may race
   to build it: the first to publish wins; a loser's copy stays immortal and unused. A
   definition that uses itself while it is being built builds itself again (as it did
   without the cache): it loops exactly when it looped before. */
WIZ_API wiz_val wiz_caf_init(wiz_val *slot, wiz_val (*build)(void)) {
  wiz_val v = __atomic_load_n(slot, __ATOMIC_ACQUIRE);
  if (!v) {
    wiz_val z = 0;
    v = build();
    wiz_immortal(v);
    if (!__atomic_compare_exchange_n(slot, &z, v, 0, __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE)) v = z;
  }
  wiz_inc(v); /* (nothing, unless the value was shared between threads already) */
  return v;
}

static void wiz_mark_mt(wiz_val v);
static pthread_mutex_t wiz_thunk_mu;
static pthread_once_t wiz_thunk_once = PTHREAD_ONCE_INIT;
static void wiz_thunk_mu_init(void) {
  pthread_mutexattr_t a;
  pthread_mutexattr_init(&a);
  pthread_mutexattr_settype(&a, PTHREAD_MUTEX_RECURSIVE);
  pthread_mutex_init(&wiz_thunk_mu, &a);
}
static void wiz_thunk_lock(void) { pthread_once(&wiz_thunk_once, wiz_thunk_mu_init); pthread_mutex_lock(&wiz_thunk_mu); }
static void wiz_thunk_unlock(void) { pthread_mutex_unlock(&wiz_thunk_mu); }

WIZ_API uint32_t wiz_tag(wiz_val v) {
  return WIZ_IS_SCALAR(v) ? (uint32_t)WIZ_UNBOX(v) : ((wiz_hdr *)v)->tag;
}
