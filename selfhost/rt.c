/* The runtime of the self-hosted backend (stages 21b, 21w): what `Backend.wiz` generates
   `#include`s. A value is a tagged word. A scalar (`BOX(n)`, low bit 1) is a number, a
   tag, or `◾`; anything else points to an object: a constructor (a tag and fields;
   payloads are nested pairs, `⟨0 a b⟩`), a closure, a suspension, a string (`Str`), an
   array or a map.

   The representation is `runtime/wiz.c`'s (stage 21w): scalar boxing, tag numbers, the
   `wiz_hdr` header and the object layouts below are shared, so a runtime leaf written for
   one runtime can serve the other. The self-hosted extensions — flat pair chains with
   field offsets, `T_HYP`, and 63-bit `Nat` — are marked as such.

   Two ways to manage memory. By default objects are collected by the Boehm garbage
   collector. A program generated in the backend's reference counting mode (stage 22)
   defines `WIZ_RC` first: every object then starts with a reference count, the generated
   code `inc`s and `dec`s precisely (Perceus), every function owns its arguments and
   returns an owned result, and the program checks at exit that every object was freed.
   The count rules (`rc > 0` owned, `rc < 0` shared, `rc == 0` immortal) are `wiz.c`'s. */

#include <stddef.h>
#ifndef WIZ_RC
#include <gc.h>
#endif
#include <sys/resource.h>
#include <unistd.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stddef.h>
#include <alloca.h>

/* ---- the shared value representation ----
   The same as `runtime/wiz.c` (and its header half `runtime/wiz_rt.h`, once the
   runtime split lands): scalar boxing, tag numbers, the object header and the layouts
   of constructors, closures, text, arrays, maps and foreign pointers. A value built by
   a self-hosted program and one built by the Lean toolchain then mean the same thing,
   so a runtime leaf can be moved from one to the other. The self-hosted extensions
   (kept out of the shared part) are listed after the layouts. */
typedef uintptr_t V;
#define BOX(n) ((((V)(n)) << 1) | 1)
#define ISBOX(v) (((v) & 1) != 0)
#define UNBOX(v) ((v) >> 1)

/* runtime/wiz.c's `WIZ_TAG_*`; `T_HYP` is the self-hosted compiler's own (the next
   free number, reserved here so it can be added to `wiz_rt.h` before values cross) */
enum { T_CLO = 0xFFFF0000u, T_BIG = 0xFFFF0001u, T_RAW = 0xFFFF0002u,
       T_EXT = 0xFFFF0003u, T_BYTES = 0xFFFF0004u, T_ARR = 0xFFFF0005u,
       T_STR = 0xFFFF0006u, T_MAP = 0xFFFF0007u, T_THUNK = 0xFFFF0008u,
       T_WARRAY = 0xFFFF0009u, T_WMAP = 0xFFFF000Au, T_ITAB = 0xFFFF000Bu };
enum { T_HYP = 0xFFFF000Cu }; /* self-hosted only: a suspension of `ind` */

/* runtime/wiz.c's `wiz_hdr`: the header of every object. `rc` is always present (the
   collector ignores it), so the layout does not depend on the memory mode. */
typedef struct { int64_t rc; uint32_t tag, size; } VHdr;
#define TAG(o) ((o)->h.tag)
#define SIZE(o) ((o)->h.size)
#define RC(o) ((o)->h.rc)

/* a constructor: `wiz_ctor` (`size` = number of fields) */
typedef struct { VHdr h; V f[]; } Obj;
/* a closure: `wiz_clo` (`size` = captured arguments, `arity` = all of them). `fn` gets
   the captured arguments followed by the applied ones, as one array. */
typedef V (*Fn)(V *a);
typedef struct { VHdr h; Fn fn; uint32_t arity; V env[]; } Clo;
/* a memoised suspension: `wiz_thunk` (`fn` is 0 once forced) */
typedef struct { VHdr h; V fn; V val; } Thunk;
/* a foreign pointer: `wiz_ext` */
typedef struct { VHdr h; void *ptr; void (*fin)(void *); } Ext;
/* UTF-8 text: `wiz_str` (`size` is 0, `len` the byte count) */
typedef struct { VHdr h; size_t len; char data[]; } Str;
/* an array of values: `wiz_array` */
typedef struct Arr { VHdr h; size_t len, cap; V *data; } Arr;
/* a hash map from text to values: `wiz_map` (open addressing, keys are `Str` objects,
   0 marks an empty slot) */
typedef struct Map { VHdr h; size_t count, cap; V *keys; V *vals; } Map;

/* the layouts above are `wiz_hdr`, `wiz_ctor`, `wiz_clo`, `wiz_thunk`, `wiz_ext`,
   `wiz_str`, `wiz_array` and `wiz_map`; these checks fail if one drifts */
_Static_assert(sizeof(VHdr) == 16 && offsetof(VHdr, tag) == 8 && offsetof(VHdr, size) == 12, "VHdr != wiz_hdr");
_Static_assert(sizeof(Obj) == 16 && offsetof(Obj, f) == 16, "Obj != wiz_ctor");
_Static_assert(sizeof(Clo) == 32 && offsetof(Clo, env) == 32, "Clo != wiz_clo");
_Static_assert(sizeof(Thunk) == 32, "Thunk != wiz_thunk");
_Static_assert(sizeof(Ext) == 32, "Ext != wiz_ext");
_Static_assert(sizeof(Str) == 24 && offsetof(Str, len) == 16, "Str != wiz_str");
_Static_assert(sizeof(Arr) == 40 && offsetof(Arr, len) == 16 && offsetof(Arr, data) == 32, "Arr != wiz_array");
_Static_assert(sizeof(Map) == 48 && offsetof(Map, count) == 16 && offsetof(Map, vals) == 40, "Map != wiz_map");

/* ---- self-hosted extensions (not in `runtime/wiz_rt.h`) ----
   * Constructor payloads: a value of `μ D i` is `(tag, fields…)`, a tag-0 object whose
     first field is the constructor tag (flat chains below), and a match reads
     `tagof(fld(x, 0))`. `runtime/wiz.c` uses flat constructors (tag = index).
   * Flat chains of pairs: `(e₀, (e₁, … (eₘ₋₁, t)))` is one object with tag 0 and
     fields `e₀ … eₘ₋₁ t` (a pair is the case m = 1). Its tail `(eᵢ, …)` is the same
     pointer with `i` in bits 1–3 (objects are 16-byte aligned; bit 0 marks a scalar),
     so taking the second component allocates nothing. A list cell is one object
     instead of three. (`runtime/wiz.c` has no offset chains; removing them is the
     next representation step, not this one.)
   * `T_HYP`, the suspension of `ind`.
   * 63-bit `Nat` scalars with wrapping arithmetic (the Lean runtime has 62-bit scalars
     and GMP objects; the self-hosted tests rely on `2^63 - 1`).
   * the Boehm mode (`WIZ_RC` off): its arrays are persistent (Baker), not `wiz_array`. */
#define OBJ(v) ((Obj *)((v) & ~(V)0xE))
#define OFF(v) ((unsigned)(((v) >> 1) & 7))

static V unreach(void) { fprintf(stderr, "wiz: unreachable\n"); exit(3); }
static void die(const char *m) { fprintf(stderr, "wiz: %s\n", m); exit(3); }

/* (`-DWIZ_STATS`: count allocations, reused cells and the peak of live objects, printed
   at exit under reference counting) */
#ifdef WIZ_STATS
static size_t rt_nalloc, rt_nreuse, rt_peak, rt_nobj, rt_nclo, rt_nfun, rt_nthunk, rt_nhyp, rt_nforced, rt_nfun0;
#define STAT(x) (x)
static size_t hypSlot(V m);
#define HYPT 8192
static uintptr_t hypKey[HYPT]; static size_t hypMade[HYPT], hypForced[HYPT];
#else
#define STAT(x) ((void)0)
#endif

#ifdef WIZ_RC
/* ---- reference counting ---- */

static size_t rt_live; /* objects allocated and not freed yet */
/* Small objects come from free lists, one per size class of 16 bytes (up to 256),
   carved from big blocks (malloc's per-object header and bookkeeping were 15% of a
   compiler's time); bigger ones from malloc. Blocks are never given back. */
#define RT_NCLS 16
static void *rt_fl[RT_NCLS + 1];
static char *rt_blk, *rt_blkEnd;
static void *rt_alloc(size_t sz) {
  size_t c = (sz + 15) >> 4;
  Obj *o;
  if (c <= RT_NCLS) {
    o = (Obj *)rt_fl[c];
    if (o) rt_fl[c] = *(void **)o;
    else {
      size_t b = c << 4;
      if (rt_blk + b > rt_blkEnd) {
        rt_blk = (char *)malloc(1 << 20);
        if (!rt_blk) die("out of memory");
        rt_blkEnd = rt_blk + (1 << 20);
      }
      o = (Obj *)rt_blk; rt_blk += b;
    }
  } else {
    o = (Obj *)malloc(sz);
    if (!o) die("out of memory");
  }
  o->h.rc = 1;
  rt_live++;
  STAT((rt_nalloc++, rt_live > rt_peak ? rt_peak = rt_live : 0));
  return o;
}
#define MALLOC_OBJ(sz) rt_alloc(sz)
#define MALLOC_BUF(sz) malloc(sz)
#define FREE_BUF(b) free(b)
static void rt_free(Obj *o);
/* the same count rules as `runtime/wiz.c`: rc > 0 belongs to one thread, rc < 0 is
   shared (atomic), rc == 0 is immortal. The self-hosted backend has no thread library,
   but the rules are kept so the representation is the same. */
static inline void inc(V v) {
  if (ISBOX(v)) return;
  VHdr *h = &OBJ(v)->h;
  int64_t rc = __atomic_load_n(&h->rc, __ATOMIC_RELAXED);
  if (rc > 0) h->rc = rc + 1;
  else if (rc < 0) __atomic_fetch_sub(&h->rc, 1, __ATOMIC_RELAXED);
}
static inline void dec(V v) {
  if (ISBOX(v)) return;
  Obj *o = OBJ(v);
  int64_t rc = __atomic_load_n(&o->h.rc, __ATOMIC_RELAXED);
  if (rc > 1) o->h.rc = rc - 1;
  else if (rc == 1) rt_free(o);
  else if (rc < 0 && __atomic_add_fetch(&o->h.rc, 1, __ATOMIC_ACQ_REL) == 0) rt_free(o);
}
#else
#define MALLOC_OBJ(sz) GC_MALLOC(sz)
#define MALLOC_BUF(sz) GC_MALLOC_ATOMIC(sz)
#define FREE_BUF(b) ((void)0)
#endif

/* (copies of a few words: inlined loops, not `memcpy` calls of a variable length,
   which were half of a compiler's time) */
#define INLINE static inline __attribute__((always_inline))
INLINE void copyV(V *d, const V *s, uint32_t n) { for (uint32_t i = 0; i < n; i++) d[i] = s[i]; }
INLINE V mkobj(uint32_t t, uint32_t n, V *fs) {
  STAT(rt_nobj++);
  Obj *o = (Obj *)MALLOC_OBJ(sizeof(Obj) + n * sizeof(V));
  if (!o) die("out of memory");
  o->h.rc = 1; o->h.tag = t; o->h.size = n;
  copyV(o->f, fs, n);
  return (V)o;
}
/* a closure of `n` captured values that takes one more argument (`ind`'s suspensions) */
INLINE V mkclo(Fn fn, uint32_t n, V *env) {
  STAT(rt_nclo++);
  Clo *c = (Clo *)MALLOC_OBJ(sizeof(Clo) + n * sizeof(V));
  if (!c) die("out of memory");
  c->h.rc = 1; c->h.tag = T_CLO; c->h.size = n; c->fn = fn; c->arity = n + 1;
  copyV(c->env, env, n);
  return (V)c;
}
/* a function closure (`runtime/wiz.c`'s `wiz_clo_new`): `arity` arguments in all, `n`
   captured, `fn` called with the whole array */
INLINE V mkfun(Fn f, uint32_t arity, uint32_t n, V *args) {
  STAT(rt_nfun++); STAT(rt_nfun0 += n == 0);
  Clo *c = (Clo *)MALLOC_OBJ(sizeof(Clo) + n * sizeof(V));
  if (!c) die("out of memory");
  c->h.rc = 1; c->h.tag = T_CLO; c->h.size = n; c->fn = f; c->arity = arity;
  copyV(c->env, args, n);
  return (V)c;
}
/* `f a₁ … aₙ`: the function is called once it has all its arguments (as
   `wiz_apply` in `runtime/wiz.c`). */
#ifndef WIZ_RC
static V apn(V f, uint32_t n, V *args) {
  uint32_t i = 0;
  while (i < n) {
    if (f == BOX(0)) return f; /* an erased function is `◾` and applies to `◾` */
    if (ISBOX(f)) die("applying a non-function");
    Obj *o = OBJ(f);
    if (TAG(o) == T_THUNK) {
      Thunk *t = (Thunk *)o;
      if (t->fn) { V g = t->fn; t->fn = 0; V u = BOX(0); t->val = apn(g, 1, &u); }
      f = t->val; i++;
      continue;
    }
    if (TAG(o) != T_CLO) die("applying a non-function");
    Clo *c = (Clo *)o;
    uint32_t have = SIZE(c), ar = c->arity, rem = ar - have;
    if (n - i < rem) {
      V *all = (V *)alloca((have + (n - i)) * sizeof(V));
      copyV(all, c->env, have);
      copyV(all + have, args + i, n - i);
      return mkfun(c->fn, ar, have + (n - i), all);
    }
    V *all = (V *)alloca(ar * sizeof(V));
    copyV(all, c->env, have);
    copyV(all + have, args + i, rem);
    f = c->fn(all);
    i += rem;
  }
  return f;
}
#else
/* `ap`/`apn` consume the function and its arguments. A unique closure's captured
   values move into the call; a shared or immortal one's are shared and its reference
   released. */
static void rt_freeShell(Obj *o);
static void takeArgs(Clo *c, V *to) {
  uint32_t have = SIZE(c);
  copyV(to, c->env, have);
  if (RC(c) == 1) rt_freeShell((Obj *)c);
  else { for (uint32_t j = 0; j < have; j++) inc(to[j]); dec((V)c); }
}
static V apn(V f, uint32_t n, V *args) {
  uint32_t i = 0;
  while (i < n) {
    if (f == BOX(0)) { for (; i < n; i++) dec(args[i]); return f; }
    if (ISBOX(f)) die("applying a non-function");
    Obj *o = OBJ(f);
    if (TAG(o) == T_THUNK) {
      Thunk *t = (Thunk *)o;
      if (t->fn) { V g = t->fn; t->fn = 0; V u = BOX(0); t->val = apn(g, 1, &u); }
      else dec(args[i]);
      V r = t->val; inc(r); dec(f); f = r; i++;
      continue;
    }
    if (TAG(o) != T_CLO) die("applying a non-function");
    Clo *c = (Clo *)o;
    Fn fn = c->fn;
    uint32_t have = SIZE(c), ar = c->arity, rem = ar - have;
    if (n - i < rem) {
      V *all = (V *)alloca((have + (n - i)) * sizeof(V));
      takeArgs(c, all);
      copyV(all + have, args + i, n - i);
      return mkfun(fn, ar, have + (n - i), all);
    }
    V *all = (V *)alloca(ar * sizeof(V));
    takeArgs(c, all);
    copyV(all + have, args + i, rem);
    f = fn(all);
    i += rem;
  }
  return f;
}
#endif
static V ap(V f, V a) { return apn(f, 1, &a); }
/* a field (of `◾`, an erased payload, `◾` again). A hypothesis of `ind` (`T_HYP`:
   `[suspension, rest, done]`) is computed when its field is first read. (Under
   reference counting the field is borrowed: the caller `inc`s it to keep it.) */
static V fld(V o, int i) {
  if (ISBOX(o)) return BOX(0);
  Obj *p = OBJ(o);
  if (TAG(p) == 0 && SIZE(p) >= 2) {
    unsigned off = OFF(o);
    if (i == 0) return p->f[off];
    if (off + 1 < SIZE(p) - 1) return (V)p | ((V)(off + 1) << 1);
    return p->f[SIZE(p) - 1];
  }
  if (TAG(p) == T_HYP && i == 0) {
    if (p->f[2] == BOX(0)) {
#ifdef WIZ_RC
      STAT(rt_nforced++); STAT(hypForced[hypSlot(p->f[0])]++);
#endif
      /* (a hypothesis being forced is `◾`: forcing it again fails rather than loops) */
      V s = p->f[0]; p->f[0] = BOX(0); p->f[0] = ap(s, BOX(0)); p->f[2] = BOX(1);
    }
    return p->f[0];
  }
  return (uint32_t)i < SIZE(p) ? p->f[i] : BOX(0);
}
static uint32_t tagof(V v) { return ISBOX(v) ? (uint32_t)UNBOX(v) : TAG(OBJ(v)); }
static V pair(V a, V b) { V fs[2] = {a, b}; return mkobj(0, 2, fs); }

/* ---- data the natives build: Bool, Prod, List, Char, String ---- */

#ifdef WIZ_RC
/* Static objects: the value of a constructor without fields, `(k, ◾)`, is the same every
   time; one per `k < 64` (Bools, `nil`, `none`, `0`'s payload…). They are immortal
   (`rc == 0`, as the constants of `runtime/wiz.c`) and are not counted as allocated. */
typedef struct { VHdr h; V f[2]; } __attribute__((aligned(16))) Nul;
#define RT_NNUL 64
static Nul rt_nul[RT_NNUL];
static void rt_nulInit(void) {
  for (uint32_t k = 0; k < RT_NNUL; k++) { rt_nul[k].h.rc = 0; rt_nul[k].h.tag = 0; rt_nul[k].h.size = 2; rt_nul[k].f[0] = BOX(k); rt_nul[k].f[1] = BOX(0); }
}
INLINE V nul(uint32_t k) { return (V)&rt_nul[k]; }
static V boolv(int b) { return nul(b ? 1 : 0); }
#else
static V boolv(int b) { return pair(BOX(b ? 1 : 0), BOX(0)); }
#endif
static V flat3(V a, V b, V t) { V fs[3] = {a, b, t}; return mkobj(0, 3, fs); }
static V flat4(V a, V b, V c, V t) { V fs[4] = {a, b, c, t}; return mkobj(0, 4, fs); }
/* `Prod.mk a b`: the payload `(tag 0, (a, (b, ◾)))` */
static V prodv(V a, V b) { return flat4(BOX(0), a, b, BOX(0)); }
static V nilv(void) {
#ifdef WIZ_RC
  return nul(0);
#else
  return pair(BOX(0), BOX(0));
#endif
}
static V consv(V h, V t) { return flat4(BOX(1), h, t, BOX(0)); }
static V charv(uint32_t c) { return flat3(BOX(0), BOX(c), BOX(0)); }
static V stringv(V list) { return flat3(BOX(0), list, BOX(0)); }

/* a Wiz string as UTF-8 (a new buffer; the string is only read) */
static char *cstr(V s) {
  size_t cap = 64, len = 0;
  char *buf = (char *)MALLOC_BUF(cap);
  V l = fld(fld(s, 1), 0);
  while (tagof(fld(l, 0)) == 1) {
    V rest = fld(l, 1);
    uint32_t c = (uint32_t)UNBOX(fld(fld(fld(rest, 0), 1), 0));
#ifndef WIZ_RC
    if (len + 5 > cap) { char *nb = (char *)GC_MALLOC_ATOMIC(cap * 2); memcpy(nb, buf, len); buf = nb; cap *= 2; }
#else
    if (len + 5 > cap) { buf = (char *)realloc(buf, cap * 2); if (!buf) die("out of memory"); cap *= 2; }
#endif
    if (c < 0x80) buf[len++] = (char)c;
    else if (c < 0x800) { buf[len++] = (char)(0xC0 | (c >> 6)); buf[len++] = (char)(0x80 | (c & 0x3F)); }
    else if (c < 0x10000) { buf[len++] = (char)(0xE0 | (c >> 12)); buf[len++] = (char)(0x80 | ((c >> 6) & 0x3F)); buf[len++] = (char)(0x80 | (c & 0x3F)); }
    else { buf[len++] = (char)(0xF0 | (c >> 18)); buf[len++] = (char)(0x80 | ((c >> 12) & 0x3F)); buf[len++] = (char)(0x80 | ((c >> 6) & 0x3F)); buf[len++] = (char)(0x80 | (c & 0x3F)); }
    l = fld(fld(rest, 1), 0);
  }
  buf[len] = 0;
  return buf;
}
/* UTF-8 text as a Wiz string */
static V wstr(const char *s, size_t n) {
  /* decode to code points, then build the list from the end */
  uint32_t *cps = (uint32_t *)MALLOC_BUF((n + 1) * sizeof(uint32_t));
  size_t k = 0;
  for (size_t i = 0; i < n;) {
    unsigned char b = (unsigned char)s[i];
    uint32_t c; int extra;
    if (b < 0x80) { c = b; extra = 0; } else if (b < 0xE0) { c = b & 0x1F; extra = 1; }
    else if (b < 0xF0) { c = b & 0x0F; extra = 2; } else { c = b & 0x07; extra = 3; }
    i++;
    for (int e = 0; e < extra && i < n; e++, i++) c = (c << 6) | ((unsigned char)s[i] & 0x3F);
    cps[k++] = c;
  }
  V l = nilv();
  while (k > 0) l = consv(charv(cps[--k]), l);
  FREE_BUF(cps);
  return stringv(l);
}

/* a string literal from its code points */
static V wcodes(const uint32_t *cps, size_t k) {
  V l = nilv();
  while (k > 0) l = consv(charv(cps[--k]), l);
  return stringv(l);
}

/* ---- primitives the erased code uses ---- */

static V p_unreachable(void) { return unreach(); }
static V p_natSucc(V n) { return BOX(UNBOX(n) + 1); }
/* a number's payload for a match: `(tag 0, ◾)` or `(tag 1, (n - 1, ◾))` */
static V p_natUnpack(V n) {
  uintptr_t k = UNBOX(n);
#ifdef WIZ_RC
  if (k == 0) return nul(0);
#endif
  return k == 0 ? pair(BOX(0), BOX(0)) : flat3(BOX(1), BOX(k - 1), BOX(0));
}
static V p_natPack(V p) {
  V r = tagof(fld(p, 0)) == 0 ? BOX(0) : BOX(UNBOX(fld(fld(p, 1), 0)) + 1);
#ifdef WIZ_RC
  dec(p);
#endif
  return r;
}

/* `ind D m i x`: `m i payload hyps`, the hypotheses computed by walking the description
   (`⟨0 i⟩` ret, `⟨1 ◾ F⟩` arg, `⟨2 j E⟩` rec, `⟨3 ◾ j E⟩` hrec) along the payload */
static V apn(V f, uint32_t n, V *args);
static V p_ind(V nat, V D, V m, V i, V x);
#ifndef WIZ_RC
static V hrecFn(V *a) { return p_ind(a[0], a[1], a[2], ap(a[3], a[5]), ap(a[4], a[5])); }
/* the hypothesis of a recursive field, suspended: `p_ind … j y` when first read (eager
   hypotheses made every structural function walk its whole argument) */
static V recFn(V *a) { return p_ind(a[0], a[1], a[2], a[3], a[4]); }
static V lazyHyp(V nat, V D, V m, V j, V y, V rest) {
  V env[5] = {nat, D, m, j, y};
  V fs[3] = {mkclo(recFn, 5, env), rest, BOX(0)};
  return mkobj(T_HYP, 3, fs);
}
static V hyps(V nat, V D, V m, V d, V pl) {
  switch (tagof(d)) {
  case 1: return hyps(nat, D, m, ap(fld(d, 1), fld(pl, 0)), fld(pl, 1));
  case 2: return lazyHyp(nat, D, m, fld(d, 0), fld(pl, 0), hyps(nat, D, m, fld(d, 1), fld(pl, 1)));
  case 3: { V env[5] = {nat, D, m, fld(d, 1), fld(pl, 0)};
    return pair(mkclo(hrecFn, 5, env), hyps(nat, D, m, fld(d, 2), fld(pl, 1))); }
  default: return BOX(0);
  }
}
static V p_ind(V nat, V D, V m, V i, V x) {
  V pl = UNBOX(nat) ? p_natUnpack(x) : x;
  V args[3] = {i, pl, hyps(nat, D, m, D, pl)};
  return apn(m, 3, args);
}
#else
#ifdef WIZ_STATS
/* (per method of `ind`: hypotheses created and forced, keyed by the method's code) */
static size_t hypSlot(V m) {
  uintptr_t k = 0;
  if (!ISBOX(m) && TAG(OBJ(m)) == T_CLO) { Clo *c = (Clo *)OBJ(m); k = (uintptr_t)c->fn; }
  size_t h = (size_t)((k >> 4) * 2654435761u) % HYPT;
  while (hypKey[h] && hypKey[h] != k) h = (h + 1) % HYPT;
  hypKey[h] = k ? k : 1;
  return h;
}
#endif
/* (the captured values are moved into the call, so they are owned here) */
static V hrecFn(V *a) {
  V h = a[5];
  inc(h);
  V j = ap(a[3], h);
  return p_ind(a[0], a[1], a[2], j, ap(a[4], h));
}
static V recFn(V *a) {
  return p_ind(a[0], a[1], a[2], a[3], a[4]);
}
/* (`D`, `m`, and the fields `j`, `y` are borrowed; `rest` is owned) */
static V lazyHyp(V nat, V D, V m, V j, V y, V rest) {
  inc(D); inc(m); inc(j); inc(y);
  V env[5] = {nat, D, m, j, y};
  V fs[3] = {mkclo(recFn, 5, env), rest, BOX(0)};
  STAT(rt_nhyp++); STAT(hypMade[hypSlot(m)]++);
  return mkobj(T_HYP, 3, fs);
}
/* (`D`, `m`, `d`, `pl` borrowed) */
static V hyps(V nat, V D, V m, V d, V pl) {
  switch (tagof(d)) {
  case 1: {
    V F = fld(d, 1), a = fld(pl, 0);
    inc(F); inc(a);
    V d2 = ap(F, a);
    V r = hyps(nat, D, m, d2, fld(pl, 1));
    dec(d2);
    return r;
  }
  case 2: return lazyHyp(nat, D, m, fld(d, 0), fld(pl, 0), hyps(nat, D, m, fld(d, 1), fld(pl, 1)));
  case 3: { V env[5] = {nat, D, m, fld(d, 1), fld(pl, 0)};
    inc(D); inc(m); inc(env[3]); inc(env[4]);
    V c = mkclo(hrecFn, 5, env);
    return pair(c, hyps(nat, D, m, fld(d, 2), fld(pl, 1))); }
  default: return BOX(0);
  }
}
static V p_ind(V nat, V D, V m, V i, V x) {
  V pl = UNBOX(nat) ? p_natUnpack(x) : x;
  V h = hyps(nat, D, m, D, pl);
  dec(D);
  V args[3] = {i, pl, h};
  return apn(m, 3, args);
}
/* Unmemoised hypotheses (`indv`, see Backend.wiz): the method gets a view
   `[nat, D, m, payload]` instead of the chain, and reads the `j`-th hypothesis with
   `p_hypAt`, computed there (the backend uses this only for methods that read each at
   most once on a path, or whose result is a function) */
static V p_indv(V nat, V D, V m, V i, V x) {
  V pl = UNBOX(nat) ? p_natUnpack(x) : x;
  inc(m); inc(pl);
  V vw = mkobj(0, 4, (V[]){nat, D, m, pl});
  V args[3] = {i, pl, vw};
  return apn(m, 3, args);
}
static V hrecFnV(V *a) {
  V h = a[5];
  inc(h);
  V j = ap(a[3], h);
  return p_indv(a[0], a[1], a[2], j, ap(a[4], h));
}
/* (the view is owned and released; the description is walked along the payload as
   `hyps` does, keeping the descriptions it computes alive until the end) */
static V p_hypAt(V vw, V jj) {
  Obj *o = OBJ(vw);
  V nat = o->f[0], D = o->f[1], m = o->f[2], p = o->f[3], d = D, own = BOX(0), r = BOX(0);
  uintptr_t k = UNBOX(jj);
  for (;;) {
    switch (tagof(d)) {
    case 1: {
      V F = fld(d, 1), a = fld(p, 0);
      inc(F); inc(a);
      V d2 = ap(F, a);
      dec(own); own = d2; d = d2; p = fld(p, 1);
      continue;
    }
    case 2:
      if (k == 0) {
        V j = fld(d, 0), y = fld(p, 0);
        inc(D); inc(m); inc(j); inc(y);
        r = p_indv(nat, D, m, j, y);
        goto done;
      }
      k--; d = fld(d, 1); p = fld(p, 1);
      continue;
    case 3:
      if (k == 0) {
        V env[5] = {nat, D, m, fld(d, 1), fld(p, 0)};
        inc(D); inc(m); inc(env[3]); inc(env[4]);
        r = mkclo(hrecFnV, 5, env);
        goto done;
      }
      k--; d = fld(d, 2); p = fld(p, 1);
      continue;
    default:
      r = unreach();
      goto done;
    }
  }
done:
  dec(own);
  dec(vw);
  return r;
}
#endif

/* ---- natives: curried functions of `n` arguments ---- */

typedef Fn NF;
static V native(NF f, int arity) { return mkfun(f, (uint32_t)arity, 0, NULL); }
#ifndef WIZ_RC
#define NATIVE(name, arity, ...) \
  static V nf_##name(V *a) { __VA_ARGS__ } \
  V get_##name(void) { static V c = 0; if (!c) c = native(nf_##name, arity); return c; }
#else
/* the constants a program keeps (globals, string literals, natives' closures), released
   at exit before the check for leaks */
static V **rt_roots; static size_t rt_nroots, rt_caproots;
static void rt_root(V *p) {
  if (rt_nroots == rt_caproots) {
    rt_caproots = rt_caproots ? 2 * rt_caproots : 256;
    rt_roots = (V **)realloc(rt_roots, rt_caproots * sizeof(V *));
    if (!rt_roots) die("out of memory");
  }
  rt_roots[rt_nroots++] = p;
}
#define NATIVE(name, arity, ...) \
  static V nf_##name(V *a) { __VA_ARGS__ } \
  V get_##name(void) { static V c = 0; if (!c) { c = native(nf_##name, arity); rt_root(&c); } inc(c); return c; }
#endif

V get_Nat_46_zero(void) { return BOX(0); }
NATIVE(Nat_46_succ, 1, return BOX(UNBOX(a[0]) + 1);)
NATIVE(Nat_46_pred, 1, return UNBOX(a[0]) ? BOX(UNBOX(a[0]) - 1) : BOX(0);)
NATIVE(Nat_46_add, 2, return BOX(UNBOX(a[0]) + UNBOX(a[1]));)
NATIVE(Nat_46_sub, 2, return UNBOX(a[0]) > UNBOX(a[1]) ? BOX(UNBOX(a[0]) - UNBOX(a[1])) : BOX(0);)
NATIVE(Nat_46_mul, 2, return BOX(UNBOX(a[0]) * UNBOX(a[1]));)
NATIVE(Nat_46_beq, 2, return boolv(UNBOX(a[0]) == UNBOX(a[1]));)
NATIVE(Nat_46_blt, 2, return boolv(UNBOX(a[0]) < UNBOX(a[1]));)
NATIVE(Nat_46_lt, 2, return boolv(UNBOX(a[0]) < UNBOX(a[1]));)
NATIVE(Nat_46_le, 2, return boolv(UNBOX(a[0]) <= UNBOX(a[1]));)
/* as the Prelude defines them: n / 0 = 0, n % 0 = n, log2 0 = 0 (words wrap, as in `mul`) */
NATIVE(Nat_46_div, 2, return BOX(UNBOX(a[1]) ? UNBOX(a[0]) / UNBOX(a[1]) : 0);)
NATIVE(Nat_46_mod, 2, return BOX(UNBOX(a[1]) ? UNBOX(a[0]) % UNBOX(a[1]) : UNBOX(a[0]));)
NATIVE(Nat_46_pow, 2, uintptr_t r = 1, b = UNBOX(a[0]); for (uintptr_t e = UNBOX(a[1]); e; e >>= 1, b *= b) if (e & 1) r *= b; return BOX(r);)
NATIVE(Nat_46_land, 2, return BOX(UNBOX(a[0]) & UNBOX(a[1]));)
NATIVE(Nat_46_lor, 2, return BOX(UNBOX(a[0]) | UNBOX(a[1]));)
NATIVE(Nat_46_xor, 2, return BOX(UNBOX(a[0]) ^ UNBOX(a[1]));)
NATIVE(Nat_46_shiftLeft, 2, return BOX(UNBOX(a[1]) >= 64 ? 0 : UNBOX(a[0]) << UNBOX(a[1]));)
NATIVE(Nat_46_shiftRight, 2, return BOX(UNBOX(a[1]) >= 64 ? 0 : UNBOX(a[0]) >> UNBOX(a[1]));)
NATIVE(Nat_46_log2, 1, uintptr_t x = UNBOX(a[0]); return BOX(x ? 63 - __builtin_clzll((unsigned long long)x) : 0);)
NATIVE(Nat_46_toString, 1, char b[32]; int n = snprintf(b, sizeof b, "%lu", (unsigned long)UNBOX(a[0])); return wstr(b, (size_t)n);)
/* the program's arguments, without its name (stage 21k; `rt_start` saves them) */
static int rt_argc; static char **rt_argv;
NATIVE(IO_46_argCount, 1, return prodv(BOX((uintptr_t)(rt_argc > 1 ? rt_argc - 1 : 0)), a[0]);)
NATIVE(IO_46_arg, 2,
  uintptr_t i = UNBOX(a[0]);
  const char *s = i + 1 < (uintptr_t)rt_argc ? rt_argv[i + 1] : "";
  return prodv(wstr(s, strlen(s)), a[1]);)
/* end the program with an exit code (as `Process.exit` of lib/Sys.wiz: no leak check) */
NATIVE(Process_46_exit, 2, fflush(stdout); exit((int)UNBOX(a[0])); return a[1];)
#ifndef WIZ_RC
/* IO: `String → World → Prod Unit World` */
NATIVE(IO_46_println, 2, puts(cstr(a[0])); return prodv(BOX(0), a[1]);)
NATIVE(IO_46_print, 2, fputs(cstr(a[0]), stdout); return prodv(BOX(0), a[1]);)
NATIVE(IO_46_ePrintln, 2, fflush(stdout); fprintf(stderr, "%s\n", cstr(a[0])); return prodv(BOX(0), a[1]);)
NATIVE(IO_46_readFile, 2,
  FILE *f = fopen(cstr(a[0]), "rb");
  if (!f) return prodv(wstr("", 0), a[1]);
  size_t cap = 4096, len = 0; char *buf = (char *)GC_MALLOC_ATOMIC(cap);
  for (size_t r; (r = fread(buf + len, 1, cap - len, f)) > 0;) {
    len += r;
    if (len == cap) { char *nb = (char *)GC_MALLOC_ATOMIC(cap * 2); memcpy(nb, buf, len); buf = nb; cap *= 2; }
  }
  fclose(f);
  return prodv(wstr(buf, len), a[1]);)
#else
NATIVE(IO_46_println, 2, char *s = cstr(a[0]); dec(a[0]); puts(s); free(s); return prodv(BOX(0), a[1]);)
NATIVE(IO_46_print, 2, char *s = cstr(a[0]); dec(a[0]); fputs(s, stdout); free(s); return prodv(BOX(0), a[1]);)
NATIVE(IO_46_ePrintln, 2, char *s = cstr(a[0]); dec(a[0]); fflush(stdout); fprintf(stderr, "%s\n", s); free(s); return prodv(BOX(0), a[1]);)
NATIVE(IO_46_readFile, 2,
  char *p = cstr(a[0]); dec(a[0]);
  FILE *f = fopen(p, "rb");
  free(p);
  if (!f) return prodv(wstr("", 0), a[1]);
  size_t cap = 4096, len = 0; char *buf = (char *)malloc(cap);
  for (size_t r; (r = fread(buf + len, 1, cap - len, f)) > 0;) {
    len += r;
    if (len == cap) { buf = (char *)realloc(buf, cap * 2); if (!buf) die("out of memory"); cap *= 2; }
  }
  fclose(f);
  V s = wstr(buf, len);
  free(buf);
  return prodv(s, a[1]);)
#endif

/* `memo f` and the backend's suspended `let`s: a `T_THUNK` (`wiz_thunk`), forced by
   `apn`. `fn` is the suspension (0 once forced), `val` its value — the same object and
   protocol as `runtime/wiz.c`. */
static V mkthunk_val(V f) {
  STAT(rt_nthunk++);
  Thunk *t = (Thunk *)MALLOC_OBJ(sizeof(Thunk));
  if (!t) die("out of memory");
  t->h.rc = 1; t->h.tag = T_THUNK; t->h.size = 0;
  t->fn = f; t->val = BOX(0);
  return (V)t;
}
static V p_memo(V f) { return mkthunk_val(f); }
/* a suspended `let`: the code (a function of the captured variables and the unit) as a
   closure, then a thunk over it */
INLINE V mkthunk(NF f, uint32_t nc, V *caps) {
  return mkthunk_val(mkfun(f, nc + 1, nc, caps));
}
NATIVE(memo, 2, return mkthunk_val(a[1]);)

/* `Str`: immutable UTF-8 text (`wiz_str`: `size` is 0, `len` the byte count) */
static V mkstr(const char *s) {
  size_t n = strlen(s);
#ifndef WIZ_RC
  Str *t = (Str *)GC_MALLOC_ATOMIC(sizeof(Str) + n + 1);
#else
  Str *t = (Str *)rt_alloc(sizeof(Str) + n + 1);
#endif
  t->h.rc = 1; t->h.tag = T_STR; t->h.size = 0; t->len = n;
  memcpy(t->data, s, n + 1);
  return (V)t;
}
#ifndef WIZ_RC
NATIVE(Str_46_ofString, 1, return mkstr(cstr(a[0]));)
#else
NATIVE(Str_46_ofString, 1, char *s = cstr(a[0]); dec(a[0]); V r = mkstr(s); free(s); return r;)
#endif

#ifndef WIZ_RC
/* Arrays: persistent, Baker's trick. The newest version holds the vector; an older one
   is a difference from a newer one, and is made the holder again when it is used. */
typedef struct BArr {
  VHdr h;
  uint32_t kind; /* 0: holds the vector; 1: `next` with element `idx` set to `val`;
                    2: `next` cut to length `idx`; 3: `next` extended by `saved` */
  V *data; size_t len, cap;
  size_t idx; V val; struct BArr *next;
  V *saved; size_t nsaved;
} BArr;
static BArr *arrNode(void) { BArr *a = (BArr *)GC_MALLOC(sizeof(BArr)); a->h.rc = 1; a->h.tag = T_ARR; a->h.size = 0; return a; }
/* make `a` hold the vector, turning the holder into the inverse difference */
static void reroot(BArr *a) {
  if (a->kind == 0) return;
  reroot(a->next);
  BArr *n = a->next;
  if (a->kind == 1) {
    V old = n->data[a->idx];
    n->data[a->idx] = a->val;
    n->kind = 1; n->idx = a->idx; n->val = old;
    a->len = n->len;
  } else if (a->kind == 2) {
    size_t k = n->len - a->idx;
    V *sv = (V *)GC_MALLOC(k * sizeof(V) + sizeof(V));
    memcpy(sv, n->data + a->idx, k * sizeof(V));
    n->kind = 3; n->saved = sv; n->nsaved = k;
    a->len = a->idx;
  } else {
    size_t need = n->len + a->nsaved;
    if (need > n->cap) {
      size_t cap = n->cap ? n->cap : 8;
      while (cap < need) cap *= 2;
      V *nd = (V *)GC_MALLOC(cap * sizeof(V));
      memcpy(nd, n->data, n->len * sizeof(V));
      n->data = nd; n->cap = cap;
    }
    memcpy(n->data + n->len, a->saved, a->nsaved * sizeof(V));
    n->kind = 2; n->idx = n->len;
    a->len = need;
  }
  a->data = n->data; a->cap = n->cap; a->kind = 0;
  n->next = a;
}
static BArr *arrAt(V v) { BArr *a = (BArr *)v; reroot(a); return a; }
NATIVE(Array_46_empty, 1, BArr *r = arrNode(); r->kind = 0; return (V)r;)
NATIVE(Array_46_size, 2, return BOX(arrAt(a[1])->len);)
NATIVE(Array_46_getD, 4, BArr *r = arrAt(a[1]); uintptr_t i = UNBOX(a[2]); return i < r->len ? r->data[i] : a[3];)
NATIVE(Array_46_push, 3,
  BArr *r = arrAt(a[1]);
  if (r->len == r->cap) {
    size_t cap = r->cap ? 2 * r->cap : 8;
    V *nd = (V *)GC_MALLOC(cap * sizeof(V));
    memcpy(nd, r->data, r->len * sizeof(V));
    r->data = nd; r->cap = cap;
  }
  r->data[r->len] = a[2];
  BArr *n = arrNode(); n->kind = 0; n->data = r->data; n->len = r->len + 1; n->cap = r->cap;
  r->kind = 2; r->idx = r->len; r->next = n;
  return (V)n;)
NATIVE(Array_46_set, 4,
  BArr *r = arrAt(a[1]); uintptr_t i = UNBOX(a[2]);
  if (i >= r->len) return a[1];
  V old = r->data[i];
  r->data[i] = a[3];
  BArr *n = arrNode(); n->kind = 0; n->data = r->data; n->len = r->len; n->cap = r->cap;
  r->kind = 1; r->idx = i; r->val = old; r->next = n;
  return (V)n;)
#else
/* Arrays under reference counting: updated in place when unique, else copied (as in
   Lean). Baker's versions point from old to new, so an array stored in its own
   successor would be a cycle; and the count already tells when an update can be in
   place. */
typedef struct Arr Arr;
static Arr *arrNew(size_t cap) {
  Arr *r = (Arr *)rt_alloc(sizeof(Arr));
  r->h.rc = 1; r->h.tag = T_ARR; r->h.size = 0;
  r->len = 0; r->cap = cap;
  r->data = cap ? (V *)malloc(cap * sizeof(V)) : NULL;
  if (cap && !r->data) die("out of memory");
  return r;
}
/* an array to update: `v` itself if unique, else a copy (and `v` released) */
static Arr *arrMut(V v, size_t extra) {
  Arr *a = (Arr *)v;
  if (RC(a) == 1) return a;
  Arr *r = arrNew(a->len + extra);
  memcpy(r->data, a->data, a->len * sizeof(V));
  r->len = a->len;
  for (size_t i = 0; i < r->len; i++) inc(r->data[i]);
  dec(v);
  return r;
}
NATIVE(Array_46_empty, 1, return (V)arrNew(0);)
NATIVE(Array_46_size, 2, V n = BOX(((Arr *)a[1])->len); dec(a[1]); return n;)
NATIVE(Array_46_getD, 4,
  Arr *r = (Arr *)a[1]; uintptr_t i = UNBOX(a[2]);
  if (i < r->len) { V x = r->data[i]; inc(x); dec(a[1]); dec(a[3]); return x; }
  dec(a[1]); return a[3];)
NATIVE(Array_46_push, 3,
  Arr *r = arrMut(a[1], 1);
  if (r->len == r->cap) {
    size_t cap = r->cap ? 2 * r->cap : 8;
    r->data = (V *)realloc(r->data, cap * sizeof(V));
    if (!r->data) die("out of memory");
    r->cap = cap;
  }
  r->data[r->len++] = a[2];
  return (V)r;)
NATIVE(Array_46_set, 4,
  uintptr_t i = UNBOX(a[2]);
  if (i >= ((Arr *)a[1])->len) { dec(a[3]); return a[1]; }
  Arr *r = arrMut(a[1], 0);
  dec(r->data[i]);
  r->data[i] = a[3];
  return (V)r;)
#endif

#ifndef WIZ_RC
/* StrMap: a persistent treap on the keys' text (priorities from a hash) */
typedef struct Node { VHdr h; uint32_t pri; const char *key; V val; struct Node *l, *r; } Node;
static uint32_t hashs(const char *s) { uint32_t h = 2166136261u; for (; *s; s++) h = (h ^ (unsigned char)*s) * 16777619u; return h; }
static Node *mk(const char *k, uint32_t p, V v, Node *l, Node *r) {
  Node *n = (Node *)GC_MALLOC(sizeof(Node));
  n->h.rc = 1; n->h.tag = T_MAP; n->h.size = 0; n->pri = p; n->key = k; n->val = v; n->l = l; n->r = r;
  return n;
}
static Node *rotR(Node *n) { Node *l = n->l; return mk(l->key, l->pri, l->val, l->l, mk(n->key, n->pri, n->val, l->r, n->r)); }
static Node *rotL(Node *n) { Node *r = n->r; return mk(r->key, r->pri, r->val, mk(n->key, n->pri, n->val, n->l, r->l), r->r); }
static Node *ins(Node *n, const char *k, uint32_t p, V v) {
  if (!n) return mk(k, p, v, NULL, NULL);
  int c = strcmp(k, n->key);
  if (c == 0) return mk(n->key, n->pri, v, n->l, n->r);
  if (c < 0) { Node *m = mk(n->key, n->pri, n->val, ins(n->l, k, p, v), n->r); return m->l->pri > m->pri ? rotR(m) : m; }
  Node *m = mk(n->key, n->pri, n->val, n->l, ins(n->r, k, p, v));
  return m->r->pri > m->pri ? rotL(m) : m;
}
static size_t count(Node *n) { return n ? 1 + count(n->l) + count(n->r) : 0; }
/* a map is `◾` (empty) or a node */
static Node *mapOf(V v) { return ISBOX(v) ? NULL : (Node *)v; }
NATIVE(StrMap_46_empty, 1, return BOX(0);)
NATIVE(StrMap_46_insert, 4, const char *k = ((Str *)a[2])->data; return (V)ins(mapOf(a[1]), k, hashs(k), a[3]);)
NATIVE(StrMap_46_findD, 4,
  const char *k = ((Str *)a[2])->data;
  for (Node *n = mapOf(a[1]); n;) { int c = strcmp(k, n->key); if (c == 0) return n->val; n = c < 0 ? n->l : n->r; }
  return a[3];)
NATIVE(StrMap_46_size, 2, return BOX(count(mapOf(a[1])));)
#else
/* StrMap under reference counting: `wiz_map` as in `runtime/wiz.c` (open addressing,
   updated in place when unique, else copied) */
static uint64_t strhash(Str *t) {
  uint64_t h = 1469598103934665603ULL;
  for (size_t i = 0; i < t->len; i++) { h ^= (unsigned char)t->data[i]; h *= 1099511628211ULL; }
  return h;
}
static int strsame(Str *x, Str *y) { return x->len == y->len && memcmp(x->data, y->data, x->len) == 0; }
static Map *mapNew(size_t cap) {
  Map *m = (Map *)rt_alloc(sizeof(Map));
  m->h.rc = 1; m->h.tag = T_MAP; m->h.size = 0;
  m->count = 0; m->cap = cap;
  m->keys = (V *)calloc(cap, sizeof(V));
  m->vals = (V *)calloc(cap, sizeof(V));
  if (!m->keys || !m->vals) die("out of memory");
  return m;
}
static void mapPut(Map *m, V k, V x) {
  size_t i = strhash((Str *)k) & (m->cap - 1);
  while (m->keys[i] && !strsame((Str *)m->keys[i], (Str *)k)) i = (i + 1) & (m->cap - 1);
  if (m->keys[i]) { dec(m->keys[i]); dec(m->vals[i]); } else m->count++;
  m->keys[i] = k; m->vals[i] = x;
}
static Map *mapUnique(V v) {
  Map *m = (Map *)v;
  if (RC(m) == 1) return m;
  Map *c = mapNew(m->cap);
  c->count = m->count;
  for (size_t i = 0; i < m->cap; i++)
    if (m->keys[i]) { c->keys[i] = m->keys[i]; c->vals[i] = m->vals[i]; inc(m->keys[i]); inc(m->vals[i]); }
  dec(v);
  return c;
}
NATIVE(StrMap_46_empty, 1, return (V)mapNew(8);)
NATIVE(StrMap_46_insert, 4,
  Map *m = mapUnique(a[1]);
  if (2 * (m->count + 1) > m->cap) {
    size_t oc = m->cap;
    V *ok = m->keys, *ov = m->vals;
    m->cap *= 2; m->count = 0;
    m->keys = (V *)calloc(m->cap, sizeof(V));
    m->vals = (V *)calloc(m->cap, sizeof(V));
    if (!m->keys || !m->vals) die("out of memory");
    for (size_t i = 0; i < oc; i++) if (ok[i]) mapPut(m, ok[i], ov[i]);
    free(ok); free(ov);
  }
  mapPut(m, a[2], a[3]);
  return (V)m;)
NATIVE(StrMap_46_findD, 4,
  Map *m = (Map *)a[1];
  size_t i = strhash((Str *)a[2]) & (m->cap - 1);
  V r = a[3];
  while (m->keys[i]) {
    if (strsame((Str *)m->keys[i], (Str *)a[2])) { r = m->vals[i]; inc(r); dec(a[3]); break; }
    i = (i + 1) & (m->cap - 1);
  }
  dec(a[1]); dec(a[2]);
  return r;)
NATIVE(StrMap_46_size, 2, V n = BOX(((Map *)a[1])->count); dec(a[1]); return n;)
#endif

#ifdef WIZ_RC
/* ---- freeing: a worklist, not recursion (a list a million long is no deeper) ---- */

static Obj **rt_work; static size_t rt_nwork, rt_capwork;
static void rt_push(Obj *o) {
  if (rt_nwork == rt_capwork) {
    rt_capwork = rt_capwork ? 2 * rt_capwork : 1024;
    rt_work = (Obj **)realloc(rt_work, rt_capwork * sizeof(Obj *));
    if (!rt_work) die("out of memory");
  }
  rt_work[rt_nwork++] = o;
}
static inline void rt_decChild(V v) {
  if (!v || ISBOX(v)) return;
  Obj *o = OBJ(v);
  int64_t rc = __atomic_load_n(&o->h.rc, __ATOMIC_RELAXED);
  if (rc > 1) o->h.rc = rc - 1;
  else if (rc == 1) rt_push(o);
  else if (rc < 0 && __atomic_add_fetch(&o->h.rc, 1, __ATOMIC_ACQ_REL) == 0) rt_push(o);
}
/* an object's size, as allocated */
static size_t rt_size(Obj *o) {
  switch (TAG(o)) {
  case T_CLO: return sizeof(Clo) + SIZE(o) * sizeof(V);
  case T_THUNK: return sizeof(Thunk);
  case T_EXT: return sizeof(Ext);
  case T_STR: return sizeof(Str) + ((Str *)o)->len + 1;
  case T_ARR: return sizeof(Arr);
  case T_MAP: return sizeof(Map);
  default: return sizeof(Obj) + SIZE(o) * sizeof(V);
  }
}
static void rt_freeShell(Obj *o) {
  size_t c = (rt_size(o) + 15) >> 4;
  if (c <= RT_NCLS) { *(void **)o = rt_fl[c]; rt_fl[c] = o; } else free(o);
  rt_live--;
}
static int rt_freeing;
static void rt_drain(void);
static void rt_free(Obj *o) {
  rt_push(o);
  rt_drain();
}
static void rt_drain(void) {
  if (rt_freeing) return;
  rt_freeing = 1;
  while (rt_nwork) {
    Obj *x = rt_work[--rt_nwork];
    uint32_t t = TAG(x);
    if (t < T_CLO || t == T_HYP) { for (uint32_t i = 0; i < SIZE(x); i++) rt_decChild(x->f[i]); }
    else if (t == T_CLO) {
      Clo *c = (Clo *)x;
      for (uint32_t i = 0; i < SIZE(c); i++) rt_decChild(c->env[i]);
    } else if (t == T_THUNK) {
      Thunk *th = (Thunk *)x;
      rt_decChild(th->fn ? th->fn : th->val);
    } else if (t == T_ARR) {
      Arr *a = (Arr *)x;
      for (size_t i = 0; i < a->len; i++) rt_decChild(a->data[i]);
      free(a->data);
    } else if (t == T_MAP) {
      Map *m = (Map *)x;
      for (size_t i = 0; i < m->cap; i++) if (m->keys[i]) { rt_decChild(m->keys[i]); rt_decChild(m->vals[i]); }
      free(m->keys); free(m->vals);
    } else if (t == T_EXT) {
      /* a foreign pointer: its finalizer runs with the last reference */
      Ext *e = (Ext *)x;
      if (e->ptr && e->fin) e->fin(e->ptr);
    }
    rt_freeShell(x);
  }
  rt_freeing = 0;
}
/* ---- reuse (Perceus' reuse tokens) and drop specialisation ---- */

/* the size class of a constructor of `n` fields (0: too big for reuse) */
static inline size_t rt_cls(uint32_t n) { size_t c = (sizeof(Obj) + n * sizeof(V) + 15) >> 4; return c <= RT_NCLS ? c : 0; }
/* `x` dies, and an allocation of `n` fields follows: if `x` is a unique constructor
   (offset 0) of the same size class, its fields are released and its cell is the token,
   else `x` is released and the token is 0 */
static V reset(V x, uint32_t n) {
  if (ISBOX(x)) return 0;
  Obj *o = OBJ(x);
  if (RC(o) == 1 && OFF(x) == 0 && TAG(o) < T_CLO && rt_cls(SIZE(o)) == rt_cls(n) && rt_cls(n)) {
    for (uint32_t i = 0; i < SIZE(o); i++) rt_decChild(o->f[i]);
    rt_drain();
    return x;
  }
  dec(x);
  return 0;
}
/* a constructor in the token's cell, or a new one */
INLINE V reuseobj(V w, uint32_t t, uint32_t n, V *fs) {
  if (!w) return mkobj(t, n, fs);
  Obj *o = (Obj *)w;
  o->h.tag = t; o->h.size = n;
  copyV(o->f, fs, n);
  STAT(rt_nreuse++);
  return w;
}
/* `x` dies at its projection `r` (borrowed): a unique `x` gives its reference to `r`
   (if `r` is one of its fields) and releases the others; its cell is kept as the token
   when `n` (> 0) fits; otherwise `r` is `inc`ed and `x` released. (`r` is a field of `x`,
   or a part of one, or a tail of `x`'s own chain.) */
static V resetTakeU(V x, uint32_t n, V r) {
  Obj *o = OBJ(x);
  uint32_t k = SIZE(o);
  if (!ISBOX(r)) { for (k = 0; k < SIZE(o) && o->f[k] != r; k++) {} if (k == SIZE(o)) inc(r); }
  for (uint32_t i = 0; i < SIZE(o); i++) if (i != k) rt_decChild(o->f[i]);
  if (n && OFF(x) == 0 && rt_cls(SIZE(o)) == rt_cls(n) && rt_cls(n)) { rt_drain(); return x; }
  rt_freeShell(o);
  rt_drain();
  return 0;
}
INLINE V resetTake(V x, uint32_t n, V r) {
  if (ISBOX(x)) return 0;
  Obj *o = OBJ(x);
  if (OBJ(r) == o && !ISBOX(r)) return 0; /* (a tail of `x`'s chain: `x`'s reference is `r`'s) */
  if (RC(o) != 1 || TAG(o) >= T_CLO) { inc(r); dec(x); return 0; }
  return resetTakeU(x, n, r);
}
INLINE void dropTake(V x, V r) { (void)resetTake(x, 0, r); }

/* at exit: release the constants; then every object must have been freed */
static void rt_finish(void) {
  for (size_t i = rt_nroots; i > 0; i--) dec(*rt_roots[i - 1]);
#ifdef WIZ_STATS
  fprintf(stderr, "wiz stats: %zu allocations, %zu reused, peak %zu live (mkobj %zu, mkclo %zu, mkfun %zu, mkthunk %zu; hypotheses %zu, forced %zu; capture-free mkfun %zu)\n",
          rt_nalloc, rt_nreuse, rt_peak, rt_nobj, rt_nclo, rt_nfun, rt_nthunk, rt_nhyp, rt_nforced, rt_nfun0);
  fprintf(stderr, "wiz hyp base rt_finish %p\n", (void *)rt_finish);
  for (size_t i = 0; i < HYPT; i++) if (hypMade[i] > 1000000) fprintf(stderr, "wiz hyp %p: %zu made, %zu forced\n", (void *)hypKey[i], hypMade[i], hypForced[i]);
#endif
  if (rt_live) { fflush(stdout); fprintf(stderr, "wiz: %zu objects leaked\n", rt_live); exit(4); }
}
#endif

/* ---- the C FFI (stage 21l): what the wrappers of `extern` functions call ----
   The wrappers own their arguments (`rt_drop` releases one under reference counting).
   `Nat` is a scalar of 63 bits (a bigger C result is cut to them); `UInt64` and
   `Float64` (its bits) are scalars when the top bit is clear, else a `T_RAW` object; a
   foreign pointer is a `T_EXT` object whose finalizer runs when it is freed (under the
   collector: when it is collected; `rt_finishGC` collects once more at exit). */
INLINE void rt_drop(V v) {
#ifdef WIZ_RC
  dec(v);
#else
  (void)v;
#endif
}
/* (21r) another reference (a field read from a borrowed structure, then converted) */
INLINE void rt_dup(V v) {
#ifdef WIZ_RC
  inc(v);
#else
  (void)v;
#endif
}
static uint64_t rt_in_nat(V v) { return ISBOX(v) ? (uint64_t)UNBOX(v) : 0; }
/* (21p) a `Nat` here is 63 bits: a C number that doesn't fit is an error, not cut */
static V rt_out_nat(uint64_t n) {
  if (n >> 63) die("a foreign function's Nat does not fit in 63 bits (the self-hosted runtime's Nat)");
  return BOX(n);
}
static uint64_t rt_in_u64(V v) {
  if (ISBOX(v)) return (uint64_t)UNBOX(v);
  uint64_t b = (uint64_t)OBJ(v)->f[0];
  rt_drop(v);
  return b;
}
static V rt_out_u64(uint64_t b) {
  if (!(b >> 63)) return BOX(b);
  V fs[1] = {(V)b};
  return mkobj(T_RAW, 1, fs);
}
static double rt_in_f64(V v) { uint64_t b = rt_in_u64(v); double d; memcpy(&d, &b, 8); return d; }
static V rt_out_f64(double d) { uint64_t b; memcpy(&b, &d, 8); return rt_out_u64(b); }
static int rt_in_bool(V v) {
  int b = ISBOX(v) ? UNBOX(v) != 0 : tagof(fld(v, 0)) != 0;
  rt_drop(v);
  return b;
}
static char *rt_in_str(V v) {
  char *s = cstr(v);
  rt_drop(v);
  return s;
}
static void rt_free_cstr(char *s) {
#ifdef WIZ_RC
  free(s);
#else
  (void)s;
#endif
}
static V rt_out_str(const char *s) { return s ? wstr(s, strlen(s)) : wstr("", 0); }
/* (21o) an exported function's `String` result: a `malloc`ed copy the caller frees */
static char *rt_export_str(V v) {
  char *s = rt_in_str(v);
#ifdef WIZ_RC
  return s;
#else
  return strdup(s);
#endif
}
static void *rt_in_ptr(V v) { return ISBOX(v) ? NULL : ((Ext *)OBJ(v))->ptr; }
#ifndef WIZ_RC
static size_t rt_nfin;
static void rt_extFin(void *o, void *cd) {
  (void)cd;
  Ext *x = (Ext *)o;
  if (x->ptr && x->fin) x->fin(x->ptr);
}
#endif
static V rt_out_ptr(void *p, void (*fin)(void *)) {
  Ext *e = (Ext *)MALLOC_OBJ(sizeof(Ext));
  if (!e) die("out of memory");
  e->h.rc = 1; e->h.tag = T_EXT; e->h.size = 0;
  e->ptr = p; e->fin = fin;
  V o = (V)e;
#ifndef WIZ_RC
  if (fin) { GC_register_finalizer((void *)o, rt_extFin, NULL, NULL, NULL); rt_nfin++; }
#endif
  return o;
}
#ifndef WIZ_RC
/* at exit (the collector): finalize the foreign pointers nothing reaches any more */
static void rt_finishGC(void) {
  if (rt_nfin) { GC_gcollect(); GC_invoke_finalizers(); }
  fflush(stdout);
}
#endif
/* the runtime functions `lib/IO.wiz` binds (as in `runtime/wiz.c`) */
static uint64_t wiz_u64_id(uint64_t a) { return a; }
static uint64_t wiz_u64_add(uint64_t a, uint64_t b) { return a + b; }
static uint64_t wiz_u64_sub(uint64_t a, uint64_t b) { return a - b; }
static uint64_t wiz_u64_mul(uint64_t a, uint64_t b) { return a * b; }
static uint64_t wiz_u64_div(uint64_t a, uint64_t b) { return b ? a / b : 0; }
static uint64_t wiz_u64_mod(uint64_t a, uint64_t b) { return b ? a % b : a; }
static int wiz_u64_lt(uint64_t a, uint64_t b) { return a < b; }
static int wiz_u64_eq(uint64_t a, uint64_t b) { return a == b; }
static double wiz_f64_of_nat(uint64_t a) { return (double)a; }
static double wiz_f64_add(double a, double b) { return a + b; }
static double wiz_f64_sub(double a, double b) { return a - b; }
static double wiz_f64_mul(double a, double b) { return a * b; }
static double wiz_f64_div(double a, double b) { return a / b; }
static int wiz_f64_lt(double a, double b) { return a < b; }
static const char *wiz_f64_show(double a) { static char buf[64]; snprintf(buf, sizeof buf, "%.17g", a); return buf; }

/* (P2) The step budget of a proof's read-back in the self-hosted toolchain (selfhost/Kernel.wiz,
   `forceProof`; `Budget` in Wiz/Core/Term.lean is the Lean frontend's; as in runtime/wiz.c): a counter behind a
   pure interface, as in Lean. `start` begins a budget of `steps` closure instantiations
   (1: it did; 0: one is already running, the caller counts on it), `tick` takes one step
   (1, or 0 once it ran out; always 1 when no budget runs), `end` stops it (1: it did not
   run out). Only the read-back of a suspended proof starts one, so the kernel's own
   evaluation never finds one running. */
static int wiz_proof_on = 0;
static uint64_t wiz_proof_left = 0;
static int wiz_proof_start(uint64_t steps) { if (wiz_proof_on) return 0; wiz_proof_on = 1; wiz_proof_left = steps + 1; return 1; }
static int wiz_proof_tick(uint64_t x) { (void)x; if (!wiz_proof_on) return 1; if (wiz_proof_left <= 1) { wiz_proof_left = 0; return 0; } wiz_proof_left--; return 1; }
static int wiz_proof_end(uint64_t x) { (void)x; wiz_proof_on = 0; return wiz_proof_left > 0; }
/* (21s) the runtime's set-up, once: by `rt_start`, or by the first exported function a C
   program calls (a library has no `main`) */
static int rt_ready;
static void rt_ensure(void) {
  if (rt_ready) return;
  rt_ready = 1;
#ifdef WIZ_RC
  rt_nulInit();
#else
  GC_INIT();
  /* collect less often: the heap of a compiler is mostly live (20% faster) */
  GC_set_free_space_divisor(1);
#endif
}

/* (21s) Handles, as in `runtime/wiz.c` (stage 9g): C owns the reference to a Wiz value it
   gets (from an export, or a `Callback`'s context), `wiz_retain` makes one more and
   `wiz_release` gives one back. `wiz_live_objects` counts the objects alive, for leak
   checks in C tests: under reference counting, those allocated and not freed, less the
   program's constants (what the roots reach: globals computed once, natives' closures);
   under the collector nothing is counted (0). */
#ifdef WIZ_RC
static int rt_isNul(Obj *o) { return (void *)o >= (void *)rt_nul && (void *)o < (void *)(rt_nul + RT_NNUL); }
/* a set of objects (open addressing), and a stack of objects to visit */
static Obj **rt_seenT; static size_t rt_seenCap, rt_seenN;
static Obj **rt_todo; static size_t rt_todoN, rt_todoCap;
static int rt_seenAdd(Obj *o) {
  if (2 * (rt_seenN + 1) > rt_seenCap) {
    size_t oc = rt_seenCap; Obj **old = rt_seenT;
    rt_seenCap = oc ? 2 * oc : 1024;
    rt_seenT = (Obj **)calloc(rt_seenCap, sizeof(Obj *));
    if (!rt_seenT) die("out of memory");
    rt_seenN = 0;
    for (size_t i = 0; i < oc; i++) if (old[i]) (void)rt_seenAdd(old[i]);
    free(old);
  }
  size_t h = ((uintptr_t)o >> 4) * 11400714819323198485ull & (rt_seenCap - 1);
  while (rt_seenT[h]) { if (rt_seenT[h] == o) return 0; h = (h + 1) & (rt_seenCap - 1); }
  rt_seenT[h] = o; rt_seenN++;
  return 1;
}
static void rt_visit(V v) {
  if (!v || ISBOX(v)) return;
  if (rt_todoN == rt_todoCap) {
    rt_todoCap = rt_todoCap ? 2 * rt_todoCap : 256;
    rt_todo = (Obj **)realloc(rt_todo, rt_todoCap * sizeof(Obj *));
    if (!rt_todo) die("out of memory");
  }
  rt_todo[rt_todoN++] = OBJ(v);
}
static size_t rt_rooted(void) {
  size_t n = 0;
  rt_seenN = 0;
  if (rt_seenT) memset(rt_seenT, 0, rt_seenCap * sizeof(Obj *));
  for (size_t i = 0; i < rt_nroots; i++) rt_visit(*rt_roots[i]);
  while (rt_todoN) {
    Obj *x = rt_todo[--rt_todoN];
    if (rt_isNul(x) || !rt_seenAdd(x)) continue;
    n++;
    uint32_t t = TAG(x);
    /* (the children, as `rt_drain` releases them) */
    if (t < T_CLO || t == T_HYP) { for (uint32_t i = 0; i < SIZE(x); i++) rt_visit(x->f[i]); }
    else if (t == T_CLO) {
      Clo *c = (Clo *)x;
      for (uint32_t i = 0; i < SIZE(c); i++) rt_visit(c->env[i]);
    } else if (t == T_THUNK) {
      Thunk *th = (Thunk *)x;
      rt_visit(th->fn ? th->fn : th->val);
    } else if (t == T_ARR) {
      Arr *a = (Arr *)x;
      for (size_t i = 0; i < a->len; i++) rt_visit(a->data[i]);
    } else if (t == T_MAP) {
      Map *m = (Map *)x;
      for (size_t i = 0; i < m->cap; i++) if (m->keys[i]) { rt_visit(m->keys[i]); rt_visit(m->vals[i]); }
    }
  }
  return n;
}
void wiz_release(void *v) { dec((V)v); }
void wiz_retain(void *v) { inc((V)v); }
long wiz_live_objects(void) { return (long)(rt_live - rt_rooted()); }
#else
void wiz_release(void *v) { (void)v; }
void wiz_retain(void *v) { (void)v; }
long wiz_live_objects(void) { return 0; }
#endif

/* the program needs a big stack (deep recursion): raise the limit and start again (a
   thread with a big stack would do, but the collector's stopping of the world lost
   its signals) */
static void rt_start(char **argv) {
  rt_argv = argv;
  for (rt_argc = 0; argv[rt_argc]; rt_argc++) ;
  struct rlimit r;
  rlim_t want = (rlim_t)8 << 30;
  if (getrlimit(RLIMIT_STACK, &r) == 0 && r.rlim_cur != RLIM_INFINITY && r.rlim_cur < want && !getenv("WIZ_STACK_SET")) {
    r.rlim_cur = (r.rlim_max == RLIM_INFINITY || r.rlim_max >= want) ? want : r.rlim_max;
    if (setrlimit(RLIMIT_STACK, &r) == 0) { setenv("WIZ_STACK_SET", "1", 1); execv("/proc/self/exe", argv); }
  }
  rt_ensure();
}
