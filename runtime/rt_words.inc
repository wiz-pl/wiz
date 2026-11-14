
/* ---- flat objects: tags and fields by runtime values (`pack`, `unpack`) ---- */

WIZ_API wiz_val wiz_tag_of(wiz_val v) {
  uint32_t t = wiz_tag(v);
  wiz_dec(v);
  return WIZ_BOX(t);
}
WIZ_API wiz_val wiz_nat_tag(wiz_val v) {
  int zero = WIZ_IS_SCALAR(v) && WIZ_UNBOX(v) == 0;
  wiz_dec(v);
  return WIZ_BOX(zero ? 0 : 1);
}
WIZ_API wiz_val wiz_field_at(wiz_val v, wiz_val n) {
  wiz_val f = ((wiz_ctor *)v)->fields[WIZ_UNBOX(n)];
  wiz_inc(f);
  wiz_dec(v);
  return f;
}
/* an object with the tag of `t` and the fields listed by `l` (nested pairs ending in ◾) */
WIZ_API wiz_val wiz_mk_obj(wiz_val t, wiz_val l) {
  uint32_t tag = wiz_tag(t), n = 0;
  wiz_dec(t);
  for (wiz_val c = l; !WIZ_IS_SCALAR(c); c = ((wiz_ctor *)c)->fields[1]) n++;
  if (n == 0) { wiz_dec(l); return WIZ_BOX(tag); }
  wiz_val r = wiz_ctor_new(tag, n);
  uint32_t i = 0;
  for (wiz_val c = l; !WIZ_IS_SCALAR(c); c = ((wiz_ctor *)c)->fields[1]) {
    wiz_val f = ((wiz_ctor *)c)->fields[0];
    wiz_inc(f);
    WIZ_SET(r, i++, f);
  }
  wiz_dec(l);
  return r;
}

/* ---- fields ---- */

/* A number's constructor tag (0 for zero) is field 0 of its unary view. Its other fields
   would be fresh objects (`natView`), but `proj` is borrowed since stage 8e: nobody would
   own, and so free, them. The lowering takes numbers apart with `natTag`/`nat.pred`, so
   reaching this is a compiler bug: stop instead of leaking. */
WIZ_API wiz_val wiz_proj(wiz_val v, uint32_t i) {
  /* a projection of `◾` is `◾`: a pair of proofs reaches code that is generic in the
     sorts of its components as `◾` (as in the interpreters) */
  if (v == WIZ_BOX(0)) return v;
  if (WIZ_IS_SCALAR(v) || wiz_is_big(v)) {
    if (i == 0) return WIZ_BOX(WIZ_IS_SCALAR(v) && WIZ_UNBOX(v) == 0 ? 0 : 1);
    wiz_panic("internal error: proj of a field of a number (use natTag/nat.pred)");
  }
  /* borrowed: no new reference (the IR `dup`s it if it needs one) */
  return ((wiz_ctor *)v)->fields[i];
}

/* `0` for an observed coinductive value, `1` for coit, `2` for scofix, `3` for a lazy
   cell already observed (tag 1002: its one field is the payload) */
WIZ_API wiz_val wiz_lazy_tag(wiz_val v) {
  uint32_t t = WIZ_IS_SCALAR(v) ? 0 : ((wiz_hdr *)v)->tag;
  wiz_dec(v);
  return WIZ_BOX(t == 1000 ? 1 : t == 1001 ? 2 : t == 1002 ? 3 : 0);
}

/* Memoised observation: `out` has computed the payload `p` of the lazy cell `x` (both
   owned) and returns `p`. A shared cell is overwritten in place by an observed cell
   ⟨1002 p⟩, so its other references don't unfold it again (like a forced `memo`
   thunk). The payload's corecursive fields are new cells, never `x`: no cycle forms.
   A unique cell (rc 1) dies here, so there is nothing to keep (the plain-thunk case);
   an immortal cell (a hoisted constant) is not overwritten, or it would keep its
   observed prefix for ever.
   A cell shared between threads (rc < 0) is not overwritten either (25a): its other
   observers recompute the payload, which is the same value. (Keeping it would need a
   CAS of the tag to a blackhole, and observers waiting for the payload.) */
WIZ_API wiz_val wiz_lazy_set(wiz_val x, wiz_val p) {
  wiz_hdr *h = (wiz_hdr *)x;
  if (WIZ_IS_SCALAR(x) || WIZ_RC(h) <= 1 || (h->tag != 1000 && h->tag != 1001)) {
    wiz_dec(x);
    return p;
  }
  wiz_ctor *o = (wiz_ctor *)x;
  uint32_t n = h->size;
  for (uint32_t i = 0; i < n; i++) wiz_dec(o->fields[i]);
  h->tag = 1002;
  h->size = 1;
  wiz_inc(p);
  o->fields[0] = p;
  h->rc--; /* shared: still alive */
  return p;
}

/* ---- closures ---- */

WIZ_API wiz_val wiz_clo_new(wiz_boxed_fn fn, uint32_t arity, uint32_t n, wiz_val *args) {
  wiz_clo *c = (wiz_clo *)wiz_alloc(sizeof(wiz_clo) + n * sizeof(wiz_val), WIZ_TAG_CLO, n);
  c->fn = fn;
  c->arity = arity;
  for (uint32_t i = 0; i < n; i++) c->args[i] = args[i];
  return (wiz_val)c;
}

/* `memo A f`: the suspension `f` (owned), run at most once */
WIZ_API wiz_val wiz_memo(wiz_val ty, wiz_val f) {
  (void)ty;
  wiz_thunk *t = (wiz_thunk *)wiz_alloc(sizeof(wiz_thunk), WIZ_TAG_THUNK, 0);
  t->fn = f;
  t->val = WIZ_BOX(0);
  return (wiz_val)t;
}

/* Apply a closure (owned) to `n` arguments (owned). */
WIZ_API wiz_val wiz_apply(wiz_val f, uint32_t n, wiz_val *args) {
  if (!WIZ_IS_SCALAR(f) && ((wiz_hdr *)f)->tag == WIZ_TAG_THUNK) {
    /* force: the first argument is the unit */
    wiz_thunk *t = (wiz_thunk *)f;
    /* a thunk shared between threads is forced under one (recursive) lock, and its
       value is shared too; pure code never blocks, so the lock can't deadlock */
    /* An immortal thunk (part of a constant, which every thread can see) is forced
       under the lock too, and its value made immortal: the constant keeps it. */
    int64_t rc = WIZ_RC(&t->h);
    int shared = rc <= 0;
    if (shared) wiz_thunk_lock();
    if (t->fn) {
      wiz_val g = t->fn;
      t->fn = 0;
      t->val = wiz_apply(g, 1, args);
      if (rc < 0) wiz_mark_mt(t->val); else if (rc == 0) wiz_immortal(t->val);
    } else wiz_dec(args[0]);
    wiz_val r = t->val;
    wiz_inc(r);
    if (shared) wiz_thunk_unlock();
    wiz_dec(f);
    return n > 1 ? wiz_apply(r, n - 1, args + 1) : r;
  }
  /* `◾` applied is `◾`: a function with no runtime content (a proof, or an erased function
     into `Unit`, `erasedFunTy` in Erase.lean) reaches generic code as `◾`, and generic
     code applies it like any function */
  if (f == WIZ_BOX(0)) { for (uint32_t i = 0; i < n; i++) wiz_dec(args[i]); return f; }
  if (WIZ_IS_SCALAR(f) || ((wiz_hdr *)f)->tag != WIZ_TAG_CLO) wiz_panic("applying a non-function");
  wiz_clo *c = (wiz_clo *)f;
  uint32_t m = c->h.size, total = m + n;
  wiz_val *all = (wiz_val *)alloca(total * sizeof(wiz_val));
  for (uint32_t i = 0; i < m; i++) all[i] = c->args[i];
  for (uint32_t i = 0; i < n; i++) all[m + i] = args[i];
  wiz_boxed_fn fn = c->fn;
  uint32_t arity = c->arity;
  /* take the captured arguments: move them out of a unique closure, else share them */
  if (WIZ_RC(&c->h) == 1) { wiz_live--; wiz_untrack(c); free(c); }
  else { for (uint32_t i = 0; i < m; i++) wiz_inc(all[i]); wiz_dec(f); }
  if (total == arity) return fn(all);
  if (total < arity) return wiz_clo_new(fn, arity, total, all);
  wiz_val r = fn(all);
  return wiz_apply(r, total - arity, all + arity);
}

/* ---- reuse (Perceus): `reset` keeps a unique object's cell, `reuse` fills it ---- */

WIZ_API wiz_val wiz_reset(wiz_val x) {
  if (!WIZ_IS_SCALAR(x)) {
    wiz_hdr *h = (wiz_hdr *)x;
    /* only a constructor's cell can be reused: closures, numbers and the runtime's own
       objects (arrays, strings, maps …) own more than their fields */
    if (WIZ_RC(h) == 1 && h->tag < WIZ_TAG_FIRST_SPECIAL) {
      for (uint32_t i = 0; i < h->size; i++) wiz_dec(((wiz_ctor *)x)->fields[i]);
      return x;
    }
  }
  wiz_dec(x);
  return WIZ_BOX(0);
}

/* drop specialisation (stage 8e): drop `x`, whose fields in `mask` were read and are
   still needed. Unique: they move out (the others are dropped) and the cell is freed;
   shared: they get a reference each and `x` is decremented. */
WIZ_API wiz_val wiz_drop_moved(wiz_val x, wiz_val mask) {
  if (WIZ_IS_SCALAR(x)) return WIZ_BOX(0);
  wiz_hdr *h = (wiz_hdr *)x;
  uint64_t m = WIZ_UNBOX(mask);
  if (h->tag >= WIZ_TAG_FIRST_SPECIAL) { wiz_dec(x); return WIZ_BOX(0); }
  wiz_val *fs = ((wiz_ctor *)x)->fields;
  if (WIZ_RC(h) == 1) {
    for (uint32_t i = 0; i < h->size; i++)
      if (i >= 62 || !((m >> i) & 1)) wiz_dec(fs[i]);
    wiz_live--;
    wiz_untrack(h);
    free(h);
  } else {
    for (uint32_t i = 0; i < h->size && i < 62; i++)
      if ((m >> i) & 1) wiz_inc(fs[i]);
    wiz_dec(x); /* shared, or immortal (no count), or shared between threads */
  }
  return WIZ_BOX(0);
}

WIZ_API wiz_val wiz_reuse(wiz_val tok, uint32_t tag, uint32_t n) {
  if (!WIZ_IS_SCALAR(tok)) {
    wiz_hdr *h = (wiz_hdr *)tok;
    if (h->size == n) { h->tag = tag; return tok; }
    wiz_live--;
    wiz_untrack(h);
    free(h);
  }
  /* without fields the result is a scalar: `reuse w in ctor t` just frees the token */
  if (n == 0) return WIZ_BOX(tag);
  return wiz_ctor_new(tag, n);
}

/* list the objects still alive (with WIZ_LEAKS set) */
static void wiz_report_leaks(void) {
  if (wiz_leaks != 1) return;
  for (size_t i = 0; i < wiz_track_cap; i++) {
    wiz_hdr *h = (wiz_hdr *)wiz_track_tab[i];
    if (!h) continue;
    fprintf(stderr, "  leaked %p: tag %u, %u fields, rc %u:", (void *)h, h->tag, h->size, (unsigned)h->rc);
    if (h->tag < 1000) {
      wiz_ctor *o = (wiz_ctor *)h;
      for (uint32_t k = 0; k < h->size; k++) {
        wiz_val f = o->fields[k];
        if (WIZ_IS_SCALAR(f)) fprintf(stderr, " %lu", (unsigned long)WIZ_UNBOX(f));
        else fprintf(stderr, " <tag %u>", ((wiz_hdr *)f)->tag);
      }
    }
    fprintf(stderr, "\n");
  }
}

WIZ_API void wiz_unreachable(void) { wiz_panic("reached an impossible case"); }

/* ---- the FFI (stage 9): machine types and marshalling ---- */

/* UInt64 and Float64 are boxed raw words */
WIZ_API wiz_val wiz_raw_box(uint64_t bits) {
  wiz_ctor *o = (wiz_ctor *)wiz_alloc(sizeof(wiz_ctor) + sizeof(uint64_t), WIZ_TAG_RAW, 1);
  memcpy(o->fields, &bits, sizeof(uint64_t));
  return (wiz_val)o;
}
static uint64_t wiz_raw_bits(wiz_val v) {
  uint64_t b;
  memcpy(&b, ((wiz_ctor *)v)->fields, sizeof(uint64_t));
  return b;
}

/* each `wiz_in_*` consumes the Wiz value; each `wiz_out_*` makes one */
WIZ_API uint64_t wiz_in_u64(wiz_val v) { uint64_t b = wiz_raw_bits(v); wiz_dec(v); return b; }
WIZ_API wiz_val wiz_out_u64(uint64_t b) { return wiz_raw_box(b); }
WIZ_API double wiz_in_f64(wiz_val v) { uint64_t b = wiz_in_u64(v); double d; memcpy(&d, &b, 8); return d; }
WIZ_API wiz_val wiz_out_f64(double d) { uint64_t b; memcpy(&b, &d, 8); return wiz_raw_box(b); }
WIZ_API uint64_t wiz_in_nat(wiz_val v) {
  if (WIZ_IS_SCALAR(v)) return WIZ_UNBOX(v);
  if (mpz_sizeinbase(((wiz_big *)v)->z, 2) > 64) wiz_panic("a number is too big for a C integer");
  uint64_t r = mpz_get_ui(((wiz_big *)v)->z);
  wiz_dec(v);
  return r;
}
WIZ_API wiz_val wiz_out_nat(uint64_t n) {
  if (n <= WIZ_MAX_SMALL) return WIZ_BOX(n);
  mpz_t z;
  mpz_init_set_ui(z, n);
  return wiz_big_norm(z);
}

/* ---- machine words (lib/Word.wiz, stages 22c-d) ----
   `UIntN w` and `IntN w` (and `BitVec n`, which is `UIntN n`) are, in the model,
   `mk (toNat : Nat)` with the width a phantom parameter (stage 22e), so the model's
   object is `⟨0 bits⟩`: the bits as a number below 2^w (two's complement for `IntN`). Compiled code represents them natively
   (`attribute [implemented_by mk get] UIntN.mk`): a value is its bits b,
     * a scalar if b < 2^63 (no allocation),
     * a raw box (WIZ_TAG_RAW) if 2^63 <= b < 2^64,
     * a big number (GMP) if b >= 2^64 (widths above 64 only).
   The representation depends only on b, not on the width (generic code over `UIntN w`
   doesn't know w), so each value has exactly one. `wiz_word_of_bits`/`wiz_word_to_bits`
   convert from and to the number (the model's constructor and field); the operations
   below implement the Wiz definitions: on uint64_t up to 64 bits, with GMP beyond.
   Each consumes its arguments. */
enum { WIZ_W_ADD, WIZ_W_SUB, WIZ_W_MUL, WIZ_W_UDIV, WIZ_W_UMOD, WIZ_W_NOT, WIZ_W_SHL,
       WIZ_W_SDIV, WIZ_W_SREM, WIZ_W_ASHR, WIZ_W_SLT, WIZ_W_SLE,
       WIZ_W_AND, WIZ_W_OR, WIZ_W_XOR, WIZ_W_LSHR, WIZ_W_EQ, WIZ_W_ULT, WIZ_W_ULE, WIZ_W_BIT };
/* for operations whose result never exceeds their arguments: no width needed */
#define WIZ_W_ANY (~(uint64_t)0)
#define WIZ_WORD_SCALAR_MAX ((((uint64_t)1) << 63) - 1)
static inline wiz_val wiz_word_out(uint64_t b) { return b <= WIZ_WORD_SCALAR_MAX ? WIZ_BOX(b) : wiz_raw_box(b); }
/* the bits of a word below 2^64 (without consuming it) */
static inline int wiz_word_in(wiz_val v, uint64_t *b) {
  if (WIZ_IS_SCALAR(v)) { *b = WIZ_UNBOX(v); return 1; }
  if (((wiz_hdr *)v)->tag == WIZ_TAG_RAW) { *b = wiz_raw_bits(v); return 1; }
  return 0;
}
static void wiz_word_mpz(mpz_t z, wiz_val v) {
  uint64_t b;
  if (wiz_word_in(v, &b)) mpz_init_set_ui(z, (unsigned long)b);
  else mpz_init_set(z, ((wiz_big *)v)->z);
}
/* a number >= 0 (cleared) as a word */
static wiz_val wiz_word_of_mpz(mpz_t z) {
  if (mpz_sizeinbase(z, 2) <= 64) { uint64_t b = mpz_get_ui(z); mpz_clear(z); return wiz_word_out(b); }
  wiz_big *o = (wiz_big *)wiz_alloc(sizeof(wiz_big), WIZ_TAG_BIG, 0);
  memcpy(o->z, z, sizeof(mpz_t));
  return (wiz_val)o;
}
/* the model's constructor: a number below 2^w (a Nat) as a word */
WIZ_API wiz_val wiz_word_of_bits(wiz_val n) {
  if (WIZ_IS_SCALAR(n)) return n;  /* below 2^62: the same scalar */
  if (mpz_sizeinbase(((wiz_big *)n)->z, 2) > 64) return n;  /* at least 2^64: the same number */
  uint64_t b = mpz_get_ui(((wiz_big *)n)->z);
  wiz_dec(n);
  return wiz_word_out(b);
}
/* the model's field: a word as its number (a Nat) */
WIZ_API wiz_val wiz_word_to_bits(wiz_val v) {
  if (WIZ_IS_SCALAR(v)) return WIZ_UNBOX(v) <= WIZ_MAX_SMALL ? v : wiz_out_nat(WIZ_UNBOX(v));
  if (((wiz_hdr *)v)->tag == WIZ_TAG_RAW) { uint64_t b = wiz_raw_bits(v); wiz_dec(v); return wiz_out_nat(b); }
  return v;
}
/* a shift or bit index (a Nat): beyond 2^64, as good as infinite */
static uint64_t wiz_word_amount(wiz_val k) {
  if (WIZ_IS_SCALAR(k)) return WIZ_UNBOX(k);
  wiz_dec(k);
  return ~(uint64_t)0;
}
/* bits of width w as a signed number (in place) */
static void wiz_word_signed(mpz_t x, uint64_t w) {
  if (w > 0 && mpz_tstbit(x, w - 1)) { mpz_t p; mpz_init(p); mpz_setbit(p, w); mpz_sub(x, x, p); mpz_clear(p); }
}
static inline uint64_t wiz_word_mask(uint64_t w) { return w >= 64 ? ~(uint64_t)0 : (((uint64_t)1 << w) - 1); }
/* op on words of width w (k: a shift or bit index). Comparisons and `bit` give the
   scalar 0 or 1; everything else a word. */
static inline wiz_val wiz_word_op(int op, uint64_t w, wiz_val a, wiz_val b, uint64_t k) {
  uint64_t x, y = 0;
  if ((w <= 64 || w == WIZ_W_ANY) && wiz_word_in(a, &x) && wiz_word_in(b, &y)) {
    uint64_t mask = wiz_word_mask(w), r;
    int s = w >= 64 ? 0 : 64 - (int)w;
    int64_t sx = w ? (int64_t)(x << s) >> s : 0, sy = w ? (int64_t)(y << s) >> s : 0;
    if (!WIZ_IS_SCALAR(a)) wiz_dec(a);
    if (!WIZ_IS_SCALAR(b)) wiz_dec(b);
    switch (op) {
    case WIZ_W_ADD: r = x + y; break;
    case WIZ_W_SUB: r = x - y; break;
    case WIZ_W_MUL: r = x * y; break;
    case WIZ_W_UDIV: r = y ? x / y : 0; break;
    case WIZ_W_UMOD: r = y ? x % y : x; break;
    case WIZ_W_NOT: r = ~x; break;
    case WIZ_W_SHL: r = k >= w ? 0 : x << k; break;
    case WIZ_W_SDIV: r = y == 0 ? 0 : (sy == -1 ? (uint64_t)0 - x : (uint64_t)(sx / sy)); break;
    case WIZ_W_SREM: r = y == 0 ? x : (sy == -1 ? 0 : (uint64_t)(sx % sy)); break;
    case WIZ_W_ASHR: r = (uint64_t)(sx >> (k >= w ? (w ? w - 1 : 0) : k)); break;
    case WIZ_W_SLT: return WIZ_BOX(sx < sy);
    case WIZ_W_SLE: return WIZ_BOX(sx <= sy);
    case WIZ_W_AND: r = x & y; break;
    case WIZ_W_OR: r = x | y; break;
    case WIZ_W_XOR: r = x ^ y; break;
    case WIZ_W_LSHR: r = k >= 64 ? 0 : x >> k; break;
    case WIZ_W_EQ: return WIZ_BOX(x == y);
    case WIZ_W_ULT: return WIZ_BOX(x < y);
    case WIZ_W_ULE: return WIZ_BOX(x <= y);
    default: return WIZ_BOX(k < 64 && ((x >> k) & 1));
    }
    return wiz_word_out(r & mask);
  }
  mpz_t mx, my;
  wiz_word_mpz(mx, a); wiz_word_mpz(my, b);
  wiz_dec(a); wiz_dec(b);
  int cmp = 2;
  switch (op) {
  case WIZ_W_ADD: mpz_add(mx, mx, my); break;
  case WIZ_W_SUB: mpz_sub(mx, mx, my); break;
  case WIZ_W_MUL: mpz_mul(mx, mx, my); break;
  case WIZ_W_UDIV: if (mpz_sgn(my) == 0) mpz_set_ui(mx, 0); else mpz_fdiv_q(mx, mx, my); break;
  case WIZ_W_UMOD: if (mpz_sgn(my) != 0) mpz_fdiv_r(mx, mx, my); break;
  case WIZ_W_NOT: mpz_com(mx, mx); break;
  case WIZ_W_SHL: if (k >= w) mpz_set_ui(mx, 0); else mpz_mul_2exp(mx, mx, k); break;
  case WIZ_W_SDIV: case WIZ_W_SREM:
    if (mpz_sgn(my) == 0) { if (op == WIZ_W_SDIV) mpz_set_ui(mx, 0); break; }
    wiz_word_signed(mx, w); wiz_word_signed(my, w);
    if (op == WIZ_W_SDIV) mpz_tdiv_q(mx, mx, my); else mpz_tdiv_r(mx, mx, my);
    break;
  case WIZ_W_ASHR: wiz_word_signed(mx, w); mpz_fdiv_q_2exp(mx, mx, k >= w ? w : k); break;
  case WIZ_W_SLT: case WIZ_W_SLE: wiz_word_signed(mx, w); wiz_word_signed(my, w); /* fall through */
  case WIZ_W_EQ: case WIZ_W_ULT: case WIZ_W_ULE: cmp = mpz_cmp(mx, my); break;
  case WIZ_W_AND: mpz_and(mx, mx, my); break;
  case WIZ_W_OR: mpz_ior(mx, mx, my); break;
  case WIZ_W_XOR: mpz_xor(mx, mx, my); break;
  case WIZ_W_LSHR: mpz_fdiv_q_2exp(mx, mx, k); break;
  default: cmp = mpz_tstbit(mx, k) ? 0 : 1; mpz_clear(mx); mpz_clear(my); return WIZ_BOX(cmp == 0);
  }
  mpz_clear(my);
  if (cmp != 2) {
    mpz_clear(mx);
    switch (op) {
    case WIZ_W_EQ: return WIZ_BOX(cmp == 0);
    case WIZ_W_SLT: case WIZ_W_ULT: return WIZ_BOX(cmp < 0);
    default: return WIZ_BOX(cmp <= 0);
    }
  }
  if (w != WIZ_W_ANY) mpz_fdiv_r_2exp(mx, mx, w);
  return wiz_word_of_mpz(mx);
}
#define WIZ_WORD_BIN(name, op) \
  WIZ_API wiz_val wiz_word_##name(uint64_t w, wiz_val a, wiz_val b) { return wiz_word_op(op, w, a, b, 0); }
WIZ_WORD_BIN(add, WIZ_W_ADD)
WIZ_WORD_BIN(sub, WIZ_W_SUB)
WIZ_WORD_BIN(mul, WIZ_W_MUL)
WIZ_WORD_BIN(udiv, WIZ_W_UDIV)
WIZ_WORD_BIN(umod, WIZ_W_UMOD)
WIZ_WORD_BIN(sdiv, WIZ_W_SDIV)
WIZ_WORD_BIN(srem, WIZ_W_SREM)
#define WIZ_WORD_ANY(name, op) \
  WIZ_API wiz_val wiz_word_##name(wiz_val a, wiz_val b) { return wiz_word_op(op, WIZ_W_ANY, a, b, 0); }
WIZ_WORD_ANY(and, WIZ_W_AND)
WIZ_WORD_ANY(or, WIZ_W_OR)
WIZ_WORD_ANY(xor, WIZ_W_XOR)
#define WIZ_WORD_CMP(name, op, w) \
  WIZ_API int wiz_word_##name(uint64_t width, wiz_val a, wiz_val b) { return WIZ_UNBOX(wiz_word_op(op, w, a, b, 0)) != 0; }
WIZ_WORD_CMP(slt, WIZ_W_SLT, width)
WIZ_WORD_CMP(sle, WIZ_W_SLE, width)
WIZ_API int wiz_word_eq(wiz_val a, wiz_val b) { return WIZ_UNBOX(wiz_word_op(WIZ_W_EQ, WIZ_W_ANY, a, b, 0)) != 0; }
WIZ_API int wiz_word_ult(wiz_val a, wiz_val b) { return WIZ_UNBOX(wiz_word_op(WIZ_W_ULT, WIZ_W_ANY, a, b, 0)) != 0; }
WIZ_API int wiz_word_ule(wiz_val a, wiz_val b) { return WIZ_UNBOX(wiz_word_op(WIZ_W_ULE, WIZ_W_ANY, a, b, 0)) != 0; }
WIZ_API wiz_val wiz_word_not(uint64_t w, wiz_val a) { return wiz_word_op(WIZ_W_NOT, w, a, WIZ_BOX(0), 0); }
WIZ_API wiz_val wiz_word_shl(uint64_t w, wiz_val a, wiz_val k) {
  return wiz_word_op(WIZ_W_SHL, w, a, WIZ_BOX(0), wiz_word_amount(k));
}
WIZ_API wiz_val wiz_word_ashr(uint64_t w, wiz_val a, wiz_val k) {
  return wiz_word_op(WIZ_W_ASHR, w, a, WIZ_BOX(0), wiz_word_amount(k));
}
WIZ_API wiz_val wiz_word_lshr(wiz_val a, wiz_val k) {
  return wiz_word_op(WIZ_W_LSHR, WIZ_W_ANY, a, WIZ_BOX(0), wiz_word_amount(k));
}
WIZ_API int wiz_word_bit(wiz_val a, wiz_val i) {
  return WIZ_UNBOX(wiz_word_op(WIZ_W_BIT, WIZ_W_ANY, a, WIZ_BOX(0), wiz_word_amount(i))) != 0;
}
/* the top bit of a width-w word (the sign of an `IntN w`); Nat.testBit a (w - 1) */
WIZ_API int wiz_word_msb(uint64_t w, wiz_val a) {
  return WIZ_UNBOX(wiz_word_op(WIZ_W_BIT, WIZ_W_ANY, a, WIZ_BOX(0), w ? w - 1 : 0)) != 0;
}
/* n mod 2^w, and (-n) mod 2^w, for a number n (a Nat) */
static wiz_val wiz_word_reduce(uint64_t w, wiz_val n, int neg) {
  if (WIZ_IS_SCALAR(n) && w <= 64) {
    uint64_t x = WIZ_UNBOX(n);
    return wiz_word_out((neg ? (uint64_t)0 - x : x) & wiz_word_mask(w));
  }
  mpz_t z;
  wiz_to_mpz(z, n);
  wiz_dec(n);
  if (neg) mpz_neg(z, z);
  mpz_fdiv_r_2exp(z, z, w);
  return wiz_word_of_mpz(z);
}
WIZ_API wiz_val wiz_word_of_nat(uint64_t w, wiz_val n) { return wiz_word_reduce(w, n, 0); }
WIZ_API wiz_val wiz_word_of_neg(uint64_t w, wiz_val n) { return wiz_word_reduce(w, n, 1); }
/* the same bits at another type (`toIntN`, `toUIntN`) */
WIZ_API wiz_val wiz_word_cast(wiz_val a) { return a; }
/* to width v: zero-extending or truncating */
WIZ_API wiz_val wiz_word_zext(uint64_t v, wiz_val a) {
  uint64_t x;
  if (wiz_word_in(a, &x)) { if (!WIZ_IS_SCALAR(a)) wiz_dec(a); return wiz_word_out(x & wiz_word_mask(v)); }
  mpz_t z;
  wiz_word_mpz(z, a);
  wiz_dec(a);
  mpz_fdiv_r_2exp(z, z, v);
  return wiz_word_of_mpz(z);
}
/* from width w to width v: sign-extending or truncating */
WIZ_API wiz_val wiz_word_sext(uint64_t w, uint64_t v, wiz_val a) {
  uint64_t x;
  if (w <= 64 && v <= 64 && wiz_word_in(a, &x)) {
    int s = w >= 64 ? 0 : 64 - (int)w;
    int64_t sx = w ? (int64_t)(x << s) >> s : 0;
    if (!WIZ_IS_SCALAR(a)) wiz_dec(a);
    return wiz_word_out((uint64_t)sx & wiz_word_mask(v));
  }
  mpz_t z;
  wiz_word_mpz(z, a);
  wiz_dec(a);
  wiz_word_signed(z, w);
  mpz_fdiv_r_2exp(z, z, v);
  return wiz_word_of_mpz(z);
}
