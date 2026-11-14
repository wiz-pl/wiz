
/* ---- numbers: small scalars, or GMP objects ---- */

static int wiz_is_big(wiz_val v) { return !WIZ_IS_SCALAR(v) && ((wiz_hdr *)v)->tag == WIZ_TAG_BIG; }

static wiz_val wiz_big_norm(mpz_t z) {
  if (mpz_cmp_ui(z, 0) >= 0 && mpz_sizeinbase(z, 2) <= 62) {
    wiz_val r = WIZ_BOX(mpz_get_ui(z));
    mpz_clear(z);
    return r;
  }
  wiz_big *b = (wiz_big *)wiz_alloc(sizeof(wiz_big), WIZ_TAG_BIG, 0);
  memcpy(b->z, z, sizeof(mpz_t));
  return (wiz_val)b;
}

static void wiz_to_mpz(mpz_t z, wiz_val v) {
  if (WIZ_IS_SCALAR(v)) mpz_init_set_ui(z, (unsigned long)WIZ_UNBOX(v));
  else mpz_init_set(z, ((wiz_big *)v)->z);
}

WIZ_API wiz_val wiz_nat_lit(const char *digits) {
  mpz_t z;
  mpz_init_set_str(z, digits, 10);
  return wiz_big_norm(z);
}

WIZ_API wiz_val wiz_nat_add(wiz_val a, wiz_val b) {
  if (WIZ_IS_SCALAR(a) && WIZ_IS_SCALAR(b)) {
    uintptr_t r = WIZ_UNBOX(a) + WIZ_UNBOX(b);
    if (r <= WIZ_MAX_SMALL) return WIZ_BOX(r);
  }
  mpz_t x, y;
  wiz_to_mpz(x, a); wiz_to_mpz(y, b);
  mpz_add(x, x, y); mpz_clear(y);
  wiz_dec(a); wiz_dec(b);
  return wiz_big_norm(x);
}

WIZ_API wiz_val wiz_nat_sub(wiz_val a, wiz_val b) {
  if (WIZ_IS_SCALAR(a) && WIZ_IS_SCALAR(b))
    return WIZ_BOX(WIZ_UNBOX(a) > WIZ_UNBOX(b) ? WIZ_UNBOX(a) - WIZ_UNBOX(b) : 0);
  mpz_t x, y;
  wiz_to_mpz(x, a); wiz_to_mpz(y, b);
  if (mpz_cmp(x, y) <= 0) mpz_set_ui(x, 0); else mpz_sub(x, x, y);
  mpz_clear(y);
  wiz_dec(a); wiz_dec(b);
  return wiz_big_norm(x);
}

WIZ_API wiz_val wiz_nat_mul(wiz_val a, wiz_val b) {
  if (WIZ_IS_SCALAR(a) && WIZ_IS_SCALAR(b)) {
    uintptr_t r;
    if (!__builtin_mul_overflow(WIZ_UNBOX(a), WIZ_UNBOX(b), &r) && r <= WIZ_MAX_SMALL) return WIZ_BOX(r);
  }
  mpz_t x, y;
  wiz_to_mpz(x, a); wiz_to_mpz(y, b);
  mpz_mul(x, x, y); mpz_clear(y);
  wiz_dec(a); wiz_dec(b);
  return wiz_big_norm(x);
}

WIZ_API wiz_val wiz_nat_succ(wiz_val a) { return wiz_nat_add(a, WIZ_BOX(1)); }
WIZ_API wiz_val wiz_nat_pred(wiz_val a) { return wiz_nat_sub(a, WIZ_BOX(1)); }

static int wiz_nat_eq(wiz_val a, wiz_val b) {
  if (WIZ_IS_SCALAR(a) && WIZ_IS_SCALAR(b)) return a == b;
  if (WIZ_IS_SCALAR(a) || WIZ_IS_SCALAR(b)) return 0;
  return mpz_cmp(((wiz_big *)a)->z, ((wiz_big *)b)->z) == 0;
}

/* the prelude's `Bool`: a constructor without fields is its tag. The comparisons
   borrow their arguments (stage 8e, `primBorrows`): the caller keeps its references. */
WIZ_API wiz_val wiz_nat_beq(wiz_val a, wiz_val b) {
  int eq = wiz_nat_eq(a, b);
  return WIZ_BOX(eq ? 1 : 0);
}
WIZ_API wiz_val wiz_nat_blt(wiz_val a, wiz_val b) {
  int lt;
  if (WIZ_IS_SCALAR(a) && WIZ_IS_SCALAR(b)) lt = WIZ_UNBOX(a) < WIZ_UNBOX(b);
  else { mpz_t x, y; wiz_to_mpz(x, a); wiz_to_mpz(y, b); lt = mpz_cmp(x, y) < 0; mpz_clear(x); mpz_clear(y); }
  return WIZ_BOX(lt ? 1 : 0);
}

/* division, powers and bits; as the Prelude defines them: n / 0 = 0, n % 0 = n,
   log2 0 = 0 */
enum { WIZ_OP_DIV, WIZ_OP_MOD, WIZ_OP_AND, WIZ_OP_OR, WIZ_OP_XOR };
static wiz_val wiz_nat_big_op(int op, wiz_val a, wiz_val b) {
  mpz_t x, y;
  wiz_to_mpz(x, a); wiz_to_mpz(y, b);
  switch (op) {
  case WIZ_OP_DIV: if (mpz_sgn(y) == 0) mpz_set_ui(x, 0); else mpz_fdiv_q(x, x, y); break;
  case WIZ_OP_MOD: if (mpz_sgn(y) != 0) mpz_fdiv_r(x, x, y); break;
  case WIZ_OP_AND: mpz_and(x, x, y); break;
  case WIZ_OP_OR: mpz_ior(x, x, y); break;
  default: mpz_xor(x, x, y); break;
  }
  mpz_clear(y);
  wiz_dec(a); wiz_dec(b);
  return wiz_big_norm(x);
}
WIZ_API wiz_val wiz_nat_div(wiz_val a, wiz_val b) {
  if (WIZ_IS_SCALAR(a) && WIZ_IS_SCALAR(b))
    return WIZ_BOX(WIZ_UNBOX(b) ? WIZ_UNBOX(a) / WIZ_UNBOX(b) : 0);
  return wiz_nat_big_op(WIZ_OP_DIV, a, b);
}
WIZ_API wiz_val wiz_nat_mod(wiz_val a, wiz_val b) {
  if (WIZ_IS_SCALAR(a) && WIZ_IS_SCALAR(b))
    return WIZ_BOX(WIZ_UNBOX(b) ? WIZ_UNBOX(a) % WIZ_UNBOX(b) : WIZ_UNBOX(a));
  return wiz_nat_big_op(WIZ_OP_MOD, a, b);
}
WIZ_API wiz_val wiz_nat_land(wiz_val a, wiz_val b) {
  if (WIZ_IS_SCALAR(a) && WIZ_IS_SCALAR(b)) return WIZ_BOX(WIZ_UNBOX(a) & WIZ_UNBOX(b));
  return wiz_nat_big_op(WIZ_OP_AND, a, b);
}
WIZ_API wiz_val wiz_nat_lor(wiz_val a, wiz_val b) {
  if (WIZ_IS_SCALAR(a) && WIZ_IS_SCALAR(b)) return WIZ_BOX(WIZ_UNBOX(a) | WIZ_UNBOX(b));
  return wiz_nat_big_op(WIZ_OP_OR, a, b);
}
WIZ_API wiz_val wiz_nat_xor(wiz_val a, wiz_val b) {
  if (WIZ_IS_SCALAR(a) && WIZ_IS_SCALAR(b)) return WIZ_BOX(WIZ_UNBOX(a) ^ WIZ_UNBOX(b));
  return wiz_nat_big_op(WIZ_OP_XOR, a, b);
}
/* `a * 2^n`; a shift by a big number of a nonzero number has no representation */
WIZ_API wiz_val wiz_nat_shiftLeft(wiz_val a, wiz_val n) {
  if (WIZ_IS_SCALAR(a) && WIZ_UNBOX(a) == 0) { wiz_dec(n); return a; }
  if (!WIZ_IS_SCALAR(n)) wiz_panic("Nat.shiftLeft: the shift is too big");
  uintptr_t k = WIZ_UNBOX(n);
  if (WIZ_IS_SCALAR(a) && k < 62 && WIZ_UNBOX(a) <= (WIZ_MAX_SMALL >> k)) return WIZ_BOX(WIZ_UNBOX(a) << k);
  mpz_t x;
  wiz_to_mpz(x, a);
  mpz_mul_2exp(x, x, (mp_bitcnt_t)k);
  wiz_dec(a);
  return wiz_big_norm(x);
}
WIZ_API wiz_val wiz_nat_shiftRight(wiz_val a, wiz_val n) {
  if (!WIZ_IS_SCALAR(n)) { wiz_dec(a); wiz_dec(n); return WIZ_BOX(0); }
  uintptr_t k = WIZ_UNBOX(n);
  if (WIZ_IS_SCALAR(a)) return WIZ_BOX(k >= 64 ? 0 : WIZ_UNBOX(a) >> k);
  mpz_t x;
  wiz_to_mpz(x, a);
  mpz_fdiv_q_2exp(x, x, (mp_bitcnt_t)k);
  wiz_dec(a);
  return wiz_big_norm(x);
}
WIZ_API wiz_val wiz_nat_pow(wiz_val b, wiz_val e) {
  if (WIZ_IS_SCALAR(b) && WIZ_UNBOX(b) <= 1) {
    /* 0^0 = 1, 0^e = 0, 1^e = 1, even for a big e */
    int zero = WIZ_IS_SCALAR(e) && WIZ_UNBOX(e) == 0;
    wiz_dec(e);
    return WIZ_BOX(zero ? 1 : WIZ_UNBOX(b));
  }
  if (!WIZ_IS_SCALAR(e)) wiz_panic("Nat.pow: the exponent is too big");
  uintptr_t k = WIZ_UNBOX(e);
  if (WIZ_IS_SCALAR(b)) {
    uintptr_t r = 1, x = WIZ_UNBOX(b), i = 0;
    for (; i < k; i++)
      if (__builtin_mul_overflow(r, x, &r) || r > WIZ_MAX_SMALL) break;
    if (i == k) return WIZ_BOX(r);
  }
  mpz_t x;
  wiz_to_mpz(x, b);
  mpz_pow_ui(x, x, (unsigned long)k);
  wiz_dec(b);
  return wiz_big_norm(x);
}
WIZ_API wiz_val wiz_nat_log2(wiz_val a) {
  if (WIZ_IS_SCALAR(a)) {
    uintptr_t x = WIZ_UNBOX(a);
    return WIZ_BOX(x == 0 ? 0 : 63 - __builtin_clzll((unsigned long long)x));
  }
  size_t bits = mpz_sizeinbase(((wiz_big *)a)->z, 2);
  wiz_dec(a);
  return WIZ_BOX(bits - 1);
}
