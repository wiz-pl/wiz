/* Numbers and machine words.

   One pool holds Nats (small scalars, GMP objects and shifts into both), the other
   words (scalars, raw boxes for 2^63..2^64-1, and GMP objects above 64 bits). Every
   operation gets owned arguments, so the harness exercises the small fast paths, the
   GMP fallback, wrapping at a width, signed division by -1 and division by zero. Shift
   amounts, exponents and input sizes are bounded here so a fuzzer cannot turn an input
   into gigabytes: that is the harness's limit, not the runtime's. */
#include "fuzz_common.h"

#define WSLOTS 6
#define WSTEPS 320

static const uint64_t fz_widths[] = {0, 1, 7, 8, 16, 31, 32, 63, 64, 65, 127, 128};

static uint64_t fz_width(fz_input *in) {
  return fz_widths[fz_below(in, sizeof fz_widths / sizeof fz_widths[0])];
}

static wiz_val fz_nat_new(fz_input *in) {
  char digits[25];
  switch (fz_below(in, 4)) {
  case 0: return wiz_out_nat(fz_u64(in) & 0xFF);
  case 1: return wiz_out_nat(fz_u64(in));
  case 2: {
    size_t n = 1 + fz_below(in, 24);
    for (size_t i = 0; i < n; i++) digits[i] = (char)('0' + fz_below(in, 10));
    digits[n] = 0;
    return wiz_nat_lit(digits);
  }
  default: return wiz_nat_shiftLeft(wiz_out_nat(1), wiz_out_nat(fz_below(in, 201)));
  }
}

static wiz_val fz_word_new(fz_input *in) {
  switch (fz_below(in, 5)) {
  case 0: return wiz_word_of_nat(fz_width(in), fz_nat_new(in));
  case 1: return wiz_word_of_neg(fz_width(in), fz_nat_new(in));
  case 2: return wiz_out_u64(fz_u64(in));
  case 3: return wiz_word_of_bits(fz_nat_new(in));
  default: return WIZ_BOX(fz_u64(in) & WIZ_MAX_SMALL);
  }
}

/* Keep a pool value small enough that a long sequence cannot make GMP allocate an
   unbounded result (a fuzz-input limit, not a runtime one). */
static void fz_cap(wiz_val *s, unsigned n) {
  for (unsigned i = 0; i < n; i++)
    if (s[i] && !WIZ_IS_SCALAR(s[i]) && ((const wiz_hdr *)s[i])->tag == WIZ_TAG_BIG &&
        mpz_sizeinbase(((const wiz_big *)s[i])->z, 2) > 4096) {
      wiz_dec(fz_take(s, i));
      s[i] = WIZ_BOX(0);
    }
}

/* consume two references to the (possibly equal) slots */
static void fz_two(wiz_val *s, unsigned a, unsigned b, wiz_val *x, wiz_val *y) {
  *x = fz_take(s, a);
  *y = a == b ? fz_share(*x) : fz_take(s, b);
}

static void fz_nats(fz_input *in, wiz_val *s) {
  unsigned a = (unsigned)fz_below(in, WSLOTS);
  unsigned b = (unsigned)fz_below(in, WSLOTS);
  unsigned op = (unsigned)fz_below(in, 17);
  wiz_val x, y;
  switch (op) {
  case 0: fz_put(s, a, fz_nat_new(in)); break;
  case 1: fz_put(s, a, wiz_nat_succ(s[a] ? fz_take(s, a) : fz_nat_new(in))); break;
  case 2: fz_put(s, a, wiz_nat_pred(s[a] ? fz_take(s, a) : fz_nat_new(in))); break;
  case 3: fz_put(s, a, wiz_nat_log2(s[a] ? fz_take(s, a) : fz_nat_new(in))); break;
  case 4: { /* shiftLeft: a GMP amount is only representable for zero */
    if (!s[a]) s[a] = fz_nat_new(in);
    fz_put(s, a, wiz_nat_shiftLeft(fz_take(s, a), wiz_out_nat(fz_below(in, 201))));
    break;
  }
  case 5: {
    if (!s[a]) s[a] = fz_nat_new(in);
    wiz_val k = fz_below(in, 2) ? wiz_out_nat(fz_below(in, 201))
                                : wiz_nat_shiftLeft(wiz_out_nat(1), wiz_out_nat(70));
    fz_put(s, a, wiz_nat_shiftRight(fz_take(s, a), k));
    break;
  }
  case 6: { /* power, with a bounded exponent */
    if (!s[a]) s[a] = fz_nat_new(in);
    fz_put(s, a, wiz_nat_pow(fz_take(s, a), wiz_out_nat(fz_below(in, 9))));
    break;
  }
  case 7: { /* comparisons borrow both roots */
    if (!s[a]) s[a] = fz_nat_new(in);
    if (!s[b]) s[b] = fz_nat_new(in);
    /* beq/blt borrow their arguments (they do not consume or increment them) */
    wiz_val e = wiz_nat_beq(s[a], s[b]);
    wiz_val l = wiz_nat_blt(s[a], s[b]);
    fz_put(s, a, wiz_nat_add(e, l));
    break;
  }
  default: {
    if (!s[a]) s[a] = fz_nat_new(in);
    if (!s[b]) s[b] = fz_nat_new(in);
    fz_two(s, a, b, &x, &y);
    switch (op) {
    case 8: fz_put(s, a, wiz_nat_add(x, y)); break;
    case 9: fz_put(s, a, wiz_nat_sub(x, y)); break;
    case 10: fz_put(s, a, wiz_nat_mul(x, y)); break;
    case 11: fz_put(s, a, wiz_nat_div(x, y)); break;
    case 12: fz_put(s, a, wiz_nat_mod(x, y)); break;
    case 13: fz_put(s, a, wiz_nat_land(x, y)); break;
    case 14: fz_put(s, a, wiz_nat_lor(x, y)); break;
    case 15: fz_put(s, a, wiz_nat_xor(x, y)); break;
    default: fz_put(s, a, wiz_out_nat(fz_u64(in))); wiz_dec(x); wiz_dec(y); break;
    }
    break;
  }
  }
  fz_cap(s, WSLOTS);
}

static void fz_words(fz_input *in, wiz_val *s) {
  unsigned a = (unsigned)fz_below(in, WSLOTS);
  unsigned b = (unsigned)fz_below(in, WSLOTS);
  unsigned op = (unsigned)fz_below(in, 22);
  wiz_val x, y;
  switch (op) {
  case 0: fz_put(s, a, fz_word_new(in)); break;
  case 1: { /* ofBits / toBits round trip */
    if (!s[a]) s[a] = fz_word_new(in);
    wiz_val n = wiz_word_to_bits(fz_take(s, a));
    fz_put(s, a, wiz_word_of_bits(n));
    break;
  }
  case 2: fz_put(s, a, wiz_word_not(fz_width(in), s[a] ? fz_take(s, a) : fz_word_new(in))); break;
  case 3: { /* left shift: a width and a bounded amount */
    if (!s[a]) s[a] = fz_word_new(in);
    uint64_t w = fz_width(in), k = fz_below(in, 221);
    fz_put(s, a, wiz_word_shl(w, fz_take(s, a), wiz_out_nat(k)));
    break;
  }
  case 4: { /* arithmetic right shift */
    if (!s[a]) s[a] = fz_word_new(in);
    uint64_t w = fz_width(in), k = fz_below(in, 221);
    fz_put(s, a, wiz_word_ashr(w, fz_take(s, a), wiz_out_nat(k)));
    break;
  }
  case 5: { /* logical right shift; a GMP shift amount is "infinite" */
    if (!s[a]) s[a] = fz_word_new(in);
    wiz_val k = fz_below(in, 2) ? wiz_out_nat(fz_below(in, 221))
                                : wiz_nat_shiftLeft(wiz_out_nat(1), wiz_out_nat(70));
    fz_put(s, a, wiz_word_lshr(fz_take(s, a), k));
    break;
  }
  case 6: { /* bit and msb */
    if (!s[a]) s[a] = fz_word_new(in);
    int bit = wiz_word_bit(fz_take(s, a), wiz_out_nat(fz_u64(in)));
    fz_put(s, a, WIZ_BOX((uint64_t)bit));
    break;
  }
  case 7: { /* msb */
    if (!s[a]) s[a] = fz_word_new(in);
    int r = wiz_word_msb(fz_width(in), fz_take(s, a));
    fz_put(s, a, WIZ_BOX((uint64_t)r));
    break;
  }
  case 8: { /* zero/sign extension and truncation */
    if (!s[a]) s[a] = fz_word_new(in);
    uint64_t w = fz_width(in), v = fz_width(in);
    fz_put(s, a, fz_below(in, 2) ? wiz_word_zext(v, fz_take(s, a))
                                 : wiz_word_sext(w, v, fz_take(s, a)));
    break;
  }
  case 9: fz_put(s, a, wiz_word_cast(s[a] ? fz_take(s, a) : fz_word_new(in))); break;
  case 10: { /* a word's bits as a Nat, then back into the pool */
    if (!s[a]) s[a] = fz_word_new(in);
    wiz_val n = wiz_word_to_bits(fz_take(s, a));
    fz_put(s, a, wiz_word_of_bits(n));
    break;
  }
  case 11: { /* UInt64/Float64 raw words */
    wiz_val u = wiz_out_u64(fz_u64(in));
    uint64_t bits = wiz_in_u64(u);
    wiz_val f = wiz_out_f64((double)(int64_t)bits);
    double d = wiz_in_f64(f);
    fz_put(s, a, wiz_out_f64(d + (double)(int64_t)fz_u64(in)));
    break;
  }
  case 12: case 13: case 14: case 15: { /* comparisons */
    if (!s[a]) s[a] = fz_word_new(in);
    if (!s[b]) s[b] = fz_word_new(in);
    fz_two(s, a, b, &x, &y);
    int r;
    if (op == 12) r = wiz_word_eq(x, y);
    else if (op == 13) r = wiz_word_ult(x, y);
    else if (op == 14) r = wiz_word_ule(x, y);
    else { uint64_t w = fz_width(in); r = wiz_word_slt(w, x, y); }
    fz_put(s, a, WIZ_BOX((uint64_t)r));
    break;
  }
  case 16: {
    if (!s[a]) s[a] = fz_word_new(in);
    if (!s[b]) s[b] = fz_word_new(in);
    fz_two(s, a, b, &x, &y);
    uint64_t w = fz_width(in);
    fz_put(s, a, WIZ_BOX((uint64_t)wiz_word_sle(w, x, y)));
    break;
  }
  default: {
    if (!s[a]) s[a] = fz_word_new(in);
    if (!s[b]) s[b] = fz_word_new(in);
    fz_two(s, a, b, &x, &y);
    switch (op) {
    case 17: fz_put(s, a, wiz_word_add(fz_width(in), x, y)); break;
    case 18: fz_put(s, a, wiz_word_sub(fz_width(in), x, y)); break;
    case 19: fz_put(s, a, wiz_word_mul(fz_width(in), x, y)); break;
    case 20: fz_put(s, a, wiz_word_udiv(fz_width(in), x, y)); break;
    case 21: fz_put(s, a, wiz_word_umod(fz_width(in), x, y)); break;
    default: fz_put(s, a, wiz_word_sdiv(fz_width(in), x, y)); break;
    }
    break;
  }
  }
  fz_cap(s, WSLOTS);
}

static void fz_run(fz_input *in) {
  wiz_val nat[WSLOTS] = {0}, word[WSLOTS] = {0};
  for (unsigned step = 0; step < WSTEPS && fz_more(in); step++) {
    if (fz_below(in, 2)) fz_nats(in, nat);
    else fz_words(in, word);
  }
  fz_drop_all(nat, WSLOTS);
  fz_drop_all(word, WSLOTS);
}

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
  long before = wiz_live_objects();
  fz_input in = {data, size, 0};
  fz_run(&in);
  fz_check_live(before);
  return 0;
}
