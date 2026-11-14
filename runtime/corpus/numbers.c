/* The runtime's numbers: small scalars and GMP (Nat), machine words (UIntN/IntN), and
   the FFI's UInt64/Float64. Big results are compared against a literal of the expected
   decimal text. */
#include "corpus.h"
#include <string.h>

static int nat_eq(wiz_val a, wiz_val b) { return WIZ_UNBOX(wiz_nat_beq(a, b)) != 0; }

static int nat_is(wiz_val v, const char *decimal) {
  wiz_val e = wiz_nat_lit(decimal);
  int r = nat_eq(v, e);
  wiz_dec(e);
  return r;
}

/* a word of width w with the bits of n */
static wiz_val word(uint64_t w, uint64_t n) { return wiz_word_of_nat(w, wiz_out_nat(n)); }

static uint64_t word_bits(wiz_val v) { return nat_of(wiz_word_to_bits(v)); }

static wiz_val entry(void) {
  /* small numbers */
  check(nat_of(wiz_nat_add(wiz_out_nat(2), wiz_out_nat(3))) == 5, "Nat.add");
  check(nat_of(wiz_nat_sub(wiz_out_nat(2), wiz_out_nat(3))) == 0, "Nat.sub saturates at 0");
  check(nat_of(wiz_nat_mul(wiz_out_nat(7), wiz_out_nat(6))) == 42, "Nat.mul");
  check(nat_of(wiz_nat_div(wiz_out_nat(7), wiz_out_nat(2))) == 3, "Nat.div");
  check(nat_of(wiz_nat_mod(wiz_out_nat(7), wiz_out_nat(2))) == 1, "Nat.mod");
  check(nat_of(wiz_nat_div(wiz_out_nat(7), wiz_out_nat(0))) == 0, "Nat.div by zero is 0");
  check(nat_of(wiz_nat_mod(wiz_out_nat(7), wiz_out_nat(0))) == 7, "Nat.mod by zero is the dividend");
  check(nat_of(wiz_nat_succ(wiz_out_nat(41))) == 42, "Nat.succ");
  check(nat_of(wiz_nat_pred(wiz_out_nat(0))) == 0, "Nat.pred of zero");
  check(nat_eq(wiz_out_nat(9), wiz_out_nat(9)), "Nat.beq");
  check(!nat_eq(wiz_out_nat(9), wiz_out_nat(10)), "Nat.beq of different numbers");
  check(WIZ_UNBOX(wiz_nat_blt(wiz_out_nat(9), wiz_out_nat(10))), "Nat.blt");
  check(nat_of(wiz_nat_land(wiz_out_nat(12), wiz_out_nat(10))) == 8, "Nat.land");
  check(nat_of(wiz_nat_lor(wiz_out_nat(12), wiz_out_nat(10))) == 14, "Nat.lor");
  check(nat_of(wiz_nat_xor(wiz_out_nat(12), wiz_out_nat(10))) == 6, "Nat.xor");
  check(nat_of(wiz_nat_shiftLeft(wiz_out_nat(1), wiz_out_nat(10))) == 1024, "Nat.shiftLeft");
  check(nat_of(wiz_nat_shiftRight(wiz_out_nat(1024), wiz_out_nat(3))) == 128, "Nat.shiftRight");
  check(nat_of(wiz_nat_pow(wiz_out_nat(2), wiz_out_nat(10))) == 1024, "Nat.pow");
  check(nat_of(wiz_nat_pow(wiz_out_nat(0), wiz_out_nat(0))) == 1, "Nat.pow 0 0");
  check(nat_of(wiz_nat_log2(wiz_out_nat(1024))) == 10, "Nat.log2");
  check(nat_of(wiz_nat_log2(wiz_out_nat(0))) == 0, "Nat.log2 of zero");

  /* big numbers (GMP) */
  wiz_val big = wiz_nat_lit("123456789012345678901234567890");
  check(nat_is(big, "123456789012345678901234567890"), "a big literal");
  wiz_val plus = wiz_nat_add(big, wiz_out_nat(1));
  check(nat_is(plus, "123456789012345678901234567891"), "big addition");
  wiz_val twice = wiz_nat_mul(share(plus), wiz_out_nat(2));
  check(nat_is(twice, "246913578024691357802469135782"), "big multiplication");
  wiz_dec(twice);
  wiz_inc(plus); /* div and mod each consume a reference */
  wiz_val div = wiz_nat_div(plus, wiz_out_nat(1000));
  check(nat_is(div, "123456789012345678901234567"), "big division");
  wiz_dec(div);
  wiz_val mod = wiz_nat_mod(plus, wiz_out_nat(1000));
  check(nat_is(mod, "891"), "big remainder");
  wiz_dec(mod);
  wiz_val shift = wiz_nat_shiftLeft(wiz_out_nat(1), wiz_out_nat(100));
  check(nat_is(shift, "1267650600228229401496703205376"), "a shift into big numbers");
  wiz_val back = wiz_nat_shiftRight(shift, wiz_out_nat(100));
  check(nat_of(back) == 1, "a shift back to a small number");
  wiz_val pow = wiz_nat_pow(wiz_out_nat(10), wiz_out_nat(30));
  check(nat_is(pow, "1000000000000000000000000000000"), "10^30");
  wiz_dec(pow);
  wiz_val log = wiz_nat_log2(wiz_nat_shiftLeft(wiz_out_nat(1), wiz_out_nat(100)));
  check(nat_of(log) == 100, "log2 of 2^100");
  check(nat_is(wiz_nat_add(wiz_out_nat(1), wiz_out_nat(2)), "3"), "a small sum is not a big number");

  /* machine words: UIntN/IntN of a width, with wrapping and two's complement */
  check(word_bits(wiz_word_add(8, word(8, 250), word(8, 10))) == 4, "word add wraps at 2^w");
  check(word_bits(wiz_word_sub(8, word(8, 3), word(8, 5))) == 254, "word sub wraps");
  check(word_bits(wiz_word_mul(8, word(8, 16), word(8, 16))) == 0, "word mul wraps");
  check(word_bits(wiz_word_udiv(8, word(8, 250), word(8, 10))) == 25, "word udiv");
  check(word_bits(wiz_word_umod(8, word(8, 250), word(8, 10))) == 0, "word umod");
  check(word_bits(wiz_word_udiv(8, word(8, 1), word(8, 0))) == 0, "word divide by zero");
  check(word_bits(wiz_word_sdiv(8, wiz_word_of_neg(8, wiz_out_nat(6)), word(8, 2))) == 253,
        "word sdiv of -6 by 2 is -3");
  check(word_bits(wiz_word_srem(8, wiz_word_of_neg(8, wiz_out_nat(7)), word(8, 3))) == 255,
        "word srem of -7 by 3 is -1");
  check(word_bits(wiz_word_and(word(8, 12), word(8, 10))) == 8, "word and");
  check(word_bits(wiz_word_or(word(8, 12), word(8, 10))) == 14, "word or");
  check(word_bits(wiz_word_xor(word(8, 12), word(8, 10))) == 6, "word xor");
  check(word_bits(wiz_word_not(8, word(8, 0))) == 255, "word not");
  check(word_bits(wiz_word_shl(8, word(8, 1), wiz_out_nat(3))) == 8, "word shl");
  check(word_bits(wiz_word_shl(8, word(8, 1), wiz_out_nat(80))) == 0, "a shift past the width");
  check(word_bits(wiz_word_ashr(8, word(8, 128), wiz_out_nat(1))) == 192, "word ashr of -128");
  check(word_bits(wiz_word_lshr(word(8, 128), wiz_out_nat(1))) == 64, "word lshr");
  check(wiz_word_slt(8, word(8, 255), word(8, 0)), "word slt of -1");
  check(!wiz_word_ult(word(8, 255), word(8, 0)), "word ult is unsigned");
  check(wiz_word_eq(word(8, 255), word(8, 255)), "word eq");
  check(wiz_word_bit(word(8, 4), wiz_out_nat(2)), "word bit");
  check(!wiz_word_bit(word(8, 4), wiz_out_nat(3)), "word bit is 0");
  check(wiz_word_msb(8, word(8, 128)), "word msb");
  check(!wiz_word_msb(8, word(8, 127)), "word msb is 0");
  check(word_bits(wiz_word_of_nat(8, wiz_out_nat(300))) == 44, "word ofNat reduces");
  check(word_bits(wiz_word_of_neg(8, wiz_out_nat(6))) == 250, "word ofNeg");
  check(word_bits(wiz_word_cast(word(8, 200))) == 200, "word cast");
  check(word_bits(wiz_word_zext(16, word(8, 250))) == 250, "word zext");
  check(word_bits(wiz_word_sext(8, 16, word(8, 255))) == 65535, "word sext");
  check(word_bits(wiz_word_of_bits(wiz_out_nat(77))) == 77, "word ofBits/toBits");

  /* the same bits at 64 bits: 2^63 is a raw box, not a GMP number */
  wiz_val top = wiz_word_of_bits(wiz_out_nat(1ull << 63));
  check(wiz_tag(top) == WIZ_TAG_RAW, "a word of 2^63 is a raw box");
  check(word_bits(top) == (1ull << 63), "the raw box's bits");
  check(wiz_word_ult(word(64, 1), word(64, 2)), "64-bit word comparison");

  /* UInt64 and Float64 (the FFI's boxed raw words) */
  check(wiz_u64_add(20, 22) == 42, "UInt64.add");
  check(wiz_u64_sub(3, 5) == (uint64_t)-2, "UInt64.sub wraps");
  check(wiz_u64_mul(6, 7) == 42, "UInt64.mul");
  check(wiz_u64_div(7, 0) == 0, "UInt64.div by zero");
  check(wiz_u64_mod(7, 0) == 7, "UInt64.mod by zero");
  check(wiz_u64_lt(1, 2) && !wiz_u64_lt(2, 1), "UInt64.lt");
  check(wiz_u64_eq(2, 2), "UInt64.eq");
  check(wiz_f64_add(1.5, 2.5) == 4.0, "Float64.add");
  check(wiz_f64_mul(1.5, 2.0) == 3.0, "Float64.mul");
  check(wiz_f64_lt(1.0, 2.0), "Float64.lt");
  check(strcmp(wiz_nat_show(42), "42") == 0, "Nat.show");
  check(strcmp(wiz_f64_show(1.5), "1.5") == 0, "Float64.show");

  printf("numbers: ok\n");
  return WIZ_BOX(0);
}

int main(void) {
  int rc = wiz_run_main(entry, 0);
  if (wiz_corpus_failures) fprintf(stderr, "corpus: %d check(s) failed\n", wiz_corpus_failures);
  return wiz_corpus_failures ? 1 : rc;
}
