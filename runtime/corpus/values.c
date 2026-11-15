/* The runtime's value representation: constructors, reference counting, closures and
   application, memoised suspensions, constants, reuse, and the FFI's raw words.
   Every root is dropped before the program returns, so `wiz_finish`'s leak check and
   the sanitizer's leak detector must both stay quiet. */
#include "corpus.h"

static wiz_val pair(wiz_val a, wiz_val b) {
  wiz_val p = wiz_ctor_new(7, 2);
  wiz_set(p, 0, a);
  wiz_set(p, 1, b);
  return p;
}

static wiz_val add_fn(wiz_val *args) { return wiz_nat_add(args[0], args[1]); }
static wiz_val dup_fn(wiz_val *args) { wiz_inc(args[0]); return wiz_nat_add(args[0], args[0]); }

static int memo_builds;
static wiz_val memo_fn(wiz_val *args) {
  wiz_dec(args[0]); /* the unit */
  memo_builds++;
  return wiz_out_nat(7);
}

static int caf_builds;
static wiz_val caf_slot;
static wiz_val caf_build(void) {
  caf_builds++;
  return wiz_str_of_cstr("a constant");
}

static wiz_val entry(void) {
  /* a constructor and its fields */
  wiz_val p = pair(wiz_str_of_cstr("left"), wiz_out_nat(2));
  check(wiz_tag(p) == 7, "a constructor keeps its tag");
  wiz_val p0 = wiz_proj(p, 0);
  wiz_inc(p0);
  check(wiz_str_eq(p0, wiz_str_of_cstr("left")), "field 0 (borrowed)");
  wiz_val right = wiz_field_at(p, WIZ_BOX(1)); /* consumes p, returns field 1 */
  check(nat_of(right) == 2, "field 1 (wiz_field_at)");
  wiz_val left = pair(wiz_str_of_cstr("x"), wiz_out_nat(0));
  wiz_val borrow = wiz_proj(left, 0);
  wiz_inc(borrow);
  wiz_dec(left);
  check(wiz_str_eq(borrow, wiz_str_of_cstr("x")), "a borrowed field outlives its cell");

  /* reference counting */
  wiz_val s = wiz_str_of_cstr("shared");
  wiz_inc(s);
  wiz_inc(s);
  wiz_dec(s);
  wiz_dec(s);
  check(wiz_str_eq(s, wiz_str_of_cstr("shared")), "a value stays alive while shared");

  /* closures: capture, partial application, and an erased function */
  wiz_val captured[1] = {wiz_out_nat(10)};
  wiz_val f = wiz_clo_new(add_fn, 2, 1, captured);
  wiz_val arg10 = wiz_out_nat(5);
  check(nat_of(wiz_apply(f, 1, &arg10)) == 15, "a closure captures an argument");
  wiz_val g = wiz_clo_new(dup_fn, 2, 0, NULL);
  wiz_val none = wiz_apply(g, 0, NULL); /* no argument yet: the same closure */
  wiz_val args[2] = {wiz_out_nat(3), wiz_out_nat(4)};
  check(nat_of(wiz_apply(none, 2, args)) == 6, "a partially applied closure");
  wiz_val erased_arg = wiz_str_of_cstr("dropped");
  wiz_val erased = wiz_apply(WIZ_BOX(0), 1, &erased_arg);
  check(erased == WIZ_BOX(0), "an erased function returns unit");
  wiz_dec(erased);

  /* memoised suspensions: the body runs once */
  memo_builds = 0;
  wiz_val thunk_body = wiz_clo_new(memo_fn, 1, 0, NULL);
  wiz_val thunk = wiz_memo(WIZ_BOX(0), thunk_body);
  wiz_val unit1 = WIZ_BOX(0), unit2 = WIZ_BOX(0);
  wiz_inc(thunk); /* the first force consumes the thunk */
  check(nat_of(wiz_apply(thunk, 1, &unit1)) == 7, "a memoised value");
  check(nat_of(wiz_apply(thunk, 1, &unit2)) == 7, "a memoised value, forced again");
  check(memo_builds == 1, "a memoised body runs once");

  /* constants: built once, and immortal (so not a leak) */
  caf_builds = 0;
  caf_slot = 0;
  wiz_val c1 = wiz_caf_init(&caf_slot, caf_build);
  wiz_val c2 = wiz_caf_init(&caf_slot, caf_build);
  check(caf_builds == 1, "a constant is built once");
  check(c1 == c2, "a constant is one value");
  check(wiz_str_eq(c1, wiz_str_of_cstr("a constant")), "the constant's text");
  wiz_dec(c2);

  /* reset/reuse (Perceus) */
  wiz_val cell = pair(wiz_out_nat(1), wiz_out_nat(2));
  wiz_val token = wiz_reset(cell); /* fields dropped, the cell kept */
  wiz_val again = wiz_reuse(token, 9, 2);
  check(wiz_tag(again) == 9, "reuse retags a cell of the same size");
  wiz_set(again, 0, wiz_out_nat(3));
  wiz_set(again, 1, wiz_out_nat(4));
  wiz_dec(again);
  wiz_val other = wiz_reset(pair(wiz_out_nat(0), wiz_out_nat(0)));
  wiz_val sized = wiz_reuse(other, 8, 1); /* another size: a fresh cell */
  check(wiz_tag(sized) == 8, "reuse of another size makes a new cell");
  wiz_set(sized, 0, wiz_out_nat(0));
  wiz_dec(sized);

  /* drop specialisation: the fields in the mask move out */
  wiz_val cell2 = pair(wiz_str_of_cstr("drop"), wiz_str_of_cstr("keep"));
  wiz_val keep = wiz_proj(cell2, 1); /* drop_moved moves it out: do not inc */
  wiz_drop_moved(cell2, WIZ_BOX(2)); /* keeps field 1 */
  check(wiz_str_eq(keep, wiz_str_of_cstr("keep")), "drop_moved keeps a field");

  /* the FFI's raw words, machine words, floats and Bool */
  wiz_val u = wiz_out_u64(0xDEADBEEFCAFEBABEull);
  check(wiz_in_u64(u) == 0xDEADBEEFCAFEBABEull, "a UInt64 round trip");
  check(wiz_in_f64(wiz_out_f64(3.5)) == 3.5, "a Float64 round trip");
  wiz_val wide = wiz_word_of_bits(wiz_out_nat(1ull << 63));
  check(nat_of(wiz_word_to_bits(wide)) == (1ull << 63), "a word of 2^63");
  check(wiz_word_eq(wiz_word_of_bits(wiz_out_nat(5)), wiz_out_nat(5)), "word equality");
  check(wiz_in_bool(wiz_out_bool(1)) == 1, "a Bool round trip");
  check(nat_of(wiz_tag_of(WIZ_BOX(12))) == 12, "tag_of a constructor");
  check(nat_of(wiz_nat_tag(WIZ_BOX(0))) == 0, "nat_tag of zero");
  check(nat_of(wiz_nat_tag(WIZ_BOX(3))) == 1, "nat_tag of a successor");

  /* an IO result is a pair (value, world) */
  wiz_val io = wiz_io_result(wiz_out_nat(1), WIZ_BOX(0));
  check(wiz_tag(io) == 0 && wiz_tag(wiz_proj(io, 0)) == 1, "an IO result's shape");
  wiz_dec(io);

  printf("values: ok\n");
  return WIZ_BOX(0);
}

int main(void) {
  int rc = wiz_run_main(entry, 0);
  if (wiz_corpus_failures) fprintf(stderr, "corpus: %d check(s) failed\n", wiz_corpus_failures);
  return wiz_corpus_failures ? 1 : rc;
}
