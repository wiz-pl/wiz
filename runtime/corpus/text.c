/* The runtime's data structures: Str, Bytes, Array, StrMap, the word arrays and maps,
   intern tables, and the C string of a Wiz String. Every root is dropped, so both leak
   checks (the runtime's count and the sanitizer's detector) must stay quiet. */
#include "corpus.h"
#include <string.h>

static wiz_val entry(void) {
  /* Str: an immutable byte string, updated/copied with reference counting */
  wiz_val a = wiz_str_of_cstr("hello");
  check(wiz_str_size(share(a)) == 5, "Str.size");
  check(wiz_str_byte(share(a), 1) == 'e', "Str.byte");
  check(wiz_str_byte(share(a), 99) == 0, "Str.byte past the end");
  wiz_val b = wiz_str_of_cstr(" world");
  wiz_val ab = wiz_str_append(a, b); /* consumes both */
  check(strcmp(wiz_str_to_cstr(share(ab)), "hello world") == 0, "Str.append");
  wiz_dec(ab);
  wiz_val cut = wiz_str_slice(wiz_str_of_cstr("abcdef"), 2, 4); /* "cd" */
  check(strcmp(wiz_str_to_cstr(share(cut)), "cd") == 0, "Str.slice");
  wiz_dec(cut);
  wiz_val empty = wiz_str_of_cstr("");
  check(wiz_str_size(share(empty)) == 0, "an empty Str");
  wiz_dec(empty);
  check(wiz_str_eq(wiz_str_of_cstr("same"), wiz_str_of_cstr("same")), "Str.eq");
  check(!wiz_str_eq(wiz_str_of_cstr("a"), wiz_str_of_cstr("b")), "Str.eq of different text");
  check(wiz_str_lt(wiz_str_of_cstr("a"), wiz_str_of_cstr("b")), "Str.lt");
  check(!wiz_str_lt(wiz_str_of_cstr("b"), wiz_str_of_cstr("a")), "Str.lt the other way");

  /* Bytes: a functional byte buffer, in place when unique */
  wiz_val bytes = wiz_bytes_empty();
  for (int i = 0; i < 256; i++) bytes = wiz_bytes_push(bytes, (uint64_t)i);
  check(wiz_bytes_size(share(bytes)) == 256, "Bytes.size");
  check(wiz_bytes_get(share(bytes), 200) == 200, "Bytes.get");
  check(wiz_bytes_get(share(bytes), 300) == 0, "Bytes.get past the end");
  wiz_val bs = wiz_bytes_slice(share(bytes), 250, 10);
  check(wiz_bytes_size(share(bs)) == 6, "Bytes.slice cuts at the end");
  check(wiz_bytes_get(share(bs), 0) == 250, "Bytes.slice's first byte");
  wiz_val bs2 = wiz_bytes_of_string("xyz");
  check(wiz_bytes_eq(wiz_bytes_of_string("xyz"), share(bs2)), "Bytes.ofString/eq");
  wiz_val joined = wiz_bytes_append(wiz_bytes_of_string("ab"), wiz_bytes_of_string("cd"));
  check(strcmp(wiz_bytes_to_string(share(joined)), "abcd") == 0, "Bytes.to_string");
  wiz_dec(joined);
  check(wiz_bytes_size(share(bytes)) == 256, "a shared Bytes is copied, not changed");
  wiz_dec(bytes);
  wiz_dec(bs);
  wiz_dec(bs2);

  /* the empty buffer: its data pointer is NULL, and converting it must not pass NULL to
     memcpy (the UBSAN finding this corpus started from) */
  check(wiz_bytes_to_string(wiz_bytes_empty())[0] == 0, "an empty Bytes to string");
  wiz_val shared_empty = wiz_bytes_empty();
  wiz_inc(shared_empty);
  wiz_val copy = wiz_bytes_push(shared_empty, 1); /* a unique copy of a NULL buffer */
  wiz_dec(shared_empty);
  check(wiz_bytes_size(share(copy)) == 1, "push onto a shared empty Bytes");
  wiz_dec(copy);

  /* Array: Wiz values, in place when unique */
  wiz_val arr = wiz_array_empty();
  arr = wiz_array_push(arr, wiz_out_nat(10));
  arr = wiz_array_push(arr, wiz_str_of_cstr("x"));
  check(wiz_array_size(share(arr)) == 2, "Array.size");
  check(nat_of(wiz_array_get(share(arr), 0, WIZ_BOX(0))) == 10, "Array.get");
  check(nat_of(wiz_array_get(share(arr), 9, wiz_out_nat(99))) == 99, "Array.get's default");
  arr = wiz_array_set(arr, 0, wiz_out_nat(11));
  check(nat_of(wiz_array_get(share(arr), 0, WIZ_BOX(0))) == 11, "Array.set");
  wiz_val array_copy = wiz_array_push(share(arr), wiz_out_nat(1)); /* arr is shared */
  check(wiz_array_size(share(array_copy)) == 3, "push onto a shared Array copies it");
  check(wiz_array_size(share(arr)) == 2, "the shared Array is unchanged");
  wiz_dec(array_copy);
  wiz_dec(arr);

  /* StrMap: a map from Str to a value */
  wiz_val m = wiz_map_empty();
  m = wiz_map_insert(m, wiz_str_of_cstr("one"), wiz_out_nat(1));
  m = wiz_map_insert(m, wiz_str_of_cstr("two"), wiz_out_nat(2));
  m = wiz_map_insert(m, wiz_str_of_cstr("one"), wiz_out_nat(11)); /* replaces */
  check(wiz_map_size(share(m)) == 2, "StrMap.size");
  check(nat_of(wiz_map_find(share(m), wiz_str_of_cstr("one"), wiz_out_nat(0))) == 11, "StrMap.findD");
  check(nat_of(wiz_map_find(share(m), wiz_str_of_cstr("none"), wiz_out_nat(9))) == 9, "StrMap.findD's default");
  wiz_dec(m);

  /* word arrays: U8/U32/U64Array over 1/4/8-byte elements */
  wiz_val wa = wiz_u8array_empty();
  for (int i = 0; i < 5; i++) wa = wiz_warray_push(wa, wiz_word_of_bits(wiz_out_nat((uint64_t)i)));
  check(nat_of(wiz_warray_size(share(wa))) == 5, "U8Array.size");
  check(nat_of(wiz_word_to_bits(wiz_warray_get(share(wa), wiz_out_nat(2), wiz_out_nat(0)))) == 2, "U8Array.get");
  check(nat_of(wiz_word_to_bits(wiz_warray_get(share(wa), wiz_out_nat(9), wiz_out_nat(77)))) == 77,
        "U8Array.get's default");
  wa = wiz_warray_set(wa, wiz_out_nat(0), wiz_word_of_bits(wiz_out_nat(9)));
  wiz_val slice = wiz_warray_slice(share(wa), wiz_out_nat(1), wiz_out_nat(2));
  check(nat_of(wiz_warray_size(share(slice))) == 2, "U8Array.slice");
  wiz_val appended = wiz_warray_append(wa, slice); /* consumes both */
  check(nat_of(wiz_warray_size(share(appended))) == 7, "U8Array.append");
  wiz_val alist = wiz_warray_to_list(share(appended));
  check(list_len_is(alist, 7), "U8Array.toList");
  wiz_dec(alist);
  wiz_dec(appended);
  wiz_val popped = wiz_warray_pop(wiz_u8array_of_list(cons(wiz_word_of_bits(wiz_out_nat(1)),
                                                             cons(wiz_word_of_bits(wiz_out_nat(2)), WIZ_BOX(0)))));
  check(nat_of(wiz_warray_size(share(popped))) == 1, "U8Array.pop");
  wiz_dec(popped);
  uint8_t raw[3] = {7, 8, 9};
  wiz_val ofc = wiz_warray_of_c(1, raw, 3);
  check(wiz_warray_len(ofc) == 3 && ((const uint8_t *)wiz_warray_data(ofc))[2] == 9, "U8Array.ofC");
  wiz_dec(ofc);
  wiz_val u32 = wiz_warray_set(wiz_u32array_empty(), wiz_out_nat(0), wiz_word_of_bits(wiz_out_nat(0)));
  wiz_dec(u32); /* an empty set stays empty */

  /* word maps: U64 keys to values, sorted when read back */
  wiz_val wm = wiz_wmap_empty();
  wm = wiz_wmap_insert(wm, wiz_word_of_bits(wiz_out_nat(7)), wiz_out_nat(70));
  wm = wiz_wmap_insert(wm, wiz_word_of_bits(wiz_out_nat(3)), wiz_out_nat(30));
  wm = wiz_wmap_insert(wm, wiz_word_of_bits(wiz_out_nat(7)), wiz_out_nat(71));
  check(nat_of(wiz_wmap_size(share(wm))) == 2, "WordMap.size");
  check(wiz_wmap_contains(share(wm), wiz_word_of_bits(wiz_out_nat(3))), "WordMap.contains");
  check(!wiz_wmap_contains(share(wm), wiz_word_of_bits(wiz_out_nat(4))), "WordMap.contains a missing key");
  wiz_val found = wiz_wmap_find(share(wm), wiz_word_of_bits(wiz_out_nat(7)));
  check(wiz_tag(found) == 1 && nat_of(wiz_field_at(found, WIZ_BOX(0))) == 71, "WordMap.find");
  wiz_val found_d = wiz_wmap_find_d(share(wm), wiz_word_of_bits(wiz_out_nat(8)), wiz_out_nat(88));
  check(nat_of(found_d) == 88, "WordMap.findD's default");
  wiz_val wlist = wiz_wmap_to_list(share(wm));
  check(list_len_is(wlist, 2), "WordMap.toList");
  wiz_dec(wlist);
  wiz_val erased = wiz_wmap_erase(share(wm), wiz_word_of_bits(wiz_out_nat(3)));
  check(nat_of(wiz_wmap_size(share(erased))) == 1, "WordMap.erase");
  wiz_dec(erased);
  wiz_dec(wm);

  /* intern tables: String -> id, in first-seen order */
  wiz_val it = wiz_itab_empty();
  wiz_val p = wiz_itab_intern(it, wiz_out_string("one"));
  wiz_val table = wiz_proj(p, 0);
  wiz_inc(table);
  uint64_t id = nat_of(wiz_field_at(share(p), WIZ_BOX(1)));
  wiz_dec(p);
  it = table;
  check(id == 0, "Internet.intern's first id");
  wiz_val p2 = wiz_itab_intern(it, wiz_out_string("two"));
  wiz_val table2 = wiz_proj(p2, 0);
  wiz_inc(table2);
  uint64_t id2 = nat_of(wiz_field_at(share(p2), WIZ_BOX(1)));
  wiz_dec(p2);
  it = table2;
  check(id2 == 1, "Internet.intern's second id");
  wiz_val dup = wiz_itab_intern(share(it), wiz_out_string("one"));
  wiz_val table3 = wiz_proj(dup, 0);
  wiz_inc(table3);
  uint64_t id3 = nat_of(wiz_field_at(share(dup), WIZ_BOX(1)));
  wiz_dec(dup);
  wiz_dec(it); /* the shared table: intern copied it, so drop the original */
  it = table3;
  check(id3 == 0, "Internet.intern of a known string keeps its id");
  check(nat_of(wiz_itab_size(share(it))) == 2, "Internet.size");
  wiz_val opt = wiz_itab_find(share(it), wiz_out_string("two"));
  check(wiz_tag(opt) == 1 && nat_of(wiz_field_at(opt, WIZ_BOX(0))) == 1, "Internet.find");
  wiz_val miss = wiz_itab_find(share(it), wiz_out_string("three"));
  check(wiz_tag(miss) == 0, "Internet.find of a missing string");
  wiz_dec(miss);
  wiz_val byid = wiz_itab_lookup(share(it), wiz_word_of_bits(wiz_out_nat(0)));
  check(strcmp(string_text(byid), "one") == 0, "Internet.lookup");
  wiz_dec(byid);
  wiz_val ilist = wiz_itab_to_list(share(it));
  check(list_len_is(ilist, 2), "Internet.toList");
  wiz_dec(ilist);
  wiz_val from = wiz_itab_of_list(cons(wiz_out_string("a"), cons(wiz_out_string("b"), WIZ_BOX(0))));
  check(nat_of(wiz_itab_size(share(from))) == 2, "Internet.ofList");
  wiz_dec(from);
  wiz_dec(it);

  /* a Wiz String is a list of Chars; its C string is UTF-8 */
  wiz_val s = wiz_out_string("aλ✓𝄞");
  check(strcmp(string_text(s), "aλ✓𝄞") == 0, "a String's C string (UTF-8)");
  char *back = wiz_in_string(s); /* consumes */
  check(strcmp(back, "aλ✓𝄞") == 0, "wiz_in_string");
  free(back);

  printf("text: ok\n");
  return WIZ_BOX(0);
}

int main(void) {
  int rc = wiz_run_main(entry, 0);
  if (wiz_corpus_failures) fprintf(stderr, "corpus: %d check(s) failed\n", wiz_corpus_failures);
  return wiz_corpus_failures ? 1 : rc;
}
