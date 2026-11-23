/* Quire's page seal (`extern "quire_seal"` + `link_c "quire_seal.c"`).

   `quire_seal(page, off)` is FNV-1a-64 over the page's bytes with the 8-byte checksum
   field at `off` read as zero, then writes the hash there. It takes and returns the Wiz
   `Bytes` value (one ownership pass-through), so the builder never copies the page.
   Doing this in C matters: a 4 KiB page is 4096 Wiz-level steps, which dominates a small
   commit.

   The C name deliberately has no `wiz_` prefix: the compiler emits an `extern` prototype
   for such a foreign name, so this file needs no header of its own. `wiz_val` is
   `uintptr_t`; the `Bytes` value is one word, so the arguments pass through unchanged.

   The page builder's last reference to the buffer is unique (Perceus), so the in-place
   write is the same in-place `Bytes` update the runtime itself makes. The purity is
   conditional on that: `seal` mutates the value it is handed and returns it, so a caller
   that seals a `Bytes` it still holds elsewhere would observe the change. Both call
   sites pass a page/record built on the spot (`QPage.make`, `QMeta.encode`); keep it
   that way. A buffer shorter than `off + 8` is returned unsealed (no fault): `pageSize`
   and the 96-byte meta are the sizes the writers use. The `wiz_bytes`
   layout is repeated here because a `link_c` file is compiled on its own, next to (not
   inside) the generated unit that includes `wiz_rt.h`. */
#include <stddef.h>
#include <stdint.h>

typedef struct {
  int64_t rc;
  uint32_t tag;
  uint32_t size;
} quire_hdr;

typedef struct {
  quire_hdr h;
  size_t len, cap;
  unsigned char *data;
} quire_bytes;

uintptr_t quire_seal(uintptr_t v, uint64_t off) {
  quire_bytes *b = (quire_bytes *)v;
  /* `off + 8` must not wrap: a wrapped window would read the wrong bytes as the
     checksum and, worse, pass the write guard below with a huge `off` (an
     out-of-bounds write into memory after the buffer). The module seals at 16 (page)
     and 88 (96-byte meta), but an `extern` is callable from anywhere. */
  if (off > UINT64_MAX - 8) return v;
  uint64_t end = off + 8;
  uint64_t h = 0xcbf29ce484222325ULL;
  for (uint64_t i = 0; i < b->len; i++) {
    unsigned char c = (i >= off && i < end) ? 0 : b->data[i];
    h ^= (uint64_t)c;
    h *= 0x100000001b3ULL;
  }
  if (b->len >= end) {
    for (int k = 0; k < 8; k++) b->data[off + k] = (unsigned char)(h >> (8 * k));
  }
  return v;
}
