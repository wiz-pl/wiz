/* ---- storage: a read-only `mmap` of the store's file (storage plan, slice 3) ----

   The read path of the storage engine (`drafts/storage-engine/Mmap.wiz`): pages are
   read in place through a read-only mapping, so a snapshot is a page number plus this
   handle and a page read is a load, not a syscall and a copy.

   * `wiz_store_mmap_ro` maps `PROT_READ | MAP_SHARED`, clamped to the file's size:
     mapping past the end would `SIGBUS` on the first read there. `len == 0` and a
     failed `fstat`/`mmap` are an error (`NULL`, `wiz_sys_err`). The descriptor may be
     closed afterwards: the mapping holds the inode.
   * Writes never go through the mapping. The commit path is `pwrite` + `fsync` (the
     durable slice), so the mapping is read-only, there are no dirty pages to write
     back and `msync` is not needed. Never truncate a file under a live mapping: a
     snapshot keeps the old inode through compaction's rename instead.
   * `wiz_store_get_u64` is the wide, unaligned load (the format is little-endian). It
     does not bounds-check: the callers use it only inside a page they have bounded.
     `wiz_store_get_u64_at` does bounds-check and returns `Option U64` (`none` outside
     the mapping), so a bad page number or offset is an error, never a fault.
   * `wiz_store_map_free` is the `foreign_type Map` finalizer (`munmap`). */

#include <sys/mman.h>

typedef struct {
  void *addr;
  size_t len;
} wiz_store_map;

WIZ_API void *wiz_store_mmap_ro(void *p, uint64_t len) {
  wiz_sys_fdh *h = (wiz_sys_fdh *)p;
  if (!h || h->fd < 0) { wiz_sys_err = EBADF; return NULL; }
  struct stat st;
  if (fstat(h->fd, &st) != 0) { wiz_sys_err = errno; return NULL; }
  if (st.st_size <= 0) { wiz_sys_err = EINVAL; return NULL; }
  uint64_t size = (uint64_t)st.st_size;
  if (len > size) len = size; /* never map past the end (SIGBUS) */
  if (len == 0) { wiz_sys_err = EINVAL; return NULL; }
  void *a = mmap(NULL, (size_t)len, PROT_READ, MAP_SHARED, h->fd, 0);
  if (a == MAP_FAILED) { wiz_sys_err = errno; return NULL; }
  wiz_store_map *m = (wiz_store_map *)wiz_xmalloc(sizeof *m);
  m->addr = a;
  m->len = (size_t)len;
  wiz_sys_err = 0;
  return m;
}

WIZ_API void wiz_store_map_free(void *p) {
  wiz_store_map *m = (wiz_store_map *)p;
  if (!m) return; /* `mmap` failed and `Sys.check` turned it into an error value */
  if (m->addr) munmap(m->addr, m->len);
  free(m);
}

WIZ_API uint64_t wiz_store_map_len(void *p) { return (uint64_t)((wiz_store_map *)p)->len; }

/* the little-endian u64 at p (unaligned: memcpy, no cast) */
static uint64_t wiz_store_le64(const unsigned char *p) {
  return (uint64_t)p[0] | ((uint64_t)p[1] << 8) | ((uint64_t)p[2] << 16) |
         ((uint64_t)p[3] << 24) | ((uint64_t)p[4] << 32) | ((uint64_t)p[5] << 40) |
         ((uint64_t)p[6] << 48) | ((uint64_t)p[7] << 56);
}

/* no bounds check: the caller checked `off + 8 <= Map.len`. The result is a Wiz `U64`
   value, not a raw C integer: a `UIntN 64` is kind `w` at the FFI boundary (a scalar or
   a raw box), while `UInt64`/`Nat` are the raw-word kinds. */
WIZ_API wiz_val wiz_store_get_u64(void *p, uint64_t off) {
  wiz_store_map *m = (wiz_store_map *)p;
  return wiz_word_out(wiz_store_le64((const unsigned char *)m->addr + off));
}

/* the safe load: none unless all eight bytes are inside the mapping */
WIZ_API wiz_val wiz_store_get_u64_at(void *p, uint64_t off) {
  wiz_store_map *m = (wiz_store_map *)p;
  if (!m || off > (uint64_t)m->len || (uint64_t)m->len - off < 8) return WIZ_BOX(0);
  wiz_val fs[1] = {wiz_word_out(wiz_store_le64((const unsigned char *)m->addr + off))};
  return wiz_con(1, 1, fs);
}
