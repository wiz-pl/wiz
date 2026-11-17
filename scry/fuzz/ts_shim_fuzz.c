/* libFuzzer target for scry's C front end (native/ts_shim.c).

   The fuzzer feeds arbitrary bytes to `scry_parse("c", …)` and checks the
   struct-of-arrays contract that the Wiz side reads:

     * ids are in range and preorder (a parent id is smaller than its child's);
     * the root is unique and every non-root node has a parent;
     * child CSR rows, first-child/next-sibling links and the edge arrays agree;
     * spans are ordered byte ranges inside the input;
     * kind/field ids and the intern tables agree;
     * ERROR/MISSING flags are the only flag bits, and error counts match.

   A violation aborts with a `SCRY-FUZZ INVARIANT` line that includes the
   offending node's input byte offset.  `fuzz-span` maps that offset to the
   smallest CST node that contains it, so a minimised artifact is reported with
   the same `start`/`stop` span shape as the static findings.

   This file includes ts_shim.c in the same translation unit so the harness can
   inspect the store directly; it is not linked a second time.  `wiz_warray_of_c`
   is only needed to link the column accessors, which this target does not call:
   the fuzzer tests the shim's own columns, not the Wiz array copy. */

#include <stdint.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "../native/ts_shim.c"

/* The column accessors in ts_shim.c refer to this runtime symbol.  The target
   never calls them; returning NULL keeps the linker happy without pretending to
   be the runtime's owned-array implementation. */
uintptr_t wiz_warray_of_c(uint32_t width, const void *p, size_t n) {
  (void)width; (void)p; (void)n;
  return 0;
}

#define MAX_INPUT (1u << 20)

static void invariant_fail(const char *what, uint32_t node, uint64_t offset) {
  fprintf(stderr,
    "SCRY-FUZZ INVARIANT: %s (node=%u, input_offset=%llu)\n",
    what, node, (unsigned long long)offset);
  abort();
}

static void check_node(ScryStore *s, uint32_t i, uint64_t len) {
  uint64_t start = s->span[i] >> 32;
  uint64_t stop = s->span[i] & 0xffffffffu;

  if (s->kind[i] >= s->nk)
    invariant_fail("kind id out of range", i, start);
  if (s->field[i] >= s->nf)
    invariant_fail("field id out of range", i, start);
  if ((s->flags[i] & ~7u) != 0)
    invariant_fail("unknown flag bit", i, start);
  if (s->parent[i] > i)
    invariant_fail("parent id is not smaller than the child", i, start);
  if (i == 0 && s->parent[i] != 0)
    invariant_fail("root has a parent", i, start);
  if (i != 0 && s->parent[i] == 0)
    invariant_fail("non-root node has no parent", i, start);

  if (start > stop || stop > len)
    invariant_fail("span is not inside the input", i, start);

  if (s->first_child[i] > s->n)
    invariant_fail("first-child id out of range", i, start);
  if (s->next_sibling[i] > s->n)
    invariant_fail("next-sibling id out of range", i, start);

  if (s->first_child[i] != 0) {
    uint32_t c = s->first_child[i] - 1;
    if (c <= i || s->parent[c] != i + 1)
      invariant_fail("first child is not a child", i, start);
  }
  if (s->next_sibling[i] != 0) {
    uint32_t n = s->next_sibling[i] - 1;
    if (n <= i || n >= s->n || s->parent[n] != s->parent[i])
      invariant_fail("next sibling has a different parent", i, start);
  }

  if (s->child_off[i] > s->child_off[i + 1])
    invariant_fail("child CSR is not monotone", i, start);
}

static void check_store(ScryStore *s, uint64_t len) {
  uint32_t i, e;
  uint64_t errors = 0;

  if (s->n == 0)
    invariant_fail("empty store", 0, 0);
  if (s->roots == 0 || s->roots > s->n)
    invariant_fail("bad root count", 0, 0);
  if ((uint64_t)s->m + (uint64_t)s->roots != (uint64_t)s->n)
    invariant_fail("node/edge/root counts disagree", 0, 0);
  if (s->nk == 0 || s->nf == 0)
    invariant_fail("empty intern table", 0, 0);
  if (s->child_off[0] != 0 || s->child_off[s->n] != s->m)
    invariant_fail("child CSR endpoints disagree with the edge count", 0, 0);

  for (i = 0; i < s->nk; i++) {
    if (!s->kind_names[i]) invariant_fail("null kind name", i, 0);
  }
  for (i = 0; i < s->nf; i++) {
    if (!s->field_names[i]) invariant_fail("null field name", i, 0);
  }

  for (i = 0; i < s->n; i++) {
    uint32_t j;
    check_node(s, i, len);
    if (s->flags[i] & 6u) errors++;
    for (j = s->child_off[i]; j < s->child_off[i + 1]; j++) {
      uint32_t c = s->children[j];
      if (c >= s->n || s->parent[c] != i + 1)
        invariant_fail("CSR child is not a child", i, s->span[i] >> 32);
      if (s->child_field[j] >= s->nf)
        invariant_fail("CSR field id out of range", i, s->span[i] >> 32);
      if (s->child_field[j] != s->field[c])
        invariant_fail("CSR field disagrees with the child", i, s->span[i] >> 32);
    }
  }

  {
    uint32_t dst = 0;
    for (e = 0; e < s->m; e++) {
      uint32_t src;
      while (dst < s->n && s->parent[dst] == 0) dst++;
      if (dst >= s->n || s->edge_dst[e] != dst)
        invariant_fail("edge order disagrees with the non-root node order", 0, 0);
      src = s->edge_src[e];
      if (src >= s->n || s->parent[dst] != src + 1)
        invariant_fail("edge does not follow a parent arc", src, 0);
      if (s->edge_label[e] != s->field[dst])
        invariant_fail("edge label disagrees with the child field", src, 0);
      dst++;
    }
  }

  if (errors != scry_error_count(s))
    invariant_fail("error count disagrees with the flags", 0, 0);
}

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
  ScryStore *s;
  char *src;

  if (size > MAX_INPUT) return 0;

  src = (char *)malloc(size ? size : 1);
  if (!src) abort();
  if (size) memcpy(src, data, size);

  s = scry_parse("c", src, (uint64_t)size);
  if (!s) {
    free(src);
    abort();
  }
  if (!s->ok) {
    if (!s->err[0]) invariant_fail("failed parse without an error message", 0, 0);
  } else {
    check_store(s, (uint64_t)size);
  }
  free(s);
  free(src);
  return 0;
}
