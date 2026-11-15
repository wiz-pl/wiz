/* The tree-sitter shim for scry (design §4.1).

   One call parses one source file and walks the tree with a `TSTreeCursor`,
   bulk-loading the result into a compact struct-of-arrays CST: no `TSNode` (or any
   other struct) ever crosses the FFI by value. The store is one `calloc` block, so
   the Wiz `foreign_type` finalizer is plain `free`.

   Columns, per node (ids are preorder: the root is 0):

     kind         compact kind id (first visit of a tree-sitter symbol assigns one)
     field        compact field id of the arc from its parent (0 = no field)
     flags        bit 0 named, bit 1 ERROR, bit 2 MISSING
     parent       parent id + 1 (0 = root)
     span         start_byte << 32 | end_byte
     first_child  first child id + 1 (0 = leaf)
     next_sibling next sibling id + 1 (0 = last)

   Edges: one per child arc, in child-id order, (parent, child, field id). The CSR
   columns `child_off`/`children`/`child_field` are the same arcs grouped by parent.

   Kind and field names are interned by the store: `kind_names[0 .. kind_count)` and
   `field_names[0 .. field_count)`; field id 0 is the empty name (no field). The names
   point into the grammar (static storage), so they need no freeing.

   The runtime ABI used here is the C interface of `lib/WordArray.wiz`
   (`wiz_warray_of_c`), documented in docs/stages/29-natives.md: one `wiz_val` is a
   `uintptr_t`, and a column becomes an owned `U32Array`/`U64Array` by copying it. */

#include <stdint.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "tree-sitter/lib/include/tree_sitter/api.h"

const TSLanguage *tree_sitter_c(void);

typedef uintptr_t wiz_val;
extern wiz_val wiz_warray_of_c(uint32_t width, const void *p, size_t n);

#define SCRY_MAX_NODES 0xFFFFFFF0u
#define SCRY_ERROR_SYMBOL ((TSSymbol)-1)

/* The returned store: a fixed header followed by every column in one allocation. */
typedef struct ScryStore {
  int ok;
  char err[512];
  uint64_t bytes;

  uint32_t n;    /* nodes */
  uint32_t m;    /* edges (child arcs) */
  uint32_t roots;
  uint32_t nk;   /* kind names */
  uint32_t nf;   /* field names (id 0 is "") */

  uint32_t *kind;
  uint32_t *field;
  uint32_t *flags;
  uint32_t *parent;
  uint32_t *first_child;
  uint32_t *next_sibling;
  uint64_t *span;

  uint32_t *child_off; /* n + 1 */
  uint32_t *children;  /* m */
  uint32_t *child_field;

  uint32_t *edge_src;
  uint32_t *edge_dst;
  uint32_t *edge_label;

  const char **kind_names;
  uint16_t *kind_symbols;
  const char **field_names;
  uint16_t *field_symbols;
} ScryStore;

/* Parse-time state, freed before `scry_parse` returns. */
typedef struct {
  uint32_t n;
  uint32_t nk;
  uint32_t nf;
  uint16_t *kind_symbols;
  size_t kind_cap;
  uint16_t *field_symbols;
  size_t field_cap;
  uint32_t *symbol_to_kind; /* 65536 entries, UINT32_MAX = not seen */
  uint32_t *field_to_id;    /* field_count + 1 entries, 0 = none */
} Builder;

static size_t align8(size_t x) {
  return (x + 7u) & ~(size_t)7u;
}

static void set_error(ScryStore *s, const char *what) {
  s->ok = 0;
  snprintf(s->err, sizeof s->err, "%s", what);
}

static uint32_t kind_id(Builder *b, TSSymbol sym) {
  uint32_t id = b->symbol_to_kind[sym];
  if (id != UINT32_MAX) return id;
  id = b->nk++;
  b->symbol_to_kind[sym] = id;
  if (b->nk > b->kind_cap) {
    size_t cap = b->kind_cap ? b->kind_cap * 2 : 32;
    uint16_t *p = (uint16_t *)realloc(b->kind_symbols, cap * sizeof(uint16_t));
    if (!p) return UINT32_MAX;
    b->kind_symbols = p;
    b->kind_cap = cap;
  }
  b->kind_symbols[id] = sym;
  return id;
}

static uint32_t field_id(Builder *b, TSFieldId field) {
  if (field == 0) return 0;
  uint32_t id = b->field_to_id[field];
  if (id != 0) return id;
  id = b->nf++;
  b->field_to_id[field] = id;
  if (b->nf > b->field_cap) {
    size_t cap = b->field_cap ? b->field_cap * 2 : 32;
    uint16_t *p = (uint16_t *)realloc(b->field_symbols, cap * sizeof(uint16_t));
    if (!p) return 0;
    b->field_symbols = p;
    b->field_cap = cap;
  }
  b->field_symbols[id] = field;
  return id;
}

/* Pass 1: assign the kind/field ids and count the nodes. */
static void count_walk(Builder *b, TSTreeCursor *cur) {
  TSNode node = ts_tree_cursor_current_node(cur);
  b->n++;
  kind_id(b, ts_node_symbol(node));
  field_id(b, ts_tree_cursor_current_field_id(cur));
  if (ts_tree_cursor_goto_first_child(cur)) {
    do { count_walk(b, cur); } while (ts_tree_cursor_goto_next_sibling(cur));
    ts_tree_cursor_goto_parent(cur);
  }
}

/* The block layout: header, then every column, with pointer/64-bit arrays aligned. */
typedef struct {
  size_t span, kind, field, flags, parent, first_child, next_sibling;
  size_t child_off, children, child_field;
  size_t edge_src, edge_dst, edge_label;
  size_t kind_names, kind_symbols;
  size_t field_names, field_symbols;
  size_t total;
} Layout;

static Layout layout_of(uint32_t n, uint32_t m, uint32_t nk, uint32_t nf) {
  Layout l;
  size_t off = align8(sizeof(ScryStore));
  l.span = off; off += (size_t)n * 8;
  l.kind = off; off += (size_t)n * 4;
  l.field = off; off += (size_t)n * 4;
  l.flags = off; off += (size_t)n * 4;
  l.parent = off; off += (size_t)n * 4;
  l.first_child = off; off += (size_t)n * 4;
  l.next_sibling = off; off += (size_t)n * 4;
  l.child_off = off; off += ((size_t)n + 1) * 4;
  l.children = off; off += (size_t)(m ? m : 1) * 4;
  l.child_field = off; off += (size_t)(m ? m : 1) * 4;
  l.edge_src = off; off += (size_t)(m ? m : 1) * 4;
  l.edge_dst = off; off += (size_t)(m ? m : 1) * 4;
  l.edge_label = off; off += (size_t)(m ? m : 1) * 4;
  l.kind_names = align8(off); off = l.kind_names + (size_t)(nk ? nk : 1) * sizeof(char *);
  l.kind_symbols = off; off += (size_t)(nk ? nk : 1) * 2;
  l.field_names = align8(off); off = l.field_names + (size_t)(nf ? nf : 1) * sizeof(char *);
  l.field_symbols = off; off += (size_t)(nf ? nf : 1) * 2;
  l.total = align8(off);
  return l;
}

/* Pass 2: fill the node columns of `s` (ids in the same preorder as pass 1). */
static void fill_walk(ScryStore *s, Builder *b, TSTreeCursor *cur, uint32_t parent_plus1) {
  uint32_t id = b->n++;
  TSNode node = ts_tree_cursor_current_node(cur);
  s->kind[id] = kind_id(b, ts_node_symbol(node));
  s->field[id] = field_id(b, ts_tree_cursor_current_field_id(cur));
  s->flags[id] = (ts_node_is_named(node) ? 1u : 0u)
    | (ts_node_is_error(node) ? 2u : 0u)
    | (ts_node_is_missing(node) ? 4u : 0u);
  s->parent[id] = parent_plus1;
  s->first_child[id] = 0;
  s->next_sibling[id] = 0;
  s->span[id] = ((uint64_t)ts_node_start_byte(node) << 32)
    | (uint64_t)ts_node_end_byte(node);

  if (ts_tree_cursor_goto_first_child(cur)) {
    uint32_t prev = 0;
    do {
      uint32_t child = b->n;
      fill_walk(s, b, cur, id + 1);
      if (prev == 0) s->first_child[id] = child + 1;
      else s->next_sibling[prev] = child + 1;
      prev = child;
    } while (ts_tree_cursor_goto_next_sibling(cur));
    ts_tree_cursor_goto_parent(cur);
  }
}

static void build_edges(ScryStore *s) {
  uint32_t *counts = (uint32_t *)calloc(s->n ? s->n : 1, sizeof(uint32_t));
  if (!counts) { set_error(s, "out of memory (child counts)"); return; }
  s->roots = 0;
  for (uint32_t i = 0; i < s->n; i++) {
    uint32_t p = s->parent[i];
    if (p == 0) s->roots++;
    else counts[p - 1]++;
  }
  s->m = s->n - s->roots;
  uint32_t sum = 0;
  for (uint32_t i = 0; i < s->n; i++) {
    s->child_off[i] = sum;
    sum += counts[i];
  }
  s->child_off[s->n] = sum;
  uint32_t *cursor = (uint32_t *)malloc(((size_t)s->n + 1) * sizeof(uint32_t));
  if (!cursor) { free(counts); set_error(s, "out of memory (child cursor)"); return; }
  memcpy(cursor, s->child_off, ((size_t)s->n + 1) * sizeof(uint32_t));
  uint32_t e = 0;
  for (uint32_t i = 0; i < s->n; i++) {
    uint32_t p = s->parent[i];
    if (p != 0) {
      uint32_t j = cursor[p - 1]++;
      s->children[j] = i;
      s->child_field[j] = s->field[i];
      s->edge_src[e] = p - 1;
      s->edge_dst[e] = i;
      s->edge_label[e] = s->field[i];
      e++;
    }
  }
  free(cursor);
  free(counts);
}

ScryStore *scry_parse(const char *lang, const char *src, uint64_t len) {
  /* An error store is still a valid, freeable block. */
  Layout empty = layout_of(0, 0, 1, 1);
  ScryStore *bad = (ScryStore *)calloc(1, empty.total);
  if (!bad) abort();
  bad->ok = 1;
  bad->kind_names = (const char **)((char *)bad + empty.kind_names);
  bad->kind_symbols = (uint16_t *)((char *)bad + empty.kind_symbols);
  bad->field_names = (const char **)((char *)bad + empty.field_names);
  bad->field_symbols = (uint16_t *)((char *)bad + empty.field_symbols);
  bad->kind_names[0] = "";
  bad->field_names[0] = "";

  if (!lang || strcmp(lang, "c") != 0) {
    set_error(bad, "unknown language (this shim has tree-sitter-c only)");
    return bad;
  }
  if (len > UINT32_MAX) {
    set_error(bad, "source file is larger than 2^32 - 1 bytes");
    return bad;
  }

  const TSLanguage *language = tree_sitter_c();
  Builder b;
  memset(&b, 0, sizeof b);
  b.nf = 1; /* field id 0 is the empty name */
  b.symbol_to_kind = (uint32_t *)malloc(65536 * sizeof(uint32_t));
  b.field_to_id = (uint32_t *)calloc(65536, sizeof(uint32_t));
  if (!b.symbol_to_kind || !b.field_to_id) {
    set_error(bad, "out of memory (intern maps)");
    free(b.symbol_to_kind); free(b.field_to_id);
    return bad;
  }
  for (uint32_t i = 0; i < 65536; i++) b.symbol_to_kind[i] = UINT32_MAX;

  TSParser *parser = ts_parser_new();
  if (!parser) {
    set_error(bad, "tree-sitter: cannot create a parser");
    free(b.symbol_to_kind); free(b.field_to_id);
    return bad;
  }
  if (!ts_parser_set_language(parser, language)) {
    set_error(bad, "tree-sitter: the grammar's ABI is not this runtime's");
    ts_parser_delete(parser);
    free(b.symbol_to_kind); free(b.field_to_id);
    return bad;
  }
  TSTree *tree = ts_parser_parse_string(parser, NULL, src, (uint32_t)len);
  if (!tree) {
    set_error(bad, "tree-sitter: parse returned no tree (out of memory)");
    ts_parser_delete(parser);
    free(b.symbol_to_kind); free(b.field_to_id);
    return bad;
  }

  TSTreeCursor cur = ts_tree_cursor_new(ts_tree_root_node(tree));
  count_walk(&b, &cur);
  if (b.n >= SCRY_MAX_NODES) {
    set_error(bad, "tree-sitter parse: more than 2^32 - 16 nodes");
    ts_tree_cursor_delete(&cur); ts_tree_delete(tree); ts_parser_delete(parser);
    free(b.kind_symbols); free(b.field_symbols);
    free(b.symbol_to_kind); free(b.field_to_id);
    return bad;
  }

  /* One node per arc except the root(s); count the roots after the parent pass, so
     allocate room for `n` edges (CSR rows are cheap; `m` is set exactly later). */
  Layout l = layout_of(b.n, b.n, b.nk, b.nf);
  ScryStore *s = (ScryStore *)calloc(1, l.total);
  if (!s) abort();
  s->ok = 1;
  s->bytes = len;
  s->n = b.n;
  s->nk = b.nk;
  s->nf = b.nf;
  s->span = (uint64_t *)((char *)s + l.span);
  s->kind = (uint32_t *)((char *)s + l.kind);
  s->field = (uint32_t *)((char *)s + l.field);
  s->flags = (uint32_t *)((char *)s + l.flags);
  s->parent = (uint32_t *)((char *)s + l.parent);
  s->first_child = (uint32_t *)((char *)s + l.first_child);
  s->next_sibling = (uint32_t *)((char *)s + l.next_sibling);
  s->child_off = (uint32_t *)((char *)s + l.child_off);
  s->children = (uint32_t *)((char *)s + l.children);
  s->child_field = (uint32_t *)((char *)s + l.child_field);
  s->edge_src = (uint32_t *)((char *)s + l.edge_src);
  s->edge_dst = (uint32_t *)((char *)s + l.edge_dst);
  s->edge_label = (uint32_t *)((char *)s + l.edge_label);
  s->kind_names = (const char **)((char *)s + l.kind_names);
  s->kind_symbols = (uint16_t *)((char *)s + l.kind_symbols);
  s->field_names = (const char **)((char *)s + l.field_names);
  s->field_symbols = (uint16_t *)((char *)s + l.field_symbols);

  for (uint32_t i = 0; i < b.nk; i++) {
    TSSymbol sym = b.kind_symbols[i];
    const char *name = ts_language_symbol_name(language, sym);
    if (!name) name = (sym == SCRY_ERROR_SYMBOL) ? "ERROR" : "<anonymous>";
    s->kind_names[i] = name;
    s->kind_symbols[i] = sym;
  }
  s->field_names[0] = "";
  s->field_symbols[0] = 0;
  for (uint32_t i = 1; i < b.nf; i++) {
    TSFieldId f = b.field_symbols[i];
    const char *name = ts_language_field_name_for_id(language, f);
    s->field_names[i] = name ? name : "";
    s->field_symbols[i] = f;
  }

  b.n = 0;
  fill_walk(s, &b, &cur, 0);
  ts_tree_cursor_delete(&cur);
  ts_tree_delete(tree);
  ts_parser_delete(parser);
  free(b.kind_symbols); free(b.field_symbols);
  free(b.symbol_to_kind); free(b.field_to_id);

  build_edges(s);
  if (!s->ok) {
    /* `build_edges` failed; the block is still freeable and `storeError` says why. */
  }
  return s;
}

/* ---- Scalars ------------------------------------------------------------ */

uint64_t scry_store_ok(ScryStore *s) { return (uint64_t)s->ok; }
const char *scry_store_error(ScryStore *s) { return s->err; }
uint64_t scry_store_bytes(ScryStore *s) { return s->bytes; }
uint64_t scry_node_count(ScryStore *s) { return s->n; }
uint64_t scry_edge_count(ScryStore *s) { return s->m; }
uint64_t scry_root_count(ScryStore *s) { return s->roots; }
uint64_t scry_kind_count(ScryStore *s) { return s->nk; }
uint64_t scry_field_count(ScryStore *s) { return s->nf; }

uint64_t scry_error_count(ScryStore *s) {
  uint64_t n = 0;
  for (uint32_t i = 0; i < s->n; i++) if (s->flags[i] & 6u) n++;
  return n;
}

const char *scry_kind_name(ScryStore *s, uint64_t id) {
  return id < s->nk ? s->kind_names[id] : "";
}
uint64_t scry_kind_symbol(ScryStore *s, uint64_t id) {
  return id < s->nk ? (uint64_t)s->kind_symbols[id] : 0;
}
const char *scry_field_name(ScryStore *s, uint64_t id) {
  return id < s->nf ? s->field_names[id] : "";
}
uint64_t scry_field_symbol(ScryStore *s, uint64_t id) {
  return id < s->nf ? (uint64_t)s->field_symbols[id] : 0;
}

/* ---- Columns (owned Wiz word arrays) ------------------------------------ */

wiz_val scry_kind_column(ScryStore *s) {
  return wiz_warray_of_c(4, s->kind, s->n);
}
wiz_val scry_field_column(ScryStore *s) {
  return wiz_warray_of_c(4, s->field, s->n);
}
wiz_val scry_flags_column(ScryStore *s) {
  return wiz_warray_of_c(4, s->flags, s->n);
}
wiz_val scry_parent_column(ScryStore *s) {
  return wiz_warray_of_c(4, s->parent, s->n);
}
wiz_val scry_span_column(ScryStore *s) {
  return wiz_warray_of_c(8, s->span, s->n);
}
wiz_val scry_first_child_column(ScryStore *s) {
  return wiz_warray_of_c(4, s->first_child, s->n);
}
wiz_val scry_next_sibling_column(ScryStore *s) {
  return wiz_warray_of_c(4, s->next_sibling, s->n);
}
wiz_val scry_child_off_column(ScryStore *s) {
  return wiz_warray_of_c(4, s->child_off, (size_t)s->n + 1);
}
wiz_val scry_children_column(ScryStore *s) {
  return wiz_warray_of_c(4, s->children, s->m);
}
wiz_val scry_child_field_column(ScryStore *s) {
  return wiz_warray_of_c(4, s->child_field, s->m);
}
wiz_val scry_edge_src_column(ScryStore *s) {
  return wiz_warray_of_c(4, s->edge_src, s->m);
}
wiz_val scry_edge_dst_column(ScryStore *s) {
  return wiz_warray_of_c(4, s->edge_dst, s->m);
}
wiz_val scry_edge_label_column(ScryStore *s) {
  return wiz_warray_of_c(4, s->edge_label, s->m);
}
