/* droste.c-style recovery fixture: same generated C++-guard shape, with a
 * struct field destination (the `b->str + b->used` pattern in both generated
 * projects). The one top-level ERROR holds every function below; the unit must
 * still be lowered and must report the recovered strcpy calls.
 */
#ifdef __cplusplus
extern "C" {
#endif

struct str_builder {
  char *str;
  size_t used;
  size_t capacity;
};

static void str_builder_str(struct str_builder *b, const char *s) {
  strcpy(b->str + b->used, s);
}

static char *strconcat(const char *src_fragments[]) {
  const char **p;
  char *src = (char*) malloc(1);
  size_t n = 0;
  for (p = src_fragments; *p; p++) {
    strcpy(src + n, *p);
    n += strlen(*p);
  }
  return src;
}
