/* old-wizard.c-style recovery fixture.
 *
 * The C++ guard is valid C-preprocessor input but not valid C, so tree-sitter-c
 * recovers by wrapping every following declaration in one top-level ERROR node.
 * Lowering only `translation_unit`'s direct children would find no function at
 * all and report an empty unit; the recovered functions and their strcpy calls
 * must survive.
 */
#ifdef __cplusplus
extern "C" {
#endif

static char *strclone(const char *str) {
  size_t size = strlen(str) + 1;
  char *copy = (char*) malloc(size);
  if (copy == NULL) {
    return NULL;
  }
  memcpy(copy, str, size);
  return copy;
}

static void str_builder_str(char *dst, const char *s) {
  strcpy(dst, s);
}

static char *strconcat(const char *src_fragments[]) {
  size_t src_len = 0;
  const char **p;

  for (p = src_fragments; *p; p++) {
    src_len += strlen(*p);
  }

  char *src = (char*) malloc(src_len + 1);
  size_t n = 0;
  for (p = src_fragments; *p; p++) {
    strcpy(src + n, *p);
    n += strlen(*p);
  }

  return src;
}
