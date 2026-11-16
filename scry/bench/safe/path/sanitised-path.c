/* CWE-22 safe: a policy sanitiser removes traversal components before the
   path reaches the file API. */
char *getenv(const char *name);
char *sanitize_path(const char *s);
void *fopen(const char *path, const char *mode);

int main(void) {
  char *name = getenv("FILE");
  char *safe = sanitize_path(name);
  fopen(safe, "r");
  return 0;
}
