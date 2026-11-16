/* CWE-22: an explicit confinement sanitiser cleans the path. */
typedef void FILE;
char *getenv(const char *name);
char *sanitize_path(const char *path);
FILE *fopen(const char *path, const char *mode);

int main(void) {
  char *raw = getenv(0);
  char *path = sanitize_path(raw);
  FILE *f = fopen(path, "r");
  return 0;
}
