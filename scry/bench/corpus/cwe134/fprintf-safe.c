/* CWE-134: the fprintf format string is constant. */
typedef void FILE;
char *getenv(const char *name);
int fprintf(FILE *stream, const char *fmt);

int main(void) {
  char *s = getenv(0);
  char *fmt = 0;
  FILE *out = 0;
  fprintf(out, fmt, s);
  return 0;
}
