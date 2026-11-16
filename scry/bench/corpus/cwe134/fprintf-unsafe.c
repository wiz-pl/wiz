/* CWE-134: fprintf's format string is argument 1 in the default pack. */
typedef void FILE;
char *getenv(const char *name);
int fprintf(FILE *stream, const char *fmt);

int main(void) {
  char *fmt = getenv(0);
  FILE *out = 0;
  fprintf(out, fmt);
  return 0;
}
