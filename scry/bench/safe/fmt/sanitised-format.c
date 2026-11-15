/* CWE-134 safe: a policy model returns a format string with no conversions.
   The result is a sanitised format, so printf may use it as argument 0. */
char *getenv(const char *name);
char *sanitize_format(const char *s);
int printf(const char *fmt, ...);

int main(void) {
  char *fmt = getenv("FORMAT");
  char *safe = sanitize_format(fmt);
  printf(safe);
  return 0;
}
