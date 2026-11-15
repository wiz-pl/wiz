/* CWE-134: the tainted value is an argument, not the format string. */
char *getenv(const char *name);
int printf(const char *fmt);

int main(void) {
  char *s = getenv(0);
  char *fmt = 0;
  printf(fmt, s);
  return 0;
}
