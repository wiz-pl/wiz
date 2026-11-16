/* CWE-134: the format string crosses a direct call. */
char *getenv(const char *name);
int printf(const char *fmt);

void logmsg(char *fmt) {
  printf(fmt);
  return;
}

int main(void) {
  char *fmt = getenv(0);
  logmsg(fmt);
  return 0;
}
