/* buffer content: the formatted destination is a format string at printf; the rule
   fires on the buffer's content, not on a direct argument. */
char *getenv(const char *name);
int sprintf(char *dst, const char *fmt, ...);
int printf(const char *fmt, ...);
int main(void) {
  char buf[64];
  char *t = getenv(0);
  sprintf(buf, "%s", t);
  printf(buf);
  return 0;
}
