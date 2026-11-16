/* external model: a tainted sprintf format is a format-string sink. */
char *getenv(const char *name);
int sprintf(char *dst, const char *fmt, ...);
int main(void) {
  char buf[64];
  char *fmt = getenv(0);
  sprintf(buf, fmt);
  return 0;
}
