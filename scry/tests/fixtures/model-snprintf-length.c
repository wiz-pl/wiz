/* external model: snprintf's size argument (1) is a length sink; a tainted bound is a
   buffer-overflow finding even when the format is constant. */
char *getenv(const char *name);
int snprintf(char *dst, unsigned long n, const char *fmt, ...);
int main(void) {
  char buf[64];
  char *n = getenv(0);
  snprintf(buf, n, "%s", "x");
  return 0;
}
