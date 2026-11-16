/* CWE-120 safe in intent: the wire length is clamped to the buffer size
   before snprintf. The clamp is a branch, not a sanitiser result, so a
   flow-insensitive length rule keeps the tainted value. */
int read(int fd, void *buf, unsigned long count);
int snprintf(char *dst, unsigned long n, const char *fmt, ...);

int main(void) {
  char lenbuf[16];
  char src[256];
  char dst[64];
  read(0, lenbuf, 15);
  read(0, src, 255);
  unsigned long n = lenbuf[0];
  if (n > 63) {
    n = 63;
  }
  snprintf(dst, n, "%s", src);
  return 0;
}
