/* CWE-787 safe: a project clamp helper bounds the wire length before the next
   read. The helper returns its argument on one path, so the interprocedural
   summary taints the result; the default pack trusts clamp_len as a bounds
   sanitiser. */
int read(int fd, void *buf, unsigned long count);

unsigned long clamp_len(unsigned long n, unsigned long max) {
  if (n > max) {
    return max;
  }
  return n;
}

int main(void) {
  char lenbuf[16];
  char dst[64];
  read(0, lenbuf, 15);
  unsigned long n = lenbuf[0];
  read(0, dst, clamp_len(n, 63));
  return 0;
}
