/* CWE-190 safe in intent: the wire length is checked before it reaches the
   allocation. malloc is lowered to Wil.alloc, so the size sink cannot fire in
   the C pipeline today; this case is the coverage probe for that gap. */
int read(int fd, void *buf, unsigned long count);
void *malloc(unsigned long n);

int main(void) {
  char lenbuf[16];
  read(0, lenbuf, 15);
  unsigned long n = lenbuf[0];
  if (n > 0) {
    if (n <= 4096) {
      char *p = malloc(n);
      if (p != 0) {
        p[0] = 0;
      }
    }
  }
  return 0;
}
