/* CWE-120 safe: the size argument is a compile-time literal, not the
   attacker-supplied length. The copy is bounded even though the source is
   attacker-controlled. */
int read(int fd, void *buf, unsigned long count);
void *memcpy(void *dst, const void *src, unsigned long n);

int main(void) {
  char src[64];
  char dst[16];
  read(0, src, 63);
  memcpy(dst, src, 16);
  return 0;
}
