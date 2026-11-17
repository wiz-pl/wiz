/* CWE-125 control: the count is checked against the source size before the copy. */
void *memcpy(void *dst, const void *src, unsigned long n);
char *getenv(const char *name);

int main(void) {
  char *arg = getenv("LEN");
  unsigned long n = arg[0];
  unsigned long cap = 16;
  char src[16];
  char dst[32];

  if (n > cap)
    return 1;
  memcpy(dst, src, n);
  return dst[0];
}
