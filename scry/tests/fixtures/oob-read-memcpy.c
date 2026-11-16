/* CWE-125: a copy length from attacker data reads past a 16-byte source. memcpy's
   source is argument 1 and its count is argument 2. */
void *memcpy(void *dst, const void *src, unsigned long n);
char *getenv(const char *name);

int main(void) {
  char *arg = getenv("LEN");
  unsigned long n = arg[0];
  char src[16];
  char dst[32];

  memcpy(dst, src, n);
  return dst[0];
}
