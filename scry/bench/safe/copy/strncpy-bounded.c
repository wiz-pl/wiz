/* CWE-120 safe: a bounded copy with the terminator written explicitly. The
   bounded alternative is not the forbidden strcpy/strcat pair. */
char *getenv(const char *name);
char *strncpy(char *dst, const char *src, unsigned long n);

int main(void) {
  char dst[32];
  char *src = getenv("NAME");
  strncpy(dst, src, 31);
  dst[31] = 0;
  return 0;
}
