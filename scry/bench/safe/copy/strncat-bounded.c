/* CWE-120 safe: the append is bounded by the space left in the destination.
   Same strcat shape as cwe120/strcat-unsafe.c, with the size argument. */
char *getenv(const char *name);
unsigned long strlen(const char *s);
char *strncat(char *dst, const char *src, unsigned long n);

int main(void) {
  char dst[64];
  char *src = getenv("SUFFIX");
  strncat(dst, src, 63 - strlen(dst));
  return 0;
}
