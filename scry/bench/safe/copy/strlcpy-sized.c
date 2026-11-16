/* CWE-120 safe: strlcpy takes the destination size, so the copy cannot run
   past the buffer. Not in the forbidden call set. */
char *getenv(const char *name);
unsigned long strlcpy(char *dst, const char *src, unsigned long size);

int main(void) {
  char dst[32];
  char *src = getenv("NAME");
  strlcpy(dst, src, sizeof(dst));
  return 0;
}
