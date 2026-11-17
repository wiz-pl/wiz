/* CWE-121: the forbidden call is reported, but the destination array is a
   lowering boundary, so the case is detected and marked unknown. */
char *strcpy(char *dst, const char *src);

int main(void) {
  char dst[16];
  char *src = 0;
  strcpy(dst, src);
  return 0;
}
