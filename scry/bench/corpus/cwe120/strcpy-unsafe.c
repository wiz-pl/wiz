/* CWE-120: strcpy does not bound the copy. */
char *strcpy(char *dst, const char *src);

int main(void) {
  char *dst = 0;
  char *src = 0;
  strcpy(dst, src);
  return 0;
}
