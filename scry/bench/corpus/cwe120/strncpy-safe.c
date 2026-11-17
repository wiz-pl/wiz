/* CWE-120: the bounded copy is not in the forbidden set. */
char *strncpy(char *dst, const char *src, unsigned long n);

int main(void) {
  char *dst = 0;
  char *src = 0;
  strncpy(dst, src, 0);
  return 0;
}
