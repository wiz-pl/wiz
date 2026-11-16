/* CWE-120 CWE-121 safe: a literal is copied into a buffer that is known to be
   large enough. The blanket strcpy rule fires on the call, not on the data. */
int system(const char *command);

int main(void) {
  char dst[32];
  char *strcpy(char *d, const char *s);
  strcpy(dst, "/bin/true");
  system("/bin/true");
  return 0;
}
