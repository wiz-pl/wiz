/* Alias precision safe: two distinct destinations, one copy each, and the
   clean destination is the one used. Distinct stack slots must not meet in the
   points-to set. */
char *getenv(const char *name);
char *strncpy(char *dst, const char *src, unsigned long n);
int system(const char *command);

int main(void) {
  char a[32];
  char b[32];
  char *src = getenv("VALUE");
  strncpy(a, src, 31);
  strncpy(b, "true", 31);
  system(b);
  return 0;
}
