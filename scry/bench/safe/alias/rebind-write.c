/* Alias precision: the copy runs while p points at `a`; `b` is initialised
   separately and p is re-bound to it only afterwards. A flow-insensitive
   points-to set unions a and b, so the copy's store taints b too. */
char *getenv(const char *name);
char *strncpy(char *dst, const char *src, unsigned long n);
int system(const char *command);

int main(void) {
  char a[32];
  char b[32];
  b[0] = 'x';
  b[1] = 0;
  char *p = a;
  strncpy(p, getenv("NAME"), 31);
  p = b;
  system(b[0]);
  return 0;
}
