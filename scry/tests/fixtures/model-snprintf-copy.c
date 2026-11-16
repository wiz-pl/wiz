/* external model: snprintf's formatted arguments are copied into the destination; the
   explicit bound is clean, so there is no length finding. */
char *getenv(const char *name);
int system(int command);
int snprintf(char *dst, unsigned long n, const char *fmt, ...);
int main(void) {
  char buf[64];
  char *t = getenv(0);
  snprintf(buf, 63, "%s", t);
  system(buf[0]);
  return 0;
}
