/* external model: sprintf formats its variadic argument into the destination, so the
   destination carries the taint even though the format string is constant. */
char *getenv(const char *name);
int system(int command);
int sprintf(char *dst, const char *fmt, ...);
int main(void) {
  char buf[64];
  char *t = getenv(0);
  sprintf(buf, "%s", t);
  system(buf[0]);
  return 0;
}
