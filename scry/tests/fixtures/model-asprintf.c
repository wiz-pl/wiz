/* asprintf/easprintf fill their output pointer; a later vfprintf sees the taint. */
char *getenv(const char *name);
char *easprintf(char **strp, const char *fmt, ...);
int vfprintf(void *stream, const char *format, ...);

int main(void) {
  char *f;
  easprintf(&f, "%s", getenv("X"));
  vfprintf(0, f, 0);
  return 0;
}
