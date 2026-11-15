/* CWE-120/134 safe: the destination is size-limited and both format strings
   are literals. The copy effect still taints the buffer, but the buffer is only
   printed through a literal format. */
char *getenv(const char *name);
int snprintf(char *dst, unsigned long n, const char *fmt, ...);
int fprintf(void *stream, const char *fmt, ...);

int main(void) {
  char buf[64];
  char *s = getenv("USER");
  snprintf(buf, sizeof(buf), "%s", s);
  fprintf(0, "%s\n", buf);
  return 0;
}
