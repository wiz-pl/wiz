/* CWE-134: syslog's format string is argument 1. */
char *getenv(const char *name);
void syslog(int priority, const char *fmt);

int main(void) {
  char *fmt = getenv(0);
  syslog(3, fmt);
  return 0;
}
