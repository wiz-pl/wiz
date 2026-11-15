/* CWE-134 safe: a vprintf-style wrapper receives a literal format from every
   caller, and the value is an argument. Same call chain as cwe134/chain-unsafe.c
   with the format and the value separated. */
char *getenv(const char *name);
int vprintf(const char *fmt, void *ap);
int printf(const char *fmt, ...);

void log_value(char *fmt, char *value) {
  printf(fmt, value);
  return;
}

int main(void) {
  char *value = getenv("VALUE");
  log_value("%s\n", value);
  return 0;
}
