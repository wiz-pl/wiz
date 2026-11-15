/* CWE-134 safe: the attacker value is an printf argument, the format string is
   a literal. This is the same source with the sink argument moved. */
char *getenv(const char *name);
int printf(const char *fmt, ...);

int main(void) {
  char *msg = getenv("GREETING");
  printf("%s\n", msg);
  return 0;
}
