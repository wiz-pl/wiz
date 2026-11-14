/* CWE-134: the attacker-controlled value is the format string. */
char *getenv(const char *name);
int printf(const char *fmt);

int main(void) {
  char *fmt = getenv(0);
  printf(fmt);
  return 0;
}
