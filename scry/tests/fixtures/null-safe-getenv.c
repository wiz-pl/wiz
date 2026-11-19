/* CWE-476 fixed: an early return on the NULL path kills the null value. */
char *getenv(const char *name);

int main(void) {
  char *p = getenv("HOME");
  if (p == 0)
    return 1;
  return *p;
}
