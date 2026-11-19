/* CWE-476: getenv's result is dereferenced without a NULL check. */
char *getenv(const char *name);

int main(void) {
  char *p = getenv("HOME");
  return *p;
}
