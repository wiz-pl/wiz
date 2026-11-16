/* CWE-78: a store/load through a pointer is outside the register/def-use
   model at this commit (expect: unknown). */
char *getenv(const char *name);
int system(const char *command);

int main(void) {
  char *x = 0;
  char **p = &x;
  *p = getenv(0);
  system(*p);
  return 0;
}
