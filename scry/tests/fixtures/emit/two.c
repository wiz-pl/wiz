/* emit/two.c: the same rule in a different function -- a "new" finding when
   emit/one.c is the baseline. */
char *getenv(const char *name);
int system(const char *command);

int run(void) {
  char *arg = getenv(1);
  system(arg);
  return 0;
}
