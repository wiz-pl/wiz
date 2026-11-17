/* CWE-787: a heap array indexed by attacker-controlled data. `malloc(32)` is four
   analysis cells; the index is a byte read from getenv's string, and there is no bound
   check before the store. */
int *malloc(unsigned long size);
char *getenv(const char *name);

int main(void) {
  char *arg = getenv("IDX");
  int i = arg[0];
  int *a = malloc(32);

  a[i] = 7;
  return a[0];
}
