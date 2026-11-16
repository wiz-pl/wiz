/* CWE-787 control: the same heap store with an explicit `i < 4` check on the path.
   The allocation is four cells, so the dominating branch proves the index in range. */
int *malloc(unsigned long size);
char *getenv(const char *name);

int main(void) {
  char *arg = getenv("IDX");
  int i = arg[0];
  int *a = malloc(32);

  if (i >= 4)
    return 1;
  a[i] = 7;
  return a[0];
}
