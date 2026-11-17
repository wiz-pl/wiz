/* CWE-125 control: the read is guarded by `i < 4`, the capacity of the four-cell
   allocation. */
int *malloc(unsigned long size);
char *getenv(const char *name);

int main(void) {
  char *arg = getenv("IDX");
  int i = arg[0];
  int *a = malloc(32);

  if (i >= 4)
    return 1;
  return a[i];
}
