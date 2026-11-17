/* The size trap: malloc's size is a runtime value, so the analysis must not claim a
   capacity. The access is reported as an `unknown-memory` boundary, not a finding. */
int *malloc(unsigned long size);
char *getenv(const char *name);

int main(void) {
  char *arg = getenv("LEN");
  unsigned long n = arg[0];
  int *a = malloc(n);
  int i = arg[0];

  a[i] = 7;
  return a[0];
}
