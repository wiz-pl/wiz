/* CWE-190: this C lowering folds malloc/calloc into Wil.alloc, which does not keep the
   size expression, so the allocation-size sink cannot fire. The case is an explicit
   coverage probe, not a silent miss. */
int getenv(const char *name);
void *malloc(int n);

int main(void) {
  int n = getenv(0);
  void *p = malloc(n);
  return 0;
}
