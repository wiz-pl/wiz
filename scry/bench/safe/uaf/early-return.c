/* CWE-416 safe: the object is freed only on the error path that returns, so
   the success path never sees a dangling pointer. The branches are CFG
   exclusive, not merely condition exclusive. */
void *malloc(unsigned long n);
void free(void *p);

int use(char *p) {
  if (p == 0) {
    return 1;
  }
  return p[0];
}

int main(void) {
  char *p = malloc(16);
  if (p == 0) {
    return 1;
  }
  if (p[0] == 0) {
    free(p);
    return 2;
  }
  int v = use(p);
  free(p);
  return v;
}
